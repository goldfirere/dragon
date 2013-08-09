Require Import Arith.
Require Import List.
Require Import Program.
Require Import Specif.
Require Import LibVar.
Require Import ListSet.
Require Import LibTactics.

Require Import type coercion utils subst co_kind var tactics compose ty_kind.
Require Import subset.

Set Implicit Arguments.

Inductive mapping : ctxt -> coercion -> var -> type -> type -> Type :=
| mkMapping : forall Si g f lhs target, Si |-co g ~: TFun f lhs ~~ target
                                      -> mapping Si g f lhs target.

Inductive substn Si : list (var * type) -> nat -> Type :=
| nilSubst : substn Si nil 0
| consSubst : forall g f lhs target dom n,
                mapping Si g f lhs target -> 
                substn Si dom n ->
                substn Si ((f, lhs) :: dom) (n + size_of_co g).

Lemma push_domelt_eq : forall A f ty (a b : A),
  (if domelt_eq_decide (f,ty) (f,ty)
  then a else b) = a.
Proof.
  intros. destruct (domelt_eq_decide (f, ty) (f, ty)) as [ Heq | Hneq ].
  - auto.
  - specialize (Hneq eq_refl). contradiction.
Qed.

Inductive wrapped_type : Type :=
| wTBVar : nat -> wrapped_type
| wTFun : var -> wrapped_type -> wrapped_type
| wTArrow : wrapped_type -> wrapped_type -> wrapped_type
| wTTycon : var -> wrapped_type
| wTApp : wrapped_type -> wrapped_type -> wrapped_type
| wWrap : type -> wrapped_type.

Fixpoint wrap (t : type) : wrapped_type :=
  match t with
    | TBVar n => wTBVar n
    | TFun f ty => wTFun f (wrap ty)
    | TArrow arg res => wTArrow (wrap arg) (wrap res)
    | TTycon T => wTTycon T
    | TApp t1 t2 => wTApp (wrap t1) (wrap t2)
  end.

Fixpoint unwrap (wt : wrapped_type) : type :=
  match wt with
    | wTBVar n => TBVar n
    | wTFun f ty => TFun f (unwrap ty)
    | wTArrow arg res => TArrow (unwrap arg) (unwrap res)
    | wTTycon T => TTycon T
    | wTApp t1 t2 => TApp (unwrap t1) (unwrap t2)
    | wWrap t => t
  end.

Definition domelt_eq_decide_w (d1 d2 : var * wrapped_type) : decide (d1 = d2).
  unfold decide. repeat decide equality; apply var_eq_decide.
Qed.

Lemma wrap_inj : forall t1 t2,
  wrap t1 = wrap t2 -> t1 = t2.
Proof.
  induction t1; destruct t2; introv Heq; simpls; inverts Heq; auto.
  - apply IHt1 in H1. subst. auto.
  - apply IHt1_1 in H0. apply IHt1_2 in H1. subst. auto.
  - apply IHt1_1 in H0. apply IHt1_2 in H1. subst. auto.
Qed.

Lemma wrap_neq : forall (f1 f2 : var) lhs1 lhs2,
  (f1, lhs1) <> (f2, lhs2) -> (f1, wrap lhs1) <> (f2, wrap lhs2).
Proof.
  intros. intro Hcon. inverts Hcon. apply wrap_inj in H2. subst. not_equal.
Qed.

Lemma unwrap_wrap : forall t,
  unwrap (wrap t) = t.
Proof.
  induction t; simpl; auto.
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt1. rewrite IHt2. auto.
Qed.

Fixpoint apply1 Si g lhs_f lhs_ty target (mx : mapping Si g lhs_f lhs_ty target)
                                         (ty : wrapped_type) : wrapped_type :=
  if type_eq_decide (TFun lhs_f lhs_ty) target
    (* special-case for Refl to avoid wrapping *)
  then ty
  else
  match ty with
    | wTBVar n => wTBVar n
    | wTFun f lhs => if domelt_eq_decide_w (lhs_f,wrap lhs_ty) (f,lhs)
                   then wWrap target
                   else ty
    | wTArrow ty1 ty2 => wTArrow (apply1 mx ty1) (apply1 mx ty2)
    | wTTycon T => wTTycon T
    | wTApp ty1 ty2 => wTApp (apply1 mx ty1) (apply1 mx ty2)
    | wWrap _ => ty
  end.

Ltac silly_if :=
  let silly b x := replace (if b then x else x) with x in * by (destruct b; auto) in
  match goal with
    | [ |- context[if ?b then ?x else ?x] ] => silly b x
    | [ H : context[if ?b then ?x else ?x] |- _ ] => silly b x
  end.

Lemma apply1_commutes_self : forall t Si g1 g2 f1 f2 lhs1 lhs2 target1 target2
  (mx1 : mapping Si g1 f1 lhs1 target1) (mx2 : mapping Si g2 f2 lhs2 target2),
  (f1,lhs1) <> (f2,lhs2) ->
  apply1 mx1 (apply1 mx2 t) = apply1 mx2 (apply1 mx1 t).
Proof.
  induction t; intros; simpl; auto.
  - silly_if. silly_if. simpl. silly_if. silly_if. auto.
  - destruct_if; destruct_if; simpl; destruct_if; simpl; auto; destruct_if; simpl; auto;
    destruct_if; try destruct_if; auto. rewrite <- C2 in C0. apply wrap_neq in H.
    rewrite C0 in H. not_equal.
  - destruct_if; destruct_if; simpl; destruct_if; destruct_if; simpl; auto.
    rewrite IHt1; auto. rewrite IHt2; auto.
  - silly_if. silly_if. simpl. silly_if. silly_if. auto.
  - destruct_if; destruct_if; simpl; destruct_if; destruct_if; simpl; auto.
    rewrite IHt1; auto. rewrite IHt2; auto.
  - silly_if. silly_if. simpl. silly_if. silly_if. auto.
Qed.

Lemma apply1_refl : forall t Si g f ty (m : mapping Si g f ty (TFun f ty)),
  apply1 m t = t.
Proof.
  induction t; intros; simpl; destruct_if; auto.
Qed.

Lemma apply1_size0 : forall t Si g f ty ty2 (m : mapping Si g f ty ty2),
  size_of_co g = 0 ->
  apply1 m t = t.
Proof.
  induction t; intros; simpl; destruct_if; auto.
  - destruct_if. eapply size0_refl in H. apply C in H. contradiction.
    destruct m. eassumption. auto.
  - rewrite IHt1; auto. rewrite IHt2; auto. 
  - rewrite IHt1; auto. rewrite IHt2; auto.
Qed.

Fixpoint apply_w Si dom n (subst : substn Si dom n) (t : wrapped_type) : wrapped_type :=
  match subst with
    | nilSubst => t
    | consSubst _ _ _ _ _ _ mx rest => apply1 mx (apply_w rest t)
  end.

Lemma apply_w_commutes Si dom n (sub : substn Si dom n) t :
  match t with
    | wTFun f ty => True
    | wTArrow ty1 ty2 => apply_w sub t = wTArrow (apply_w sub ty1) (apply_w sub ty2)
    | wTApp ty1 ty2 => apply_w sub t = wTApp (apply_w sub ty1) (apply_w sub ty2)
    | t => apply_w sub t = t
  end.
Proof.
  generalize dependent t.
  induction sub; intro t; [ | destruct m ]; destruct t; simpl; auto;
  match goal with
    | [ |- context[apply_w sub ?ty] ] => specialize (IHsub ty)
  end; simpl in IHsub; rewrite IHsub; simpl; destruct_if; auto.
  generalize (mkMapping c). rewrite <- C. intro m. repeat rewrite apply1_refl. auto.
  generalize (mkMapping c). rewrite <- C. intro m. repeat rewrite apply1_refl. auto.
Qed.

Lemma apply_w_size0 : forall Si dom (w_empty : substn Si dom 0) t,
  apply_w w_empty t = t.
Proof.
  intros. remember 0. induction w_empty.
  - reflexivity.
  - simpl. rewrite IHw_empty. apply apply1_size0. omega. omega.
Qed.

Lemma apply_w_empty_dom : forall Si n (w : substn Si [] n) t,
  apply_w w t = t.
Proof.
  remember []. induction w; intros.
  - simpl. auto.
  - discriminate.
Qed.

Ltac is_bare_type t :=
  match t with
    | TBVar _ => idtac
    | TFun _ _ => idtac
    | TArrow _ _ => idtac
    | TTycon _ => idtac
    | TApp _ _ => idtac
  end.

Ltac apply_w_commutes :=
  let Ha_c := fresh in
  repeat match goal with
    | [ H : context[apply_w ?sub ?t] |- _ ] => is_bare_type t;
                                             pose proof (apply_w_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c in H;
                                             clear Ha_c
  end;
  repeat match goal with
    | [ |- context[apply_w ?sub ?t] ] => is_bare_type t;
                                             pose proof (apply_w_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c;
                                             clear Ha_c
  end.

Definition apply Si dom n (w : substn Si dom n) t : type :=
  unwrap (apply_w w (wrap t)).

Definition apply_empty_dom : forall Si n (w : substn Si [] n) t,
  apply w t = t.
Proof.
  intros. unfold apply. rewrite apply_w_empty_dom. apply unwrap_wrap.
Qed.

Fixpoint union_dom (dom1 dom2 : list (var * type)) : list (var * type) :=
  set_union domelt_eq_decide dom1 dom2.

Definition undefined {A} : A. Admitted.

Fixpoint yank_dom f ty (dom : list (var * type)) : list (var * type) :=
  match dom with
    | nil => nil
    | (f1,ty1) :: rest => if domelt_eq_decide (f,ty) (f1, ty1)
                          then rest
                          else (f1,ty1) :: yank_dom f ty rest
  end.

Lemma yank_dom_head : forall f ty dom,
  yank_dom f ty ((f,ty) :: dom) = dom.
Proof.
  intros. simpl. rewrite push_domelt_eq. reflexivity.
Qed.

Lemma yank_dom_tail : forall f ty f1 ty1 dom,
  (f, ty) <> (f1, ty1) ->
  yank_dom f ty ((f1, ty1) :: dom) = (f1, ty1) :: yank_dom f ty dom.
Proof.
  intros. simpl. destruct (domelt_eq_decide (f,ty) (f1,ty1)).
    - apply H in e. contradiction.
    - auto.
Qed.

Lemma in_yank_dom : forall dom f ty f' ty',
  In (f,ty) (yank_dom f' ty' dom) -> In (f,ty) dom.
Proof.
  induction dom; intros.
  - simpl in H. auto.
  - simpl in H. destruct a. destruct (domelt_eq_decide (f,ty) (v,t)).
    * inverts e. constructor. auto.
    * apply in_cons. destruct (domelt_eq_decide (f',ty') (v,t)).
      + auto.
      + eapply IHdom. apply in_inv in H. inversion H. rewrite H0 in n. not_equal.
        eassumption.
Qed.

Lemma no_dup_yank_dom : forall dom f ty,
  NoDup dom -> NoDup (yank_dom f ty dom).
Proof.
  induction dom; intros.
  - simpl. auto.
  - inverts H. destruct a. destruct (domelt_eq_decide (f,ty) (v,t)).
    * inverts e. rewrite yank_dom_head. auto.
    * rewrite yank_dom_tail; auto. constructor. intro Hcon.
      apply in_yank_dom in Hcon. contradiction.
      apply IHdom. assumption.
Qed.

Lemma yank_dom_removes : forall dom f ty,
  NoDup dom ->
  In (f,ty) (yank_dom f ty dom) -> False.
Proof.
  induction dom; intros.
  - simpl in H0. inverts H0.
  - specialize (IHdom f ty). lapplies IHdom. contradiction.
    * simpl in H0. destruct a. destruct_if.
      + exfalso. inverts H. inverts C. contradiction.
      + apply in_inv in H0. inverts H0. rewrite H1 in C. not_equal. auto.
    * inverts H. auto.
Qed.

Lemma in_neq : forall A (a h : A) (t : list A),
  In a (h :: t) -> a <> h -> In a t.
Proof.
  intros. inverts H.
  - not_equal.
  - auto.
Qed.

Definition yank_mapping Si dom n f ty (w : substn Si dom n)
  (HIn : In (f, ty) dom) :
  { g : coercion &
  { target : type &
  { n' : nat &
  { (mx, w') : (mapping Si g f ty target * substn Si (yank_dom f ty dom) n') |
    (n' + size_of_co g = n /\
     forall t, apply_w w t = apply1 mx (apply_w w' t)) }}}}.
  induction w as [ ? | ? f1 ty1 ? ? ? mx rest ].
  - (* nil *) inversion HIn.
  - (* cons *) destruct (domelt_eq_decide (f1,ty1) (f,ty)) as [ Heq | Hneq ].
    * (* equal *) inverts Heq; subst.
                  exists g. exists target. exists n. 
                  rewrite yank_dom_head.
                  exists (mx, rest).
                  auto.
    * (* not equal *) apply in_neq in HIn; auto.
      apply IHrest in HIn.
      destruct HIn as [g1 [target1 [n1 [[mx1 w1] pf]]]].
      exists g1. exists target1. exists (n1 + size_of_co g).
      rewrite yank_dom_tail by auto.
      exists (mx1, consSubst mx w1).
      inverts pf.
      split. omega.
  intros. simpl. rewrite H0. apply apply1_commutes_self. assumption.
Qed.

Lemma subset_yank_dom : forall f ty dom1 dom2,
  subset (yank_dom f ty dom1) dom2 -> subset dom1 ((f,ty)::dom2).
Proof.
  (* This is a terrible proof. I'm ashamed. Please fix. *)
  unfolds subset. induction dom1; intros.
  - inverts H0.
  - destruct (domelt_eq_decide (f,ty) domelt).
    * rewrite e. apply in_eq.
    * destruct (domelt_eq_decide a domelt).
      + subst. apply in_cons. apply H. destruct domelt. rewrite yank_dom_tail.
        apply in_eq. auto.
      + apply IHdom1. intros. apply H. destruct (domelt_eq_decide (f,ty) a).
          rewrite <- e. rewrite yank_dom_head. destruct domelt0.
          eapply in_yank_dom. eassumption. destruct a. rewrite yank_dom_tail by auto.
          apply in_cons. assumption. apply in_inv in H0. inverts H0. not_equal.
          assumption.
Qed.

Lemma subset_yank_dom_2 : forall f ty dom1 dom2,
  NoDup dom1 ->
  subset dom1 ((f,ty)::dom2) -> subset (yank_dom f ty dom1) dom2.
Proof.
  intros. induction dom1.
  - simpl. apply subset_nil.
  - simpl. destruct a. destruct_if.
    * rewrite C in H0. rewrite <- subset_cons in H0. auto. inverts H. auto.
    * apply subset_cons1 in H0. inverts H0. apply IHdom1 in H1.
      apply subset_in. apply in_inv in H2. inverts H2. contradiction. auto. auto.
      inverts H. auto.
Qed.

Unset Implicit Arguments.
Obligation Tactic := program_simpl.
Program Fixpoint fix_dom Si dom1 n (w : substn Si dom1 n)
                           dom2 n2 (w2 : substn Si dom2 n2)
  (HNoDup1 : NoDup dom1) (HNoDup2 : NoDup dom2)
  : { dom : list (var * type) &
    { w1' : substn Si dom n |
      (forall t, apply_w w1' t = apply_w w t) /\
      subset dom1 dom /\ subset dom2 dom /\ (subset dom1 dom2 -> dom = dom2) /\
      (forall domelt, In domelt dom -> (In domelt dom1 \/ In domelt dom2)) /\
      NoDup dom }} :=
  match w2 with
    | nilSubst => existT _ dom1 w
    | consSubst _ f1 ty1 _ rest _ _ w2' =>
      match in_dec domelt_eq_decide (f1,ty1) dom1 with
        | left HIn =>
          let yanked := yank_mapping f1 ty1 w HIn in
          match yanked with
            | existT _ (existT _ (existT _ (exist (mx, w1') _))) =>
          let fixed :=  fix_dom _ _ _ w1' _ _ w2' _ _ in
          match fixed with
            | existT dom fixed_w =>
          existT _ ((f1,ty1)::dom) (consSubst mx fixed_w)
          end end
        | right Hcon =>
          let t := TFun f1 ty1 in
          let k_w_proof := typeKind Si t _ in
          let fixed := fix_dom _ _ _ w _ _ w2' _ _ in
          match fixed with
            | existT dom fixed_w =>
          existT _ ((f1,ty1)::dom) (consSubst (mkMapping (@CKRefl _ _ k_w_proof _)) fixed_w)
          end
      end
  end.

Next Obligation.
  repeat split.
  - apply subset_refl.
  - apply subset_nil.
  - intro. destruct dom1.
    * auto.
    * unfolds subset. specialize (H p). lapplies H. inverts H0. apply in_eq.
  - intros. tauto.
  - assumption.
Qed.

Next Obligation.
  clear Heq_yanked.
  apply no_dup_yank_dom. auto.
Qed.

Next Obligation.
  inverts HNoDup2. auto.
Qed.

Next Obligation.
    repeat split.
  - intros. squash_eq_rect. rewrite e0. rewrite e1.
    reflexivity.

  - clear Heq_fixed Heq_yanked. apply subset_yank_dom. assumption.
  - clear Heq_fixed Heq_yanked. apply subset_cons. inverts HNoDup2. auto. assumption.
  - clear Heq_fixed Heq_yanked. intros. f_equal. apply e2.
    apply subset_yank_dom_2. assumption. assumption.
  - clear Heq_fixed Heq_yanked. intros. inverts H.
    * tauto.
    * apply o in H0. inverts H0.
      + destruct domelt. apply in_yank_dom in H. tauto.
      + tauto.
  - clear Heq_fixed Heq_yanked. constructor; auto. intro Hcon.
    apply o in Hcon. inverts Hcon.
    * apply yank_dom_removes in H. auto. auto.
    * inverts HNoDup2. contradiction.
Defined.

Next Obligation.
  clear Heq_w2. inverts wildcard'2. apply co_kind_reg_t1 in H. auto.
Qed.

Next Obligation.
  inverts HNoDup2. auto.
Qed.

Next Obligation.
  abstract_sig. auto.
Defined.

Next Obligation.
  repeat split; try clear Heq_fixed.
  - squash_eq_rect. intro.
    match goal with
      | [ |- context[apply1 ?garbage _] ] => generalize garbage
    end. intro.
    clear Heq_fixed. rewrite e. apply apply1_refl.

  - apply subset_cons2. assumption.
  - apply subset_cons. inverts HNoDup2. assumption. assumption.
  - intro. f_equal. apply e0. eapply subset_neq. apply Hcon. assumption.
  - intros. inverts H. tauto. apply o in H0. inverts H0; tauto.
  - constructor; auto. intro. apply o in H. inverts H.
    * contradiction.
    * inverts HNoDup2. contradiction.
Defined.

Arguments fix_dom [_ _ _] _ [_ _] _ _ _.

