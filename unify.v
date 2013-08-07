Require Import Arith.
Require Import List.
Require Import Program.
Require Import Specif.
Require Import LibVar.
Require Import ListSet.
Require Import LibTactics.

Require Import type coercion utils subst co_kind var tactics compose ty_kind.

Set Implicit Arguments.

Inductive mapping : ctxt -> coercion -> var -> type -> type -> Type :=
| mkMapping : forall Si g f lhs target, Si |-co g ~: TFun f lhs ~~ target
                                      -> mapping Si g f lhs target.

Inductive substn Si : list (var * type) -> nat -> Type :=
| nilSubst : forall n, substn Si nil n
| consSubst : forall g f lhs target dom n,
                mapping Si g f lhs target -> 
                substn Si dom n ->
                substn Si ((f, lhs) :: dom) (n + size_of_co false g).

Definition domelt_eq_decide (d1 d2 : var * type) : decide (d1 = d2) :=
  tuple_eq_decide var_eq_decide type_eq_decide d1 d2.

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

Fixpoint apply_w Si dom n (subst : substn Si dom n) (t : wrapped_type) : wrapped_type :=
  match subst with
    | nilSubst _ => t
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

Inductive InT A : A -> list A -> Type :=
| InHere : forall h t, InT h (h :: t)
| InThere : forall a h t, InT a t -> InT a (h :: t).

Lemma InT__In : forall A (a : A) (l : list A),
  InT a l -> In a l.
Proof.
  induction l; intros.
  - inverts X.
  - inverts X. constructor. auto. apply in_cons. auto.
Qed.

Lemma in_yank_dom : forall dom f ty f' ty',
  InT (f,ty) (yank_dom f' ty' dom) -> InT (f,ty) dom.
Proof.
  induction dom; intros.
  - simpl in H. auto.
  - simpl in H. destruct a. destruct (domelt_eq_decide (f,ty) (v,t)).
    * inverts e. constructor.
    * constructor. destruct (domelt_eq_decide (f',ty') (v,t)).
      + auto.
      + eapply IHdom. inversion H. subst. not_equal. eauto.
Qed.

Lemma in_yank_dom_P : forall dom f ty f' ty',
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
      apply in_yank_dom_P in Hcon. contradiction.
      apply IHdom. assumption.
Qed.

Lemma yank_dom_removes : forall dom f ty,
  NoDup dom ->
  InT (f,ty) (yank_dom f ty dom) -> False.
Proof.
  induction dom; intros.
  - simpl in H0. inverts H0.
  - specialize (IHdom f ty). lapplies IHdom. contradiction.
    * simpl in H0. destruct a. destruct_if.
      + exfalso. inverts H. apply InT__In in H0. inverts C. contradiction.
      + inverts H0. not_equal. auto.
    * inverts H. auto.
Qed.

Definition yank_mapping Si dom n f ty (w : substn Si dom n) :
  InT (f, ty) dom ->
  { g : coercion &
  { target : type &
  { n' : nat &
  { (mx, w') : (mapping Si g f ty target * substn Si (yank_dom f ty dom) n') |
    (n' + size_of_co false g = n /\
     forall t, apply_w w t = apply1 mx (apply_w w' t)) }}}}.
  intro HIn.
  induction w as [ ? | ? f1 ty1 ? ? ? mx rest ].
  - (* nil *) inversion HIn.
  - (* cons *) destruct (domelt_eq_decide (f1,ty1) (f,ty)) as [ Heq | Hneq ].
    * (* equal *) inverts Heq; subst.
                  exists g. exists target. exists n. 
                  rewrite yank_dom_head.
                  exists (mx, rest).
                  auto.
    * (* not equal *) inversion HIn. 
      + (* InHere *) subst. not_equal.
      + (* InThere *) apply IHrest in H1.
                      destruct H1 as [g1 [target1 [n1 [[mx1 w1] pf]]]].
                      exists g1. exists target1. exists (n1 + size_of_co false g).
                      rewrite yank_dom_tail by auto.
                      exists (mx1, consSubst mx w1).
                      inverts pf.
                      split. omega.
  intros. simpl. rewrite H3. apply apply1_commutes_self. assumption.
Qed.

Fixpoint InT_decide {A} (a : A) (l : list A) :
  (forall (a1 a2 : A), decide (a1 = a2)) ->
  (InT a l) + {InT a l -> False}.
Proof.
  intro Hdec_eq.
  refine (match l with
            | nil => inright _
            | b :: rest => if Hdec_eq a b then inleft _ else
                             if InT_decide A a rest Hdec_eq then inleft _ else inright _
          end).
  intro Hcon. inversion Hcon.
  subst. constructor.
  constructor. auto.
  intro Hcon. inversion Hcon. subst. not_equal. apply _H0 in X. contradiction.
Qed.

Unset Implicit Arguments.
Obligation Tactic := idtac.
Program Fixpoint fix_dom Si dom1 n (w : substn Si dom1 n)
                           dom2 n2 (w2 : substn Si dom2 n2)
  (HNoDup : NoDup dom1)
  (HIn : forall f ty, InT (f,ty) dom1 -> InT (f,ty) dom2)
  : { w_res : substn Si dom2 n | forall t, apply_w w t = apply_w w_res t } :=
  match w2 with
    | nilSubst _ => nilSubst _ _
    | consSubst _ f1 ty1 _ rest _ _ w2' =>
      match InT_decide (f1,ty1) dom1 domelt_eq_decide with
        | inleft HInT =>
          let sig_mapping := projT2 (projT2 (projT2 (yank_mapping w HInT))) in
          consSubst (fst (proj1_sig sig_mapping)) (fix_dom _ _ _ (snd (proj1_sig sig_mapping)) _ _ w2' _ _)
        | inright Hcon =>
          let t := TFun f1 ty1 in
          let k_w_proof := typeKind Si t _ in
          consSubst (mkMapping (CKRefl (proj2_sig k_w_proof)))
                    (fix_dom _ _ _ w _ _ w2' _ _)
      end
  end.
Require Import Tactics.
Next Obligation.
  program_simpl.
  assert (dom1 = []). { destruct dom1. auto. destruct p. specialize (HIn v t0).
                        lapplies HIn. inverts H. constructor. }
  destruct w.
    - reflexivity.
    - discriminate.
Qed.

Next Obligation.
  intros.
  apply no_dup_yank_dom. assumption.
Qed.

Next Obligation.
  program_simpl.
  pose proof H as Hyank. apply in_yank_dom in H. apply HIn in H. inverts H.
  - apply yank_dom_removes in Hyank; auto. contradiction.
  - auto.
Qed.

Next Obligation.
  program_simpl. generalize (yank_mapping w HInT). intro s. destruct s. destruct s.
  destruct s. simpl. pose proof (proj2_sig s). simpl in H. destruct s. simpls.
  destruct x2. tauto.
Qed.

Ltac squash_eq_rect :=
  let H := fresh in
  match goal with
    | [ |- context[eq_rect _ _ _ _ ?Heq] ] => generalize Heq; intro H; destruct H; simpl
  end.

Next Obligation.
  intros. squash_eq_rect. destruct sig_mapping. destruct x. simpl. abstract_sig.
  rewrite <- H0. inversion y. apply H2.
Defined.

Obligation Tactic := program_simpl.

Next Obligation.
  clear Heq_w2. inverts w2. inverts X. apply co_kind_reg_t1 in H0. assumption.
Qed.

Next Obligation.
  pose proof H as Hcopy. apply HIn in H. inverts H. 
  - contradiction.
  - auto.
Qed.

Next Obligation.
  squash_eq_rect.
  match goal with
    | [ |- context[mkMapping ?garbage] ] => generalize garbage
  end.
  intro c. generalize (mkMapping c). intro m.
  rewrite apply1_refl. apply e.
Defined.

Arguments fix_dom [_ _ _] _ [_ _] _ _ _.

