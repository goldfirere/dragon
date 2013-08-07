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

Inductive substn : ctxt -> list (var * type) -> nat -> Type :=
| nilSubst : forall Si n, substn Si nil n
| consSubst : forall Si g f lhs target dom n,
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

Fixpoint apply1 Si g lhs_f lhs_ty target (mx : mapping Si g lhs_f lhs_ty target)
                                         (ty : type) : type :=
  match ty with
    | TBVar n => TBVar n
    | TFun f ty => if domelt_eq_decide (lhs_f,lhs_ty) (f,ty)
                   then target
                   else ty
    | TArrow ty1 ty2 => TArrow (apply1 mx ty1) (apply1 mx ty2)
    | TTycon T => TTycon T
    | TApp ty1 ty2 => TApp (apply1 mx ty1) (apply1 mx ty2)
  end.

Fixpoint apply Si dom n (subst : substn Si dom n) (t : type) : type :=
  match subst with
    | nilSubst _ _ => t
    | consSubst _ _ _ _ _ _ _ mx rest => apply1 mx (apply rest t)
  end.

Lemma apply_commutes Si dom n (sub : substn Si dom n) t :
  match t with
    | TFun f ty => True
    | TArrow ty1 ty2 => apply sub t = TArrow (apply sub ty1) (apply sub ty2)
    | TApp ty1 ty2 => apply sub t = TApp (apply sub ty1) (apply sub ty2)
    | t => apply sub t = t
  end.
Proof.
  generalize dependent t.
  induction sub; intro t; [ | destruct m ]; destruct t; simpl; auto;
  match goal with
    | [ |- context[apply sub ?ty] ] => specialize (IHsub ty)
  end; simpl in IHsub; rewrite IHsub; simpl; auto.
Qed.

Ltac is_bare_type t :=
  match t with
    | TBVar _ => idtac
    | TFun _ _ => idtac
    | TArrow _ _ => idtac
    | TTycon _ => idtac
    | TApp _ _ => idtac
  end.

Ltac apply_commutes :=
  let Ha_c := fresh in
  repeat match goal with
    | [ H : context[apply ?sub ?t] |- _ ] => is_bare_type t;
                                             pose proof (apply_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c in H;
                                             clear Ha_c
  end;
  repeat match goal with
    | [ |- context[apply ?sub ?t] ] => is_bare_type t;
                                             pose proof (apply_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c;
                                             clear Ha_c
  end.

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

Ltac not_equal :=
  match goal with
    | [ Hneq : ?x <> ?x |- _ ] => specialize (Hneq eq_refl); contradiction
  end.

Definition yank_mapping Si dom n f ty (w : substn Si dom n) :
  InT (f, ty) dom ->
  { g : coercion &
  { target : type &
  { n' : nat &
  (mapping Si g f ty target * substn Si (yank_dom f ty dom) n')%type }}}.
  intro HIn.
  induction w as [ ? ? | ? ? f1 ty1 ? ? ? mx rest ].
  - (* nil *) inversion HIn.
  - (* cons *) destruct (domelt_eq_decide (f1,ty1) (f,ty)) as [ Heq | Hneq ].
    * (* equal *) inverts Heq; subst. do 3 eexists. rewrite yank_dom_head.
                  exact (mx, rest).
    * (* not equal *) inversion HIn. 
      + (* InHere *) subst. not_equal.
      + (* InThere *) apply IHrest in H1. inverts H1. inverts X. inverts X0. do 3 eexists.
                      inverts X. rewrite yank_dom_tail by auto.
                      exact (X0, consSubst mx X1).
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

Definition fix_dom Si dom1 n (w : substn Si dom1 n) dom2
  (HIn : forall f ty, InT (f,ty) dom1 -> InT (f,ty) dom2) : substn Si dom2 n.
  generalize dependent n. induction dom2; intros.
  - exact (nilSubst _ _).
  - destruct a as [f1 ty1]. destruct (InT_decide (f1,ty1) dom1 domelt_eq_decide).
    * set (yanked := yank_mapping w i). inverts yanked. inverts X. inverts X0.
      inverts X. lapplies IHdom2.

  refine (
  match dom2 with
    | nil => nilSubst _ _
    | (f,ty) :: rest => let (mx, w') := projT2 (projT2 (projT2 (yank_mapping w _))) in
                        consSubst mx (fix_dom w' rest)
  end).

Definition trans_unify : forall Si dom1 dom2 n1 n2 n_left n_right t1 t2 t3
  (w1 : substn Si dom1 n1)
  (w2a : substn Si dom1 n1)
  (w2b : substn Si dom2 n2)
  (w3 : substn Si dom2 n2),
  n1 <= n_left ->
  n2 <= n_right ->
  apply w1 t1 = apply w2a t2 ->
  apply w2b t2 = apply w3 t3 ->
  { dom : list (var * type) &
  { n1' : nat &
  { w1' : substn Si dom n1' &
  { n3' : nat &
  { w3' : substn Si dom n3' |
    n1' <= S (n_left + n_right) /\
    n3' <= S (n_left + n_right) /\
    apply w1' t1 = apply w3' t3 }}}}}.
Proof.
  

Definition subs_commute sub1 sub2 :=
  forall t, apply sub1 (apply sub2 t) = apply sub2 (apply sub1 t).

Fixpoint dom (sub : substn) : fset xvar :=
  match sub with
    | nil => \{}
    | (xv,_) :: rest => \{xv} \u dom rest
  end.

Fixpoint fv_range (sub : substn) : fset xvar :=
  match sub with
    | nil => \{}
    | (_,t) :: rest => fv(t) \u fv_range rest
  end.

Inductive ok_sub : substn -> Type :=
| ok_sub_nil : ok_sub nil
| ok_sub_cons : forall xv t sub,
   xv \notin (dom sub) -> ok_sub sub -> ok_sub ((xv,t) :: sub).

Axiom in_notin : forall {A} (x : A) s,
  x \in s -> x \notin s -> False.

Axiom in_inter_empty : forall {A} (x : A) s1 s2,
  s1 \n s2 = \{} -> x \in s1 -> x \notin s2.

Lemma is_sub_or_not xv sub :
  ok_sub sub -> 
  xv \in dom sub \/ apply sub (TFVar xv) = TFVar xv.
Proof.
  induction sub; intros.
  right. simpl. auto.
  inverts H. apply IHsub in H3. inverts H3.
  - left. simpl. rewrite in_union. tauto.
  - simpl. destruct (xvar_eq_decide xv xv0).
    * subst. left. simpl. rewrite in_union. left. apply in_singleton_self.
    * right. auto.
Qed.

Axiom notin_sub_id : forall xv sub,
  xv \notin dom sub -> apply sub (TFVar xv) = TFVar xv.

Lemma subs_commute_dec sub1 sub2 : 
  ok_sub sub1 -> ok_sub sub2 ->
  decide (subs_commute sub1 sub2).
Proof.
  introv Hok1 Hok2.
  refine (let dom1 := dom sub1 in
          let dom2 := dom sub2 in
          let r1 := fv_range sub1 in
          let r2 := fv_range sub2 in
          If dom1 \n dom2 = \{} /\ dom1 \n r2 = \{} /\ dom2 \n r1 = \{}
          then left _
          else right _).
  inverts _H. inverts H0.
  intro t. induction t; apply_commutes; auto.
  - apply (is_sub_or_not x) in Hok2. inverts Hok2.
    * assert (x \notin dom sub1). {
        unfold dom2 in H. eapply in_inter_empty. unfold dom1 in H.
        rewrite inter_comm. apply H. auto.
      }
      replace (apply sub1 (TFVar x)) with (TFVar x) by
        (symmetry; apply notin_sub_id; auto).
      admit. (* to prove : apply sub1 (apply sub2 (TFVar x)) = apply sub2 (TFVar x)
                   but, this is true because dom sub1 \n fv (apply sub2 (TFVar x))
                   must be empty. *)
    * rewrite H0. admit. (* similar *)   
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  
  - intro Hcon. unfold subs_commute in Hcon.
    apply Decidable.not_and in _H. inverts _H.
    