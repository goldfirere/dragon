Require Import LibLN.
Require Import Arith.
Require Import List.
Require Import Program.

Require Import type coercion utils subst co_kind var tactics compose.

Set Implicit Arguments.

Inductive mapping : Set :=
| mkMapping : var -> type -> type -> coercion -> mapping.

Definition mappingLhsFun m :=
  match m with
    | mkMapping f _ _ _ => f
  end.

Definition mappingLhsType m :=
  match m with
    | mkMapping _ t _ _ => t
  end.

Definition mappingTarget m :=
  match m with
    | mkMapping _ _ t _ => t
  end.

Definition mappingCo m :=
  match m with
    | mkMapping _ _ _ g => g
  end.

Definition mappingX Si := { bnd : mapping |
                            Si |-co (mappingCo bnd) ~:
                                    TFun (mappingLhsFun bnd)
                                         (mappingLhsType bnd) ~~
                                    mappingTarget bnd }.

Arguments proj1_sig {_ _} _.
Definition substnX Si n := { maps : list (mappingX Si) |
                             sum (map (size_of_co false ∘
                                       mappingCo ∘
                                       proj1_sig) maps) <= n }.

Fixpoint apply1 {Si} (mx : mappingX Si) (ty : type) : type :=
  match proj1_sig mx with
    | mkMapping lhs_f lhs_ty target _ =>
  match ty with
    | TBVar n => TBVar n
    | TFun f ty => if tuple_eq_decide var_eq_decide type_eq_decide (lhs_f,lhs_ty) (f,ty)
                   then target
                   else ty
    | TArrow ty1 ty2 => TArrow (apply1 mx ty1) (apply1 mx ty2)
    | TTycon T => TTycon T
    | TApp ty1 ty2 => TApp (apply1 mx ty1) (apply1 mx ty2)
  end end.

Fixpoint apply_mapping {Si} (mappings : list (mappingX Si)) (t : type) : type :=
  match mappings with
    | nil => t
    | (m :: tail) => apply_mapping tail (apply1 m t)
  end.

Definition apply {Si n} (s : substnX Si n) (ty : type) : type :=
  apply_mapping (proj1_sig s) ty.

Lemma apply_mapping_commutes Si (mappings : list (mappingX Si)) t :
  match t with
    | TFun f ty => True
    | TArrow ty1 ty2 => apply_mapping mappings t =
                        TArrow (apply_mapping mappings ty1) (apply_mapping mappings ty2)
    | TApp ty1 ty2 => apply_mapping mappings t =
                      TApp (apply_mapping mappings ty1) (apply_mapping mappings ty2)
    | t => apply_mapping mappings t = t
  end.
Proof.
  generalize dependent t.
  induction mappings as [ | m tail ]; intro t; [ | destruct m; simpl; destruct x ]; destruct t; simpl; auto;
  match goal with
      | [ |- apply_mapping _ ?ty = _ ] => specialize (IHtail ty)
  end; simpl in IHtail; auto.
Qed.

Lemma apply_commutes Si n (sub : substnX Si n) t :
  match t with
    | TFun f ty => True
    | TArrow ty1 ty2 => apply sub t = TArrow (apply sub ty1) (apply sub ty2)
    | TApp ty1 ty2 => apply sub t = TApp (apply sub ty1) (apply sub ty2)
    | t => apply sub t = t
  end.
Proof.
  destruct sub as [mappings pf]. unfold apply. simpl. apply apply_mapping_commutes.
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
    