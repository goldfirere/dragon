Require Import LibTactics.

Require Import type coercion unify flatten tactics.

Inductive value_type : type -> Prop :=
| VArrow : forall t1 t2, value_type (TArrow t1 t2)
| VApp : forall t1 t2, value_type t1 -> value_type (TApp t1 t2)
| VTycon : forall T, value_type (TTycon T)
| VForAll : forall k ty, value_type (TForAll k ty).

Inductive heads_same : type -> type -> Prop :=
| SameArrow : forall t1 t2 t1' t2', heads_same (TArrow t1 t2) (TArrow t1' t2')
| SameApp: forall t1 t2 t1' t2', heads_same t1 t1' -> heads_same (TApp t1 t2) (TApp t1' t2')
| SameTycon : forall T, heads_same (TTycon T) (TTycon T)
| SameForAll : forall k1 k2 ty1 ty2, heads_same (TForAll k1 ty1) (TForAll k2 ty2).

Definition consistent t1 t2 :=
  value_type t1 ->
  value_type t2 ->
  heads_same t1 t2.

Ltac not_value_type :=
  try (unfold consistent; intros;
       match goal with
         | [ H : value_type _ |- _ ] => solve [inversion H]
       end).

Hint Constructors value_type heads_same.
Hint Unfold consistent.

Ltac flatten_unify_consistent :=
  simpl in *; apply_commutes; try discriminate.

Lemma flatten_unify_consistent : forall t1 t2,
  unifies (flatten t1) (flatten t2) ->
  consistent t1 t2.
Proof.
  induction t1; intros; inverts H; not_value_type;
    destruct t2; not_value_type; flatten_unify_consistent; auto.
  inverts H0. auto.
  inverts H0. unfold unifies in IHt1_1. specialize (IHt1_1 t2_1). lapplies IHt1_1.
    unfolds consistent. intros. inverts H0. apply H in H5. auto. inverts H3. auto.
    exists x. auto.
Qed.