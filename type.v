Require Import LibLN.
Require Import LibTactics.
Require Import List.
Require Import Arith.

Require Import tactics utils var.

Set Implicit Arguments.

Inductive kind :=
| KStar : kind
| KArrow : kind -> kind -> kind.

Inductive type :=
| TBVar : nat -> type
| TFun : var -> type -> type
| TArrow : type -> type -> type
| TTycon : var -> type
| TApp : type -> type -> type.

Fixpoint size_of_ty (fl : bool) ty :=
  match ty with
    | TBVar _ => 1
    | TFun f ty => if fl then 1 else S (size_of_ty fl ty)
    | TArrow ty1 ty2 => S (size_of_ty fl ty1 + size_of_ty fl ty2)
    | TTycon _ => 1
    | TApp ty1 ty2 => S (size_of_ty fl ty1 + size_of_ty fl ty2)
  end.

Lemma type_eq_decide : forall (ty1 ty2 : type), decide (ty1 = ty2).
Proof.
  generalize var_eq_decide. unfold decide. repeat decide equality.
Qed.