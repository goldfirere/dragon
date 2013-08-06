Require Import LibNat.
Require Import LibLN.
Require Import List.

Require Import type tactics utils.

Set Implicit Arguments.

Fixpoint open_rec (k : nat) (u : type) (t : type) {struct t} : type :=
  match t with
    | TBVar i => if eq_nat_decide k i then u else (TBVar i)
    | TFun f ty => TFun f (open_rec k u ty)
    | TArrow t1 t2 => TArrow (open_rec k u t1) (open_rec k u t2)
    | TTycon T => TTycon T
    | TApp ty1 ty2 => TApp (open_rec k u ty1) (open_rec k u ty2)
  end.

Fixpoint open_telescope (k : nat) (rhos : list type) (t : type) : type :=
  match rhos with
    | nil => t
    | first :: rest => open_rec (k + length rest) first (open_telescope k rest t)
  end.

Notation "t [ ^ rhos // n ]" := (open_telescope n rhos t) (at level 66).
Notation "t [ ^ rhos ]" := (open_telescope 0 rhos t) (at level 66).
Notation "ts [ ^^ rhos // n ]" := (map (open_telescope n rhos) ts) (at level 66).
Notation "ts [ ^^ rhos ]" := (map (open_telescope 0 rhos) ts) (at level 66).



