Require Import LibLN.
Require Import LibReflect.
Require Import Arith.
Require Import List.

Require Import type coercion.

Definition mapping := (xvar * type)%type.
Definition substn := list mapping.

Parameter xvar_eq_decide :
  forall (xv1 xv2 : xvar), sumbool (xv1 = xv2) (xv1 <> xv2).

Fixpoint apply1 (m : mapping) ty :=
  let (xv, target) := m in
  match ty with
    | TFVar x => if xvar_eq_decide x xv then target else ty
    | TBVar n => TBVar n
    | TFun f ty => TFun f (apply1 m ty)
    | TArrow ty1 ty2 => TArrow (apply1 m ty1) (apply1 m ty2)
    | TTycon T => TTycon T
    | TForAll k ty => TForAll k (apply1 m ty)
    | TApp ty1 ty2 => TApp (apply1 m ty1) (apply1 m ty2)
  end.

Fixpoint apply (s : substn) ty :=
  match s with
    | nil => ty
    | (m :: tail) => apply tail (apply1 m ty)
  end.

Definition unifies t1 t2 :=
  exists sub, apply sub t1 = apply sub t2.

Lemma apply_commutes sub t :
  match t with
    | TFVar _ => True
    | TFun f ty => apply sub t = TFun f (apply sub ty)
    | TArrow ty1 ty2 => apply sub t = TArrow (apply sub ty1) (apply sub ty2)
    | TForAll k ty => apply sub t = TForAll k (apply sub ty)
    | TApp ty1 ty2 => apply sub t = TApp (apply sub ty1) (apply sub ty2)
    | t => apply sub t = t
  end.
Proof.
  generalize dependent t.
  induction sub as [ | m sub ]; intro t; [ | destruct m ]; destruct t; simpl; auto;
  match goal with
    | [ |- apply sub ?t = _ ] => specialize (IHsub t); simpl in IHsub; auto
  end.
Qed.

Ltac apply_commutes :=
  let Ha_c := fresh in
  repeat match goal with
    | [ H : context[apply ?sub ?t] |- _ ] => pose proof (apply_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c in H;
                                             clear Ha_c
  end.

