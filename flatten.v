
Require Import type.

Fixpoint flatten t :=
  match t with
    | TFun _ _ => TFVar (fl t)
    | TArrow t1 t2 => TArrow (flatten t1) (flatten t2)
    | TForAll k ty => TForAll k (flatten ty)
    | TApp t1 t2 => TApp (flatten t1) (flatten t2)
    | t => t
  end.