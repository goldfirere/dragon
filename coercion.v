Require Import LibLN.
Require Import List.

Require Import type utils.

Inductive coercion :=
| CRefl : type -> coercion
| CSym  : coercion -> coercion
| CTrans : coercion -> coercion -> coercion
| CArrow : coercion -> coercion -> coercion
| CApp : coercion -> coercion -> coercion
| CLeft : coercion -> coercion
| CRight : coercion -> coercion
| CFun : var -> coercion -> coercion
| CAx : var -> list type -> coercion.

Inductive axiom :=
| mkAxiom : list kind -> var -> type -> type -> axiom.

Fixpoint size_of_co (fl : bool) co :=
  match co with
    | CRefl ty => 0
    | CSym co => S (size_of_co fl co)
    | CTrans co1 co2 => S (size_of_co fl co1 + size_of_co fl co2)
    | CArrow co1 co2 => S (size_of_co fl co1 + size_of_co fl co2)
    | CApp co1 co2 => S (size_of_co fl co1 + size_of_co fl co2)
    | CLeft co => S (size_of_co fl co)
    | CRight co => S (size_of_co fl co)
    | CFun _ co => S (size_of_co fl co)
    | CAx _ tys => 1
  end.
