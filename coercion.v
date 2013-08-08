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

Fixpoint size_of_co co :=
  match co with
    | CRefl ty => 0
    | CSym co => S (size_of_co co)
    | CTrans co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CArrow co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CApp co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CLeft co => S (size_of_co co)
    | CRight co => S (size_of_co co)
    | CFun _ co => S (size_of_co co)
    | CAx _ tys => 1
  end.
