Require Import LibVar.

Require Import utils.

Axiom var_eq_decide : forall (v1 v2 : var), decide (v1 = v2).