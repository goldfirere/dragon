Require Import LibVar.
Require Import LibEnv.

Require Import utils.

Axiom var_eq_decide : forall (v1 v2 : var), decide (v1 = v2).

Parameter ok__unique : forall {A} x (v v' : A) E,
  ok E -> binds x v E -> binds x v' E -> v = v'.
