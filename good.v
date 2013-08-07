Require Import LibLN.
Require Import LibTactics.
Require Import List.

Require Import type subst coercion.

Inductive tff : type -> Prop :=
| tfBVar : forall n, tff (TBVar n)
| tfArrow : forall t1 t2, tff t1 -> tff t2 -> tff (TArrow t1 t2)
| tfTycon : forall tycon, tff (TTycon tycon)
| tfApp : forall t1 t2, tff t1 -> tff t2 -> tff (TApp t1 t2).

Definition good_tff axs := forall C ks f typat target,
  binds C (mkAxiom ks f typat target) axs -> tff typat.

Inductive Good G : Prop :=
| mkGood :
    good_tff G -> 
    Good G.

Ltac invert_good :=
  match goal with
    | [ Hgood : Good _ |- _ ] => inverts Hgood as; introv Hgood_tff
  end.
