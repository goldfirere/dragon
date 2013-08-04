Require Import LibLN.
Require Import LibTactics.
Require Import List.

Require Import type subst.

Inductive tff : type -> Prop :=
| tfFVar : forall v, tff (TFVar v)
| tfBVar : forall n, tff (TBVar n)
| tfArrow : forall t1 t2, tff t1 -> tff t2 -> tff (TArrow t1 t2)
| tfTycon : forall tycon, tff (TTycon tycon)
| tfForAll : forall k t, tff t -> tff (TForAll k t)
| tfApp : forall t1 t2, tff t1 -> tff t2 -> tff (TApp t1 t2).

Definition good_tff axs := forall C D F typat t,
  binds C (mkAxiom D F typat t) axs -> tff typat.

Definition good_lc axs := forall C D F typat t,
  binds C (mkAxiom D F typat t) axs -> lc_gen (length D) t.

Inductive Good G : Prop :=
| mkGood :
    good_tff G -> 
    good_lc G ->
    Good G.

Ltac invert_good :=
  match goal with
    | [ Hgood : Good _ |- _ ] => inverts Hgood as; introv Hgood_tff Hgood_lc
  end.
