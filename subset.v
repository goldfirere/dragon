Require Import LibVar.
Require Import LibTactics.
Require Import List.

Require Import type utils var.

Set Implicit Arguments.

Definition domelt_eq_decide (d1 d2 : var * type) : decide (d1 = d2) :=
  tuple_eq_decide var_eq_decide type_eq_decide d1 d2.

Definition subset (dom1 dom2 : list (var * type)) : Prop :=
  forall domelt, In domelt dom1 -> In domelt dom2.

Lemma subset_refl : forall s,
  subset s s.
Proof.
  intros. intro. auto.
Qed.

Lemma subset_nil : forall (s : list (var * type)),
  subset nil s.
Proof.
  unfold subset. introv H. inverts H.
Qed.

Lemma subset_cons1 : forall d s1 s2,
  subset (d::s1) s2 -> (subset s1 s2 /\ In d s2).
Proof.
  unfold subset; intros; repeat split; intros.
  - apply H. apply in_cons. auto.
  - apply H. apply in_eq.
Qed.

Lemma subset_cons2 : forall d s1 s2,
  subset s1 s2 -> subset s1 (d::s2).
Proof.
  unfold subset; intros. apply in_cons. auto.
Qed.

Lemma subset_in : forall d s1 s2,
  In d s2 -> 
  subset s1 s2 ->
  subset (d::s1) s2.
Proof.
  unfold subset; intros.
  destruct (domelt_eq_decide d domelt).
   - subst. auto.
   - apply H0. apply in_inv in H1. inversion H1. contradiction. auto.
Qed.

Lemma subset_cons : forall d s1 s2,
  ~ In d s1 ->
  (subset s1 s2 <-> subset (d::s1) (d::s2)).
Proof.
  unfold subset; intros; split; intros.
  * apply in_inv in H1. inversion H1.
    - rewrite H2. apply in_eq.
    - apply in_cons. apply H0. assumption.
  * pose proof H1 as HIn.
    eapply in_cons in H1. apply H0 in H1. apply in_inv in H1. inversion H1.
    - subst. contradiction.
    - auto.
Qed.

Lemma subset_neq : forall d s1 s2,
  ~ In d s1 ->
  subset s1 (d::s2) ->
  subset s1 s2.
Proof.
  intros; induction s1.
  - apply subset_nil.
  - apply subset_in. unfold subset in H0. assert (In a (a :: s1)) by apply in_eq.
    apply H0 in H1. apply in_inv in H1. inversion H1. subst.
    assert (In a (a :: s1)) by apply in_eq. contradiction. assumption.
    apply IHs1. intro Hcon. eapply in_cons in Hcon. apply H in Hcon. auto.
    eapply subset_cons1. eassumption.
Qed.

Lemma subset_of_nil : forall s,
  subset s nil -> s = nil.
Proof.
  induction s; intros.
  - auto.
  - apply subset_cons1 in H. inverts H. inverts H1.
Qed.