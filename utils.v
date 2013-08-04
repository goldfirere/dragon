Require Import LibTactics.
Require Import LibRelation.
Require Import Arith.
Require Import List.

Require Import tactics.

Set Implicit Arguments.

(* *** decide propositions *** *)
Definition decide (P : Prop) :=
  {P} + {~P}.

(* *** between_dec --- that it is decidable that one nat is between two others *** *)

Section between_dec.

Local Open Scope nat.
Lemma between_dec : forall a b c,
  {a < b} + {b <= a < c} + {c <= a}.
Proof.
  intros. destruct (le_lt_dec c a).
    tauto.
    destruct (le_lt_dec b a).
    tauto.
    tauto.
Qed.

End between_dec.

(* *** RNth *** *)

Inductive RNth A : nat -> list A -> A -> Prop :=
  | RNth_here : forall h t, RNth (length t) (h :: t) h
  | RNth_next : forall n h t a, RNth n t a -> RNth n (h :: t) a.

Lemma RNth_nil : forall A n (a : A),
  ~ RNth n nil a.
Proof.
  inversion 1.
Qed.

Lemma RNth_length : forall A list n (a : A),
  RNth n list a -> n < length list.
Proof.
  induction list; simpl; intros.
    contradict H. apply RNth_nil.
    inverts H.
      omega.
      apply IHlist in H4. omega.
Qed.

Lemma RNth_here_inv : forall A t h (a : A),
  RNth (length t) (h :: t) a -> a = h.
Proof.
  inversion 1.
    reflexivity.
    subst. apply RNth_length in H4. omega.
Qed.

Lemma RNth_Forall : forall A list n (a : A) prop,
  Forall prop list -> RNth n list a -> prop a.
Proof.
  induction list; simpl; intros.
    contradict H0. apply RNth_nil.
    inverts H0. inverts H. assumption.
    eapply IHlist. inverts H. assumption. eassumption.
Qed.

(* *** a destruction principle for lists, from the end *** *)

Lemma rev_destruct : forall A (l : list A),
  (l = nil) \/ (exists l' a, l = l' ++ a :: nil).
Proof.
  induction l using rev_ind.
    left. reflexivity.
    right. inverts IHl; eauto.
Qed.

Ltac rev_destruct l :=
  let H := fresh in
  let Hexists := fresh in
  let l' := fresh "init" in
  let a := fresh "last" in
  let Hexists' := fresh in
  pose proof (rev_destruct l) as H; inverts H as;
    [ |
      intro Hexists;
      inversion Hexists as [ l' Hexists' ];
      inversion Hexists' as [ a ? ];
      subst;
      clear Hexists Hexists'
    ].

(* *** list lemmas *** *)

Lemma length_0_nil : forall A (l : list A),
  length l = 0 ->
  l = nil.
Proof.
  destruct l; intros.
    reflexivity.
    simpl in H. discriminate.
Qed.

(* *** Forall2 implies same length *** *)

Lemma Forall2_length : forall A (R : binary A) ls1 ls2,
  Forall2 R ls1 ls2 ->
  length ls1 = length ls2.
Proof.
  induction ls1; destruct ls2; intros.
    reflexivity.
    inverts H.
    inverts H.
    simpl. erewrite IHls1. reflexivity. inverts H. assumption.
Qed.

Lemma Forall2_app_length : forall A (R : binary A) ls1 ls1' ls2 ls2',
  Forall2 R (ls1 ++ ls2) (ls1' ++ ls2') ->
  length ls1 = length ls1' ->
  Forall2 R ls1 ls1' /\ Forall2 R ls2 ls2'.
Proof.
  induction ls1; introv HF Hlen; simpls.
    symmetry in Hlen. apply length_0_nil in Hlen. subst. simpls. auto.
    destruct ls2; simpls.
      rewrite app_nil_r in HF. pose proof HF. apply Forall2_length in H.
      rewrite app_length in H. simpls. assert (length ls2' = 0) by omega.
      apply length_0_nil in H0. subst. rewrite app_nil_r in HF. auto.
      
      destruct ls1'; simpls.
        discriminate.
        specialize (IHls1 ls1' (a0 :: ls2) ls2'). lapplies IHls1.
          inverts H0. split.
          constructor. inverts HF. assumption. assumption. assumption. omega.
        inverts HF. assumption.
Qed.

Lemma Forall2_app_tail : forall A (R : binary A) ls1 ls2 tail1 tail2,
  Forall2 R (ls1 ++ tail1 :: nil) (ls2 ++ tail2 :: nil) ->
  Forall2 R ls1 ls2 /\ R tail1 tail2.
Proof.
  introv HF. pose proof (Forall2_app_length ls1 ls2 (tail1 :: nil) (tail2 :: nil) HF).
  lapplies H. intuition. inverts H1. assumption.
  apply Forall2_length in HF. repeat rewrite app_length in HF. simpls. omega.
Qed.
    