Require Import Program.
Require Import List.

Lemma map_compose : forall A B C (f : B -> C) (g : A -> B) list,
  map (f ∘ g) list = map f (map g list).
Proof.
  induction list.
  - reflexivity.
  - simpl. rewrite IHlist. unfold compose. reflexivity.
Qed.
