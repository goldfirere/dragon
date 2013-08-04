Require Import LibTactics.
Require Import List.

(* This is closely based on LibRelation, by A. Charguéraud, but in Type, not Prop. *)

Set Implicit Arguments.

Definition binary (A : Type) := A -> A -> Type.

Section Properties.
Variables (A:Type).
Implicit Types x y z : A.
Implicit Types R : binary A.

Definition trans R := 
  forall y x z, R x y -> R y z -> R x z.
End Properties.

(* ---------------------------------------------------------------------- *)
(** Reflexive-transitive closure ( R* ) *)

Section rtclosure.
Variables (A : Type) (R : binary A).

Inductive rtclosure : binary A :=
  | rtclosure_refl : forall x,
      rtclosure x x
  | rtclosure_step : forall y x z,
      R x y -> rtclosure y z -> rtclosure x z.

Hint Constructors rtclosure.

Lemma rtclosure_once : forall x y,
  R x y -> rtclosure x y.
Proof. auto*. Qed.

Hint Resolve rtclosure_once.

Lemma rtclosure_trans : trans rtclosure.  
Proof. introv R1 R2. induction* R1. Qed.

Lemma rtclosure_last : forall y x z,
  rtclosure x y -> R y z -> rtclosure x z.
Proof. introv R1 R2. induction* R1. Qed.

Hint Resolve rtclosure_trans.

(* ---------------------------------------------------------------------- *)
(** ** Induction *)

(** Star induction principle with transitivity hypothesis *)

Lemma rtclosure_ind_trans : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall x y : A, R x y -> P x y) ->
  (forall y x z : A, rtclosure x y -> P x y -> rtclosure y z -> P y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof.
  introv Hrefl Hstep Htrans S. induction S.
  auto. apply~ (@Htrans y).
Qed.

(** Star induction principle with steps at the end *)

Lemma rtclosure_ind_right : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall y x z : A, rtclosure x y -> P x y -> R y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof.
  introv Hrefl Hlast. apply rtclosure_ind_trans. 
  auto.
  intros. apply~ (Hlast x).
  introv S1 P1 S2 _. gen x. induction S2; introv S1 P1.
     auto.
     apply IHS2. eauto. apply~ (Hlast x). 
Qed.

End rtclosure.

Inductive Forall2T (A B : Type) (R : A -> B -> Type) : list A -> list B -> Type :=
  | Forall2T_nil : Forall2T R nil nil
  | Forall2T_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                      R x y -> Forall2T R l l' -> Forall2T R (x :: l) (y :: l').

Definition list_equiv (A:Type) (E:binary A) : binary (list A) :=
   Forall2T E.
