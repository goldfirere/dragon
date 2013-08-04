Require Import LibNat.
Require Import LibLN.
Require Import List.

Require Import type tactics utils.

Set Implicit Arguments.

Inductive lc_gen n : type -> Prop :=
  | lc_fvar : forall x, lc_gen n (TFVar x)
  | lc_bvar : forall n', n' < n -> lc_gen n (TBVar n')
  | lc_fun : forall f ty, lc_gen n ty -> lc_gen n (TFun f ty)
  | lc_arrow : forall ty1 ty2, lc_gen n ty1 -> lc_gen n ty2
                               ->lc_gen n  (TArrow ty1 ty2)
  | lc_tycon : forall x, lc_gen n (TTycon x)
  | lc_forall : forall k ty,
      lc_gen (S n) ty ->
      lc_gen n (TForAll k ty)
  | lc_app : forall t1 t2,
      lc_gen n t1 -> lc_gen n t2 -> lc_gen n (TApp t1 t2).

Definition lc := lc_gen 0.
Definition lc_body := lc_gen 1.
 
Definition lc_list := Forall lc.

Ltac lc_assumption :=
  repeat match goal with
           | [ H : lc_list (_ :: _) |- _ ] => inversion_clear H
         end;
  assumption.

Tactic Notation "lc" tactic(tac) := tac; try lc_assumption.

Fixpoint open_telescope (k : nat) (rhos : list type) (t : type) : type :=
  match rhos with
    | nil => t
    | first :: rest => open_rec (k + length rest) first (open_telescope k rest t)
  end.

Notation "t [ ^ rhos // n ]" := (open_telescope n rhos t) (at level 66).
Notation "t [ ^ rhos ]" := (open_telescope 0 rhos t) (at level 66).
Notation "ts [ ^^ rhos // n ]" := (map (open_telescope n rhos) ts) (at level 66).
Notation "ts [ ^^ rhos ]" := (map (open_telescope 0 rhos) ts) (at level 66).

Fixpoint fv t :=
  match t with
    | TFVar (v x) => \{x}
    | TFVar (fl _) => \{}
    | TBVar _ => \{}
    | TFun f ty => \{f} \u (fv ty)
    | TArrow ty1 ty2 => (fv ty1) \u (fv ty2)
    | TTycon x => \{x}
    | TForAll k ty => (fv ty)
    | TApp t1 t2 => (fv t1) \u (fv t2)
  end.
(*
Fixpoint subst (z : var) (u : type) (t : type) {struct t} :=
  match t with
    | TFVar (v x) => If x = z then u else t
    | TForAllTy k ty => TForAllTy (subst z u k) (subst z u ty)
    | TApp t1 t2 => TApp (subst z u t1) (subst z u t2)
    | x => x
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 67).

Lemma subst_preserves_length : forall rhos ts,
  length ts = length (ts[^^rhos]).
Proof.
  symmetry. apply map_length.
Qed.

(*
Lemma subst_lc_id_core : forall t j v i u,
  i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) ->
  t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ; simpl in *; inverts Equ; try reflexivity.
    eq_nat_decide.
    simpl in H0. eq_nat_decide.

    f_equal.
      eauto.
      apply not_eq_S in Neq. eauto.

    f_equal; eauto.
Qed.
*)

Lemma subst_lc_gen_id : forall n t,
  lc_gen n t -> forall n0, n <= n0 -> forall a, {n0 ~> a}t = t.
Proof.
  induction 1; simpl; intros; try reflexivity.
  eq_nat_decide.
  f_equal.
    eapply IHlc_gen1. eassumption.
    apply IHlc_gen2 with (n0 := S n0). omega.

  f_equal.
    eapply IHlc_gen1. eassumption.
    eapply IHlc_gen2. eassumption.
Qed.

Lemma subst_lc_id : forall t,
  lc t -> forall n a, {n ~> a}t = t.
Proof.
  intros. apply subst_lc_gen_id with (n := 0). assumption. omega.
Qed.

Lemma subst_lc_tel_gen_id : forall rhos n t,
  lc t -> t[^rhos // n] = t.
Proof.
  induction rhos; simpl; intros.
    reflexivity.
    rewrite IHrhos by assumption. rewrite subst_lc_id by assumption. reflexivity.
Qed.

Lemma subst_lc_tel_id : forall rhos t,
  lc t -> t[^rhos] = t.
Proof.
  intros. apply subst_lc_tel_gen_id. assumption.
Qed.

Lemma subst_n : forall n t,
  {n ~> t}TBVar n = t.
Proof.
  intros. simpl. eq_nat_decide.
Qed.

Lemma subst_not_n : forall n1 n2 t,
  n1 <> n2 -> {n1 ~> t}TBVar n2 = TBVar n2.
Proof.
  intros. simpl. eq_nat_decide.
Qed.

Lemma subst_open : forall x u t1 t2, lc u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; fequals*.
  case_var*. rewrite subst_lc_id by lc_assumption. reflexivity.
  eq_nat_decide.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*.
Qed.

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> lc u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite subst_open by lc_assumption. 
  rewrite* subst_fresh. simpl. case_var*.
Qed.

Lemma lc_gen__lc_gen : forall n1 t,
  lc_gen n1 t -> forall n2, n1 <= n2 -> lc_gen n2 t.
Proof.
  induction 1; simpl; intros; try constructor; auto.
  omega.
  apply IHlc_gen2. omega.
Qed.

Lemma lc__lc_gen : forall t,
  lc t -> forall n, lc_gen n t.
Proof.
  intros. eapply lc_gen__lc_gen. eassumption. omega.
Qed.

Lemma subst_lc_gen : forall t n z u,
  lc u -> lc_gen n t -> lc_gen n ([z ~> u]t).
Proof.
  induction 2; simpl; intros; try solve [constructor; auto].
  case_var*. apply lc__lc_gen. assumption.
  constructor.
Qed.

Lemma subst_lc : forall t z u,
  lc u -> lc t -> lc ([z ~> u]t).
Proof.
  intros. apply subst_lc_gen; assumption.
Qed.

(** ** Opening a body with a term gives a term *)

(*
Lemma lc_gen_S__exists_L : forall n t,
  lc_gen (S n) t -> exists L, forall x, x \notin L -> lc_gen n ({n ~> TFVar x}t).
Proof.
  introv Hlc. remember (S n). gen n.
  induction Hlc; simpl; intros; try solve [exists (\{} : vars); intros; constructor].
  exists (\{} : vars). intros. eq_nat_decide. constructor. constructor. omega.
  pose proof Heqn0 as Heqn0'.
  apply IHHlc1 in Heqn0. inverts Heqn0. 
  apply eq_S in Heqn0'. apply IHHlc2 in Heqn0'. inverts Heqn0'.
  exists (x \u x0). intros. constructor.
    apply H. auto.
    apply H0. auto.
  pose proof Heqn0 as Heqn0'.
  apply IHHlc1 in Heqn0. inverts Heqn0.
  apply IHHlc2 in Heqn0'. inverts Heqn0'.
  exists (x \u x0). intros. constructor.
    apply H. auto.
    apply H0. auto.
Qed.

Lemma lc_body__exists_L : forall t,
  lc_body t -> exists L, forall x, x \notin L -> lc (t ^ x).
Proof.
  intros. apply lc_gen_S__exists_L. assumption.
Qed.
*)

Lemma open_lc_gen : forall n u t,
  lc_gen (S n) t -> lc u -> lc_gen n ({n ~> u}t).
Proof.
  introv Hlc_gen. remember (S n). gen n. induction Hlc_gen; intros; try solve [constructor].
    simpl. eq_nat_decide. lc apply lc__lc_gen. constructor. omega.
    constructor; auto.
    constructor; auto.
Qed.

Lemma open_lc : forall t u,
  lc_body t -> lc u -> lc (t ^^ u).
Proof.
  intros. lc apply open_lc_gen.
Qed.

Lemma subst_diff_comm : forall t n1 n2 a1 a2,
  lc a1 -> lc a2 -> n1 <> n2 ->
  {n1 ~> a1}({n2 ~> a2}t) = {n2 ~> a2}({n1 ~> a1}t).
Proof.
  induction t; simpl; intros; try reflexivity.
    eq_nat_decide; subst; repeat rewrite subst_n;
                          repeat (rewrite subst_not_n by assumption);
                          repeat (rewrite subst_lc_id by assumption);
                          try reflexivity; try omega.
    f_equal; auto.
    f_equal; auto.
Qed.

Lemma subst_one_tel_comm_geq : forall rhos t a n n',
  lc a -> lc_list rhos -> n' >= n + length rhos ->
  {n' ~> a}(t[^rhos // n]) = ({n' ~> a}t)[^rhos // n].
Proof.
  induction rhos; simpl; intros.
    reflexivity.
    rewrite subst_diff_comm. rewrite IHrhos. reflexivity.
    assumption. inversion H0. assumption. omega. assumption. inversion H0.
    assumption. omega.
Qed.

Lemma subst_one_tel_comm : forall rhos t a n,
  lc a -> lc_list rhos ->
  {n + length rhos ~> a}(t[^rhos // n]) = ({n + length rhos ~> a}t)[^rhos // n].
Proof.
  intros. apply subst_one_tel_comm_geq.
    assumption. assumption. omega.
Qed.

Ltac subst_one_tel_comm :=
  rewrite subst_one_tel_comm by lc_assumption.

Lemma subst_one_tel_comm_0 : forall rhos t a,
  lc a -> lc_list rhos ->
  {length rhos ~> a}(t[^rhos]) = ({length rhos ~> a}t)[^rhos].
Proof.
  intros. pose proof (@subst_one_tel_comm rhos t a 0) as Hsubst. simpl in Hsubst.
  apply Hsubst; lc_assumption.
Qed.

Lemma subst_comm : forall rhos t n,
  lc_list rhos ->
  t[^rhos // n] =
    match t with
      | TBVar _ => t[^rhos // n] (* nothing to say here *)
      | TForAllTy kind ty => TForAllTy (kind[^rhos //n]) (ty[^rhos // S n])
      | TApp ty1 ty2 => TApp (ty1[^rhos//n]) (ty2[^rhos//n])
      | x => x
    end.
Proof.
  induction rhos; destruct t; simpl; intros; try reflexivity;
  try (subst_one_tel_comm; simpl; apply IHrhos; lc_assumption).
  subst_one_tel_comm. simpl. rewrite IHrhos. f_equal.
    subst_one_tel_comm. reflexivity.
    rewrite subst_one_tel_comm_geq. reflexivity.
    lc_assumption. lc_assumption. omega. lc_assumption.

  subst_one_tel_comm. simpl. rewrite IHrhos.
  f_equal; subst_one_tel_comm; reflexivity. lc_assumption.
Qed.

Lemma subst_bvar_tel : forall rhos n m t,
  lc_list rhos -> n >= m -> RNth (n - m) rhos t -> (TBVar n)[^ rhos // m] = t.
Proof.
  induction rhos; simpl; introv Hlc_rhos Hge HRNth.
    contradict HRNth. apply RNth_nil.
    destruct (eq_nat_decide (n - m) (length rhos)); eq_nat.
      rewrite subst_one_tel_comm by lc_assumption. simpl. eq_nat_decide.
      rewrite e in HRNth. apply RNth_here_inv in HRNth. rewrite HRNth.
      lc apply subst_lc_tel_gen_id.

    lc rewrite IHrhos with (t := t). apply subst_lc_id. eapply RNth_Forall; eassumption.
    inverts HRNth. omega. assumption.
Qed.

Lemma subst_tel_too_low : forall rhos n m,
  n < m ->
  (TBVar n)[^ rhos // m] = TBVar n.
Proof.
  induction rhos; simpl; introv Hlt.
    reflexivity.
    rewrite IHrhos by assumption. rewrite subst_not_n. reflexivity. omega.
Qed.

Lemma subst_bvar_tel_inv : forall rhos n m t,
  lc_list rhos ->
  t = (TBVar n)[^ rhos // m] ->
  (RNth (n - m) rhos t /\ m <= n < length rhos + m) \/
  (t = TBVar n /\ (n >= length rhos + m \/ n < m)).
Proof.
  induction rhos; simpl; introv Hlc_rhos Ht.
    right. split. assumption. omega.
    destruct (between_dec n m (length rhos + m)) as [[Hlt | Hbetween] | Hgt].
      right. split. rewrite Ht. lc rewrite subst_one_tel_comm_geq. simpl. 
        eq_nat_decide. apply subst_tel_too_low. omega. omega. omega.

      left. split. constructor. specialize (IHrhos n m t). lc lapplies IHrhos.
        inverts H0. tauto.
        inverts H. omega.
        rewrite Ht. lc rewrite subst_one_tel_comm. simpl. eq_nat_decide.
        omega.

      inverts Hgt.
      left. split. replace (length rhos + m - m) with (length rhos) by omega.
        rewrite Ht. lc rewrite subst_one_tel_comm. simpl. eq_nat_decide.
        lc rewrite subst_lc_tel_gen_id. constructor.
        omega.

      right. split. rewrite Ht. lc rewrite subst_one_tel_comm_geq. simpl.
        eq_nat_decide.
        specialize (IHrhos (S m0) m (TBVar (S m0) [^rhos//m])). lc lapplies IHrhos. intuition.
        reflexivity. omega.
        omega. 
Qed.

Lemma subst_tel_lc : forall rhos t,
  lc_list rhos -> lc_gen (length rhos) t -> lc (t [^rhos]).
Proof.
  induction rhos; simpl; introv Hrhos Hlc.
    assumption.
    lc rewrite subst_one_tel_comm_0. lc apply IHrhos. lc apply open_lc_gen.
Qed.
*)