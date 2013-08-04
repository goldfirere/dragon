Require Import LibVar.
Require Import LibTactics.
Require Import List.

Require Import tactics utils.

Set Implicit Arguments.

Inductive type :=
| TFVar : var -> type
| TBVar : nat -> type
| TFun : var -> type
| TArrow : type
| TStar : type
| TTycon : var -> type
| TForAllTy : type -> type -> type
| TApp : type -> type -> type.

Inductive assumpt :=
| Ax : var -> list type -> var -> list type -> type -> assumpt.

Definition context := list assumpt.

Definition app_list t ts := fold_left TApp ts t.

Lemma app_list__app : forall ts t1,
  app_list t1 ts = t1 \/ exists ts1 s2, (app_list t1 ts = TApp (app_list t1 ts1) s2 /\
                                         ts = ts1 ++ s2 :: nil).
Proof.
  induction ts using rev_ind; intros.
    left. reflexivity.
    right. unfold app_list in *. rewrite fold_left_app. simpl. eauto.
Qed.

Ltac app_list :=
  let Happ := fresh in
  let Hcase := fresh in
  let Hcase' := fresh in
  let go Happ_list head list :=
      pose (app_list__app list head) as Happ; inverts Happ as; intro Hcase;
      [ rewrite Hcase in Happ_list; try discriminate |
        inversion_clear Hcase as [? [? [Hcase' ?]]]; rewrite Hcase' in Happ_list; try discriminate
      ] in
  match goal with
    | [ H : app_list ?head ?list = _ |- _ ] => go H head list
    | [ H : _ = app_list ?head ?list |- _ ] => go H head list
  end.

Lemma app_list_snoc : forall ts t1 tlast,
  app_list t1 (ts ++ tlast :: nil) = TApp (app_list t1 ts) tlast.
Proof.
  induction ts; simpl; intros; auto.
Qed.

Lemma app_list_inv : forall F1 F2 ts1 ts2,
  app_list (TFun F1) ts1 = app_list (TFun F2) ts2 ->
  (F1 = F2 /\ ts1 = ts2).
Proof.
  induction ts1 using rev_ind; simpl; introv Happ.
  app_list. inverts Happ.
  rev_destruct ts2. auto. rewrite app_list_snoc in H0. discriminate.
  rewrite app_list_snoc in Happ.
  rev_destruct ts2.
    simpl in Happ. discriminate.
    rewrite app_list_snoc in Happ. inverts Happ.
    apply IHts1 in H0. intuition. f_equal. assumption.
Qed.