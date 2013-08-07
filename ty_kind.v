Require Import LibVar.
Require Import LibEnv.
Require Import LibTactics.

Require Import type coercion var tactics.

Set Implicit Arguments.

Definition fun_ctxt := env (kind * kind).
Definition ax_ctxt  := env axiom.
Definition tc_ctxt  := env kind.

Definition ctxt := (fun_ctxt * ax_ctxt * tc_ctxt)%type.

Definition ok_ctxt (Si : ctxt) :=
  match Si with
    | (funs, axs, tcs) => ok funs /\ ok axs /\ ok tcs
  end.

Reserved Notation "Si |-ty t ~: k" (at level 67).
Inductive ty_kind : ctxt -> type -> kind -> Prop :=
| TKFun : forall f k1 k2 funs axs tcs ty,
            binds f (k1, k2) funs ->
            (funs, axs, tcs) |-ty ty ~: k1 ->
            (funs, axs, tcs) |-ty TFun f ty ~: k2
| TKArrow : forall Si t1 t2,
              Si |-ty t1 ~: KStar ->
              Si |-ty t2 ~: KStar ->
              Si |-ty TArrow t1 t2 ~: KStar
| TKTyCon : forall tcs T k funs axs,
              ok_ctxt (funs, axs, tcs) ->
              binds T k tcs ->
              (funs, axs, tcs) |-ty TTycon T ~: k
| TKApp : forall Si t1 t2 k1 k2,
            Si |-ty t1 ~: KArrow k1 k2 ->
            Si |-ty t2 ~: k1 ->
            Si |-ty TApp t1 t2 ~: k2
where "Si |-ty t ~: k" := (ty_kind Si t k).

Lemma ty_kind_reg : forall Si t k,
  Si |-ty t ~: k -> ok_ctxt Si.
Proof.
  induction 1; auto.
Qed.

Lemma ty_kind_det : forall Si t k1,
  Si |-ty t ~: k1 ->
  forall k2,
  Si |-ty t ~: k2 ->
  k1 = k2.
Proof.
  induction 1; intros.
  - inverts H1. pose proof (ok__unique f (k1, k2) (k3, k0) funs). lapplies H1.
    inverts H2. reflexivity.
    auto. auto. apply ty_kind_reg in H9. unfold ok_ctxt in H9. tauto.
  - inverts H1. reflexivity.
  - inverts H1. pose proof (ok__unique T k k2 tcs). lapplies H1.
    auto. auto. auto. unfolds ok_ctxt. tauto.
  - inverts H1. apply IHty_kind1 in H5. inverts H5. auto.
Qed.

Unset Implicit Arguments.
Program Fixpoint typeKind Si (ty : type) 
  (Hty : exists k, Si |-ty ty ~: k) :
  { k : kind | Si |-ty ty ~: k } :=
  match Si with
    | (funs, _, tcs) =>
  match ty with
    | TBVar _ => _
    | TFun f ty => match get f funs with
                     | None => _
                     | Some (_, kresult) => kresult
                   end
    | TArrow arg res => KStar
    | TTycon T => match get T tcs with
                    | None => _
                    | Some k => k
                  end
    | TApp t1 _ => let k1 := typeKind Si t1 _ in
                   match k1 with
                     | KStar => _
                     | KArrow _ k2 => k2
                   end
  end end.

Next Obligation.
  exfalso. inverts Hty. inverts H.
Qed.

Next Obligation.
  exfalso. inverts Hty. inverts H. apply binds_get in H6. rewrite H6 in Heq_anonymous.
  discriminate.
Qed.

Next Obligation.
  inverts H. pose proof H6.
  apply binds_get in H6. rewrite H6 in Heq_anonymous. inverts Heq_anonymous. 
  econstructor; eassumption.
Qed.

Next Obligation.
  inverts H. constructor; auto.
Qed.

Next Obligation.
  exfalso. inverts Hty. inverts H. apply binds_get in H6. rewrite H6 in Heq_anonymous.
  discriminate.
Qed.

Next Obligation.
  inverts H. pose proof H6.
  apply binds_get in H6. rewrite H6 in Heq_anonymous. inverts Heq_anonymous.
  econstructor; eassumption.
Qed.

Next Obligation.
  inverts H. eauto.
Qed.

Next Obligation.
  exfalso. inverts Hty. inverts H. apply ty_kind_det with (k1 := KStar) in H3; auto.
  discriminate.
Defined.

Next Obligation.
  econstructor. eassumption. inverts H.
  apply ty_kind_det with (k1 := KArrow k1 Hty) in t; auto. inverts t. auto.
Defined.