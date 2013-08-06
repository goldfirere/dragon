Require Import LibVar.
Require Import LibEnv.

Require Import type coercion.

Set Implicit Variables.

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

