Require Import LibLN.
Require Import LibTactics.
Require Import List.
Require Import Arith.

Require Import tactics utils.

Set Implicit Arguments.

Inductive kind :=
| KStar : kind
| KArrow : kind -> kind -> kind.

Inductive type :=
| TFVar : xvar -> type
| TBVar : nat -> type
| TFun : var -> type -> type
| TArrow : type -> type -> type
| TTycon : var -> type
| TForAll : kind -> type -> type
| TApp : type -> type -> type
with xvar :=
| v : var -> xvar
| fl : type -> xvar.

Fixpoint open_rec (k : nat) (u : type) (t : type) {struct t} : type :=
  match t with
    | TBVar i => if eq_nat_decide k i then u else (TBVar i)
    | TFun f ty => TFun f (open_rec k u ty)
    | TArrow t1 t2 => TArrow (open_rec k u t1) (open_rec k u t2)
    | TForAll kind ty => TForAll kind (open_rec (S k) u ty)
    | TApp ty1 ty2 => TApp (open_rec k u ty1) (open_rec k u ty2)
    | _ => t
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 66) : Type_scope.
Notation "t ^^ u" := (open t u) (at level 67) : Type_scope.
Notation "t ^ x" := (open t (TFVar (v x))) : Type_scope.

Bind Scope Type_scope with type.

Inductive axiom :=
| mkAxiom : list kind -> var -> type -> type -> axiom.

Definition fun_ctxt := env (kind * kind).
Definition ax_ctxt  := env axiom.
Definition tc_ctxt  := env kind.
Definition var_ctxt := env kind.

Definition gr_ctxt := (fun_ctxt * ax_ctxt * tc_ctxt)%type.

Definition ok_gr (Si : gr_ctxt) :=
  match Si with
    | (funs, axs, tcs) => ok funs /\ ok axs /\ ok tcs
  end.

Reserved Notation "Si ; D |-ty t ~: k" (at level 67).
Inductive ty_kind : gr_ctxt -> var_ctxt -> type -> kind -> Prop :=
| TKVVar : forall Si D tv k,
             ok_gr Si ->
             ok D ->
             binds tv k D ->
             Si ; D |-ty TFVar (v tv) ~: k
| TKFlVar : forall Si D ty k,
             Si ; D |-ty ty ~: k ->
             Si ; D |-ty (TFVar (fl ty)) ~: k
| TKFun : forall f k1 k2 funs axs tcs D ty,
            binds f (k1, k2) funs ->
            (funs, axs, tcs); D |-ty ty ~: k1 ->
            (funs, axs, tcs); D |-ty TFun f ty ~: k2
| TKArrow : forall Si D t1 t2,
              Si ; D |-ty t1 ~: KStar ->
              Si ; D |-ty t2 ~: KStar ->
              Si ; D |-ty TArrow t1 t2 ~: KStar
| TKTyCon : forall tcs T k funs axs D,
              ok_gr (funs, axs, tcs) ->
              ok D ->
              binds T k tcs ->
              (funs, axs, tcs); D |-ty TTycon T ~: k
| TKForAll : forall L Si D k1 ty,
               (forall a, a \notin L ->
                          Si; (D & a ~ k1) |-ty ty ^ a ~: KStar) ->
               Si; D |-ty TForAll k1 ty ~: KStar
| TKApp : forall Si D t1 t2 k1 k2,
            Si; D |-ty t1 ~: KArrow k1 k2 ->
            Si; D |-ty t2 ~: k1 ->
            Si; D |-ty TApp t1 t2 ~: k2
where "Si ; D |-ty t ~: k" := (ty_kind Si D t k).

Fixpoint size_of_ty ty :=
  match ty with
    | TFVar _ => 1
    | TBVar _ => 1
    | TFun f ty => S (size_of_ty ty)
    | TArrow ty1 ty2 => S (size_of_ty ty1 + size_of_ty ty2)
    | TTycon _ => 1
    | TForAll k ty => S (size_of_ty ty)
    | TApp ty1 ty2 => S (size_of_ty ty1 + size_of_ty ty2)
  end.


(*
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
*)