Require Import LibLN.
Require Import List.

Require Import type subst.

Inductive coercion :=
| CRefl : type -> coercion
| CSym  : coercion -> coercion
| CTrans : coercion -> coercion -> coercion
| CArrow : coercion -> coercion -> coercion
| CForAll : kind -> coercion -> coercion
| CApp : coercion -> coercion -> coercion
| CLeft : coercion -> coercion
| CRight : coercion -> coercion
| CFun : var -> coercion -> coercion
| CAx : var -> list type -> coercion.

Fixpoint open_co_rec (k : nat) (u : type) (co : coercion) {struct co} : coercion :=
  match co with
    | CRefl ty => CRefl (open_rec k u ty)
    | CSym co => CSym (open_co_rec k u co)
    | CTrans co1 co2 => CTrans (open_co_rec k u co1) (open_co_rec k u co2)
    | CArrow co1 co2 => CArrow (open_co_rec k u co1) (open_co_rec k u co2)
    | CForAll ki co => CForAll ki (open_co_rec (S k) u co)
    | CApp co1 co2 => CApp (open_co_rec k u co1) (open_co_rec k u co2)
    | CLeft co => CLeft (open_co_rec k u co)
    | CRight co => CRight (open_co_rec k u co)
    | CFun f co => CFun f (open_co_rec k u co)
    | CAx ax tys => CAx ax (map (open_rec k u) tys)
  end.

Definition open_co co u := open_co_rec 0 u co.

Notation "{ k ~> u } t" := (open_co_rec k u t) (at level 66) : Co_scope.
Notation "t ^^ u" := (open_co t u) (at level 67) : Co_scope.
Notation "t ^ x" := (open_co t (TFVar (v x))) : Co_scope.

Delimit Scope Co_scope with Co.
Bind Scope Co_scope with coercion.

Reserved Notation "Si ; D |-co g ~: t1 ~~ t2" (at level 67, t1 at next level).
Inductive co_kind : gr_ctxt -> var_ctxt -> coercion -> type -> type -> Prop :=
| CKRefl : forall Si D t k,
             Si ; D |-ty t ~: k ->
             (Si ; D |-co CRefl t ~: t ~~ t)
| CKSym : forall Si D g t1 t2,
            Si ; D |-co g ~: t1 ~~ t2 ->
            Si ; D |-co CSym g ~: t2 ~~ t1
| CKTrans : forall Si D g1 g2 t1 t2 t3,
              Si ; D |-co g1 ~: t1 ~~ t2 ->
              Si ; D |-co g2 ~: t2 ~~ t3 ->
              Si ; D |-co CTrans g1 g2 ~: t1 ~~ t3
| CKArrow : forall Si D g1 g2 t1 t1' t2 t2',
              Si ; D |-co g1 ~: t1 ~~ t2 ->
              Si ; D |-co g2 ~: t1' ~~ t2' ->
              Si ; D |-co CArrow g1 g2 ~: TArrow t1 t1' ~~ TArrow t2 t2'
| CKForAll : forall L Si D g k t1 t2,
             dom D \c L ->
             (forall a, a \notin L ->
                        Si ; (D & a ~ k) |-co (g ^ a) ~: t1 ~~ t2) ->
             Si ; D |-co CForAll k g ~: TForAll k t1 ~~ TForAll k t2
| CKApp : forall Si D g1 g2 t1 t1' t2 t2',
            Si ; D |-co g1 ~: t1 ~~ t2 ->
            Si ; D |-co g2 ~: t1' ~~ t2' ->
            Si ; D |-co CApp g1 g2 ~: TApp t1 t1' ~~ TApp t2 t2'
| CKLeft : forall Si D g t1 t1' t2 t2',
             Si ; D |-co g ~: TApp t1 t1' ~~ TApp t2 t2' ->
             Si ; D |-co CLeft g ~: t1 ~~ t2
| CKRight : forall Si D g t1 t1' t2 t2',
              Si ; D |-co g ~: TApp t1 t1' ~~ TApp t2 t2' ->
              Si ; D |-co CRight g ~: t1' ~~ t2'
| CKFun : forall Si D g t1 t2 f,
            Si ; D |-co g ~: t1 ~~ t2 ->
            Si ; D |-co CFun f g ~: TFun f t1 ~~ TFun f t2
| CKAx : forall ax ks f typat rhs axs funs tcs D tys,
           ok_gr (funs, axs, tcs) -> ok D ->
           binds ax (mkAxiom ks f typat rhs) axs ->
           (funs, axs, tcs); D |-co CAx ax tys ~: TFun f (typat [^tys]) ~~ (rhs[^tys])
where "Si ; D |-co g ~: t1 ~~ t2" := (co_kind Si D g t1 t2).

Fixpoint sum ns :=
  match ns with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Lemma sum_app : forall xs ys,
  sum (xs ++ ys) = sum xs + sum ys.
Proof.
  induction xs; intros.
    simpl. auto.
    simpl. rewrite IHxs. omega.
Qed.

Fixpoint size_of_co co :=
  match co with
    | CRefl ty => S (size_of_ty ty)
    | CSym co => S (size_of_co co)
    | CTrans co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CArrow co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CForAll k co => S (size_of_co co)
    | CApp co1 co2 => S (size_of_co co1 + size_of_co co2)
    | CLeft co => S (size_of_co co)
    | CRight co => S (size_of_co co)
    | CFun _ co => S (size_of_co co)
    | CAx _ tys => S (sum (map size_of_ty tys))
  end.
