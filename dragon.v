Require Import LibLN.
Require Import LibTactics.
Require Import Arith.
Require Import List.
Require Import Program.
Require Import ListSet.

Require Import coercion good unify type tactics subst co_kind.

Set Implicit Arguments.

Definition dom_union := set_union domelt_eq_decide.

Fixpoint dom_of_ty (ty : type) : list (var * type) :=
  match ty with
    | TBVar _ => nil
    | TFun f lhs => (f,lhs) :: nil
    | TArrow arg res => dom_union (dom_of_ty arg) (dom_of_ty res)
    | TTycon T => nil
    | TApp t1 t2 => dom_union (dom_of_ty t1) (dom_of_ty t2)
  end.

Definition dom_of_tys t1 t2 : list (var * type) :=
  dom_union (dom_of_ty t1) (dom_of_ty t2).

Definition go_result_type Si t1 t2 n :=
  sigT ( fun n1 : nat =>
  sigT ( fun n2 : nat =>
  sigT ( fun dom : list (var * type) =>
  sig  ( fun subs : (substn Si dom n1 * substn Si dom n2) =>
    apply (fst subs) t1 = apply (snd subs) t2 /\
    n1 <= n /\
    n2 <= n )))).

Definition swap Si t1 t2 n (res1 : go_result_type Si t1 t2 n) : go_result_type Si t2 t1 n.
  destruct res1. destruct s. destruct s. destruct s.
  unfold go_result_type. exists x0. exists x. exists x1. exists (snd x2, fst x2).
  simpl. intuition.
Qed.

Obligation Tactic := Tactics.program_simpl.
Unset Transparent Obligations.
Unset Implicit Arguments.
Program Fixpoint go funs axs tcs g t1 t2
  (Hgood : Good axs)
  (Hck : (funs, axs, tcs) |-co g ~: t1 ~~ t2) 
  { measure (size_of_co false g) } :
  go_result_type (funs,axs,tcs) t1 t2 (size_of_co false g) :=
  match g with
    | CRefl ty => existT _ 0 (existT _ 0 (existT _ nil (nilSubst _ _, nilSubst _ _)))
    | CSym g2 =>  _ (* Coq didn't like this case, so it's done in proof mode *)
    | CTrans g1 g2 =>
      let cKind := coercionKind funs axs tcs g1 _ in
      match cKind with
        | exist (_t1, t3) _ =>
      let res1 := go funs axs tcs g1 t1 t3 Hgood _ in
      let res2 := go funs axs tcs g2 t3 t2 Hgood _ in
      match res1 with
        | existT n1 (existT n3a (existT dom1 (exist (w1, w3a) _))) =>
      match res2 with
        | existT n3b (existT n2 (existT dom2 (exist (w3b, w2) _))) =>
      trans_unify w1 w3a w3b w2 t1 t3 t2
                 
        res1 := go funs axs tcs g1
  end.

Next Obligation.
  inverts Hck. intuition.
Qed.

Next Obligation.
  (* sym case *)
  unfolds go_result_type.
  specialize (go funs axs tcs g2 t2 t1).
  lapplies go.
  - destruct H. destruct s. destruct s. destruct s. destruct a. destruct H0.
    exists x0. exists x. exists x1. exists (snd x2, fst x2). simpl. intuition.
  - simpl. omega.
  - inverts Hck. auto.
  - auto.
Qed.

Next Obligation.
  


    | CTrans co1 co2 => let t3 := snd (coercionKind funs axs tcs D co1 _) in
                        let (sx1, sx3) := go funs axs tcs D co1 t1 t3 Hgood _ in
                        let (sx3', sx2) := go funs axs tcs D co2 t3 t2 Hgood _ in
                        if elt_in_common_dec sx1 sx2
                        then undefined
                        else combine sx1 sx2 _ *)
    | CArrow co1 co2 => undefined
    | CForAll k co => undefined
    | CApp co1 co2 => undefined
    | CLeft co => undefined
    | CRight co => undefined
    | CFun f co => undefined
    | CAx ax tys => undefined
  end.




Definition element_in_common {Si D m n} (sx1 : substnX Si D m)
                                        (sx2 : substnX Si D n) : Prop :=
  exists xv, xv_in_subx xv sx1 /\ xv_in_subx xv sx2.

Definition decide (P : Prop) :=
  sumbool P (~P).

Definition elt_in_common_dec {Si D m n} (sx1 : substnX Si D m)
                                        (sx2 : substnX Si D n) :
  decide (element_in_common sx1 sx2).
Proof.
  refine (let mxs1 := proj1_sig sx1 in
          let mxs2 := proj1_sig sx2 in
          let fix xv_in_mxs xv mxs : decide (xv_in_mx_list xv mxs) :=
              match mxs with
                | nil => right _
                | mx :: mxs => if xvar_eq_decide xv (fst (fst (proj1_sig mx)))
                               then left _
                               else if xv_in_mxs xv mxs then left _ else right _
              end in
          let fix recur mxs :
                decide (exists xv, xv_in_mx_list xv mxs /\ xv_in_mx_list xv mxs2) :=
              match mxs with
                | nil => right _
                | mx :: mxs => if xv_in_mxs (fst (fst (proj1_sig mx))) mxs2
                               then left _
                               else if recur mxs then left _ else right _
              end in
          if recur mxs1 then left _ else right _);
  unfolds xv_in_mx_list.
  - intro Hcon. inverts Hcon. tauto.
  - exists mx. split. apply in_eq. auto.
  - inverts _H0. exists x. split; try tauto. apply in_cons. tauto.
  - intro Hcon. inverts Hcon. inverts H. apply in_inv in H0. inverts H0.
    auto. unfold not in _H0. lapplies _H0. auto. exists x. tauto.
  - intro Hcon. inverts Hcon. inverts H. inverts H0. tauto.
  - inverts _H. exists (fst (fst (proj1_sig mx))). split. exists mx. split.
    apply in_eq. auto. exists x. auto.
  - inverts _H0. inverts H. inverts H0. inverts H1. exists x. split.
    exists x0. split. apply in_cons. tauto. tauto. exists x1. auto.
  - intro Hcon. inverts Hcon. inverts H. inverts H0. inverts H. apply in_inv in H0.
    inverts H0. apply _H in H1. auto. inverts H1.
    unfold not in _H0. lapplies _H0. auto. exists (fst (fst (proj1_sig x0))). split.
    exists x0. tauto. exists x. auto.
  - unfold element_in_common. inverts _H. unfold xv_in_subx. unfold xv_in_mx_list.
    exists x. auto.
  - auto.
Qed.

Definition combine {Si D m n} (sx1 : substnX Si D m) (sx2 : substnX Si D n)
  (Hdistinct : ~ element_in_common sx1 sx2) : substnX Si D (m + n).
  refine (let mxs1 := proj1_sig sx1 in
          let mxs2 := proj1_sig sx2 in
          exist _ (mxs1 ++ mxs2) _).
  rewrite map_app. rewrite sum_app. pose proof (proj2_sig sx1). pose proof (proj2_sig sx2).
  simpls. unfold mxs1. unfold mxs2. omega.
Qed.

Definition pair x := (x * x)%type.
Definition swap {A} (x : pair A) := let (a,b) := x in (b,a).

Lemma fst_swap : forall {A} (x : pair A),
  fst (swap x) = snd x.
Proof.
  intros. destruct x. auto.
Qed.

Lemma snd_swap : forall {A} (x : pair A),
  snd (swap x) = fst x.
Proof.
  intros. destruct x. auto.
Qed.


Obligation Tactic := Tactics.program_simpl.
Unset Transparent Obligations.
Program Fixpoint go funs axs tcs D g t1 t2
  (Hgood : Good axs)
  (Hck : (funs, axs, tcs); D |-co g ~: t1 ~~ t2) 
  { measure (size_of_co g) } :
    sig (fun two_subx : pair (substnX (funs, axs, tcs) D (size_of_co g)) =>
           let sub1 := sub_from_subx (fst two_subx) in
           let sub2 := sub_from_subx (snd two_subx) in
           apply sub1 (flatten t1) = apply sub2 (flatten t2)) :=
  match g with
    | CRefl ty => (nil, nil)
    | CSym co => swap (go funs axs tcs D co t2 t1 Hgood _)
    | CTrans co1 co2 => let t3 := snd (coercionKind funs axs tcs D co1 _) in
                        let (sx1, sx3) := go funs axs tcs D co1 t1 t3 Hgood _ in
                        let (sx3', sx2) := go funs axs tcs D co2 t3 t2 Hgood _ in
                        if elt_in_common_dec sx1 sx2
                        then undefined
                        else combine sx1 sx2 _ *)
    | CArrow co1 co2 => undefined
    | CForAll k co => undefined
    | CApp co1 co2 => undefined
    | CLeft co => undefined
    | CRight co => undefined
    | CFun f co => undefined
    | CAx ax tys => undefined
  end.
Obligation Tactic :=
  Tactics.program_simpl;
  repeat abstract_sig;
  try omega;
  try solve [match goal with
               | [ Hck : _;_ |-co _ ~: _ ~~ _ |- _ ] => inversion Hck
             end; auto].
Solve Obligations.

Ltac abstract_go :=
  let ss := fresh in
  let Hs := fresh in
  match goal with
    | [ |- context[proj1_sig ?blah] ] =>
  match blah with
    | _ _ _ _ _ _ _ _ _ _ _ => generalize blah; intro ss;
                                         pose proof (proj2_sig ss) as Hs;
                                         simpl in Hs
  end end.

(*
Ltac obtac :=
  intros; simpls; try match goal with
                        | [ g : coercion |- _ ] =>
                      match goal with
                        | [ Heq_g : _ = g |- _ ] => rewrite <- Heq_g in *
                      end end.

(* Obligation Tactic := obtac. *)
*)
Next Obligation.
  unfold sub_from_subx. simpl.
  abstract_go.
  unfold sub_from_subx in H0. rewrite fst_swap. rewrite snd_swap.
  symmetry. auto.
Qed.

Next Obligation.
  inverts Hck. eauto.
  Obligation Tactic := idtac. (* for some reason, Coq gets stuck without this *)
Qed.

Next Obligation.
  intros. unfold t3. abstract_sig. clear t3. rewrite <- Heq_g in Hck.
  inverts Hck. apply co_kind_det with (t1 := t1) (t2 := t3) in H0; auto.
  intuition; subst; auto.
Qed.

Next Obligation.
  intros. rewrite <- Heq_g.
  simpl; omega.
Qed.  

Next Obligation.
  intros. unfold t3. clear sx3 sx1 t3. abstract_sig. rewrite <- Heq_g in Hck.
  inverts Hck. apply co_kind_det with (t1 := t1) (t2 := t3) in H0; auto.
  intuition; subst; auto.
Qed.

Next Obligation.
  intros. rewrite <- Heq_g. simpl. omega.
Qed.  

  Tactics.program_simpl. simpl. omega.
Qed.

Next Obligation.
  intros. auto.
Qed.

Lemma size_of_combine : forall Si D m n (sx1 : substnX Si D m) (sx2 : substnX Si D n) pf,
  sum (map size_of_mxco (proj1_sig (combine sx1 sx2 pf))) <= m + n.
Proof.
  intros. abstract_sig. auto.
Qed.

Next Obligation.
  intros. abstract_sig.

  assert ((size_of_co (CTrans co1 co2)) = (S (size_of_co co1 + size_of_co co2))).
  simpl; auto.
  
  rewrite H0.
 replace 
unfold sx1 in *. unfold sx2 in *. clear sx1 sx2. abstract_go.
admit. (* bug in Coq, I think. The above Lemma proves this case. *)
Qed.

Next Obligation.
  intros. unfold sub_from_subx in sub. unfold proj1_sig in sub. simpl in sub


Theorem dragon : forall axs funs tcs D g t1 t2,
  Good axs ->
  (funs, axs, tcs); D |-co g ~: t1 ~~ t2 ->
  unifies (flatten t1) (flatten t2).
Proof.
  

