Require Import LibLN.
Require Import LibTactics.
Require Import Arith.
Require Import List.
Require Import Program.
Require Import ListSet.

Require Import coercion good unify type tactics subst co_kind subset.

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

Obligation Tactic := idtac.
Unset Transparent Obligations.
Unset Implicit Arguments.
Program Fixpoint go funs axs tcs g t1 t2
  (Hgood : Good axs)
  (Hck : (funs, axs, tcs) |-co g ~: t1 ~~ t2) 
  { measure (size_of_co g) } :
  go_result_type (funs,axs,tcs) t1 t2 (size_of_co g) :=
  match g with
    | CRefl ty => existT _ 0 (existT _ 0 (existT _ nil (nilSubst _, nilSubst _)))
    | CSym g2 =>  _ (* Coq didn't like this case, so it's done in proof mode *)
    | CTrans g1 g2 =>
      let fix trans_unify n Si dom1 n1 n3a dom2 n3b n2 
                 (w1 : substn Si dom1 n1) (w3a : substn Si dom1 n1)
                 (w3b : substn Si dom2 n3b) (w2 : substn Si dom2 n2)
                 (t1 t3 t2 : type) 
                 (HNoDup1 : NoDup dom1) (HNoDup2 : NoDup dom2)
                 (Heq13 : apply w1 t1 = apply w3a t3)
                 (Heq32 : apply w3b t3 = apply w2 t2) :
       go_result_type Si t1 t2 n :=
         let ex_w3a' := fix_dom w3a w3b _ _ in
         match ex_w3a' with
           | existT dom w3a' =>
         let ex_w3b' := fix_dom w3b w3a' _ _ in
         match ex_w3b' with
           | existT dom' w3b' => (* ASSERT(dom == dom') *)
         match w3a' with
           | nilSubst => let ex_w1' := fix_dom w1 w2 _ _ in
                         match ex_w1' with
                           | existT out_dom w1' =>
                         let ex_w2' := fix_dom w2 w1' _ _ in
                         match ex_w2' with
                           | existT out_dom1 w2' =>
                         existT _ n1 (existT _ n2 (existT _ out_dom (w1', w2')))
                         end end
           | consSubst _ _ _ _ _ _ _ _ => undefined
         end
         end end
      in
      let cKind := coercionKind funs axs tcs g1 _ in
      match cKind with
        | (_t1, t3) =>
      let res1 := go funs axs tcs g1 t1 t3 Hgood _ in
      let res2 := go funs axs tcs g2 t3 t2 Hgood _ in
      match res1 with
        | existT n1 (existT n3a (existT dom1 (exist (w1, w3a) _))) =>
      match res2 with
        | existT n3b (existT n2 (existT dom2 (exist (w3b, w2) _))) =>
      trans_unify (size_of_co g) (funs,axs,tcs) dom1 n1 n3a dom2 n3b n2
                  w1 w3a w3b w2 t1 t3 t2 _ _ _ _
      end end end
    | _ => undefined
  end.

Obligation Tactic := program_simpl.

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

Next Obligation. Defined.    
Obligation Tactic := idtac.
Next Obligation. program_simpl. Defined.
Next Obligation. program_simpl. Defined.
Next Obligation. program_simpl. Defined.
Next Obligation. program_simpl. Defined.
Next Obligation. intros. assumption. Defined.
Next Obligation. intros. assumption. Defined.
Next Obligation. intros. destruct w1'. destruct_pairs. assumption. Defined.
Next Obligation.
  intros. destruct w2'. destruct_pairs. apply e0.
  destruct w1'. destruct_pairs. assumption.
Defined.

Ltac clear_ugliness :=
  repeat match goal with
           | [ Heq_blah : existT _ _ _ = _ |- _ ] => clear Heq_blah
         end.

Next Obligation.
  intros. simpl. squash_eq_rect.
  destruct w1'. destruct w2'. simpl.
  repeat split.
  - unfold apply. clear Heq_ex_w2'. clear ex_w2'. clear Heq_ex_w1'. clear ex_w1'.
    destruct_pairs. rewrite H5. rewrite H. subst*. clear_ugliness.
    unfolds apply. rewrite Heq13. generalize w3a. clear Heq13. destruct w3a'.
    clear go. destruct w3b'. destruct_pairs. rewrite <- Heq_n1. intro.
    rewrite apply_w_size0. rewrite <- Heq32.



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
  

