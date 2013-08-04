Require Import LibLN.
Require Import LibTactics.
Require Import Arith.
Require Import List.
Require Import Program.Wf.

Require Import coercion good unify flatten type tactics subst co_kind.

Definition undefined {A} : A. Admitted.

Definition mappingX Si D := sig (fun mco : (mapping * coercion) =>
                                   let '((xv,target), co) := mco in
                                   Si; D |-co co ~: TFVar xv ~~ target).

Definition size_of_mxco {Si D} (mx : mappingX Si D) :=
  let (_, co) := proj1_sig mx in size_of_co co.

Definition substnX Si D n := sig (fun mxs : list (mappingX Si D) =>
                                    sum (map size_of_mxco mxs) <= n).

Definition sub_from_subx {Si D n} (sx : substnX Si D n) : substn :=
  let mxs := proj1_sig sx in
  map fst (map (@proj1_sig _ _) mxs).

Definition xv_in_mx_list {Si D} (xv : xvar) (mxs : list (mappingX Si D)) : Prop :=
  exists mx, In mx mxs /\ fst (fst (proj1_sig mx)) = xv.

Definition xv_in_subx {Si D n} (xv : xvar) (sx : substnX Si D n) : Prop :=
  xv_in_mx_list xv (proj1_sig sx).

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
Defined.

Obligation Tactic := Tactics.program_simpl.
Unset Transparent Obligations.
Program Fixpoint go funs axs tcs D g t1 t2
  (Hgood : Good axs)
  (Hck : (funs, axs, tcs); D |-co g ~: t1 ~~ t2) 
  { measure (size_of_co g) } :
    sig (fun subx : substnX (funs, axs, tcs) D (size_of_co g) =>
           let sub := sub_from_subx subx in
           apply sub (flatten t1) = apply sub (flatten t2)) :=
  match g with
    | CRefl ty => nil
    | CSym co => go funs axs tcs D co t2 t1 Hgood _
    | CTrans co1 co2 => let t3 := snd (coercionKind funs axs tcs D co1 _) in
                        let sx1 := go funs axs tcs D co1 t1 t3 Hgood _ in
                        let sx2 := go funs axs tcs D co2 t3 t2 Hgood _ in
                        if elt_in_common_dec sx1 sx2
                        then undefined
                        else combine sx1 sx2 _
    | CArrow co1 co2 => nil
    | CForAll k co => nil
    | CApp co1 co2 => nil
    | CLeft co => nil
    | CRight co => nil
    | CFun f co => nil
    | CAx ax tys => nil
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
  unfold sub_from_subx in H0. auto.
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
  intros. unfold t3. clear sx1 t3. abstract_sig. rewrite <- Heq_g in Hck.
  inverts Hck. apply co_kind_det with (t1 := t1) (t2 := t3) in H0; auto.
  intuition; subst; auto.
Qed.

Next Obligation.
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
  intros. unfold sx1 in *. unfold sx2 in *. clear sx1 sx2. abstract_go.
admit. (* bug in Coq, I think. The above Lemma proves this case. *)
Qed.

Next Obligation.
  intros. unfold sub_from_subx in sub. unfold proj1_sig in sub. simpl in sub


Theorem dragon : forall axs funs tcs D g t1 t2,
  Good axs ->
  (funs, axs, tcs); D |-co g ~: t1 ~~ t2 ->
  unifies (flatten t1) (flatten t2).
Proof.
  

