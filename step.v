Require Import LibRelation.
Require Import LibNat.
Require Import List.
Require Import LibTactics.
Require Import LibVar.

Require Import defns subst utils tactics good.

Set Implicit Arguments.

Reserved Notation "G |= t ~Red> t'" (at level 67).

Inductive red_step : context -> type -> type -> Prop :=
  | TS_Red : forall C D F ts t' G rhos,
      lc_list rhos -> length rhos = length D ->
      In (Ax C D F ts t') G -> 
      G |= (app_list (TFun F) (ts[^^rhos])) ~Red> (t'[^rhos])
where "G |= t ~Red> t'" := (red_step G t t').

Reserved Notation "G |= t ~Cong> t'" (at level 67).
Reserved Notation "G |= t ~> t'" (at level 67).

Inductive cong_step : context -> type -> type -> Prop :=
  | TS_Refl : forall G ty, G |= ty ~Cong> ty
  | TS_AllT : forall G k k' s s',
      G |= k ~> k' ->
      G |= s ~> s' ->
      G |= (TForAllTy k s) ~Cong> (TForAllTy k' s')
  | TS_App : forall G t t' s s',
      G |= t ~> t' ->
      G |= s ~> s' ->
      G |= (TApp t s) ~Cong> (TApp t' s')
with step : context -> type -> type -> Prop :=
  | red : forall G t t',
      G |= t ~Red> t' ->
      G |= t ~> t'
  | cong : forall G t t',
      G |= t ~Cong> t' ->
      G |= t ~> t'
where "G |= t ~Cong> t'" := (cong_step G t t')
and   "G |= t ~> t'" := (step G t t').

Scheme cong_step_mut_ind := Induction for cong_step Sort Prop
with   step_mut_ind      := Induction for step      Sort Prop. 

Lemma step_induction :
  forall (P : forall G t t', G |= t ~> t' -> Prop),
  (forall G ty, P G ty ty (cong (TS_Refl G ty))) ->
  (forall G k k' s s' (sk : G |= k ~> k'),
     P G k k' sk ->
     forall (ss : G |= s ~> s'),
       P G s s' ss ->
       P G (TForAllTy k s) (TForAllTy k' s') (cong (TS_AllT sk ss))) ->
  (forall G t t' s s' (s0 : G |= t ~> t'),
     P G t t' s0 ->
     forall (s1 : G |= s ~> s'),
       P G s s' s1 ->
       P G (TApp t s) (TApp t' s') (cong (TS_App s0 s1))) ->
  (forall G t t' (r : G |= t ~Red> t'),
     P G t t' (red r)) ->
  forall G t1 t2 (s : G |= t1 ~> t2), P G t1 t2 s.
Proof.
  intros.
  induction s using step_mut_ind with (P := fun G t t' s => P G t t' (cong s));
  auto.
Qed.

Ltac step_induction Hstep :=
  induction Hstep using step_induction.

Definition multistep G := rtclosure (step G).
Notation "G |= t ~~> t'" := (multistep G t t') (at level 67).

Definition multicong_step G := rtclosure (cong_step G).
Notation "G |= t ~~Cong> t'" := (multicong_step G t t') (at level 67).

Definition list_equiv (A:Type) (E:binary A) : binary (list A) :=
   Forall2 E.

Definition step_list G := list_equiv (step G).
Notation "G |= ts ~>> ts'" := (step_list G ts ts') (at level 67).

Definition multistep_list G := rtclosure (step_list G).
Notation "G |= ts ~~>> ts'" := (multistep_list G ts ts') (at level 67).

Hint Constructors step cong_step red_step.
Hint Constructors rtclosure Forall2.

Lemma step__multistep : forall G t t',
  G |= t ~> t' -> G |= t ~~> t'.
Proof.
  intros. econstructor; eauto.
Qed.

Lemma step_refl : forall G t,
  G |= t ~> t.
Proof.
  auto.
Qed.

Hint Resolve step_refl.

Lemma step_list_refl : forall G ts,
  G |= ts ~>> ts.
Proof.
  induction ts. constructor. constructor; auto.
Qed.

Hint Resolve step_list_refl.

(*
Lemma multistep_list_refl : forall G ts,
  G |= ts ~~>> ts.
Proof.
  induction ts. constructor. constructor. constructor. assumption.
Qed.

Hint Resolve multistep_list_refl.

Lemma multistep_list_destruct : forall G ts1 ts2 ts3,
  G |= ts1 ~>> ts2 ->
  G |= ts2 ~~>> ts3 ->
  G |= ts1 ~~>> ts3.
Proof.
  intros G ts1 ts2. gen ts1. induction ts2; introv Hts1 Hts2.
    destruct ts1; destruct ts3; auto. inverts Hts1. inverts Hts1.
    destruct ts1; destruct ts3; auto. inverts Hts1. inverts Hts2.
    inverts Hts1. inverts Hts2.
    constructor. econstructor; eassumption.
    apply IHts2; assumption.
Qed.
*)

Lemma red_lc : forall G t t',
  Good G -> G |= t ~Red> t' -> lc t'.
Proof.
  introv HGood Hred. invert_good. inverts Hred as.
  introv Hlc_rhos Hlen HIn.
  unfolds good_lc. apply Hgood_lc in HIn. lc apply subst_tel_lc. rewrite Hlen. assumption.
Qed.

Lemma step_lc_gen : forall G t t',
  Good G -> G |= t ~> t' -> forall n, lc_gen n t -> lc_gen n t'.
Proof.
  introv HGood Hstep. step_induction Hstep; introv Hlc_gen.
    assumption.
    inverts Hlc_gen. constructor; auto.
    inverts Hlc_gen. constructor; auto.
    apply lc__lc_gen. eapply red_lc; eassumption.
Qed.

Lemma step_lc : forall G t t',
  Good G -> lc t -> G |= t ~> t' -> lc t'.
Proof.
  intros. eapply step_lc_gen; eassumption.
Qed.

Lemma steps_lc : forall G t t',
  Good G -> lc t -> G |= t ~~> t' -> lc t'.
Proof.
  introv Hgood Hlc Hstep. induction Hstep.
    assumption.
    apply IHHstep. eapply step_lc; eassumption.
Qed.

Lemma step_list_lc : forall G ts ts',
  Good G -> lc_list ts -> G |= ts ~>> ts' -> lc_list ts'.
Proof.
  induction ts; introv Hgood Hlc Hstep.
  inverts Hstep. assumption.
  inverts Hstep. constructor. eapply step_lc. eassumption. inverts Hlc. eassumption.
    assumption.
  apply IHts; lc_assumption.
Qed.

Lemma steps_list_lc : forall G ts ts',
  Good G -> lc_list ts -> G |= ts ~~>> ts' -> lc_list ts'.
Proof.
  introv Hgood Hlc Hstep. induction Hstep.
  assumption.
  apply IHHstep. eapply step_list_lc; eassumption.
Qed.

Lemma step_RNth : forall rhos G t t' n,
  Good G -> lc_list rhos -> RNth n rhos t -> G |= t ~> t' ->
  exists rhos', lc_list rhos' /\ G |= rhos ~>> rhos' /\ RNth n rhos' t'.
Proof.
  induction rhos; simpl; introv HGood Hlc_rhos HRNth Hstep.
    contradict HRNth. apply RNth_nil.
    destruct (eq_nat_decide n (length rhos)); eq_nat. subst. 
      apply RNth_here_inv in HRNth. subst. exists (t' :: rhos). inverts Hlc_rhos. split.
      constructor. eapply step_lc; eassumption. assumption. split.
      constructor. assumption. apply step_list_refl. constructor.

      specialize (IHrhos G t t' n). lc lapplies IHrhos. inv_exists.
      exists (a :: x). split.
        lc constructor. tauto.
        split.
        constructor. auto.
        tauto.
        constructor. tauto.
        inverts HRNth. omega. assumption.
Qed.

Ltac app_list_red :=
  try match goal with
    | [ Hred : _ |= _ ~Red> _ |- _ ] => inversion Hred
      end;
  app_list.

Lemma tff_no_red : forall t,
  tff t -> forall G t', ~ (G |= t ~Red> t').
Proof.
  induction 1; introv Hcontra; try solve [inverts Hcontra; app_list_red].
  inverts Hcontra as. introv Hrhos Hlen HIn Happ_list.
  pose (app_list__app (ts [^^rhos]) (TFun F)) as Happ.
    inverts Happ as.
    introv Happ_list'. rewrite Happ_list' in Happ_list. discriminate.
    introv Hexists.
    inv_exists. inverts Hexists as. introv Hexists Hts.
    rewrite Hexists in Happ_list. inverts Happ_list.
    set (Ccontra := var_gen \{}).
    set (Gcontra := (Ax Ccontra nil F x TStar) :: nil).
    specialize (IHtff1 Gcontra TStar).
    contradict IHtff1.
    pose proof (@TS_Red Ccontra nil F x TStar Gcontra nil) as contra.
    simpl in contra. replace (map (fun t : type => t) x) with x in contra.
    apply contra. constructor. auto. left. reflexivity. generalize x. intro y. induction y.
      reflexivity.
      simpl. f_equal. assumption.
Qed.

Lemma single_step_subst : forall s n G t t',
  G |= t ~> t' ->
  G |= {n ~> t}s ~> {n ~> t'}s.
Proof.
  induction s; intros; unfold open in *; simpl; auto.
  eq_nat_decide.
Qed.

Lemma multi_step_subst : forall s n G t t',
  G |= t ~~> t' ->
  G |= {n ~> t}s ~~> {n ~> t'}s.
Proof.
  induction 1.
    constructor.
    econstructor. apply single_step_subst. eassumption. assumption.
Qed.

Lemma app_list_step : forall G F ts ts',
  G |= ts ~>> ts' ->
  G |= app_list (TFun F) ts ~Cong> app_list (TFun F) ts'.
Proof.
  induction ts using rev_ind; introv Hstep.
    inverts Hstep. simpl. auto.
    rev_destruct ts'.
      apply Forall2_length in Hstep. rewrite app_length in Hstep. simpl in Hstep. omega.
      repeat rewrite app_list_snoc. constructor. apply Forall2_app_tail in Hstep.
      inverts Hstep. apply IHts in H. auto.
      apply Forall2_app_tail in Hstep. tauto.
Qed.

Lemma app_list_steps : forall G F ts ts',
  G |= ts ~~>> ts' ->
  G |= app_list (TFun F) ts ~~Cong> app_list (TFun F) ts'.
Proof.
  induction 1.
    constructor.
    econstructor. apply app_list_step. eassumption. assumption.
Qed.

Lemma steps_list_length : forall G ts ts',
  G |= ts ~~>> ts' ->
  length ts = length ts'.
Proof.
  induction 1. auto. apply Forall2_length in H. omega.
Qed.