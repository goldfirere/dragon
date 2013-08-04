Require Import LibTactics.
Require Import LibLN.
Require Import List.
Require Import LibRelation.
Require Import CpdtTactics.
Require Import Compare_dec.

Require Import defns subst step utils tactics good.

Set Implicit Arguments.

Definition patternlike G :=
  forall C D F t0s t0',
  In (Ax C D F t0s t0') G ->
  forall rhos t's,
  G |= t0s[^^rhos] ~~>> t's ->
  exists rhos', G |= t's ~~>> t0s[^^rhos'] /\ G|= rhos ~~>> rhos'.

Definition joins_1step G t1 t2 :=
  exists t3, G |= t1 ~> t3 /\ G |= t2 ~> t3.
Notation "G |= t <==> t'" := (joins_1step G t t') (at level 67).

Definition joins G t1 t2 :=
  exists t3, G |= t1 ~~> t3 /\ G |= t2 ~~> t3.
Notation "G |= t <=> t'" := (joins G t t') (at level 67).

Lemma joins1__joins : forall G t1 t2,
  G |= t1 <==> t2 -> G |= t1 <=> t2.
Proof.
  intros. inversion H as [t3 [Ht1 Ht2]]. exists t3.
    split; econstructor; eauto.
Qed.

Lemma joins_sym : forall G t1 t2,
  G |= t1 <=> t2 -> G |= t2 <=> t1.
Proof.
  introv Hjoin. inverts Hjoin as. intro x. exists x. tauto.
Qed.

Lemma application : forall G s1 s1' s2 s2',
  G |= s1 <=> s1' ->
  G |= s2 <=> s2' ->
  G |= TApp s1 s2 <=> TApp s1' s2'.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H. inversion_clear H1.
  exists (TApp x x0). split. 
  induction H; induction H0.
    constructor.
    econstructor. apply cong. apply TS_App. apply step_refl. eassumption.
      apply IHrtclosure. assumption.
    econstructor. apply cong. apply TS_App. eassumption. apply step_refl.
      apply IHrtclosure. assumption.
    econstructor. apply cong. apply TS_App. eassumption. apply step_refl.
      apply IHrtclosure. assumption.
  induction H3; induction H2; intros.
    constructor.
    econstructor. apply cong. apply TS_App. apply step_refl. eassumption.
      apply IHrtclosure. assumption.
    econstructor. apply cong. apply TS_App. eassumption. apply step_refl.
      apply IHrtclosure. assumption.
    econstructor. apply cong. apply TS_App. eassumption. apply step_refl.
      apply IHrtclosure. assumption.
Qed.

Lemma forall_preserved : forall G k1 t1 s2,
  G |= TForAllTy k1 t1 ~~> s2 ->
  (exists k2 t2, s2 = TForAllTy k2 t2).
Proof.
  intros G k1 t1 s2 Hstep.
  eapply rtclosure_ind with (P := fun s1 s2 =>
                                           (exists k1 t1, s1 = TForAllTy k1 t1) ->
                                           (exists k2 t2, s2 = TForAllTy k2 t2))
                              in Hstep.
  eauto.
  eauto.
  intros. apply H1. inversion H2. inversion H3. subst. inversion H.
    inverts H4. app_list.
    inverts H4; eauto.
Qed.
    
Ltac exists_vars :=
  repeat match goal with
           | [ |- exists (_ : var), _ ] => exists (var_gen \{})
                                                  end.

Ltac notin_union :=
  repeat match goal with
           | [ Hnot : ?x \notin ?L \u _ |- ?x \notin ?L ] =>
             eapply notin_union_r1; apply Hnot
           | [ Hnot : ?x \notin _ \u ?R |- ?x \notin ?R ] =>
             eapply notin_union_r2; apply Hnot
         end.

Lemma forall_multistep_inv : forall G k1 s1 k2 s2,
  G |= TForAllTy k1 s1 ~~> TForAllTy k2 s2 ->
  G |= k1 ~~> k2 /\ G |= s1 ~~> s2.
Proof.
  intros.
  apply rtclosure_ind with (P := fun t1 t2 =>
                                   match t1, t2 with
                                     | TForAllTy k1 s1, TForAllTy k2 s2 =>
                                       G |= k1 ~~> k2 /\
                                       G |= s1 ~~> s2
                                     | _, _ => True
                                   end) in H; auto; intros.
  destruct x; auto. split; constructor.

  destruct x; destruct z; auto.
    pose H0 as Hpres. apply step__multistep in Hpres.
    apply forall_preserved in Hpres. inv_exists. subst. 

    inverts H2. split.
      inverts H0.
        inverts H2. app_list.
        inverts H2.
          assumption.
          econstructor. eassumption. assumption.
          inverts H0.
            inverts H2. app_list.
            inverts H2.
              assumption.
              econstructor. eassumption. assumption.
Qed.

Lemma forall_multistep : forall G k1 k2 s1 s2,
  G |= k1 ~~> k2 ->
  G |= s1 ~~> s2 ->
  G |= TForAllTy k1 s1 ~~> TForAllTy k2 s2.
Proof.
  intros.
  induction H. gen x. induction H0; intros.
  constructor.
  econstructor. apply cong. eapply TS_AllT. apply step_refl. eassumption.
    apply IHrtclosure.

  econstructor. apply cong. eapply TS_AllT. apply H. eauto. auto.
Qed.

Lemma red_or_not : forall G s1 s2,
  G |= s1 ~~> s2 ->
  (exists t1 t2, G |= s1 ~~Cong> t1 /\
                 G |= t1 ~Red> t2 /\
                 G |= t2 ~~> s2) \/
  G |= s1 ~~Cong> s2.
Proof.
  introv Hmstep. induction Hmstep.
    right. constructor.
    inverts H.
      left. do 2 eexists. repeat split; eauto. constructor.
    inverts IHHmstep.
      inv_exists. intuition. 
        left. exists x0. exists x1. repeat split; try assumption. econstructor; eassumption.
        right. econstructor; eassumption.
Qed.

Lemma no_short_red : forall G F ts s1 ts' s2,
  Good G ->
  G |= app_list (TFun F) ts ~Red> s1 ->
  length ts' <> length ts ->
  ~ G |= app_list (TFun F) ts' ~Red> s2.
Proof.
  introv HGood Hred Hlen Hcon.
  inverts Hred. invert_good. unfolds good_length. inverts Hcon.
  apply app_list_inv in H2. inverts H2.
  apply app_list_inv in H. inverts H. 
  specialize (Hgood_length _ _ _ _ _ _ _ _ _ H3 H7).
  repeat rewrite <- subst_preserves_length in Hlen.
  omega.
Qed.  

Ltac apply_length H :=
  let Hassumpt := fresh in
  match type of H with
    | ?x = ?y => assert (length x = length y) as Hassumpt by (f_equal; assumption)
  end;
  clear H; rename Hassumpt into H.

Lemma no_red_step_core : forall G F ts other_ts s s0,
  Good G ->
  G |= app_list (TFun F) other_ts ~Red> s0 ->
  length ts <= length other_ts ->
  G |= app_list (TFun F) ts ~Cong> s ->
  exists t's, s = app_list (TFun F) t's /\ G |= ts ~>> t's.
Proof.
    induction ts using rev_ind; introv Hgood Hred Hlength Hcong.
    simpl in *. inverts Hcong. exists (@nil type). auto.

    prepare_destruct Hcong. 
    inverts Hcong.
    eauto.
    app_list.
    app_list. inverts H1. inverts H.
      eapply_false no_short_red.
        eassumption.
        apply Hred.
        instantiate (1 := x0). intro Hcon.
        apply_length H2. repeat rewrite app_length in *. simpl in *. omega.
        eassumption.

      apply app_inj_tail in H2. inverts H2.

      specialize (IHts other_ts t' s0). lapplies IHts.
      inv_exists. inverts H2. rewrite <- app_list_snoc.
      exists (x ++ s' :: nil). split. reflexivity.
      apply Forall2_app. assumption. auto.
      assumption.
      rewrite app_length in Hlength. simpl in Hlength. omega.
      assumption.
      assumption.
Qed.

Lemma no_red_steps : forall G F other_ts ts s s0,
  Good G ->
  G |= app_list (TFun F) other_ts ~Red> s0 ->
  G |= app_list (TFun F) ts ~~Cong> s ->
  length ts = length other_ts ->
  exists t's, s = app_list (TFun F) t's /\ G |= ts ~~>> t's.
Proof.
  introv Hgood Hred Hcong. prepare_destruct Hcong. gen ts. induction Hcong; introv Ht Hlen.
    exists ts. split. assumption. constructor.
    subst. pose proof (@no_red_step_core G F ts other_ts y s0).
    lapplies H0; try assumption; try omega.
    inv_exists. inverts H0. specialize (IHHcong x).
    lapplies IHHcong.
    inv_exists. exists x0. inverts H1. split. auto.
    econstructor; eassumption.
    apply Forall2_length in H2. omega.
    reflexivity.
Qed.

Lemma red_after_apps : forall G s s1 s2,
  Good G ->
  patternlike G ->
  G |= s ~Red> s1 ->
  G |= s ~~Cong> s2 ->
  exists s3 s4, G |= s2 ~~Cong> s3 /\
                G |= s3 ~Red> s4.
Proof.
  introv Hgood Hpatt Hred Hno_red. unfolds patternlike.
  inversion Hred as [? ? ? ? ? ? ? Hlc_rhos Hlength_rhos HIn HG Hs Ht'].
  specialize (Hpatt _ _ _ _ _ HIn).
  symmetry in Hs. subst.
  pose proof (no_red_steps _ _ _ Hgood Hred Hno_red). lapplies H; auto.
  inv_exists. inverts H0.
  apply Hpatt in H1. inv_exists.
  exists (app_list (TFun F) (ts [^^ x0])).
  exists (t' [^x0]).
  split.
    apply app_list_steps. tauto.
    inverts H1. econstructor.
      eapply steps_list_lc; eassumption.
      apply steps_list_length in H0. instantiate (1 := D). omega.
      eassumption.
Qed.
 
Lemma app_preserved_1 : forall G t1 t2 s,
  G |= TApp t1 t2 ~Cong> s -> exists s1 s2, s = TApp s1 s2.
Proof.
  introv Hstep. inverts Hstep.
    eauto.
    eauto.
Qed.

Lemma app_preserved : forall G t1 t2 s,
  G |= TApp t1 t2 ~~Cong> s -> exists s1 s2, s = TApp s1 s2.
Proof.
  introv Hsteps. prepare_destruct Hsteps. gen t1 t2. induction Hsteps; introv Ht.
    eauto.
    subst. inverts H; eapply IHHsteps; reflexivity.
Qed.

Lemma app_multistep_inv : forall G t1 t2 t1' t2',
  G |= TApp t1 t2 ~~Cong> TApp t1' t2' ->
  G |= t1 ~~> t1' /\ G |= t2 ~~> t2'.
Proof.
  introv Hsteps. prepare_destruct Hsteps. gen t1 t2 t1' t2'.
  induction Hsteps; introv Ht0 Ht.
    rewrite Ht in Ht0. inverts Ht0. split; constructor.
    subst. pose proof H as Hpres. apply app_preserved_1 in Hpres. inv_exists. subst.
    specialize (IHHsteps x x0). lapplies IHHsteps; try reflexivity.
    specialize (H0 t1' t2'). lapplies H0; try reflexivity.
    inverts H.
      assumption.
      inverts H1.
      split; econstructor; eassumption.
Qed.

Lemma app_multistep : forall G t1 t1' t2 t2',
  G |= t1 ~~> t1' -> G |= t2 ~~> t2' ->
  G |= TApp t1 t2 ~~Cong> TApp t1' t2'.
Proof.
  introv Ht1 Ht2. gen t2 t2'. induction Ht1; introv Ht2; gen x; induction Ht2; intros.
    constructor.
    apply rtclosure_step with (y := TApp x0 y). auto. apply IHHt2.
    apply rtclosure_step with (y := TApp y x). auto. apply IHHt1. constructor.
    apply rtclosure_step with (y := TApp y y0). auto. apply IHHt2. auto.
Qed.
(*
Definition skew_diamond G s s2 :=
  forall s1,
  G |= s ~> s1 ->
  G |= s1 <=> s2.

Lemma confluence : forall G s s2,
  G |= s ~~> s2 ->
  skew_diamond G s s2 ->
  forall s3,
    G |= s ~~> s3 ->
    G |= s3 <=> s2.
Proof.
  induction 1; introv Hskew Hs3.
    exists s3. split. constructor. auto.
    unfold skew_diamond in Hskew. apply IHrtclosure.
    unfold skew_diamond. intros. 


  introv Hs2 Hskew Hs3. gen s2. induction Hs3; introv Hs2 Hskew.
    exists s2. split. assumption. constructor.
    unfold skew_diamond in Hskew. apply Hskew in H.
    inverts H. inverts H0. specialize (IHHs3 x0). lapplies IHHs3.
    inverts H2. inverts H0. exists x1. split. assumption.
    eapply rtclosure_trans; eassumption.
    unfold skew_diamond. intros. 
*)
Lemma skew_diamond : forall G s s1,
  G |= s ~> s1 ->
  patternlike G ->
  Good G ->
  forall s2,
  G |= s ~~> s2 ->
  G |= s1 <=> s2.
Proof.
  introv Hstep. step_induction Hstep; introv Hpatt Hgood Hsteps.

    (* Refl *) exists s2. split. assumption. constructor.
    (* ForAllTy *)
      pose proof Hsteps as Hpres.
      apply forall_preserved in Hpres. inv_exists. subst.
      apply forall_multistep_inv in Hsteps. inverts Hsteps. 
      apply IHHstep1 in H; [ | assumption | assumption ].
      apply IHHstep2 in H0 ; [ | assumption | assumption ].
      inverts H. inverts H0.
      exists (TForAllTy x1 x2). inverts H1. inverts H.
      split; apply forall_multistep; auto.

    (* TApp *)
    apply red_or_not in Hsteps. inverts Hsteps.

    inv_exists. inverts H. inverts H1.
    pose proof H0 as Hpres. apply app_preserved in Hpres. inv_exists. subst.
    apply app_multistep_inv in H0. inverts H0.
    assert (G |= t' <=> x1) by (apply IHHstep1; assumption).
    assert (G |= s' <=> x2) by (apply IHHstep2; assumption).
    inverts H0. inverts H4. intuition.
    pose proof (app_multistep H6 H7) as Happ. clear H6 H7.
    pose proof (app_multistep H4 H5) as Happ2. clear H4 H5.
    inversion H. rewrite <- H4 in H. rewrite <- H4 in Happ.
    pose proof (no_red_steps F (ts[^^rhos]) (ts[^^rhos]) Hgood H Happ eq_refl) as Hno_red.
    inv_exists. inverts Hno_red. 
    unfold patternlike in Hpatt. specialize (Hpatt _ _ _ _ _ H8 _ _ H12).
    inv_exists. inverts Hpatt.
    rewrite <- H6 in H7. 
    admit.

    pose proof H as Hpres.
    apply app_preserved in Hpres. inv_exists. subst. apply app_multistep_inv in H.
    inverts H. apply application. apply IHHstep1; assumption. apply IHHstep2; assumption.

    (* Red *)
    apply red_or_not in Hsteps. inverts Hsteps.

    inv_exists. intuition. inverts H.
    exists s2. split; [ | constructor ].
    apply trans_elim with (y := t'0[^rhos]); try assumption. apply rtclosure_trans.
    inverts r. 

