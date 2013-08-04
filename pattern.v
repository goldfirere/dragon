Lemma boring_type_1 : forall G t t',
  tff t -> G |= t ~> t' -> t = t'.
Proof.
  induction 2.
    - reflexivity.
    - inversion H. crush.
    - pose (tff_no_red H) as Hcontra. apply Hcontra in H0. contradiction.
    - inversion H. crush.
Qed.

Lemma boring_type : forall G t t',
  tff t -> G |= t ~~> t' -> t = t'.
Proof.
  induction 2.
    reflexivity.
    pose proof (boring_type_1 H H0) as Hxy. rewrite Hxy in *. apply IHrtclosure.
    assumption.
Qed.

Lemma boring_types : forall G ts ts',
  Forall tff ts -> G |= ts ~~>> ts' -> ts = ts'.
Proof.
  induction 2.
    reflexivity.
    inverts H. f_equal.
      eapply boring_type; eassumption.
      apply IHForall2. assumption.
Qed.

Ltac apply_length H :=
  let Hassumpt := fresh in
  match type of H with
    | ?x = ?y => assert (length x = length y) as Hassumpt by (f_equal; assumption)
  end;
  clear H; rename Hassumpt into H.

Lemma one_step_at_a_time_core : forall G s s1 s2,
  Good G ->
  G |= s ~> s1 ->
  G |= s ~> s2 ->
  forall n t t1 t2,
  tff t ->
  G |= {n ~> s}t ~> t1 ->
  G |= {n ~> s}t ~> t2 ->
  G |= t1 ~> {n ~> s1}t ->
  G |= t2 ~> {n ~> s2}t ->
  (G |= t1 ~> {n ~> s2}t \/ G |= t2 ~> {n ~> s1}t).
Proof.
  introv HGood Hs1 Hs2. induction Hs1; simpl; introv Htff Ht1 Ht2 Ht1' Ht2'.
  left. 
Admitted.

Lemma one_step_at_a_time_1 : forall G s s1 s2,
  Good G ->
  G |= s ~> s1 ->
  G |= s ~> s2 ->
  forall n1 n2 t1 t2 t1' t2',
  tff t1 ->
  tff t2 ->
  G |= {n1 ~> s}t1 ~> t1' ->
  G |= {n2 ~> s}t2 ~> t2' ->
  G |= t1' ~> {n1 ~> s1}t1 ->
  G |= t2' ~> {n2 ~> s2}t2 ->
  (G |= t1' ~> {n1 ~> s2}t1) \/ (G |= t2' ~> {n2 ~> s1}t2).
Proof.
  introv HGood Hs1 Hs2. induction Hs1; simpl; introv Htff1 Htff2 Ht1 Ht2 Ht1' Ht2'.
  left. 
Admitted.

Lemma it's_all_in_the_rhos_1 : forall G t t' rhos n,
  Good G -> tff t -> lc_list rhos ->
  G |= t[^rhos // n] ~> t' ->
  exists rhos', G |= t' ~> t[^rhos' // n] /\ G |= rhos ~>> rhos'.
Proof.
  introv HGood Htff Hlc Hstep. remember (t[^rhos//n]) as t0. gen t n.
  induction Hstep; introv Htff Heqt0.
    eexists; split. rewrite Heqt0. apply TS_Refl. apply step_list_refl.

    destruct t; simpl in *;
    try (rewrite subst_comm in Heqt0 by lc_assumption; discriminate).
    apply subst_bvar_tel_inv in Heqt0. inverts Heqt0 as; introv Hinv; inverts Hinv.
      apply step_RNth with (G := G) (t' := TForAllTy k' s') in H. inv_exists. inverts H. 
      exists x. split. rewrite subst_bvar_tel with (t := TForAllTy k' s'). constructor.
      assumption. omega. tauto. tauto. assumption. assumption.
      constructor; assumption.

      discriminate.
      assumption.
  
   lc rewrite subst_comm in Heqt0. inverts Heqt0.
   lapplies IHHstep1. specialize (H t1). lapplies H. specialize (H0 n). lapplies H0.
   lapplies IHHstep2. specialize (H0 t2). lapplies H0. specialize (H1 (S n)). lapplies H1.
   inv_exists.
Admitted.

Lemma it's_all_in_the_rhos : forall G ts t's rhos,
  Forall tff ts ->
  G |= ts[^^rhos] ~~>> t's ->
  Forall2 (fun t t' => exists rhos', t' = t[^rhos']) ts t's.
Admitted.        

Lemma good__patternlike : forall G,
  Good G ->
  forall C D F t0s t0',
  In (Ax C D F t0s t0') G ->
  forall rhos t's,
  G |= t0s[^^rhos] ~~>> t's ->
  exists rhos',
  G |= t's ~~>> t0s[^^rhos'] /\ G |= rhos ~~>> rhos'.
Proof.
  introv Hgood Hin Hstep.
  inverts Hgood as Htff. unfold good_tff in Htff. apply Htff in Hin.
Admitted.
