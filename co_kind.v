Require Import LibLN.
Require Import LibTactics.
Require Import Program.Wf.
Require Import Arith.

Require Import coercion subst type tactics.

Parameter ok__unique : forall {A} x (v v' : A) E,
  ok E -> binds x v E -> binds x v' E -> v = v'.

Axiom notin_subset : forall (x : var) L L',
  x \notin L' -> L \c L' -> x \notin L.

Lemma ty_kind_reg : forall Si D t k,
  Si; D |-ty t ~: k ->
  ok_gr Si /\ ok D.
Proof.
  induction 1; try tauto.
  pick_fresh_gen L x. specialize (H0 x). apply H0 in Fr. intuition.
Qed.

Lemma co_kind_reg : forall Si D co t1 t2,
  Si; D |-co co ~: t1 ~~ t2 ->
  ok_gr Si /\ ok D.
Proof.
  induction 1; auto.
  eapply ty_kind_reg. eassumption.
  pick_fresh_gen L x. specialize (H1 x). apply H1 in Fr. intuition.
Qed.

Lemma size_of_ty_open : forall ty n x,
  size_of_ty ty = size_of_ty ({n ~> TFVar (v x)}ty).
Proof.
  induction ty; intros; simpl; try omega; auto.
  destruct (eq_nat_decide n0 n); simpl; auto.
Qed.

Lemma size_of_co_open : forall co n x,
  size_of_co co = size_of_co ({n ~> TFVar (v x)}co).
Proof.
  induction co; intros; simpl; try omega; auto.
  f_equal. apply size_of_ty_open.
  f_equal. induction l; simpl. reflexivity. rewrite <- size_of_ty_open. rewrite <- IHl.
    reflexivity.
Qed.

Lemma co_kind_det : forall Si D co t1 t2,
  Si; D |-co co ~: t1 ~~ t2 ->
  forall t3 t4,
  Si; D |-co co ~: t3 ~~ t4 ->
  t1 = t3 /\ t2 = t4.
Proof.
  induction 1; inversion 1; subst; auto.
  - apply IHco_kind in H4. tauto.
  - apply IHco_kind1 in H6. apply IHco_kind2 in H9. tauto.
  - apply IHco_kind1 in H6. apply IHco_kind2 in H9. intuition; subst; auto.
  - pick_fresh_gen (L0 \u L) x. specialize (H10 x). lapplies H10; auto.
    specialize (H1 x). lapplies H1; auto. apply H4 in H3. intuition; f_equal; auto.
  - apply IHco_kind1 in H6. apply IHco_kind2 in H9. intuition; subst; auto.
  - apply IHco_kind in H4. inverts H4. inverts H1. inverts H2. auto.
  - apply IHco_kind in H4. inverts H4. inverts H1. inverts H2. auto.
  - apply IHco_kind in H7. intuition; subst; auto.
  - pose proof (ok__unique ax (mkAxiom ks f typat rhs)
                                     (mkAxiom ks0 f0 typat0 rhs0) axs). lapplies H3; auto.
    inverts H4. auto. unfolds ok_gr. tauto. 
Qed.
 
Program Fixpoint coercionKind funs axs tcs D co 
        (_ : exists t1 t2, (funs,axs,tcs); D |-co co ~: t1 ~~ t2) 
        { measure (size_of_co co) } :
  sig ( fun types : (type * type) =>
          (funs, axs, tcs); D |-co co ~: (fst types) ~~ (snd types) ) :=
  match co with
    | CRefl ty => (ty, ty)
    | CSym co => let types := coercionKind funs axs tcs D co _ in (snd types, fst types)
    | CTrans co1 co2 => let tys1 := coercionKind funs axs tcs D co1 _ in
                        let tys2 := coercionKind funs axs tcs D co2 _ in
                        (fst tys1, snd tys2)
    | CArrow co1 co2 => let tys1 := coercionKind funs axs tcs D co1 _ in
                        let tys2 := coercionKind funs axs tcs D co2 _ in
                        (TArrow (fst tys1) (fst tys2), TArrow (snd tys1) (snd tys2))
    | CForAll ki co => let x := var_gen (dom D) in
                       let tys := coercionKind funs axs tcs
                                               (D & x ~ ki) (co ^ x)%Co _ in
                       (TForAll ki (fst tys), TForAll ki (snd tys))
    | CApp co1 co2 => let tys1 := coercionKind funs axs tcs D co1 _ in
                      let tys2 := coercionKind funs axs tcs D co2 _ in
                      (TApp (fst tys1) (fst tys2), TApp (snd tys1) (snd tys2))
    | CLeft co => let tys := coercionKind funs axs tcs D co _ in
                  match tys with
                    | (ty1, ty2) => _
                  end
    | CRight co => let tys := coercionKind funs axs tcs D co _ in
                   match tys with
                     | (ty1, ty2) => _
                   end
    | CFun f co => let tys := coercionKind funs axs tcs D co _ in
                   (TFun f (fst tys), TFun f (snd tys))
    | CAx ax tys => match get ax axs with
                      | Some (mkAxiom kis f lhs rhs) => (TFun f (lhs[^tys]), rhs[^tys])
                      | None => _
                    end
  end.

Obligation Tactic :=
  Tactics.program_simpl;
  repeat abstract_sig;
  Tactics.program_simpl;
  repeat abstract_sig;
  try omega;
  try solve [match goal with
               | [ H : _;_ |-co _ ~: _ ~~ _ |- _ ] => inversion H
             end; simpl; eauto].
Hint Constructors co_kind.
Solve Obligations.

Next Obligation.
  (* trans result *)
  simpl. eapply CKTrans. simpl in H4. apply H4. simpl in H4.
  inverts H1.
  apply co_kind_det with (t1 := H) (t2 := t2) in H4; auto.
  apply co_kind_det with (t1 := t2) (t2 := H0) in H5; auto.
  intuition. subst. auto.
Defined.

Next Obligation.
  (* arrow result *)
  simpl. eauto.
Defined.

Next Obligation.
  (* forall recursion *)
  inversion H1.
  remember (var_gen (dom D)) as x. specialize (H9 x). lapplies H9. eauto.
  pose proof (@var_gen_spec (dom D)). eapply notin_subset. rewrite Heqx. apply H9.
  admit. (* cofinite quantification *)
Defined.

Next Obligation.
  (* forall size *)
  unfold open_co. rewrite <- size_of_co_open. omega.
Defined.

Next Obligation.
  (* forall result *)
  simpl. inverts H1. econstructor. eassumption. simpl in H4.
  pose proof H11.
  specialize (H11 (var_gen (dom D))). lapplies H11.
  apply co_kind_det with (t1 := t) (t2 := t0) in H0; auto. intuition. subst.
  apply H. assumption. admit. (* cofinite quantification *)
Defined.

Next Obligation.
  simpl. eauto.
Defined.

Ltac cant_happen :=
  exfalso; inv_exists;
  match goal with
    | [ H : _; _ |-co _ _ ~: _ ~~ _ |- _ ] => inverts H
  end;
  match goal with
    | [ H1 : _;_ |-co _ ~: TApp _ _ ~~ TApp _ _,
        H2 : _;_ |-co _ ~: ?t3 ~~ ?t4 |- _ ] => apply co_kind_det with (t1 := t3) (t2 := t4) in H1; auto
  end;
  intuition; discriminate.

Next Obligation.
  (* left result *)
  match type of Heq_tys with
    | context[proj1_sig ?blah] => remember blah as pair;
                                  pose proof (proj2_sig pair) as Hp; simpl in Hp
  end.
  rewrite <- Heq_tys in *. simpls. clear Heqpair.
  destruct ty1; try cant_happen. destruct ty2; try cant_happen.
  apply (exist _ (ty1_1, ty2_1)). simpl. econstructor. eassumption.
Defined.

Next Obligation.
  (* right result *)
  match type of Heq_tys with
    | context[proj1_sig ?blah] => remember blah as pair;
                                  pose proof (proj2_sig pair) as Hp; simpl in Hp
  end.
  rewrite <- Heq_tys in *. simpls. clear Heqpair.
  destruct ty1; try cant_happen. destruct ty2; try cant_happen.
  apply (exist _ (ty1_2, ty2_2)). simpl. econstructor. eassumption.
Defined.

Next Obligation.
  (* ax result *)
  inversion H1.
  subst. econstructor; auto. pose proof H12 as Hcopy. apply binds_get in Hcopy.
  rewrite Hcopy in Heq_anonymous. inverts Heq_anonymous. eassumption.
Defined.

Next Obligation.
  (* ax lookup failure impossible *)
  exfalso. inv_exists. inverts H. apply binds_get in H10. rewrite H10 in Heq_anonymous.
  discriminate.
Defined.
