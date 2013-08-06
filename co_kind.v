Require Import LibLN.
Require Import LibTactics.
Require Import Program.Wf.
Require Import Arith.

Require Import coercion type tactics ty_kind subst.

Reserved Notation "Si |-co g ~: t1 ~~ t2" (at level 67, t1 at next level).
Inductive co_kind : ctxt -> coercion -> type -> type -> Prop :=
| CKRefl : forall Si t k,
             Si |-ty t ~: k ->
             Si |-co CRefl t ~: t ~~ t
| CKSym : forall Si g t1 t2,
            Si |-co g ~: t1 ~~ t2 ->
            Si |-co CSym g ~: t2 ~~ t1
| CKTrans : forall Si g1 g2 t1 t2 t3,
              Si |-co g1 ~: t1 ~~ t2 ->
              Si |-co g2 ~: t2 ~~ t3 ->
              Si |-co CTrans g1 g2 ~: t1 ~~ t3
| CKArrow : forall Si g1 g2 t1 t1' t2 t2',
              Si |-co g1 ~: t1 ~~ t2 ->
              Si |-co g2 ~: t1' ~~ t2' ->
              Si |-co CArrow g1 g2 ~: TArrow t1 t1' ~~ TArrow t2 t2'
| CKApp : forall Si g1 g2 t1 t1' t2 t2',
            Si |-co g1 ~: t1 ~~ t2 ->
            Si |-co g2 ~: t1' ~~ t2' ->
            Si |-co CApp g1 g2 ~: TApp t1 t1' ~~ TApp t2 t2'
| CKLeft : forall Si g t1 t1' t2 t2',
             Si |-co g ~: TApp t1 t1' ~~ TApp t2 t2' ->
             Si |-co CLeft g ~: t1 ~~ t2
| CKRight : forall Si g t1 t1' t2 t2',
              Si |-co g ~: TApp t1 t1' ~~ TApp t2 t2' ->
              Si |-co CRight g ~: t1' ~~ t2'
| CKFun : forall Si g t1 t2 f,
            Si |-co g ~: t1 ~~ t2 ->
            Si |-co CFun f g ~: TFun f t1 ~~ TFun f t2
| CKAx : forall ax ks f typat rhs axs funs tcs tys,
           ok_ctxt (funs, axs, tcs) -> 
           binds ax (mkAxiom ks f typat rhs) axs ->
           (funs, axs, tcs)|-co CAx ax tys ~: TFun f (typat [^tys]) ~~ (rhs[^tys])
where "Si |-co g ~: t1 ~~ t2" := (co_kind Si g t1 t2).

Parameter ok__unique : forall {A} x (v v' : A) E,
  ok E -> binds x v E -> binds x v' E -> v = v'.

Lemma ty_kind_reg : forall Si t k,
  Si |-ty t ~: k ->
  ok_ctxt Si.
Proof.
  induction 1; try tauto.
Qed.

Lemma co_kind_reg : forall Si co t1 t2,
  Si |-co co ~: t1 ~~ t2 ->
  ok_ctxt Si.
Proof.
  induction 1; auto.
  eapply ty_kind_reg. eassumption.
Qed.

Lemma co_kind_det : forall Si co t1 t2,
  Si|-co co ~: t1 ~~ t2 ->
  forall t3 t4,
  Si|-co co ~: t3 ~~ t4 ->
  t1 = t3 /\ t2 = t4.
Proof.
  Ltac co_kind_det :=
    repeat match goal with
      | [ IH : forall _ _, _ |-co ?g ~: _ ~~ _ -> _,
            H : _ |-co ?g ~: _ ~~ _
            |- _ ] => apply IH in H
    end;
    repeat match goal with
             | [ H : _ = _ /\ _ = _ |- _ ] => inverts H
             | [ H : TApp _ _ = TApp _ _ |- _ ] => inverts H
             | [ H : TArrow _ _ = TArrow _ _ |- _ ] => inverts H
           end.

  induction 1; inversion 1; auto; co_kind_det; auto.
  match goal with
    | [ H1 : binds ?ax (mkAxiom ?ks1 ?f1 ?typat1 ?rhs1) _
      , H2 : binds ?ax (mkAxiom ?ks2 ?f2 ?typat2 ?rhs2) _
        |- TFun ?f1 (?typat1 [^_]) = TFun ?f2 (?typat2 [^_]) /\
           ?rhs1[^_] = ?rhs2[^_] ] =>
      pose proof (ok__unique ax (mkAxiom ks1 f1 typat1 rhs1)
                                (mkAxiom ks2 f2 typat2 rhs2) axs) as Hunique
  end. lapplies Hunique. inverts H11. auto. auto. auto. inverts H. tauto.
Qed.

Unset Transparent Obligations.
Program Fixpoint coercionKind funs axs tcs co 
        (_ : exists t1 t2, (funs,axs,tcs)|-co co ~: t1 ~~ t2) 
        { measure (size_of_co false co) } :
  { types : (type * type) |
          (funs, axs, tcs)|-co co ~: (fst types) ~~ (snd types) } :=
  match co with
    | CRefl ty => (ty, ty)
    | CSym co => let types := coercionKind funs axs tcs co _ in (snd types, fst types)
    | CTrans co1 co2 => let tys1 := coercionKind funs axs tcs co1 _ in
                        let tys2 := coercionKind funs axs tcs co2 _ in
                        (fst tys1, snd tys2)
    | CArrow co1 co2 => let tys1 := coercionKind funs axs tcs co1 _ in
                        let tys2 := coercionKind funs axs tcs co2 _ in
                        (TArrow (fst tys1) (fst tys2), TArrow (snd tys1) (snd tys2))
    | CApp co1 co2 => let tys1 := coercionKind funs axs tcs co1 _ in
                      let tys2 := coercionKind funs axs tcs co2 _ in
                      (TApp (fst tys1) (fst tys2), TApp (snd tys1) (snd tys2))
    | CLeft co => let tys := coercionKind funs axs tcs co _ in
                  match tys with
                    | (ty1, ty2) => _
                  end
    | CRight co => let tys := coercionKind funs axs tcs co _ in
                   match tys with
                     | (ty1, ty2) => _
                   end
    | CFun f co => let tys := coercionKind funs axs tcs co _ in
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
               | [ H : _ |-co _ ~: _ ~~ _ |- _ ] => inversion H
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
Qed.

Next Obligation.
  (* arrow result *)
  simpl. eauto.
Qed.

Next Obligation.
  simpl. eauto.
Qed.

Ltac cant_happen :=
  exfalso; inv_exists;
  match goal with
    | [ H : _ |-co _ _ ~: _ ~~ _ |- _ ] => inverts H
  end;
  match goal with
    | [ H1 : _ |-co _ ~: TApp _ _ ~~ TApp _ _,
        H2 : _ |-co _ ~: ?t3 ~~ ?t4 |- _ ] => apply co_kind_det with (t1 := t3) (t2 := t4) in H1; auto
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
Qed.

Next Obligation.
  (* right result *)
  match type of Heq_tys with
    | context[proj1_sig ?blah] => remember blah as pair;
                                  pose proof (proj2_sig pair) as Hp; simpl in Hp
  end.
  rewrite <- Heq_tys in *. simpls. clear Heqpair.
  destruct ty1; try cant_happen. destruct ty2; try cant_happen.
  apply (exist _ (ty1_2, ty2_2)). simpl. econstructor. eassumption.
Qed.

Next Obligation.
  (* ax result *)
  inversion H1.
  subst. econstructor; auto. pose proof H10 as Hcopy. apply binds_get in Hcopy.
  rewrite Hcopy in Heq_anonymous. inverts Heq_anonymous. eassumption.
Qed.

Next Obligation.
  (* ax lookup failure impossible *)
  exfalso. inv_exists. inverts H. apply binds_get in H8. rewrite H8 in Heq_anonymous.
  discriminate.
Qed.
