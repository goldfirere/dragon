Require Import LibNat.

Ltac eq_nat :=
  repeat match goal with
           | [ H : context[eq_nat _ _] |- _ ] => rewrite eq_nat_is_eq in H
         end.

Ltac eq_nat_decide :=
  repeat match goal with
           | [ |- context[eq_nat_decide ?a ?b] ] =>
               destruct (eq_nat_decide a b)
         end;
  repeat match goal with
           | [ _ : context[eq_nat_decide ?a ?b] |- _ ] =>
             destruct (eq_nat_decide a b)
         end;
  eq_nat;
  try omega;
  auto.

Ltac lapplies H :=
  let Hl := fresh in
  try match type of H with
        | _ -> _ => lapply H; clear H; [ intro Hl; lapplies Hl | ]
      end.

Ltac inv_exists :=
  let Htemp := fresh in
  repeat match goal with
    | [ Hex : exists _, _ |- _ ] => inversion Hex as [? Htemp]; clear Hex; rename Htemp into Hex
         end.

Ltac prepare_destruct H :=
  let rec go subterm :=
      match subterm with
        | ?head ?arg => first [ is_var arg | remember arg ]; go head
        | _ => idtac
      end in
  let start := type of H in
  go start.

Ltac apply_false lem :=
  let H := fresh in
  pose proof lem as H; unfold not in H; exfalso; apply H; clear H.

Ltac eapply_false lem :=
  let H := fresh in
  pose proof lem as H; unfold not in H; exfalso; eapply H; clear H.

Ltac abstract_sig :=
  let ss := fresh in
  let Hs := fresh in
  match goal with
    | [ |- context[proj1_sig ?blah] ] =>
      first [is_var blah | (* ignore atomic conditions *)
          generalize blah; intro ss;
          pose proof (proj2_sig ss) as Hs;
          simpl in Hs]
  end.

Ltac abstract_sig_in hyp :=
  let ss := fresh in
  let Hs := fresh in
  match hyp with
    | context[proj1_sig ?blah] =>
      first [is_var blah | (* ignore atomic conditions *)
          remember blah as ss;
          pose proof (proj2_sig ss) as Hs;
          simpl in Hs]
  end.
  
Ltac destruct_if :=
  let silly_if b x:=
      replace (if b then x else x) with x in *
      by (destruct b; auto) in
  first [
  match goal with
    | [ |- context[if ?b then ?x else ?x] ] => silly_if b x
    | [ H : context[if ?b then ?x else ?x] |- _ ] => silly_if b x
  end |
  match goal with
    | [ |- context[if ?foo then _ else _] ] => destruct foo
    | [ H : context[if ?foo then _ else _] |- _ ] => destruct foo
  end ].

Ltac not_equal :=
  match goal with
    | [ Hneq : ?x <> ?x |- _ ] => specialize (Hneq eq_refl); contradiction
  end.
