Require Import LibLN.
Require Import LibReflect.
Require Import Arith.
Require Import List.

Require Import type coercion utils subst.

Definition mapping := (xvar * type)%type.
Definition substn := list mapping.

Parameter xvar_eq_decide :
  forall (xv1 xv2 : xvar), sumbool (xv1 = xv2) (xv1 <> xv2).

Fixpoint apply1 (m : mapping) ty :=
  let (xv, target) := m in
  match ty with
    | TFVar x => if xvar_eq_decide x xv then target else ty
    | TBVar n => TBVar n
    | TFun f ty => TFun f (apply1 m ty)
    | TArrow ty1 ty2 => TArrow (apply1 m ty1) (apply1 m ty2)
    | TTycon T => TTycon T
    | TForAll k ty => TForAll k (apply1 m ty)
    | TApp ty1 ty2 => TApp (apply1 m ty1) (apply1 m ty2)
  end.

Fixpoint apply (s : substn) ty :=
  match s with
    | nil => ty
    | (m :: tail) => apply tail (apply1 m ty)
  end.

Lemma apply_commutes sub t :
  match t with
    | TFVar _ => True
    | TFun f ty => apply sub t = TFun f (apply sub ty)
    | TArrow ty1 ty2 => apply sub t = TArrow (apply sub ty1) (apply sub ty2)
    | TForAll k ty => apply sub t = TForAll k (apply sub ty)
    | TApp ty1 ty2 => apply sub t = TApp (apply sub ty1) (apply sub ty2)
    | t => apply sub t = t
  end.
Proof.
  generalize dependent t.
  induction sub as [ | m sub ]; intro t; [ | destruct m ]; destruct t; simpl; auto;
  match goal with
    | [ |- apply sub ?t = _ ] => specialize (IHsub t); simpl in IHsub; auto
  end.
Qed.

Ltac is_bare_type t :=
  match t with
    | TFVar _ => idtac
    | TBVar _ => idtac
    | TFun _ _ => idtac
    | TArrow _ _ => idtac
    | TTycon _ => idtac
    | TForAll _ _ => idtac
    | TApp _ _ => idtac
  end.

Ltac apply_commutes :=
  let Ha_c := fresh in
  repeat match goal with
    | [ H : context[apply ?sub ?t] |- _ ] => is_bare_type t;
                                             pose proof (apply_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c in H;
                                             clear Ha_c
  end;
  repeat match goal with
    | [ |- context[apply ?sub ?t] ] => is_bare_type t;
                                             pose proof (apply_commutes sub t) as Ha_c;
                                             simpl in Ha_c;
                                             rewrite Ha_c;
                                             clear Ha_c
  end.

Definition subs_commute sub1 sub2 :=
  forall t, apply sub1 (apply sub2 t) = apply sub2 (apply sub1 t).

Fixpoint dom (sub : substn) : fset xvar :=
  match sub with
    | nil => \{}
    | (xv,_) :: rest => \{xv} \u dom rest
  end.

Fixpoint fv_range (sub : substn) : fset xvar :=
  match sub with
    | nil => \{}
    | (_,t) :: rest => fv(t) \u fv_range rest
  end.

Inductive ok_sub : substn -> Type :=
| ok_sub_nil : ok_sub nil
| ok_sub_cons : forall xv t sub,
   xv \notin (dom sub) -> ok_sub sub -> ok_sub ((xv,t) :: sub).

Axiom in_notin : forall {A} (x : A) s,
  x \in s -> x \notin s -> False.

Axiom in_inter_empty : forall {A} (x : A) s1 s2,
  s1 \n s2 = \{} -> x \in s1 -> x \notin s2.

Lemma is_sub_or_not xv sub :
  ok_sub sub -> 
  xv \in dom sub \/ apply sub (TFVar xv) = TFVar xv.
Proof.
  induction sub; intros.
  right. simpl. auto.
  inverts H. apply IHsub in H3. inverts H3.
  - left. simpl. rewrite in_union. tauto.
  - simpl. destruct (xvar_eq_decide xv xv0).
    * subst. left. simpl. rewrite in_union. left. apply in_singleton_self.
    * right. auto.
Qed.

Axiom notin_sub_id : forall xv sub,
  xv \notin dom sub -> apply sub (TFVar xv) = TFVar xv.

Lemma subs_commute_dec sub1 sub2 : 
  ok_sub sub1 -> ok_sub sub2 ->
  decide (subs_commute sub1 sub2).
Proof.
  introv Hok1 Hok2.
  refine (let dom1 := dom sub1 in
          let dom2 := dom sub2 in
          let r1 := fv_range sub1 in
          let r2 := fv_range sub2 in
          If dom1 \n dom2 = \{} /\ dom1 \n r2 = \{} /\ dom2 \n r1 = \{}
          then left _
          else right _).
  inverts _H. inverts H0.
  intro t. induction t; apply_commutes; auto.
  - apply (is_sub_or_not x) in Hok2. inverts Hok2.
    * assert (x \notin dom sub1). {
        unfold dom2 in H. eapply in_inter_empty. unfold dom1 in H.
        rewrite inter_comm. apply H. auto.
      }
      replace (apply sub1 (TFVar x)) with (TFVar x) by
        (symmetry; apply notin_sub_id; auto).
      admit. (* to prove : apply sub1 (apply sub2 (TFVar x)) = apply sub2 (TFVar x)
                   but, this is true because dom sub1 \n fv (apply sub2 (TFVar x))
                   must be empty. *)
    * rewrite H0. admit. (* similar *)   
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt. auto.
  - rewrite IHt1. rewrite IHt2. auto.
  
  - intro Hcon. unfold subs_commute in Hcon.
    apply Decidable.not_and in _H. inverts _H.
    