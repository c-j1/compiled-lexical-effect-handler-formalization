Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.
From LSEH Require Import RelConfig.
Ltac trysolve :=
  try easy;try discriminate;
  try congruence;try tauto;
  try lia;auto;eauto.
Ltac automate :=
  repeat (trysolve;try constructor;trysolve;subst).
Ltac super_a :=
  repeat (automate;cbn).

(* ---------------------------------------------------------
   ------------------ Lemmas for Salt ----------------------
   --------------------------------------------------------- *)
Theorem reg_file_front_update : forall (R:reg_file) a v1 v2
  oi os o1 o2 o3 o4 o5 o6,
  (a = ip \/ a = sp \/ a = nat_reg 1 \/ a = nat_reg 2 \/
   a = nat_reg 3 \/ a = nat_reg 4 \/ a = nat_reg 5
   \/ a = nat_reg 6) ->
  R = [(ip,oi);(sp,os);(nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
      (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)] ->
  (a !->r v1; a !->r v2; R) = (a !->r v1; R).
Proof. intros. repeat (destruct H;super_a). Qed.
Theorem reg_file_swap : forall R a b v1 v2
  oi os o1 o2 o3 o4 o5 o6,
  (a = ip \/ a = sp \/ a = nat_reg 1 \/ a = nat_reg 2 \/
   a = nat_reg 3 \/ a = nat_reg 4 \/ a = nat_reg 5
   \/ a = nat_reg 6) ->
  (b = ip \/ b = sp \/ b = nat_reg 1 \/ b = nat_reg 2 \/
   b = nat_reg 3 \/ b = nat_reg 4 \/ b = nat_reg 5
   \/ b = nat_reg 6) ->
  reg_eqb a b = false ->
  R = [(ip,oi);(sp,os);(nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
      (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)] ->
  (a !->r v1; b !->r v2; R) = (b !->r v2; a !->r v1; R).
Proof with super_a.
  intros. subst.
  repeat (destruct H as [ | ]);
  repeat (destruct H0 as [ | ])...
Qed.
Lemma h_eqb_refl : forall (a:heap_loc), a = a -> h_eqb a a = true.
Proof. intros. unfold h_eqb. destruct a. apply eqb_refl. Qed.
Lemma c_eqb_refl : forall (a:code_loc), a = a -> c_eqb a a = true.
Proof. intros. unfold h_eqb. destruct a. apply eqb_refl. Qed.

Theorem heap_front_update : forall H a v1 v2,
  (a !->t v1; a !->t v2; H) = (a !->t v1; H).
Proof with super_a.
  intros. unfold th_update. extensionality x. destruct (h_eqb a x)...
Qed.

