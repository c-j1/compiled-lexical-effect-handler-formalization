Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
From TLC Require Import LibLN.
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
(* ---------------------------------------------------------
   ---- Helper Functions & Tactics for Locally Nameless ----
   --------------------------------------------------------- *)

Definition fv_val (v : L.value) : vars :=
  match v with
  | var_val (free_var x) => \{x}
  | var_val (dbjind_var i) => \{}
  | const_val c => \{}
  end.
Fixpoint fv_vlst (vlst : list L.value) : vars :=
  match vlst with
  | [] => \{}
  | v :: vlst' => (fv_val v) \u (fv_vlst vlst')
  end.
Definition fv_exp (exp : L.expr) : vars :=
  match exp with
  | L.val_e val => fv_val val
  | L.add val1 val2 =>
      (fv_val val1) \u (fv_val val2)
  | L.newref val_lst => fv_vlst val_lst
  | L.pi _ val => fv_val val
  | L.asgn val1 _ val2 =>
      (fv_val val1) \u (fv_val val2)
  | L.app val val_lst => (fv_val val) \u (fv_vlst val_lst)
  | L.handle _ _ _ val => fv_val val
  | L.raise _ val1 val2 =>
      (fv_val val1) \u (fv_val val2)
  | L.resume val1 val2 =>
      (fv_val val1) \u (fv_val val2)
  end.
Fixpoint fv (tm : L.term) : vars :=
  match tm with
  | bind exp t => (fv_exp exp) \u (fv t)
  | val_term v => (fv_val v)
  | L.halt => \{}
  end.
(* ********************************************************************** *)
(** ** Instantiation of tactics *)

(** Tactic [gather_vars] returns a set of variables occurring in
    the context of proofs, including domain of environments and
    free variables in terms mentionned in the context. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : L.value => fv_val x) in
  let D := gather_vars_with (fun (x : list L.value) => fv_vlst x) in
  let E := gather_vars_with (fun x : L.expr => fv_exp x) in
  let F := gather_vars_with (fun x : L.term => fv x) in
  constr:(A \u B \u C \u D \u E \u F).

(** Tactic [pick_fresh x] adds to the context a new variable x
    and a proof that it is fresh from all of the other variables
    gathered by tactic [gather_vars]. *)

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

(** Tactic [apply_fresh T as y] takes a lemma T of the form
    [forall L ..., (forall x, x \notin L, P x) -> ... -> Q.]
    instantiate L to be the set of variables occuring in the
    context (by [gather_vars]), then introduces for the premise
    with the cofinite quantification the name x as "y" (the second
    parameter of the tactic), and the proof that x is not in L. *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Hint Constructors lc_term L.step.
