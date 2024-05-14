From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Module Lexi.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
Definition hole := string. (* for now *)
Inductive variable := 
  | str_var : string -> variable.
Inductive code_label :=
  | c_lab : string -> code_label.
Inductive data_label : Type := 
  | obj_lab : string -> data_label
  | hand_lab : string -> data_label.
Inductive const : Type :=
  | int_const : nat -> const
  | c_lab_const : code_label -> const
  | d_lab_const : data_label -> const
  | ns.
Inductive value : Type :=
  | const_val : const -> value
  | var_val : variable -> value.

Inductive expr : Type :=
  | val_e : value -> expr
  | add : value -> value -> expr
  | newref : string (*recursive use of heap_val?*) -> expr
  | pi : nat -> value -> expr
  | asgn : value -> value -> value -> expr
  | app : value -> (list value) -> expr
  | handle : code_label -> code_label -> value -> expr
  | raise : value -> value -> expr
  | resume : value -> value -> expr
  | exit : value -> expr.
Inductive term : Type :=
  | val_term : value -> term
  | bind : variable -> expr -> term -> term
  | halt : const -> term.

Definition local_env : Type := variable -> value.
Inductive frame : Type := 
  | handler_f : data_label -> data_label -> code_label -> hole -> frame
  | activ_f : local_env -> variable -> hole -> term -> frame.
Definition eval_context := list frame.
Inductive heap_val : Type :=
  | tuple : list value -> heap_val
  | cont : eval_context -> heap_val.

Definition heap := data_label -> heap_val.
Inductive open_term : Type := 
  | open_tm : variable -> term -> open_term.
Definition code : Type := list (code_label -> open_term).
Inductive program : Type := 
  | letrec : code -> code_label -> program.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ------------- Interpreter -------------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
(* Map Related Helpers *)
Definition h_eqb (a b : data_label) := 
  match a,b with
  | obj_lab a', obj_lab b' => String.eqb a' b'
  | hand_lab a', hand_lab b' => String.eqb a' b'
  | _,_ => false
  end.
Definition h_empty (v : heap_val) : heap := (fun _ => v).
Definition h_update (m : heap) (x : data_label) (v : heap_val) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "'_' '!->h' v" := (h_empty v)
  (at level 100, right associativity).
Notation "x '!->h' v ';' m" := (h_update m x v)
  (at level 100, v at next level, right associativity).

Definition var_eqb (a b : variable) := 
  match a,b with
  | str_var a', str_var b' => String.eqb a' b'
  end.
Definition env_empty (v : value) : local_env := (fun _ => v).
Definition env_update (m : local_env) (x : variable) (v : value) :=
  fun x' => if var_eqb x x' then v else m x'.
Notation "'_' '!->e' v" := (env_empty v)
  (at level 100, right associativity).
Notation "x '!->e' v ';' m" := (env_update m x v)
  (at level 100, v at next level, right associativity).

(* E hat of paper *)
Definition var_deref (val:value) (E:local_env) :=
  match val with
  | var_val var => E var
  | const_val c => val
  end.
(* Other helpers *)
Fixpoint add_const c1 c2 :=
  match c1, c2 with
  | int_const i1, int_const i2 => i1 + i2
  | c_lab_const (c_lab c1'), c_lab_const (c_lab c2') => c1' + c2'
  | d_lab_const d1, d_lab_const d2 => d1 + d2
  | _,_ => 1
  end.
Fixpoint add_val v1 v2 :=
  match (var_deref v1), (var_deref v2) with
  | const_val c1, const_val c2 => add_const c1 c2
  | var_val var, _ => add_val var v2
  | _, var_val var => add_val v1 var
  end.
Inductive const : Type :=
  | int_const : nat -> const
  | c_lab_const : code_label -> const
  | d_lab_const : data_label -> const
  | ns.
(* smallstep evaluation relation *)
(* We assume that code is already initialized.
   Initialization is defined as a separate relation. *)
Inductive step (C:code) : (heap * eval_context * local_env * term)
  -> (heap * eval_context * local_env * term) -> Prop :=
  | L_arith : forall H K E t (x:variable) (v1 v2:value),
    step C (H,K,E, bind x (add v1 v2) t)
      (H,K,(x !->e add_val v1 v2; E),t)
.
(* addition: only for numbers or for strings as well? *)
End Lexi.