From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Module Lexi.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
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
Definition local_env : Type := variable -> value.
Inductive annotation : Type :=
  | tail
  | abort
  | general.
Inductive expr : Type :=
  | val_e : value -> expr
  | add : value -> value -> expr
  | newref : heap_val -> expr
  | pi : nat -> value -> expr
  | asgn : value -> value -> value -> expr
  | app : value -> (list value) -> expr
  | handle : code_label -> code_label -> annotation -> value -> expr
  | raise : annotation -> value -> value -> expr
  | resume : value -> value -> expr
  | exit : value -> expr
with term : Type :=
  | val_term : value -> term
  | bind : variable -> expr -> term -> term
  | halt : const -> term
with frame : Type := 
  | handler_f : data_label -> data_label ->
    code_label -> annotation -> frame
  | act_f : local_env -> variable -> term -> frame
with heap_val : Type :=
  | tuple : list value -> heap_val
  | cont : list frame -> heap_val.
Definition eval_context := list frame.
Definition heap := data_label -> heap_val.
Inductive function : Type := 
  | func : (list variable) -> term -> function.
Definition code : Type := code_label -> function.
Inductive program : Type := 
  | letrec : code -> code_label -> program.
(* Coercions *)
Coercion str_var : string >-> variable.
Coercion c_lab : string >-> code_label.
Coercion int_const : nat >-> const.
Coercion c_lab_const : code_label >-> const.
Coercion d_lab_const : data_label >-> const.
Coercion const_val : const >-> value.
Coercion val_e : value >-> expr.
Coercion newref : heap_val >-> expr.
(* ------------ ------------ ------------
   ------------ ------------ ------------
   ------------- Interpreter -------------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)

(* --------------------------------------------
              Map Related Helpers
   -------------------------------------------- *)
(* Heap *)
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
(* Environment *)
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
Reserved Notation "var_lst '!->!e' val_lst ';' m"
  (at level 100, val_lst at next level, right associativity).
Fixpoint env_super_update (m:local_env)
  (var_lst: list variable) (val_lst:list value) : local_env :=
  match var_lst,val_lst with
  | cons var var_lst', cons val val_lst' =>
    var_lst' !->!e val_lst' ; (var !->e val ; m)
  | _,_ => m
  end
where "var_lst '!->!e' val_lst ';' m" :=
  (env_super_update m var_lst val_lst).
(* Code *)
Definition c_eqb (a b : code_label) := 
  match a,b with
  | c_lab a', c_lab b' => String.eqb a' b'
  end.
Definition c_empty (v : function) : code := (fun _ => v).
Definition c_update (m : code) (x : code_label) (v : function) :=
  fun x' => if c_eqb x x' then v else m x'.
Notation "'_' '!->c' v" := (c_empty v)
  (at level 100, right associativity).
Notation "x '!->c' v ';' m" := (c_update m x v)
  (at level 100, v at next level, right associativity).
(* --------------------------------------------
                  Other helpers
   -------------------------------------------- *)

Fixpoint update_nth {A: Type} (n:nat) (lst:list A) (v:A) :=
  match n, lst with
  | 0, cons x lst' => cons v lst'
  | _, nil => nil
  | S n', cons x lst' => update_nth n' lst' v
  end.
(* E hat of paper *)
Definition var_deref (E:local_env) (val:value) :=
  match val with
  | var_val var => E var
  | const_val c => val
  end.

(* --------------------------------------------
                      Interpreter
   -------------------------------------------- *)
(* We assume that code is already initialized.
   Initialization is defined separately later. *)
Inductive step (C:code) : (heap * eval_context * local_env * term)
  -> (heap * eval_context * local_env * term) -> Prop :=
  | L_arith : forall H K E t (x:variable) (v1 v2:value) (i1 i2:nat),
    v1 = i1 -> v2 = i2 ->
    step C (H,K,E, bind x (add v1 v2) t)
      (H,K,(x !->e (i1+i2); E),t)
  | L_value : forall H K E t (x: variable) (v:value),
    step C (H,K,E, bind x v t) (H,K,(x !->e var_deref E v; E),t)
  | L_new : forall H K E t (x:variable)
    (lst:list value) (L:data_label), (* L is fresh location *)
    step C (H,K,E, bind x (tuple lst) t)
      (L !->h tuple (map (var_deref E) lst); H,K,x !->e L; E,t)
  | L_get : forall H K E t (x:variable) (i:nat) (v:value)
    (L:data_label) (lst:list value),
    var_deref E v = L -> H L = tuple lst ->
    step C (H,K,E, bind x (pi i v) t)
      (H,K,x !->e nth (1+i) lst ns ; E,t)
  | L_set : forall H K E t (x:variable) (i:nat)
    (v v':value) (L:data_label) (lst:list value),
    var_deref E v = L -> H L = tuple lst ->
    step C (H,K,E, bind x (asgn v i v') t)
      (L !->h tuple (update_nth (i-1) lst (var_deref E v')); H,
      K,x !->e var_deref E v'; E,t)
  | L_handle : forall H K E t t' (x x_env x_hdl:variable)
    (v_env:value) (lst:list value) (A:annotation)
    (lab_body lab_op:code_label) (L L_env:data_label),
    (*L fresh*) C lab_body = func [x_env; x_hdl] t' -> var_deref E v_env = L_env ->
    step C (H,K,E, bind x (handle lab_body lab_op A v_env) t)
      (H, ([handler_f L L_env lab_op A; act_f E x t] ++ K),
      x_env !->e L_env; x_hdl !->e L; E,t')
  | L_leave : forall H K E E' t (x':variable)
    (L L_env:data_label) (lab_op:code_label) (A:annotation) (v:value),
    step C (H, 
      [handler_f L L_env lab_op A; act_f E x' t] ++ K,
      E',val_term v)
      (H,K,x' !->e var_deref E' v; E,t)
  | L_app : forall H K E t t' (x:variable) (v:value) (v_lst:list value)
    (var_lst: list variable) (lab:code_label),
    var_deref E v = lab ->
    C lab = func var_lst t' ->
    step C (H,K,E,bind x (app v v_lst) t)
      (H, [act_f E x t] ++ K,
      var_lst !->!e v_lst ; _ !->e ns,t')
  | L_ret : forall H K E E' t (v:value) (x':variable),
    step C (H,[act_f E x' t] ++ K,E',val_term v)
      (H,K,x' !->e var_deref E' v; E,t)
  | L_raise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_k L_y:data_label) (lab_op:code_label) (x x_env y k:variable),
    (* Lk fresh *) var_deref E v1 = L -> C lab_op = func [x_env;y;k] t' ->
    var_deref E v2 = L_y ->
    step C (H,K' ++ [handler_f L L_env lab_op general] ++ K,E,
      bind x (raise general v1 v2) t)
      (L_k !->h 
      cont ([act_f E x t] ++ K' ++ [handler_f L L_env lab_op general]);
      H,K,
      x_env !->e L_env; y !->e L_y; k !->e L_k; _ !->e ns,t')
  | L_resume : forall H K K' E E' t t' (v1 v2:value)
    (L_k:data_label) (x x':variable),
    var_deref E v1 = L_k -> H L_k = cont ([act_f E' x' t'] ++ K') ->
    step C (H,K,E,bind x (resume v1 v2) t)
      (L_k !->h tuple [const_val ns]; H,
      K' ++ [act_f E x t] ++ K,
      x' !->e var_deref E v2; E',t')
  | L_tailraise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_y:data_label) (lab_op:code_label) (x x_env y:variable),
    var_deref E v1 = L -> C lab_op = func [x_env;y] t' ->
    var_deref E v2 = L_y ->
    step C (H,K' ++ [handler_f L L_env lab_op tail] ++ K,E,
      bind x (raise tail v1 v2) t)
      (H,
      [act_f E x t] ++ K' ++ [handler_f L L_env lab_op tail] ++ K,
      x_env !->e L_env; y !->e L_y; _ !->e ns,t')
  | L_abortraise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_y:data_label) (lab_op:code_label) (x x_env y:variable),
    var_deref E v1 = L -> C lab_op = func [x_env;y] t' ->
    var_deref E v2 = L_y ->
    step C (H,K' ++ [handler_f L L_env lab_op abort] ++ K,E,
      bind x (raise abort v1 v2) t)
      (H,K,x_env !->e L_env; y !->e L_y; _ !->e ns,t')
  | L_exit : forall H K E t (v:value) (x:variable) (c:const),
    var_deref E v = c ->
    step C (H,K,E,bind x (exit v) t)
      (H,K,E,halt c).

Definition multi_step_lexi (C:code) config config' : Prop :=
  Relation_Operators.clos_refl_trans_1n
  (heap * eval_context * local_env * term) (step C) config config'.

Definition init_code (p:program) : code :=
  match p with
  | letrec funcs main_func => funcs
  end.
Definition init_term (p:program) : term :=
  match p with
  | letrec funcs main_func =>
    match funcs main_func with
    | func _ body => body
    end
  end.
Definition interp (p:program) (c:const) : Prop :=
  multi_step_lexi (init_code p)
    (_ !->h tuple [const_val ns],[],_ !->e ns,init_term p)
    (_ !->h tuple [const_val ns],[],_ !->e ns,halt c).
End Lexi.