From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Program.Basics.
Declare Scope Lexi_scope.
Open Scope Lexi_scope.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
Inductive dbj_ind := dind : nat -> dbj_ind.
Inductive code_label := c_lab : string -> code_label.
Inductive data_label : Type := 
  | obj_lab : string -> data_label
  | hand_lab : string -> data_label.
Inductive const : Type :=
  | nat_const : nat -> const
  | c_lab_const : code_label -> const
  | d_lab_const : data_label -> const
  | ns.
Inductive value : Type :=
  | const_val : const -> value
  | ind_val : dbj_ind -> value.
Definition local_env : Type := list const.
Inductive annotation : Type :=
  | tail
  | abort
  | general.
Inductive expr : Type :=
  | val_e : value -> expr
  | add : value -> value -> expr
  | newref : list value -> expr
  | pi : nat -> value -> expr
  | asgn : value -> nat -> value -> expr
  | app : value -> (list value) -> expr
  | handle : code_label -> code_label -> annotation -> value -> expr
  | raise : annotation -> value -> value -> expr
  | resume : value -> value -> expr
  | exit : value -> expr
with term : Type :=
  | val_term : value -> term
  | bind : expr -> term -> term
  | halt
with a_frame: Type := act_f : local_env -> term -> a_frame
with h_frame : Type := handler_f : data_label -> data_label ->
    code_label -> annotation -> h_frame
with frame : Type :=
  | h_f : h_frame -> frame
  | a_f : a_frame -> frame
with heap_const : Type :=
  | tuple : list const -> heap_const
  | cont : list frame -> heap_const.
Definition eval_context := list frame.
Definition heap := data_label -> heap_const.
Inductive function : Type :=
  func : nat -> term -> function.
Definition code : Type := code_label -> function.
Inductive program : Type :=
  letrec : code -> term -> program.
(* Coercions *)
Coercion dind : nat >-> dbj_ind.
Coercion c_lab : string >-> code_label.
Coercion nat_const : nat >-> const.
Coercion c_lab_const : code_label >-> const.
Coercion d_lab_const : data_label >-> const.
Coercion const_val : const >-> value.
Coercion val_e : value >-> expr.
Coercion h_f : h_frame >-> frame.
Coercion a_f : a_frame >-> frame.
(* ------------ ------------ ------------
   ------------ ------------ ------------
   ------------- Interpreter -------------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)

(* --------------------------------------------
              Map Related Helpers
   -------------------------------------------- *)
(* Heap *)
Definition empty_hconst := tuple nil.
Definition h_eqb (a b : data_label) := 
  match a,b with
  | obj_lab a', obj_lab b' => String.eqb a' b'
  | hand_lab a', hand_lab b' => String.eqb a' b'
  | _,_ => false
  end.
Definition h_empty : heap := fun _ => empty_hconst.
Definition h_update (m : heap) (x : data_label) (v : heap_const) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "x '!->h' v ';' m" := (h_update m x v)
  (at level 100, v at next level, right associativity):Lexi_scope.

(* Environment *)
(*
Definition var_eqb (a b : variable) := 
  match a,b with str_var a', str_var b' => Nat.eqb a' b' end.
*)
Definition env_fetch (env: local_env) (ind:dbj_ind) : const :=
  match ind with dind n => nth n env ns end.
(*  match env with
  | cons (x,v) lst' => if var_eqb x var then v else env_fetch lst' var
  | nil => ns
  end.*)
(*Fixpoint env_update ) :=
  match env with
  | cons (x',v') env' =>
    if var_eqb x x' then cons (x,v) env' else cons (x',v') (env_update env' x v)
  | nil => cons (x,v) nil
  end.

Notation "x '!->e' v ';' m" := (env_update m x v)
  (at level 100, v at next level, right associativity):Lexi_scope.
Reserved Notation "var_lst '!->!e' val_lst ';' m"
  (at level 100, val_lst at next level, right associativity).
Fixpoint env_super_update (m:local_env)
  (var_lst: list variable) (val_lst:list const) : local_env :=
  match var_lst,val_lst with
  | cons var var_lst', cons val val_lst' =>
    var_lst' !->!e val_lst' ; (var !->e val ; m)
  | _,_ => m
  end
where "var_lst '!->!e' val_lst ';' m" :=
  (env_super_update m var_lst val_lst).
*)
(* Code *)
Definition c_eqb (a b : code_label) := 
  match a,b with
  | c_lab a', c_lab b' => String.eqb a' b'
  end.
Definition c_update (m : code) (x : code_label) (v : function) :=
  fun x' => if c_eqb x x' then v else m x'.
(* Fixpoint code_fetch (c: code) (lab: code_label) : function :=
  match c with
  | cons (x,v) c' => if c_eqb x lab then v else code_fetch c' lab
  | nil => func nil (halt 1)
  end.*)
Notation "x '!->c' v ';' m" := (c_update m x v)
  (at level 100, v at next level, right associativity):Lexi_scope.
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
Definition var_deref (E:local_env) (val:value) : const :=
  match val with
  | ind_val ind => env_fetch E ind
  | const_val c => c
  end.

(* --------------------------------------------
                      Interpreter
   -------------------------------------------- *)
(* We assume that code is already initialized.
   Initialization is defined separately later. 

   Also we view lambda x y body as lambda x (lambda y body),
   so the de brujin index for x is 1 and y is 0.*)
Inductive step (C:code) : (heap * eval_context * local_env * term)
  -> (heap * eval_context * local_env * term) -> Prop :=
  | L_arith : forall H K E t (v1 v2:value) (i1 i2:nat),
    v1 = i1 -> v2 = i2 ->
    step C (H,K,E, bind (add v1 v2) t)
      (H,K,(nat_const (i1+i2)) :: E,t)
  | L_value : forall H K E t (v:value),
    step C (H,K,E, bind v t) (H,K,(var_deref E v) :: E,t)
  | L_new : forall H K E t (lst:list value) (L:data_label),
    H L = empty_hconst ->
    step C (H,K,E, bind (newref lst) t)
      (L !->h tuple (map (var_deref E) lst); H, K, (d_lab_const L) :: E, t)
  | L_get : forall H K E t (i:nat) (v:value)
    (L:data_label) (lst:list const),
    var_deref E v = L -> H L = tuple lst ->
    step C (H,K,E, bind (pi i v) t)
      (H,K,(nth (1+i) lst ns) :: E,t)
  | L_set : forall H K E t (i:nat)
    (v v':value) (L:data_label) (lst:list const),
    var_deref E v = L -> H L = tuple lst ->
    step C (H,K,E, bind (asgn v i v') t)
      (L !->h tuple (update_nth (i-1) lst (var_deref E v')); H,
      K,(var_deref E v') :: E,t)
  | L_handle : forall H K E t t'
    (v_env:value) (lst:list value) (A:annotation)
    (lab_body lab_op:code_label) (L L_env:data_label),
    H L = empty_hconst -> C lab_body = func 2 t' ->
    var_deref E v_env = L_env ->
    step C (H,K,E, bind (handle lab_body lab_op A v_env) t)
      (H, ([h_f(handler_f L L_env lab_op A);a_f(act_f E t)] ++ K),
      [d_lab_const L; d_lab_const L_env],t')
    (*L and L_env reversed because dbj index counts from inside *)
  | L_leave : forall H K E E' t
    (L L_env:data_label) (lab_op:code_label) (A:annotation) (v:value),
    step C (H,
      [h_f (handler_f L L_env lab_op A); a_f(act_f E t)] ++ K,
      E',val_term v)
      (H,K,(var_deref E' v) :: E,t)
  | L_app : forall H K E t t' (n:nat) (v:value) (v_lst:list value)
    (lab:code_label),
    var_deref E v = lab ->
    C lab = func n t' ->
    step C (H,K,E,bind (app v v_lst) t)
      (H, (a_f(act_f E t)) :: K,
      rev (map (var_deref E) v_lst),t')
  | L_ret : forall H K E E' t (v:value),
    step C (H,(a_f(act_f E t)) :: K,E',val_term v)
      (H,K,(var_deref E' v) :: E,t)
  | L_raise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_k L_y:data_label) (lab_op:code_label),
    H L_k = empty_hconst -> var_deref E v1 = L ->
    C lab_op = func 3 t' -> var_deref E v2 = L_y ->
    step C (H,K' ++ [h_f (handler_f L L_env lab_op general)] ++ K,E,
      bind (raise general v1 v2) t)
      (L_k !->h 
      cont ([a_f(act_f E t)] ++ K' ++ [h_f(handler_f L L_env lab_op general)]);
      H,K,
      [d_lab_const L_k;d_lab_const L_y;d_lab_const L_env],t')
  | L_resume : forall H K K' E E' t t' (v1 v2:value)
    (L_k:data_label),
    var_deref E v1 = L_k -> H L_k = cont (a_f(act_f E' t') :: K') ->
    step C (H,K,E,bind (resume v1 v2) t)
      (L_k !->h tuple [ns]; H,
      K' ++ [a_f(act_f E t)] ++ K,
      (var_deref E v2) :: E',t')
  | L_tailraise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_y:data_label) (lab_op:code_label),
    var_deref E v1 = L -> (*code_fetch*) C lab_op = func 2 t' ->
    var_deref E v2 = L_y ->
    step C (H,K' ++ [h_f (handler_f L L_env lab_op tail)] ++ K,E,
      bind (raise tail v1 v2) t)
      (H,
      [a_f (act_f E t)] ++ K' ++ [h_f (handler_f L L_env lab_op tail)] ++ K,
      [d_lab_const L_y;d_lab_const L_env],t')
  | L_abortraise : forall H K K' E t t' (v1 v2:value)
    (L L_env L_y:data_label) (lab_op:code_label),
    var_deref E v1 = L -> C lab_op = func 2 t' ->
    var_deref E v2 = L_y ->
    step C (H,K' ++ [h_f (handler_f L L_env lab_op abort)] ++ K,E,
      bind (raise abort v1 v2) t)
      (H,K,[d_lab_const L_y;d_lab_const L_env],t')
  | L_exit : forall H K E t (v:value)  (c:const),
    var_deref E v = c ->
    step C (H,K,E,bind (exit v) t)
      (H,(a_f (act_f E t)) :: K,[var_deref E v],halt).
Close Scope Lexi_scope.
(*  *)