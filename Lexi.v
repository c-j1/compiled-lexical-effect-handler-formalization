From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Program.Basics.
From TLC Require Import LibLN.
Declare Scope Lexi_scope.
Open Scope Lexi_scope.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)

Inductive variable := 
| dbjind_var : nat -> variable
| free_var : var -> variable.
Inductive code_label := c_lab : string -> code_label.
Inductive obj_label := obj_lab : string -> obj_label.
Inductive hdl_label := hdl_lab : string -> hdl_label.
Inductive data_label : Type := 
| obj_data_lab : obj_label -> data_label
| hdl_data_lab : hdl_label -> data_label.
Inductive static_const : Type :=
| nat_const : nat -> static_const
| c_lab_const : code_label -> static_const.
Inductive runtime_const : Type :=
| run_const : static_const -> runtime_const
| d_lab_const : data_label -> runtime_const
| ns.
Inductive value :=
| const_val : static_const -> value
| var_val : variable -> value.
Definition local_env : Type := list runtime_const.
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
| handle : code_label -> code_label
           -> annotation -> value -> expr
| raise : annotation -> value -> value -> expr
| resume : value -> value -> expr
with term : Type :=
| val_term : value -> term
| bind : expr -> term -> term
| halt
with a_frame: Type :=
  act_f : local_env -> term -> a_frame
with h_frame : Type :=
  handler_f : hdl_label -> hdl_label ->
              code_label -> annotation -> h_frame
with frame : Type :=
| h_f : h_frame -> frame
| a_f : a_frame -> frame
with heap_cont : Type :=
| cont : list frame -> heap_cont
| empty_cont.
Inductive heap_tuple : Type :=
| tuple : list runtime_const -> heap_tuple.
Definition eval_context := list frame.
Definition tup_heap := obj_label -> heap_tuple.
Definition cont_heap := obj_label -> heap_cont.
Definition heap := (tup_heap * cont_heap)%type.
Inductive function : Type :=
| func : nat -> term -> function
| ns_func.
Definition code_mem : Type := code_label -> function.

(* Coercions *)
Coercion dbjind_var : nat >-> variable.
Coercion free_var : var >-> variable.
Coercion c_lab : string >-> code_label.
Coercion obj_data_lab : obj_label >-> data_label.
Coercion hdl_data_lab : hdl_label >-> data_label.
Coercion nat_const : nat >-> static_const.
Coercion c_lab_const : code_label >-> static_const.
Coercion run_const : static_const >-> runtime_const.
Coercion d_lab_const : data_label >-> runtime_const.
Coercion const_val : static_const >-> value.
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
Definition empty_tup := tuple nil.
Definition h_eqb (a b : obj_label) := 
  match a,b with
  | obj_lab a', obj_lab b' => String.eqb a' b'
  end.
Definition th_empty : tup_heap := fun _ => empty_tup.
Definition ch_empty : cont_heap := fun _ => empty_cont.
Definition h_empty : heap := (th_empty,ch_empty).
Definition th_update (m : tup_heap) (x : obj_label) (v : heap_tuple) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "x '!->t' v ';' m" :=
  (th_update m x v)
    (at level 100, v at next level, right associativity):Lexi_scope.
Definition ch_update (m : cont_heap) (x : obj_label) (v : heap_cont) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "x '!->ch' v ';' m" :=
  (ch_update m x v)
    (at level 100, v at next level, right associativity):Lexi_scope.

(* Environment *)
Definition env_fetch (env: local_env) (var:variable)
  : runtime_const :=
  match var with
  | dbjind_var n => nth n env ns
  | free_var str => ns
  end.

(* Code *)
Definition c_empty : code_mem := fun _ => ns_func.
Definition c_eqb (a b : code_label) := 
  match a,b with
  | c_lab a', c_lab b' => String.eqb a' b'
  end.
Definition c_update (m : code_mem) (x : code_label) (v : function) :=
  fun x' => if c_eqb x x' then v else m x'.
Definition c_comp (c1:code_mem) (c2:code_mem) :=
  fun x => match c1 x with
           | ns_func => c2 x
           | _ => c1 x
           end.
Notation "x '!->c' v ';' m" :=
  (c_update m x v)
    (at level 100, v at next level, right associativity):Lexi_scope.
(* annotation *)
Definition a_eqb (a b : annotation) :=
  match a,b with
  | general,general => true
  | tail,tail => true
  | abort,abort => true
  | _,_ => false
  end.
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
Definition var_deref (E:local_env) (val:value)
  : runtime_const :=
  match val with
  | var_val ind => env_fetch E ind
  | const_val c => run_const c
  end.

(* --------------------------------------------
               Operational Semantics
   -------------------------------------------- *)
(* We assume that code is already initialized.
   Initialization is defined separately later. 

   Also we view lambda x y body as lambda x (lambda y body),
   so the de brujin index for x is 1 and y is 0.*)
Inductive step (C:code_mem) :
  (heap * eval_context * local_env * term)
  -> (heap * eval_context * local_env * term) -> Prop :=
| L_arith : forall H K E t (v1 v2:value) (i1 i2:nat),
    v1 = i1 -> v2 = i2 -> 
    step C (H,K,E, bind (add v1 v2) t)
      (H,K,(run_const (i1+i2)) :: E,t)
| L_value : forall H K E t (v:value),
    step C (H,K,E, bind v t) (H,K,(var_deref E v) :: E,t)
| L_new : forall tH cH K E t (v:value) (L:obj_label) lst,
    tH L = empty_tup -> lst = [v] ->
    step C (tH,cH,K,E, bind (newref lst) t)
      (L !->t tuple (List.map (var_deref E) lst); tH,
         cH, K, (d_lab_const L) :: E, t)
| L_get : forall tH cH K E t (i:nat) (v:value)
                 (L:obj_label) (lst:list runtime_const),
    var_deref E v = L -> tH L = tuple lst ->
    step C (tH,cH,K,E, bind (pi i v) t)
      (tH,cH,K,(nth i lst ns) :: E,t) (* from (1+i) to i*)
| L_set : forall tH cH K E t (i:nat) (lst:list runtime_const)
                 (v v':value) (L:obj_label) (c:runtime_const),
    var_deref E v = L -> tH L = tuple lst ->
    i < List.length lst -> lst = [c] ->
    step C (tH,cH,K,E, bind (asgn v i v') t)
      (L !->t tuple (update_nth i lst (var_deref E v')); tH,
         cH,K,(var_deref E v') :: E,t) (* from i-1 to i *)
| L_app : forall H K E t t' (n:nat) (v v':value) (lst:list value)
                 (lab:code_label),
    var_deref E v = lab ->
    C lab = func (List.length lst) t' ->
    lst = [v'] ->
    step C (H,K,E,bind (app v lst) t)
      (H, (a_f (act_f E t)) :: K,
        rev (List.map (var_deref E) lst),t')
| L_ret : forall H K E E' t (v:value),
    step C (H,(a_f(act_f E t)) :: K,E',val_term v)
      (H,K,(var_deref E' v) :: E,t)
| L_handle :
  forall H K E t t'
         (v_env:value) (A:annotation)
         (lab_body lab_op:code_label) (L L_env:hdl_label),
    (* L fresh *)
    var_deref E v_env = L_env ->
    C lab_body = func 2 t' ->
    step C (H,K,E, bind (handle lab_body lab_op A v_env) t)
      (H, ([h_f(handler_f L L_env lab_op A);a_f(act_f E t)] ++ K),
        [d_lab_const L; d_lab_const L_env],t')
(*L and L_env reversed because dbj index counts from inside *)
| L_leave :
  forall H K E E' t
         (L L_env:hdl_label) (lab_op:code_label) (A:annotation) (v:value),
    step C (H,
        [h_f (handler_f L L_env lab_op A); a_f(act_f E t)] ++ K,
        E',val_term v)
      (H,K,(var_deref E' v) :: E,t)
| L_raise :
  forall tH cH K K' E t t' (v1 v2:value)
         (L L_env:hdl_label) (L_k:obj_label) (L_y:data_label) (lab_op:code_label),
    cH L_k = empty_cont -> var_deref E v1 = L ->
    var_deref E v2 = L_y ->
    C lab_op = func 3 t' ->
    step C (tH,cH,K' ++ [h_f (handler_f L L_env lab_op general)] ++ K,E,
        bind (raise general v1 v2) t)
      (tH, L_k !->ch 
             cont ([a_f(act_f E t)] ++ K' ++ [h_f(handler_f L L_env lab_op general)]);
       cH,K,
         [d_lab_const L_k;d_lab_const L_y;d_lab_const L_env],t')
| L_resume :
  forall tH cH K K' E E' t t' (v1 v2:value)
         (L_k:obj_label),
    var_deref E v1 = L_k -> cH L_k = cont (a_f(act_f E' t') :: K') ->
    step C (tH,cH,K,E,bind (resume v1 v2) t)
      (tH, L_k !->ch empty_cont; cH,
         K' ++ [a_f(act_f E t)] ++ K,
         (var_deref E v2) :: E',t')
| L_tailraise :
  forall H K K' E t t' (v1 v2:value)
         (L L_env:hdl_label) (L_y:data_label) (lab_op:code_label),
    var_deref E v1 = L ->
    var_deref E v2 = L_y ->
    C lab_op = func 2 t' ->
    step C (H,K' ++ [h_f (handler_f L L_env lab_op tail)] ++ K,E,
        bind (raise tail v1 v2) t)
      (H,
        [a_f (act_f E t)] ++ K' ++ [h_f (handler_f L L_env lab_op tail)] ++ K,
        [d_lab_const L_y;d_lab_const L_env],t')
| L_abortraise :
  forall H K K' E t t' (v1 v2:value)
         (L L_env:hdl_label) (L_y:data_label) (lab_op:code_label),
    var_deref E v1 = L ->
    var_deref E v2 = L_y ->
    C lab_op = func 2 t' ->
    step C (H,K' ++ [h_f (handler_f L L_env lab_op abort)] ++ K,E,
        bind (raise abort v1 v2) t)
      (H,K,[d_lab_const L_y;d_lab_const L_env],t').
Close Scope Lexi_scope.

(* Changes made:

Lexi heap now also starts index from 0 rather than 1.

Lexi's asignment/set ref/v[i]<-v' now has an assumption
that i can't be out of range*)
