Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Program.Basics.
Declare Scope Lexa_scope.
Open Scope Lexa_scope.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
(* In the Coq formalization we represent variables
   as de Brujin Indices.

   We also explicitly differentiate
   between static constants and runtime generated constants,
   since this makes the proof more natural to work with.*)
Inductive dbj_index := dbj_ind : nat -> dbj_index.
Inductive code_label := c_lab : string -> code_label.
Inductive obj_label := obj_lab : nat -> obj_label.
Inductive hdl_label := hdl_lab : nat -> hdl_label.
Inductive static_const : Type :=
| nat_const : nat -> static_const
| c_lab_const : code_label -> static_const.
Inductive runtime_const : Type :=
| run_const : static_const -> runtime_const
| obj_lab_const : obj_label -> runtime_const
| hdl_lab_const : hdl_label -> runtime_const
| ns.
Inductive value :=
| const_val : static_const -> value
| ind_val : dbj_index -> value.
Definition local_env : Type := list runtime_const.
Inductive annotation : Type := general.
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
  hdl_f : hdl_label -> obj_label ->
          code_label -> annotation -> h_frame
(* In the paper, the evaluation context and continuation
   are represented as list of frames that can be either 
   activation frames or handler frames. In our Coq
   formalization, we explicitly represent continuations
   and evaluation contexts as list of handler led 
   activation frames *)
with hdl_led_frm_lst : Type :=
| hdl_led_lst : h_frame -> list a_frame -> hdl_led_frm_lst
with heap_cont : Type :=
| cont : list hdl_led_frm_lst -> heap_cont
| empty_cont.
Inductive heap_tuple : Type :=
| tuple : list runtime_const -> heap_tuple.
Definition eval_context := list hdl_led_frm_lst.
(* We also explicitly split the heap into heap of tuples
   and heap of continuations *)
Definition tup_heap := obj_label -> heap_tuple.
Definition cont_heap := list (obj_label * heap_cont).
Definition heap := (tup_heap * cont_heap)%type.
(* Since code memory is represented as a meta language
   function taking a code label and returning
   a "function" in object language, ns_func is the
   default return value which means that a code label
   has no associated function *)
Inductive function : Type :=
| func : nat -> term -> function
| ns_func.
Definition code_mem : Type := code_label -> function.

(* Coercions *)
Coercion dbj_ind : nat >-> dbj_index.
Coercion c_lab : string >-> code_label.
Coercion nat_const : nat >-> static_const.
Coercion c_lab_const : code_label >-> static_const.
Coercion run_const : static_const >-> runtime_const.
Coercion obj_lab_const : obj_label >-> runtime_const.
Coercion hdl_lab_const : hdl_label >-> runtime_const.
Coercion const_val : static_const >-> value.
Coercion val_e : value >-> expr.

(* --------------------------------------
   --------------------------------------
   ------- Operational Semantics --------
   --------------------------------------
   -------------------------------------- *)

(* --------------------------------------------
              Map Related Helpers
   -------------------------------------------- *)
(* Heap *)
Definition empty_tup := tuple [].
Definition h_eqb (a b : obj_label) := 
  match a,b with
  | obj_lab a', obj_lab b' => Nat.eqb a' b'
  end.
Definition th_empty : tup_heap := fun _ => empty_tup.
Definition ch_empty : cont_heap := [].
Definition h_empty : heap := (th_empty,ch_empty).
Definition th_update (m : tup_heap) (x : obj_label) (v : heap_tuple) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "x '!->t' v ';' m" :=
  (th_update m x v)
    (at level 100, v at next level, right associativity):Lexa_scope.
Definition ch_update
  (m : cont_heap) (x : obj_label) (v : heap_cont) :=
  (x,v) :: m.
Notation "x '!->ch' v ';' m" :=
  (ch_update m x v)
    (at level 100, v at next level, right associativity):Lexa_scope.

(* Environment *)
Definition env_fetch (env: local_env) (var:dbj_index)
  : runtime_const :=
  match var with
  | dbj_ind n => nth n env ns
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
    (at level 100, v at next level, right associativity):Lexa_scope.
(* --------------------------------------------
                  Other helpers
   -------------------------------------------- *)

Fixpoint update_nth {A: Type} (n:nat) (lst:list A) (v:A) :=
  match n, lst with
  | 0, x :: lst' => v :: lst'
  | _, [] => []
  | S n', x :: lst' => update_nth n' lst' v
  end.

(* E hat of paper *)
Definition var_deref (E:local_env) (val:value)
  : runtime_const :=
  match val with
  | ind_val ind => env_fetch E ind
  | const_val c => run_const c
  end.

Fixpoint fresh_cont_lab L (H_cont:cont_heap) :=
  match H_cont with
  | [] => true
  | (L',c) :: H_cont' =>
      if h_eqb L' L
      then false
      else fresh_cont_lab L H_cont'
  end.
Definition is_h_frm_general_hdl (f:h_frame) : bool :=
  match f with
  | hdl_f _ _ _ general => true
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
         cH, K, (obj_lab_const L) :: E, t)
| L_get : forall tH cH K E t (i:nat) (v:value)
                 (L:obj_label) (lst:list runtime_const),
    var_deref E v = L -> tH L = tuple lst ->
    step C (tH,cH,K,E, bind (pi i v) t)
      (tH,cH,K,(nth i lst ns) :: E,t)
| L_set : forall tH cH K E t (i:nat) (lst:list runtime_const)
                 (v v':value) (L:obj_label) (c:runtime_const),
    var_deref E v = L -> tH L = tuple lst ->
    i < List.length lst -> lst = [c] ->
    step C (tH,cH,K,E, bind (asgn v i v') t)
      (L !->t tuple (update_nth i lst (var_deref E v')); tH,
         cH,K,(var_deref E v') :: E,t)
| L_app : forall H K E t t' (n:nat)
                 (v v':value) (lst:list value)
                 (lab:code_label) hf alst,
    var_deref E v = lab ->
    C lab = func (List.length lst) t' ->
    lst = [v'] ->
    step C (H,(hdl_led_lst hf alst) :: K,E,bind (app v lst) t)
      (H, (hdl_led_lst hf ((act_f E t) :: alst)) :: K,
            rev (List.map (var_deref E) lst),t')
| L_ret : forall H K E E' t (v:value) hf alst,
    step C (H, (hdl_led_lst hf ((act_f E t) :: alst)) :: K,E',val_term v)
      (H,(hdl_led_lst hf alst) :: K,(var_deref E' v) :: E,t)
| L_handle :
  forall H K E t t' hf alst
         (v_env:value)
         (lab_body lab_op:code_label)
         (L:hdl_label) (L_env:obj_label),
    var_deref E v_env = L_env ->
    C lab_body = func 2 t' ->
    step C (H,(hdl_led_lst hf alst) :: K,E, bind (handle lab_body lab_op general v_env) t)
      (H,(hdl_led_lst (hdl_f L L_env lab_op general) [])
         :: (hdl_led_lst hf ((act_f E t)::alst)) :: K,
        [obj_lab_const L_env; hdl_lab_const L],t')
| L_leave :
  forall H K E E' t alst hf
         (L:hdl_label) (L_env:obj_label)
         (lab_op:code_label) (v:value),
    step C (H,
        (hdl_led_lst (hdl_f L L_env lab_op general) [])
          :: (hdl_led_lst hf ((act_f E t)::alst)) :: K,
        E',val_term v)
      (H,(hdl_led_lst hf alst) :: K,(var_deref E' v) :: E,t)
| L_raise_cur_hdl :
  forall LH_tup LH_cont K E t t' (v1 v2:value)
         op_arg (lab_op:code_label)
         (L:hdl_label) (L_k L_env:obj_label)
         alst_to_cont alst hf,
    var_deref E v1 = L ->
    var_deref E v2 = op_arg ->
    C lab_op = func 3 t' ->
    fresh_cont_lab L_k LH_cont = true ->
    step C (LH_tup,LH_cont,
        (hdl_led_lst (hdl_f L L_env lab_op general) alst_to_cont) ::
          (hdl_led_lst hf alst) :: K,E,
        bind (raise general v1 v2) t)
      (LH_tup, L_k !->ch 
                 cont [hdl_led_lst (hdl_f L L_env lab_op general)
                          ((act_f E t) :: alst_to_cont)];
       LH_cont,(hdl_led_lst hf alst) :: K,
         [obj_lab_const L_env;op_arg;obj_lab_const L_k],t')
| L_raise_past_hdls :
  forall LH_tup LH_cont K K' E t t' (v1 v2:value)
         op_arg (lab_op lab_opnew:code_label)
         (L L_new:hdl_label) (L_k L_env L_envnew:obj_label)
         alst_topmost alst_to_cont alst hf_topmost,
    var_deref E v1 = L ->
    var_deref E v2 = op_arg ->
    C lab_op = func 3 t' ->
    fresh_cont_lab L_k LH_cont = true ->
    step C (LH_tup,LH_cont,
        hdl_led_lst hf_topmost alst_topmost :: K' ++
          [hdl_led_lst (hdl_f L L_env lab_op general) alst_to_cont] ++
          hdl_led_lst (hdl_f L_new L_envnew lab_opnew general) alst :: K,E,
        bind (raise general v1 v2) t)
      (LH_tup, L_k !->ch 
                 cont (hdl_led_lst hf_topmost (act_f E t::alst_topmost) :: K' ++
                         [hdl_led_lst (hdl_f L L_env lab_op general) alst_to_cont]);
       LH_cont,(hdl_led_lst
                  (hdl_f L_new
                     L_envnew lab_opnew general) alst) :: K,
         [obj_lab_const L_env;op_arg;obj_lab_const L_k],t')
| L_resume_one_hdl :
  forall LH_tup LH_cont LH_cont_ld LH_cont_ed
         K E E' t t' (v1 v2:value)
         (L_k:obj_label) hf alst hf_cont alst_cont,
    var_deref E v1 = L_k ->
    LH_cont = LH_cont_ld ++
                    (L_k,cont [hdl_led_lst hf_cont
                                 (act_f E' t'::alst_cont)])
                    :: LH_cont_ed ->
    step C (LH_tup,LH_cont,(hdl_led_lst hf alst) :: K,E,bind (resume v1 v2) t)
      (LH_tup, LH_cont_ld ++ LH_cont_ed,
         hdl_led_lst hf_cont alst_cont ::
           hdl_led_lst hf (act_f E t :: alst) :: K,
         (var_deref E v2) :: E',t')      
| L_resume_many_hdls :
  forall LH_tup LH_cont LH_cont_ld LH_cont_ed
         K K' E E' t t' (v1 v2:value)
         (L_k:obj_label) hf alst hf_cont alst_cont
         hf_newtop alst_newtop,
    var_deref E v1 = L_k ->
    LH_cont =
      LH_cont_ld ++
      (L_k,cont (hdl_led_lst hf_newtop
                   (act_f E' t'::alst_newtop)
                   :: K' ++ [hdl_led_lst hf_cont
                               alst_cont]))
      :: LH_cont_ed ->
    is_h_frm_general_hdl hf_cont = true ->
    step C (LH_tup,LH_cont,(hdl_led_lst hf alst) :: K,E,bind (resume v1 v2) t)
      (LH_tup, LH_cont_ld ++ LH_cont_ed,
         hdl_led_lst hf_newtop alst_newtop :: K' ++
           [hdl_led_lst hf_cont alst_cont] ++
           hdl_led_lst hf (act_f E t :: alst) :: K,
         (var_deref E v2) :: E',t').
Close Scope Lexa_scope.

