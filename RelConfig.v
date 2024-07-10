From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.
Compute is_in.
From TLC Require Import LibLN.
Module L := Lexi. Module S := Salt. Module LS := LexiToSalt.
Delimit Scope Lexi_scope with L_scope.

(* All salt heaps start with every label allocating 0 space *)
(* ----------------------------------------------------------
            Local Closure of Lexi terms
   ---------------------------------------------------------- *)
Definition open_val (k : nat) (u : L.variable) (v : L.value)
   : L.value :=
  match v with
  | const_val c => const_val c
  | var_val (dbjind_var i) =>
    if Nat.eqb k i then var_val u else var_val (dbjind_var i)
  | var_val (free_var str) => var_val (free_var str)
  end.
Definition open_exp (k : nat) (u : L.variable) (exp : L.expr)
  : expr :=
  match exp with
  | L.val_e val => L.val_e (open_val k u val)
  | L.add val1 val2 =>
    L.add (open_val k u val1) (open_val k u val2)
  | L.newref val_lst => L.newref (map (open_val k u) val_lst)
  | L.pi n val => L.pi n (open_val k u val)
  | L.asgn val1 i val2 =>
    L.asgn (open_val k u val1) i (open_val k u val2)
  | L.app val val_lst =>
    L.app (open_val k u val) (map (open_val k u) val_lst)
  | L.handle c_lab1 c_lab2 A val =>
    L.handle c_lab1 c_lab2 A (open_val k u val)
  | L.raise A val1 val2 =>
    L.raise A (open_val k u val1) (open_val k u val2)
  | L.resume val1 val2 =>
    L.resume (open_val k u val1) (open_val k u val2)
  | L.exit val => L.exit (open_val k u val)
  end.
Fixpoint open_tm (k : nat) (u : L.variable) (t : L.term)
  : term :=
  match t with
  | bind exp tm => bind (open_exp k u exp) (open_tm (S k) u tm)
  | val_term val => val_term (open_val k u val)
  | L.halt => L.halt
  end.

Inductive locally_closed : trm -> Prop :=
  | fvar_closed : forall str, locally_closed (free_var x)
  | bind_closed : forall exp t L, locally_closed exp ->
    (forall x, x \notin L, locally_closed (open x t))
    -> locally_closed (bind exp t).


(* ----------------------------------------------------------
    Initial & Final Predicates for Lexi and Salt 
   ---------------------------------------------------------- *)

Inductive init_S (init_lab main_lab:code_loc): S.program ->
  (S.program * S.heap * reg_file) -> Prop :=
  mk_init_S : forall (p:program) L_stack,
  init_S init_lab main_lab
    p (init_lab !->c
        ins_seq [mov 0 (cloc main_lab 0); call 0;
          push (reg_o 1); load 1 sp false 1; halt]; p,
      ((L_stack,stack [])::[],sh_empty, th_empty),
      [(ip,loc_w (cloc init_lab 0));(sp,loc_w (hloc L_stack 0));(nat_reg 1,ns);
       (nat_reg 2,ns);(nat_reg 3,ns);(nat_reg 4,ns);
       (nat_reg 5,ns);(nat_reg 6,ns)]).
(* note that the value returned after the "exit" doesn't
   matter to the translated program, so we just choose
   000 as an arbitrary value *)
Inductive init_L (init_lab:code_label): L.program -> (L.code * L.heap *
  L.eval_context * L.local_env * L.term) -> Prop :=
  mk_init_L : forall C (H:L.heap) main_lab init_tm,
    init_tm = bind (app (c_lab main_lab) [])
        (bind (exit (ind_val 1)) (val_term 000)) ->
    init_L init_lab
      (letrec C init_tm)
      (init_lab !->c func 0 init_tm ; C, L.h_empty, [] ,[],
        init_tm)%L_scope.
Inductive final_L : (L.code * L.heap * L.eval_context *
  L.local_env * L.term) -> nat -> Prop :=
  mk_final_L : forall C H (i:nat),
    final_L (C,H,[],[st_run_cst i],L.halt) i.
Inductive final_S : (S.program * S.heap * reg_file) -> word -> Prop :=
  mk_final_S : forall p H_stk H_cont H_tup R (l:code_location)
    (i:nat) lsp S,
    fetch_instr l p = halt ->
    final_S (p,((lsp,stack ((int_w i) :: S)):: H_stk,H_cont,H_tup),
    [(ip,loc_w l);(sp,loc_w (hloc lsp (1 + (List.length S))))] ++ R) i.


(* ----------------------------------------------------------
            Relate configurations of Lexi and Salt 
   ---------------------------------------------------------- *)
Inductive LS_rel_val : L.runtime_cst -> S.word -> Prop :=
  | rel_ns : LS_rel_val L.ns S.ns
  | rel_num : forall (i:nat), LS_rel_val (L.nat_const i) (S.int_w i)
  | rel_clab : forall (str:string),
    LS_rel_val (L.c_lab str) (S.cloc str 0)
  | rel_dlab : forall (str:string),
    LS_rel_val (L.obj_lab str) (S.hloc str 0).
Inductive LS_rel_vals : list L.runtime_cst -> list S.word -> Prop :=
  | rel_noval : LS_rel_vals [] []
  | rel_vals : forall v v' lstv lstv',
    LS_rel_val v v' -> LS_rel_vals lstv lstv'
    -> LS_rel_vals (v :: lstv) (v' :: lstv').
Inductive LS_rel_env : L.local_env -> S.stack_heap_val -> Prop :=
  | rel_env_base : LS_rel_env [] (stack [])
  | rel_env_cons : forall v v' env lst,
    LS_rel_val v v' -> LS_rel_env env (stack lst) ->
    LS_rel_env (v :: env)  (stack (v' :: lst)).
Inductive LS_rel_ins : (L.local_env*L.term) -> S.instr_seq -> Prop :=
  rel_tm : forall E t,
    LS_rel_ins (E,t)
      (ins_seq (LS.func_term_trans (List.length E) t)).

Inductive LS_rel_frame : L.a_frame -> S.stack_heap_val -> Prop :=
  rel_frame : forall E t Ilst C_mem C_lab i lst s,
    LS_rel_ins (E,t) (ins_seq Ilst)
    -> C_mem C_lab = ins_seq (lst ++ Ilst)(*Reverse Order Later*)
    -> List.length lst = i -> LS_rel_env E (stack s) ->
    LS_rel_frame (act_f E t)
    (stack ((loc_w (cloc C_lab i)) :: s)).
Inductive LS_rel_frames : (list L.frame)
  -> S.stack_heap_val -> Prop :=
  | rel_noframe : LS_rel_frames [] (stack [])
  | rel_frame_cons : forall Fi si Flst s',
    LS_rel_frame Fi (stack si)
    -> LS_rel_frames Flst (stack s')
    -> LS_rel_frames ((a_f Fi) :: Flst) (stack (si ++ s')).
Inductive LS_rel_hdl_led_ctx : list L.frame ->
  (S.word * S.stack_heap_val * S.stack_heap
  * S.word * S.stack_heap_val) -> Prop :=
  | rel_hdl_base : forall L s,
    LS_rel_hdl_led_ctx [] (L,s,sh_empty,L,s)
  | rel_hdl_general : forall Flst (s s' : list S.word) s_in s_out
    (L L_env Clab_op L_in:string) L_out  (H_stack:stack_heap) Ks,
    LS_rel_frames Flst (stack s) ->
    s' = s ++ [loc_w (hloc L_in (List.length s_in));
      int_w 0; loc_w (hloc L_env 0);
      loc_w (c_loc (cloc Clab_op 0))]
    -> LS_rel_hdl_led_ctx Ks 
       (loc_w (hloc L 0), stack s',H_stack,L_out,s_out) ->
    LS_rel_hdl_led_ctx
    ((h_f (handler_f (hand_lab L)
      (hand_lab L_env) Clab_op general)) :: Flst ++ Ks)
    (loc_w (hloc L_in 0), stack s_in,
      hloc_str L_in !->s stack s_in ; H_stack,
      L_out, s_out)
  | rel_hdl_tail : forall Flst s s' s_in s_out
    L L_in L_out (L_env Clab_op:string) (H_stack:stack_heap) Ks,
    LS_rel_frames Flst (stack s) ->
    s' = s ++ [ns; int_w 1; loc_w (hloc L_env 0);
      loc_w (c_loc (cloc Clab_op 0))] ++ s_in
    -> LS_rel_hdl_led_ctx Ks 
       (loc_w (hloc L_in 0), stack s',H_stack,L_out,s_out) ->
    LS_rel_hdl_led_ctx
    ((h_f (handler_f (hand_lab L)
      (hand_lab L_env) Clab_op tail)) :: Flst ++ Ks)
    (loc_w (hloc L_in 0), stack s_in, H_stack, L_out, s_out)
  | rel_hdl_abort : forall Flst s s' s_in s_out
    L L_in L_out (L_env Clab_op:string) (H_stack:stack_heap) Ks,
    LS_rel_frames Flst (stack s) ->
    s' = s ++ [ns; int_w 2; loc_w (hloc L_env 0);
      loc_w (c_loc (cloc Clab_op 0))] ++ s_in
    -> LS_rel_hdl_led_ctx Ks
       (loc_w (hloc L_in 0), stack s',H_stack,L_out,s_out) ->
    LS_rel_hdl_led_ctx
    ((h_f (handler_f (hand_lab L)
      (hand_lab L_env) Clab_op abort)) :: Flst ++ Ks)
    (loc_w (hloc L_in 0), stack s_in, H_stack, L_out, s_out).
Definition run_cst_trans (v:L.runtime_cst) : word :=
  match v with
  | st_run_cst st_c => static_const_trans st_c
  | obj_lab d => hloc d 0
  | hand_lab d => hloc d 0
  | L.ns => S.ns
  end.
Definition val_direct_trans (v:L.static_val)
  (stk_lst:list word) : S.word :=
  match v with
  | L.ind_val (dind n) =>
    nth n stk_lst ns
  | L.st_cst_val (nat_const n) => n
  | L.st_cst_val (c_lab_const (c_lab c)) => cloc c 0
  end.
Inductive LS_rel_context : (L.eval_context * L.local_env) ->
  (S.stack_heap * S.heap_location) -> Prop :=
  rel_context : forall Flst s s' s_out Ks L_0 L_out
    (E:L.local_env) (H_stack:stack_heap),
    LS_rel_frames Flst (stack s) ->
    LS_rel_hdl_led_ctx Ks
      (loc_w (hloc L_0 0),stack s,H_stack,
       loc_w (hloc L_out 0),stack s_out) ->
    s' = (map run_cst_trans E) ++ s_out ->
    LS_rel_context (Ks ++ Flst, E)
      ((L_out, stack s') :: H_stack, hloc L_out (List.length s')).
Inductive LS_rel_heap : L.heap -> (S.stack_heap * tuple_heap) -> Prop :=
  | rel_empty_heap :
    LS_rel_heap L.h_empty (sh_empty,th_empty)
  | rel_heap_tup : forall (vs:list runtime_cst) (vs':list word)
    (L:string) L_tup (LH:L.heap) (H_cont:stack_heap) (H_tup:tuple_heap),
    LS_rel_vals vs vs' -> LS_rel_heap LH (H_cont,H_tup) ->
    LS_rel_heap
      (obj_lab L_tup !->h L.tuple vs; LH)%L_scope
      (H_cont, L_tup !->t tuple vs'; H_tup)
  | rel_heap_cont : forall Fs (L:string) L_out L_env
    L_rsp s s_out (H_cont:stack_heap) (H_tup:tuple_heap) (LH:L.heap)
    Ks Clab_op,
    LS_rel_frames Fs (stack s) ->
    LS_rel_hdl_led_ctx Ks (loc_w (hloc L 0),stack s,
      H_cont,loc_w (hloc L_out 0), stack s_out) ->
    LS_rel_heap LH (H_cont,H_tup) ->
    LS_rel_heap
      (obj_lab L_rsp !->h cont (Ks ++ Fs ++
          [h_f (handler_f (hand_lab L) (hand_lab L_env)
            (c_lab Clab_op) general)]);
        LH)%L_scope
      (L !->s stack (s ++
          [loc_w (hloc L_out (List.length s_out));
            int_w 0;loc_w (hloc L_env 0);loc_w (cloc Clab_op 0)]);
        L_out !->s stack s_out; H_cont,
        L_rsp !->t tuple [loc_w (hloc L 4)];H_tup).
Inductive LS_rel_code : L.code -> S.program -> Prop :=
  | rel_code : forall C, LS_rel_code C (code_trans C)
  | rel_code_func : forall f (x:string) C,
    LS_rel_code (x !->c f ; C)%L_scope
      (cloc_str x !->c func_trans f; (code_trans C)).
(* A runtime lexi config relates to a runtime salt config if
   subparts of the configs relates to each other accordingly,
   and that the lexi term t is locally closed (i.e. without
   nonsensically large de brujin indices)

   The translation for free variables is undefined, but for
   the simplicity of the proof I will make all free variables
   dereference to L.ns, and the translated salt instruction
   will be mov r S.ns, so that they still relate. Therefore
   this LS_rel relation also relates lexi programs containing
   free variables, although we don't care about them. *)
Inductive LS_rel :
  (L.code * L.heap * L.eval_context * L.local_env * L.term)
  -> (S.program * S.heap * reg_file) -> Prop :=
  rel_LS : forall len lst SIlst
    LC LH LK LE Lt SC o1 o2 o3 o4 o5 o6
    (SH_stack:stack_heap) (SH_cont:stack_heap)
    (SH_tup:tuple_heap)
    (Slsp:heap_location) Clab,
    LS_rel_ins (LE,Lt) (ins_seq SIlst) ->
    LS_rel_context (LK,LE) (SH_stack,Slsp) ->
    LS_rel_heap LH (SH_cont,SH_tup) -> LS_rel_code LC SC ->
    SC Clab = ins_seq (lst ++ SIlst) -> List.length lst = len ->
    LS_rel (LC, LH, LK, LE, Lt)
      (SC, (SH_stack,SH_cont,SH_tup),
        [(ip,loc_w (cloc Clab len));(sp,loc_w Slsp);(nat_reg 1,o1);
        (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
        (nat_reg 5,o5);(nat_reg 6,o6)]).
(* Relation Preserved under reduction for both Lexi and Salt *)
(*
in rel_frame, the constructor for insturction sequence
shouldn't be ::, but should be ;

the rules for hdl-led ctx needs to be changed
handlers are on top not bottom, syntax wrong
  other than this the whole rules need to change

*)