From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.
Module L := Lexi. Module S := Salt. Module LS := LexiToSalt.
Delimit Scope Lexi_scope with L_scope.

(* All salt heaps start with every label allocating 0 space *)
(* ----------------------------------------------------------
            Traversal of Lexi terms
   ---------------------------------------------------------- *)
Inductive trav_exp (p : L.value -> Prop)
  : L.expr -> Prop :=
| trav_val_e : forall v, p v -> trav_exp p (L.val_e v)
| trav_add : forall v1 v2,
    p v1 -> p v2 -> trav_exp p (L.add v1 v2)
| trav_newref : forall lst,
    (forall v, In v lst -> p v) ->
    trav_exp p (newref lst)
| trav_pi : forall n v, p v -> trav_exp p (pi n v)
| trav_asgn : forall v1 v2 i,
    p v1 -> p v2 -> trav_exp p (asgn v1 i v2)
| trav_app : forall v lst,
    (forall v', In v' lst -> p v') ->
    p v -> trav_exp p (app v lst)
| trav_handle : forall c_lab1 c_lab2 A v,
    p v -> trav_exp p (handle c_lab1 c_lab2 A v)
| trav_raise : forall A v1 v2,
    p v1 -> p v2 ->
    trav_exp p (raise A v1 v2)
| trav_resume : forall v1 v2,
    p v1 -> p v2 ->
    trav_exp p (resume v1 v2).
Inductive trav_tm (p : nat -> L.value -> Prop)
  : nat -> L.term -> Prop :=
| trav_halt : forall k, trav_tm p k L.halt
| trav_val_tm : forall v k,
    p k v -> trav_tm p k (val_term v)
| trav_bind : forall exp t k, 
    trav_exp (p k) exp -> trav_tm p (1+k) t ->
    trav_tm p k (bind exp t).
(* ----------------------------------------------------------
                   Possibly don't need locally nameless     
   ---------------------------------------------------------- *)
Inductive wf_val : nat -> L.value -> Prop :=
| wf_ind : forall k ind,
    ind < k ->
    wf_val k (var_val (dbjind_var ind))
| wf_fvar : forall k fvar, wf_val k (var_val (free_var fvar))
| wf_cst : forall k cst, wf_val k (const_val cst).
Definition wf_tm (E:local_env) t := trav_tm wf_val (List.length E) t.
Inductive wf_func_tm : L.function -> Prop :=
| wf_func : forall i t,
    trav_tm wf_val i t -> wf_func_tm (func i t)
| wf_ns_func : wf_func_tm ns_func.

(* ----------------------------------------------------------
    Initial & Final Predicates for Lexi and Salt 
   ---------------------------------------------------------- *)
Definition exit_lab : string := "exit"%string.
Definition init_lab : string := "init"%string.
Definition main_lab : string := "main"%string.
(* note that the value returned after the "exit" doesn't
   matter to the translated program, so we just choose
   000 as an arbitrary value *)
Definition L_init_tm :=
  bind (app (c_lab main_lab) [])
    (bind (app exit_lab [var_val 0]) (val_term 000)).
Definition L_init_func :=
  (exit_lab !->c func 1 L.halt;
   init_lab !->c func 0 L_init_tm ; L.c_empty)%L_scope.

Definition handle_loc : S.code_loc := "handle"%string.
Definition handle_sm_stk_loc : S.code_loc := "handle_sm_stk"%string.
Definition raise_loc : S.code_loc := "raise"%string.
Definition resume_loc : S.code_loc := "resume"%string.

Definition S_init_ins :=
  code_mem_trans L_init_func.
Definition S_builtin_ins :=
  (handle_loc !->c
     ins_seq
     [mov r5 sp; mkstk sp;
      push r2; push r3;
      push r4; push r5;
      mov r6 r1; mov r2 sp;
      mov r1 r3; call r6;
      pop r2; sfree 3;
      mov sp r2; ret];
   handle_sm_stk_loc !->c
     ins_seq
     [push r2; push r3;
      push r4; push ns;
      mov r6 r1; mov r2 sp;
      mov r1 r3; call r6;
      sfree 4; ret];
   raise_loc !->c
     ins_seq
     [load r4 r1 false 0; (*r4 <- L_prev^|s_prev|*)
      store r1 false 0 sp; (*L_prev^|s_prev| -> cursp*)
      mov sp r4; (*sp <- L_prev^|s_prev|*)
      load r5 r1 false 3;(*r5 <- P_op*)
      malloc r3 1;store r3 true 0 r1;(*make heap tuple for L_rsp*)
      load r1 r1 false 2;(*r1 <- L_env*)
      call r5;
      ret];
   resume_loc !->c
     ins_seq
     [(*rewrite the tuple for L_rsp*)
       load r3 r1 true 0; store r1 true 0 ns;
       (*replace L^|s| in continuation*)
       load r4 r3 false 1;store r3 false 1 sp;
       mov r1 r2; mov sp r4;
       ret];
   c_empty).

Definition ns_hdl_lab : L.hdl_label := hdl_lab ""%string.
Definition ns_obj_lab : L.obj_label := obj_lab ""%string.
Definition ns_clab : L.code_label := ""%string.
Inductive init_L :
  L.code_mem -> (L.code_mem * L.heap * L.eval_context
                * L.local_env * L.term) -> Prop :=
| mk_init_L : forall (C:L.code_mem) (H:L.heap) dummy_hdl,
    dummy_hdl = handler_f ns_hdl_lab
                  ns_obj_lab ns_clab general ->
    (forall (x:string) n t,
        L.c_comp L_init_func C x = func n t ->
        S_builtin_ins x = ns_ins_seq) ->
    (forall x, wf_func_tm (C x)) ->
    init_L C
      (L.c_comp L_init_func C,
        L.h_empty, [hdl_led_lst dummy_hdl []] ,[], L_init_tm)%L_scope.
Definition ns_hloc_str : S.heap_loc := hloc_str ""%string.
Definition ns_hloc : S.word := hloc ns_hloc_str 0.
Definition ns_hdl_hloc : S.word := hloc ns_hloc_str 4.
Definition ns_cloc : S.word := cloc ""%string 0.
Inductive init_S : S.code_mem ->
  (S.code_mem * S.heap * reg_file) -> Prop :=
| mk_init_S : forall (uc:code_mem) dummy_hdl_stk,
    (* a stack section as a dummy handler *)
    dummy_hdl_stk = [loc_w (cloc handle_loc 10);
                     ns_hdl_hloc;int_w 0;ns_hloc;ns_cloc] ->
    (forall LC x,
        uc = code_mem_trans LC ->
        wf_func_tm (LC x)) ->
    (forall x lst,
        c_comp S_init_ins uc x = ins_seq lst ->
        S_builtin_ins x = ns_ins_seq) ->
    init_S
      uc (c_comp S_builtin_ins (c_comp S_init_ins uc),
        ([(ns_hloc_str,stack dummy_hdl_stk)] ++ [],th_comp th_empty th_empty),
        [(ip,loc_w (cloc init_lab 0));(sp,loc_w (hloc ns_hloc_str 5));
         (r0,ns);(r1,ns);
         (r2,ns);(r3,ns);(r4,ns);
         (r5,ns);(r6,ns)]).


Inductive final_L : (L.code_mem * L.heap * L.eval_context *
  L.local_env * L.term) -> nat -> Prop :=
  mk_final_L : forall C H K (i:nat),
    final_L (C,H,K,[run_const i],L.halt) i.
Inductive final_S : (S.code_mem * S.heap * reg_file) -> word -> Prop :=
| mk_final_S :
  forall p H_stk H_tup H_cont H_ctup R (l:code_location)
         (i:nat) lsp S,
    fetch_instr l p = halt ->
    final_S (p,((lsp,stack ((int_w i) :: S)) :: H_stk ++ H_cont,
                 th_comp H_tup H_ctup),
        [(ip,loc_w l);
         (sp,loc_w (hloc lsp (1 + (List.length S))))]
          ++ R) i.


(* ----------------------------------------------------------
            Relate configurations of Lexi and Salt 
   ---------------------------------------------------------- *)
Inductive LS_rel_run_cst :
  L.runtime_const -> S.word -> Prop :=
| rel_run_cst :
  forall cst, LS_rel_run_cst cst (run_cst_trans cst).
Definition run_cstlst_trans
  (lstv:list L.runtime_const) : list S.word :=
  List.map run_cst_trans lstv.
Inductive LS_rel_run_cstlst :
  list L.runtime_const -> list S.word -> Prop :=
| rel_run_csts : forall lstv,
    LS_rel_run_cstlst lstv (run_cstlst_trans lstv).
Definition env_trans
  (lstv:L.local_env) : S.stack_heap_val :=
  stack (run_cstlst_trans lstv).
Inductive LS_rel_env : L.local_env -> S.stack_heap_val -> Prop :=
| rel_env : forall envlst,
    LS_rel_env envlst (env_trans envlst).
Definition ins_trans (E:L.local_env) (t:L.term) :
  S.instr_seq :=
  ins_seq (LS.func_term_trans (List.length E) t).
Inductive LS_rel_ins : (L.local_env*L.term) -> S.instr_seq -> Prop :=
| rel_ins : forall E t,
    wf_tm E t ->
    LS_rel_ins (E,t)
      (ins_trans E t).
(*Definition frame_trans (af:L.a_frame) : S.stack_heap_val :=
  match af with
  | act_f E t =>
      stack ((loc_w (cloc C_lab (List.length lst)))
               :: (run_cst_trans E))
  end.
Inductive LS_rel_frame (C_mem : S.code_mem): L.a_frame -> S.stack_heap_val -> Prop :=
| rel_frame : forall E t Ilst C_lab i lst s,
    LS_rel_ins (L.ns :: E,t) (ins_seq (tl Ilst))
    -> C_mem C_lab = ins_seq (lst ++ Ilst)
    -> nth 0 Ilst halt = push r1 ->
    
    LS_rel_frame C_mem (act_f E t)
      (stack ((loc_w (cloc C_lab i)) :: s)).*)

Inductive LS_rel_frame (C_mem : S.code_mem): L.a_frame -> S.stack_heap_val -> Prop :=
  rel_frame : forall E t Ilst C_lab i lst s,
    LS_rel_ins (L.ns :: E,t) (ins_seq (tl Ilst))
    -> C_mem C_lab = ins_seq (lst ++ Ilst)
    -> List.length lst = i -> LS_rel_env E (stack s)
    -> nth 0 Ilst halt = push r1 ->
    LS_rel_frame C_mem (act_f E t)
    (stack ((loc_w (cloc C_lab i)) :: s)).
Inductive LS_rel_frames (C_mem : S.code_mem) : (list L.a_frame)
  -> S.stack_heap_val -> Prop :=
  | rel_noframe : LS_rel_frames C_mem [] (stack [])
  | rel_frame_cons : forall Fi si Flst s',
    LS_rel_frame C_mem Fi (stack si)
    -> LS_rel_frames C_mem Flst (stack s')
    -> LS_rel_frames C_mem (Fi :: Flst) (stack (si ++ s')).
Inductive LS_rel_hdl (L : string)
  : L.h_frame -> list S.word -> Prop :=
| rel_hdl_general : forall (L_env Clab_op:string) L_prev (s_prev:list word),
    LS_rel_hdl L
      (handler_f (hdl_lab L)
              (obj_lab L_env) Clab_op general)
      [loc_w (cloc handle_loc 10);
       loc_w (hloc L_prev (List.length s_prev));
       int_w 0; loc_w (hloc L_env 0);
       loc_w (c_loc (cloc Clab_op 0))].
Definition is_h_frm_general_hdl (f:L.h_frame) : bool :=
  match f with
  | handler_f _ _ _ general => true
  | _ => false
  end.
Inductive LS_rel_hdl_stk
  (C_mem : S.code_mem) (L : string) :
  L.hdl_led_frm_lst -> S.stack_heap_val -> Prop :=
| rel_hdl_stk_base : forall Flst s frm frm_stk,
    LS_rel_frames C_mem Flst (stack s) ->
    LS_rel_hdl L frm frm_stk ->
    is_h_frm_general_hdl frm = true ->
    LS_rel_hdl_stk C_mem L (hdl_led_lst frm Flst) (stack (s ++ frm_stk)).
(* ensures that each stack in the list of stacks
   relates to the corresponding frames of K, in
   the same and correct order
   
   also ensures that all stacks except the first one
   should point to the previous stack*)
Definition stk_points_to
  (s s_prev:list S.word) (L:heap_loc) :=
  nth_error (rev s) 3 = Some (loc_w (hloc L (List.length s_prev))).
Inductive LS_rel_eval_ctx (C_mem : S.code_mem) :
  L.eval_context -> S.stack_heap -> Prop :=
| rel_eval_ctx_nil : LS_rel_eval_ctx C_mem [] []
| rel_eval_ctx_lst : forall Ks H K s L,
    LS_rel_eval_ctx C_mem Ks H ->
    LS_rel_hdl_stk C_mem L K (stack s) ->
    (forall L' s' H',
        H = (L',stack s') :: H' -> 
        stk_points_to s s' L') ->
    LS_rel_eval_ctx C_mem (K :: Ks) ((hloc_str L,stack s) :: H).
Inductive LS_rel_env_context (C_mem : S.code_mem) : (L.eval_context * L.local_env) ->
  (S.stack_heap * S.heap_location) -> Prop :=
| rel_env_context :
  forall s' s_out Ks L_out (E:L.local_env) (H_stack:stack_heap),
    LS_rel_eval_ctx C_mem Ks ((L_out,stack s_out) :: H_stack) ->
    s' = (List.map run_cst_trans E) ++ s_out ->
    LS_rel_env_context C_mem (Ks, E)
      ((L_out, stack s') :: H_stack,
        hloc L_out (List.length s')).
Inductive LS_rel_tup_heap : L.tup_heap -> S.tuple_heap -> Prop :=
  rel_tup_heap :
    forall (LH_tup:L.tup_heap) (SH_tup:S.tuple_heap),
    (forall (L_tup:string) vs,
        LH_tup (obj_lab L_tup) = L.tuple vs
        -> SH_tup L_tup = tuple (List.map run_cst_trans vs)) ->
    LS_rel_tup_heap LH_tup SH_tup.
Inductive LS_rel_cont (C_mem : S.code_mem) :
  L.heap_cont -> S.stack_heap -> Prop :=
| rel_cont_stks :
  forall Ks H L_fst s_fst L_lst s_lst stks,
  LS_rel_eval_ctx C_mem Ks H ->
  H = (L_fst, stack s_fst)
        :: stks ++ [(L_lst, stack s_lst)] ->
  stk_points_to s_lst s_fst L_fst ->
  LS_rel_cont C_mem (cont Ks) H.
Inductive LS_rel_cont_heap (C_mem : S.code_mem) :
  L.cont_heap -> (S.stack_heap * S.tuple_heap) -> Prop :=
| rel_cont_heap :
  forall LH_cont SH_cont (SH_ctup:S.tuple_heap),
    (forall (L_rsp:string) L_last
            H_one_cont H_one_cont_ld
            H_conts_ld  H_conts_ed s_last,
        LS_rel_cont C_mem (LH_cont (obj_lab L_rsp)) H_one_cont ->
        H_one_cont = H_one_cont_ld ++ [(L_last,stack s_last)] ->
        SH_cont = H_conts_ld ++ H_one_cont ++ H_conts_ed
        /\ SH_ctup L_rsp = tuple [loc_w (hloc L_last 4)]) ->
    LS_rel_cont_heap C_mem LH_cont (SH_cont,SH_ctup).
(* each continuation is a list of stacks, like H_stk.
   The difference is that the first stack doesn't point
   back to the context frame where it was cut off, but rather
   circularly points to the last stack of this continuation.*)
Inductive LS_rel_heap (C_mem : S.code_mem) :
  L.heap -> (S.stack_heap * tuple_heap * tuple_heap) -> Prop :=
  rel_heap :
  forall LH_tup SH_tup
         (SH_conts:stack_heap * tuple_heap)
         (LH_cont:L.cont_heap),
    LS_rel_tup_heap LH_tup SH_tup ->
    LS_rel_cont_heap C_mem LH_cont SH_conts ->
    (forall (x:string) e lst,
        LH_tup (obj_lab x) = L.tuple (e :: lst) ->
        SH_tup x <> tuple []) ->
    LS_rel_heap C_mem (LH_tup,LH_cont) (SH_conts,SH_tup).
Inductive LS_rel_code_mem : L.code_mem -> S.code_mem -> Prop :=
| rel_code : forall LC SC,
    SC = code_mem_trans LC ->
    (forall x, wf_func_tm (LC x)) ->
    (forall (x:string) n t,
        LC x = func n t ->
        S_builtin_ins x = ns_ins_seq) ->
    LS_rel_code_mem LC SC.
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
  (L.code_mem * L.heap * L.eval_context * L.local_env * L.term)
  -> (S.code_mem * S.heap * reg_file) -> Prop :=
  rel_LS : forall len lst SIlst
    LC LH LK LE Lt SC o0 o1 o2 o3 o4 o5 o6
    (SH_stack SH_cont:stack_heap)
    (SH_tup SH_ctup:tuple_heap)
    (Slsp:heap_location) Clab,
    LS_rel_ins (LE,Lt) (ins_seq SIlst) ->
    LS_rel_env_context (c_comp S_builtin_ins SC)
      (LK,LE) (SH_stack,Slsp) ->
    LS_rel_heap SC LH ((SH_cont,SH_ctup),SH_tup) ->
    LS_rel_code_mem LC SC ->
    (c_comp S_builtin_ins SC) Clab = ins_seq (lst ++ SIlst) ->
    List.length lst = len ->
    (*lc_term Lt \/ body Lt*)
    LS_rel (LC, LH, LK, LE, Lt)
      (c_comp S_builtin_ins SC,
        (SH_stack ++ SH_cont,th_comp SH_tup SH_ctup),
        [(ip,loc_w (cloc Clab len));(sp,loc_w Slsp);
         (r0,o0);(r1,o1);
         (r2,o2);(r3,o3);(r4,o4);
         (r5,o5);(r6,o6)]).
(*
in rel_frame, the constructor for insturction sequence
shouldn't be ::, but should be ;

the rules for hdl-led ctx needs to be changed
handlers are on top not bottom, syntax wrong
  other than this the whole rules need to change


built in raise instruction sequence have 1 offset
wrong, and they should all be load _ [_-_], not
load _ [_+_] (same for store), because you go 
down the stack
*)
