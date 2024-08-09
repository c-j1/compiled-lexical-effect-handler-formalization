From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.
From TLC Require Import LibLN.
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
    trav_exp p (resume v1 v2)
| trav_exit : forall v, p v -> trav_exp p (exit v).
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
Definition wf_func_tm (f:L.function) :=
  match f with func i t => trav_tm wf_val i t end.
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
  : L.expr :=
  match exp with
  | L.val_e val => L.val_e (open_val k u val)
  | L.add val1 val2 =>
      L.add (open_val k u val1) (open_val k u val2)
  | L.newref val_lst => L.newref (List.map (open_val k u) val_lst)
  | L.pi n val => L.pi n (open_val k u val)
  | L.asgn val1 i val2 =>
      L.asgn (open_val k u val1) i (open_val k u val2)
  | L.app val val_lst =>
      L.app (open_val k u val) (List.map (open_val k u) val_lst)
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
Definition open var tm := open_tm 0 var tm.
Notation "t ^ x" := (open (free_var x) t).
Inductive lc_val : L.value -> Prop :=
| lc_fvar : forall x, lc_val (var_val (free_var x))
| lc_const : forall c, lc_val (const_val c).
Inductive lc_exp : L.expr -> Prop :=
| lc_val_e : forall v, lc_val v -> lc_exp (L.val_e v)
| lc_add : forall v1 v2,
    lc_val v1 -> lc_val v2 -> lc_exp (L.add v1 v2)
| lc_newref_nil : lc_exp (newref [])
| lc_newref_cons : forall lst v,
    lc_exp (newref lst) -> lc_val v -> lc_exp (newref (v::lst))
| lc_pi : forall n v, lc_val v -> lc_exp (pi n v)
| lc_asgn : forall v1 v2 i,
    lc_val v1 -> lc_val v2 -> lc_exp (asgn v1 i v2)
| lc_app_nil : forall v, lc_val v -> lc_exp (app v [])
| lc_app_cons : forall v v' lst,
    lc_val v -> lc_exp (app v lst)
    -> lc_exp (app v (v'::lst))
| lc_handle : forall c_lab1 c_lab2 A v,
    lc_val v -> lc_exp (handle c_lab1 c_lab2 A v)
| lc_raise : forall A v1 v2,
    lc_val v1 -> lc_val v2 ->
    lc_exp (raise A v1 v2)
| lc_resume : forall v1 v2,
    lc_val v1 -> lc_val v2 ->
    lc_exp (resume v1 v2)
| lc_exit : forall v, lc_val v -> lc_exp (exit v).

Inductive lc_term : L.term -> Prop :=
  | lc_bind : forall L exp t,
    (forall x, x \notin L -> lc_term (t ^ x))
    -> lc_exp exp -> lc_term (bind exp t)
  | lc_val_tm : forall v, lc_val v -> lc_term (val_term v)
  | lc_halt : lc_term L.halt.
Definition body t :=
  exists L, forall x, x \notin L -> lc_term (t ^ x).

(* ----------------------------------------------------------
    Initial & Final Predicates for Lexi and Salt 
   ---------------------------------------------------------- *)
Definition ns_hloc : S.word := hloc ""%string 0.
Definition ns_cloc : S.word := cloc ""%string 0.
Definition ns_hdl_lab : L.hdl_label := hdl_lab ""%string.
Definition ns_clab : L.code_label := ""%string.
Inductive init_S (init_lab main_lab:code_loc): S.program ->
  (S.program * S.heap * reg_file) -> Prop :=
| mk_init_S : forall (p:program) L_stack dummy_hdl_stk,
    (* a stack section as a dummy handler *)
    dummy_hdl_stk = [ns_hloc;int_w 0;ns_hloc;ns_cloc] ->
    (forall LC x, p = code_trans LC -> wf_func_tm (LC x)) ->
    init_S init_lab main_lab
      p (init_lab !->c
           ins_seq [mov 0 (cloc main_lab 0); call (reg_o 0);
                    push (reg_o 1); load 1 sp false 0; halt]; p,
           ([(L_stack,stack dummy_hdl_stk)],th_empty,(sh_empty, th_empty)),
           [(ip,loc_w (cloc init_lab 0));(sp,loc_w (hloc L_stack 4));
            (nat_reg 0,ns);(nat_reg 1,ns);
            (nat_reg 2,ns);(nat_reg 3,ns);(nat_reg 4,ns);
            (nat_reg 5,ns);(nat_reg 6,ns)]).
(* note that the value returned after the "exit" doesn't
   matter to the translated program, so we just choose
   000 as an arbitrary value *)
Inductive init_L (init_lab:code_label):
  L.program -> (L.code * L.heap * L.eval_context
                * L.local_env * L.term) -> Prop :=
| mk_init_L : forall C (H:L.heap) main_lab init_tm dummy_hdl,
    init_tm = bind (app (c_lab main_lab) [])
                (bind (exit (var_val 0)) (val_term 000)) ->
    dummy_hdl = h_f (handler_f ns_hdl_lab
                       ns_hdl_lab ns_clab general) ->
    (forall x, wf_func_tm (C x)) ->
    init_L init_lab
      (letrec C init_tm)
      (init_lab !->c func 0 init_tm ; C, L.h_empty, [dummy_hdl] ,[],
         init_tm)%L_scope.
Inductive final_L : (L.code * L.heap * L.eval_context *
  L.local_env * L.term) -> nat -> Prop :=
  mk_final_L : forall C H K (i:nat),
    final_L (C,H,K,[run_const i],L.halt) i.
Inductive final_S : (S.program * S.heap * reg_file) -> word -> Prop :=
  mk_final_S : forall p H_stk H_conts H_tup R (l:code_location)
    (i:nat) lsp S,
    fetch_instr l p = halt ->
    final_S (p,((lsp,stack ((int_w i) :: S)):: H_stk,H_tup,H_conts),
    [(ip,loc_w l);(sp,loc_w (hloc lsp (1 + (List.length S))))] ++ R) i.


(* ----------------------------------------------------------
            Relate configurations of Lexi and Salt 
   ---------------------------------------------------------- *)
Inductive LS_rel_run_cst :
  L.runtime_const -> S.word -> Prop :=
  rel_run_cst :
  forall cst, LS_rel_run_cst cst (run_cst_trans cst).
                     
Inductive LS_rel_run_csts :
  list L.runtime_const -> list S.word -> Prop :=
  rel_run_csts : forall lstv,
    LS_rel_run_csts lstv (List.map run_cst_trans lstv).

Inductive LS_rel_env : L.local_env -> S.stack_heap_val -> Prop :=
  rel_env : forall envlst,
    LS_rel_env envlst (stack (List.map run_cst_trans envlst)).
Inductive LS_rel_ins : (L.local_env*L.term) -> S.instr_seq -> Prop :=
  rel_tm : forall E t,
    LS_rel_ins (E,t)
      (ins_seq (LS.func_term_trans (List.length E) t)).

Inductive LS_rel_frame : L.a_frame -> S.stack_heap_val -> Prop :=
  rel_frame : forall E t Ilst C_mem C_lab i lst s,
    LS_rel_ins (L.ns :: E,t) (ins_seq (tl Ilst))
    -> C_mem C_lab = ins_seq (lst ++ Ilst)
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
Inductive LS_rel_hdl : L.h_frame -> list S.word -> Prop :=
| rel_hdl_general : forall (L L_env Clab_op:string) L_prev (s_prev:list word),
    LS_rel_hdl
      (handler_f (hdl_lab L)
              (hdl_lab L_env) Clab_op general)
      [loc_w (hloc L_prev (List.length s_prev));
       int_w 0; loc_w (hloc L_env 0);
       loc_w (c_loc (cloc Clab_op 0))]
| rel_hdl_other : forall (L L_env Clab_op:string) A num,
    (A = tail -> num = 1) -> (A = abort -> num = 2) ->
    LS_rel_hdl
      (handler_f (hdl_lab L)
              (hdl_lab L_env) Clab_op A)
      [ns; int_w num; loc_w (hloc L_env 0);
       loc_w (c_loc (cloc Clab_op 0))].
Definition is_general_hdl_frame (f:L.h_frame) : bool :=
  match f with
  | handler_f _ _ _ general => true
  | _ => false
  end.
Inductive LS_rel_hdl_stk :
  list L.frame -> list S.word -> Prop :=
| rel_hdl_stk_base : forall Flst s frm frm_stk,
    LS_rel_frames Flst (stack s) ->
    LS_rel_hdl frm frm_stk ->
    is_general_hdl_frame frm = true ->
    LS_rel_hdl_stk (Flst ++ [h_f frm]) (s ++ frm_stk)
| rel_hdl_stk : forall Flst s frm frm_stk Klst slst,
    LS_rel_hdl_stk Klst slst ->
    LS_rel_frames Flst (stack s) ->
    LS_rel_hdl frm frm_stk ->
    is_general_hdl_frame frm = false ->
    LS_rel_hdl_stk (Flst ++ [h_f frm] ++ Klst) (s ++ frm_stk ++ slst).
(* ensures that each stack in the list of stacks
   relates to the corresponding frames of K, in
   the same and correct order
   
   also ensures that all stacks except the first one
   should point to the previous stack*)
Inductive LS_rel_hdl_stk_lst :
  list L.frame -> list (S.heap_loc * S.stack_heap_val) -> Prop :=
| rel_hdl_stk_nil : LS_rel_hdl_stk_lst [] []
| rel_hdl_stk_lst : forall Ks H K s L,
    LS_rel_hdl_stk_lst Ks H ->
    LS_rel_hdl_stk K s ->
    LS_rel_hdl_stk_lst (K ++ Ks) ((L,stack s)::H).
Definition stk_points_to
  (s s_prev:list S.word) (L:string) :=
  nth_error (rev s) 3 = Some (loc_w (hloc L (List.length s_prev))).
(* must have at least 1 stack *)
Inductive LS_rel_eval_ctx :
  L.eval_context -> S.stack_heap -> Prop :=
| rel_hdl_led_ctx : forall Ks H,
    (forall L s s' L' H',
        H = [(L,stack s);(hloc_str L',stack s')] ++ H' ->
        stk_points_to s s' L') ->
    LS_rel_hdl_stk_lst Ks H ->
    LS_rel_eval_ctx Ks H.

Inductive LS_rel_env_context : (L.eval_context * L.local_env) ->
  (S.stack_heap * S.heap_location) -> Prop :=
| rel_env_context :
  forall s' s_out Ks L_out (E:L.local_env) (H_stack:stack_heap),
    LS_rel_eval_ctx Ks ((L_out,stack s_out) :: H_stack) ->
    s' = (List.map run_cst_trans E) ++ s_out ->
    LS_rel_env_context (Ks, E)
      ((L_out, stack s') :: H_stack,
        hloc L_out (List.length s')).
Inductive LS_rel_tup_heap : L.tup_heap -> S.tuple_heap -> Prop :=
  rel_tup_heap :
    forall (LH_tup:L.tup_heap) (SH_tup:S.tuple_heap),
    (forall (L_tup:string) vs,
        LH_tup (obj_lab L_tup) = L.tuple vs
        -> SH_tup L_tup = tuple (List.map run_cst_trans vs)) ->
    LS_rel_tup_heap LH_tup SH_tup.
(*
  
Inductive LS_rel_cont_stks :
  list L.frame -> S.stack_heap -> Prop :=
  rel_cont_stks :
    LS_rel_hdl_led_ctx Ks H_one_cont ->
    H_one_cont =
      [(L_last, stack (s_last))]
        ++ stks ++
        [stack (s_0 ++ [loc_w (hloc L_last (List.length s_last));
                          int_w 0; loc_w (hloc L_env 0);
                          loc_w (c_loc (cloc Clab_op 0))])]
                                                          
Inductive LS_rel_cont_heap :
  L.cont_heap -> (S.stack_heap * S.tuple_heap) -> Prop :=
  rel_cont_heap :
    forall LH_cont SH_cont (SH_ctup:S.tuple_heap),
      (forall (L_rsp:string) (L:string) L_out L_env  
              s s_out Ks Clab_op,
          LH_cont (obj_lab L_rsp) = cont Ks ->
          Ks = ([h_f (handler_f (hdl_lab L_out) (hdl_lab L_env')
                        (c_lab Clab_op') general)]
                  ++ Ks_middle ++
                  [h_f (handler_f (hdl_lab L) (hdl_lab L_env)
                          (c_lab Clab_op) general)]) ->
          LS_rel_hdl_led_ctx Ks SH_cont ->
          SH_ctup L_rsp = tuple [loc_w (hloc L 4)]
          /\ stk_heap_app SH_cont L_out = stack s_out
          /\ stk_heap_app SH_cont L =
           stack (s ++ [loc_w (hloc L_out (List.length s_out));
                        int_w 0;loc_w (hloc L_env 0);loc_w (cloc Clab_op 0)]))
      -> LS_rel_cont_heap LH_cont (SH_cont,SH_ctup).*)
(* each continuation is a list of stacks, like H_stk.
   The difference is that the first stack doesn't point
   back to the context frame where it was cut off, but rather
   circularly points to the last stack of this continuation.*)
Inductive LS_rel_heap :
  L.heap -> (S.stack_heap * tuple_heap * tuple_heap) -> Prop :=
  rel_heap :
  forall LH_tup SH_tup
         (SH_conts:stack_heap * tuple_heap) (LH_cont:L.cont_heap),
    LS_rel_tup_heap LH_tup SH_tup ->
    (* LS_rel_cont_heap LH_cont SH_conts -> *)
    LS_rel_heap (LH_tup,LH_cont) (SH_conts,SH_tup).
Inductive LS_rel_code : L.code -> S.program -> Prop :=
| rel_code : forall LC SC,
    SC = code_trans LC ->
    (forall x, wf_func_tm (LC x)) ->
    LS_rel_code LC SC.
(* | rel_code_func : forall f (x:string) C,
    LS_rel_code (x !->c f ; C)%L_scope
      (cloc_str x !->c func_trans f; (code_trans C)).*)
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
    LC LH LK LE Lt SC o0 o1 o2 o3 o4 o5 o6
    (SH_stack:stack_heap) (SH_conts:stack_heap * tuple_heap)
    (SH_tup:tuple_heap)
    (Slsp:heap_location) Clab,
    LS_rel_ins (LE,Lt) (ins_seq SIlst) ->
    LS_rel_env_context (LK,LE) (SH_stack,Slsp) ->
    LS_rel_heap LH (SH_conts,SH_tup) -> LS_rel_code LC SC ->
    SC Clab = ins_seq (lst ++ SIlst) -> List.length lst = len ->
    (*lc_term Lt \/ body Lt*)
    wf_tm LE Lt ->
    LS_rel (LC, LH, LK, LE, Lt)
      (SC, (SH_stack,SH_tup,SH_conts),
        [(ip,loc_w (cloc Clab len));(sp,loc_w Slsp);
         (nat_reg 0,o0);(nat_reg 1,o1);
         (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
         (nat_reg 5,o5);(nat_reg 6,o6)]).
(*
in rel_frame, the constructor for insturction sequence
shouldn't be ::, but should be ;

the rules for hdl-led ctx needs to be changed
handlers are on top not bottom, syntax wrong
  other than this the whole rules need to change

*)
