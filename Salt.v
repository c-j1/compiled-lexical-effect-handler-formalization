Require Import Lists.List. Import ListNotations.
Require Import Strings.String.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
(* Rather than having a "next" constructor that
   increments heap and code location, we implemented
   heap and code locations as some base location with
   some increments *)
Inductive heap_loc := hloc_num : nat -> heap_loc.
Inductive code_loc := cloc_str : string -> code_loc.
Inductive heap_location :=
  hloc : heap_loc -> nat -> heap_location.
Inductive code_location :=
  cloc : code_loc -> nat -> code_location.
Inductive location : Type :=
| h_loc : heap_location -> location
| c_loc : code_location -> location.
Inductive register : Type :=
| nat_reg : nat -> register
| ip
| sp.
Inductive word : Type :=
| loc_w : location -> word
| int_w : nat -> word
| ns.
Inductive operand : Type :=
| reg_o : register -> operand
| wd_o : word -> operand.
Inductive instr : Type :=
| add : register -> operand -> instr
| mkstk : register -> instr
| salloc : nat -> instr
| sfree : nat -> instr
| malloc : register -> nat -> instr
| mov : register -> operand -> instr
| load : register -> register -> bool -> nat -> instr
| store : register -> bool -> nat -> operand -> instr
| push : operand -> instr
| pop : register -> instr
| call : operand -> instr
| jmp : operand -> instr
| ret
| halt.
(* We explicitly separated heap values that are stacks,
   and heap values that are tuples, so that we can 
   explicitly split the heap into 2 parts that are easier
   to work with *)
Inductive stack_heap_val : Type :=
| stack : list word -> stack_heap_val.
Inductive tuple_heap_val : Type :=
| tuple : list word -> tuple_heap_val.
Definition heap_val := (stack_heap_val + tuple_heap_val)%type.
Inductive instr_seq : Type :=
| ins_seq : list instr -> instr_seq
| ns_ins_seq.
Definition reg_file : Type := list (register * word).
Definition stack_heap : Type :=
  list (heap_loc * stack_heap_val).
Definition tuple_heap : Type := heap_loc -> tuple_heap_val.
Definition heap : Type :=
  (stack_heap * tuple_heap).
Definition code_mem : Type := code_loc -> instr_seq.
(* Coercions *)
Coercion hloc_num : nat >-> heap_loc.
Coercion cloc_str : string >-> code_loc.
Coercion h_loc : heap_location >-> location.
Coercion c_loc : code_location >-> location.
Coercion loc_w : location >-> word.
Coercion int_w : nat >-> word.
Coercion wd_o : word >-> operand.
Coercion reg_o : register >-> operand.
(* --------------------------------------
   --------------------------------------
   ------- Operational Semantics --------
   --------------------------------------
   -------------------------------------- *)

(* --------------------------------------------
   initialization and update functions for
           registers and heaps
   -------------------------------------------- *)
Definition reg_eqb a b :=
  match a,b with
  | nat_reg n, nat_reg n' => (Nat.eqb n n')
  | ip, ip => true
  | sp, sp => true
  | _,_ => false
  end.
(* register file is always an association list,
   ordered by the order of registers *)
Fixpoint reg_update (rf : reg_file) (x : register)
  (v : word) :=
  match x,rf with
  | _,[] => (x,v) :: []
  | ip, (ip,w) :: rf' => (ip,v) :: rf'
  | sp, (sp,w) :: rf' => (sp,v) :: rf'
  | ip, (sp,w) :: rf' => (ip,v) :: rf
  | ip, ((nat_reg _),w) :: rf' => (ip,v) :: rf
  | sp, ((nat_reg _),w) :: rf' => (sp,v) :: rf
  | nat_reg n, ((nat_reg n'),w) :: rf' =>
    if Nat.eqb n n' then (x,v) :: rf'
    else (if Nat.ltb n n' then (x,v) :: rf
      else ((nat_reg n'),w) :: (reg_update rf' x v))
  | _, (r,w) :: rf' => (r,w) :: (reg_update rf' x v)
  end.
Fixpoint reg_app (rf:reg_file) r :=
  match rf with
  | (x,v) :: rf' => if reg_eqb x r then v else reg_app rf' r
  | [] => ns
  end.
Notation "x '!->r' v ';' m" := (reg_update m x v)
  (at level 100, v at next level, right associativity).
Definition h_eqb a b :=
  match a,b with
  | hloc_num a', hloc_num b' => Nat.eqb a' b'
  end.
Definition sh_empty : stack_heap := [].
Definition th_empty : tuple_heap := fun _ => tuple [].
Definition h_empty : heap :=
  (sh_empty, th_empty).
Fixpoint sh_update (sh:stack_heap) (x:heap_loc)
  (v:stack_heap_val) :=
  match sh with
  | [] => (x,v) :: []
  | (hl,shv) :: sh' => if h_eqb hl x then (hl,v) :: sh'
                       else (hl,shv) :: (sh_update sh' x v)
  end.
Definition th_update (th:tuple_heap) (x:heap_loc)
  (v:tuple_heap_val) :=
  (fun x' => if h_eqb x x' then v else th x').
Definition th_comp (h1:tuple_heap) (h2:tuple_heap) :=
  fun x => match h1 x with
           | tuple [] => h2 x
           | _ => h1 x
           end.
Notation "x '!->s' v ';' m" := (sh_update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '!->t' v ';' m" := (th_update m x v)
  (at level 100, v at next level, right associativity).

Definition c_empty : code_mem := fun _ => ns_ins_seq.
Definition c_eqb a b :=
  match a,b with
  | cloc_str a', cloc_str b' => eqb a' b'
  end.
Definition c_update (m : code_mem) (x : code_loc)
  (v : instr_seq) :=
  fun x' => if c_eqb x x' then v else m x'.
Definition c_comp (c1:code_mem) (c2:code_mem) :=
  fun x => match c1 x with
           | ns_ins_seq => c2 x
           | _ => c1 x
           end.
Notation "x '!->c' v ';' m" := (c_update m x v)
  (at level 100, v at next level, right associativity).

(* --------------------------------------------
                  Other helpers
   -------------------------------------------- *)
(* change number of increments in a location label *)
Definition next_cloc cl :=
  match cl with cloc loc n => cloc loc (S n) end.
Definition next_hloc (hl:heap_location) : heap_location :=
  match hl with hloc loc n => hloc loc (S n) end.
Fixpoint incr_cloc n (cl:code_location) : code_location :=
  match n with
  | 0 => cl
  | S n' => incr_cloc n' (next_cloc cl)
  end.
Fixpoint incr_hloc n (hl:heap_location) : heap_location :=
  match n with
  | 0 => hl
  | S n' => incr_hloc n' (next_hloc hl)
  end.

(* add n words to a list of words, used for adding
   ns to stacks *)
Fixpoint n_cons {A:Type} n v (lst:list A) :=
  match n with
  | 0 => lst
  | S n' => n_cons n' v (v :: lst)
  end.

Fixpoint update_nth {A: Type} (n:nat) (lst:list A) (v:A) :=
  match n, lst with
  | 0, x :: lst' => v :: lst'
  | S n', x :: lst' => x :: update_nth n' lst' v
  | _, [] => []
  end.
(* --------------------------------------------
    Section for the cursive H hat of paper 
   -------------------------------------------- *)
(* returns instruction at given location *)
Definition fetch_instr (cl : code_location) (c : code_mem) 
  : instr :=
  match cl with
  | cloc cloc' n =>
      match c cloc' with
      | ins_seq lst => nth n lst halt
      | ns_ins_seq => halt
      end
  end.

(* --------------------------------------------
          Section for R hat of paper
   -------------------------------------------- *)
(* returns word if given word,
   returns word in register if given register *)
Definition operand_value o (r_file:reg_file) :=
  match o with
  | reg_o r => reg_app r_file r
  | wd_o w => w
  end.
(* --------------------------------------------
                      Interpreter
   -------------------------------------------- *)
Inductive step (P:code_mem) :
  (heap * reg_file) -> (heap * reg_file) -> Prop :=
| S_add :
  forall (H:heap) (R:reg_file) (l:code_location)
         (reg:register) (o:operand) (w1 w2: nat),
    reg_app R ip = l -> fetch_instr l P = add reg o ->
    reg_app R reg = int_w w1 -> operand_value o R = int_w w2 ->
    step P (H,R)
      (H, ip !->r next_cloc l; reg !->r w1+w2 ; R)
| S_mkstk :
  forall (H_stk:stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location) (reg:register) (L:heap_loc),
    reg_app R ip = l -> fetch_instr l P = mkstk reg
    ->
    step P (H_stk,H_tup,R)
      ((L,stack []) :: H_stk,H_tup,
      ip !->r next_cloc l; reg !->r hloc L 0; R)
| S_salloc :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location) (n j:nat)
         (lsp:heap_loc) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = salloc n
    -> reg_app R sp = hloc lsp j
    -> H_stk = (lsp, stack lst) :: H_stk'
    -> List.length lst = j ->
    step P (H_stk,H_tup,R)
      ((lsp,stack (n_cons n ns lst)) :: H_stk',H_tup,
        ip !->r next_cloc l; sp !->r  hloc lsp (j+n); R)
| S_push :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (o:operand) (j:nat) (lsp:heap_loc) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = push o
    -> reg_app R sp = hloc lsp j
    -> H_stk = (lsp, stack lst) :: H_stk'
    -> List.length lst = j ->
    step P (H_stk,H_tup,R)
      ((lsp,stack ((operand_value o R) :: lst)) :: H_stk',
        H_tup,
        ip !->r next_cloc l; sp !->r hloc lsp (1+j); R)
| S_sfree :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (j n:nat) (lsp:heap_loc) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = sfree n
    -> reg_app R sp = hloc lsp j
    -> H_stk = (lsp, stack lst) :: H_stk'
    -> n <= j -> List.length lst = j ->
    step P (H_stk,H_tup,R)
      ((lsp,stack (skipn n lst)) :: H_stk',H_tup,
        ip !->r next_cloc l; sp !->r  hloc lsp (j-n); R)
| S_pop :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (j:nat) (reg:register) (lsp:heap_loc) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = pop reg
    -> reg_app R sp = hloc lsp j
    -> H_stk = (lsp, stack lst) :: H_stk'
    -> 0 < j -> List.length lst = j ->
    step P (H_stk,H_tup,R)
      ((lsp,stack (tl lst)) :: H_stk',H_tup,
        ip !->r next_cloc l; reg !->r (List.hd ns lst);
       sp !->r  hloc lsp (j-1); R)
| S_malloc_v :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location) (i:nat)
         (d:register) (L:heap_loc),
    reg_app R ip = l -> fetch_instr l P = malloc d i ->
    H_tup = th_comp H_vtup H_ctup ->
      step P (H_stk,H_tup,R)
        (H_stk,th_comp (L !->t tuple (n_cons i ns []) ; H_vtup)
          H_ctup,
           ip !->r next_cloc l ; d !->r hloc L 0 ;R)
| S_malloc_c :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location) (i:nat)
         (d:register) (L:heap_loc),
    reg_app R ip = l -> fetch_instr l P = malloc d i ->
    H_tup = th_comp H_vtup H_ctup ->
      step P (H_stk,H_tup,R)
        (H_stk,th_comp H_vtup
                 (L !->t tuple (n_cons i ns []) ; H_ctup),
           ip !->r next_cloc l ; d !->r hloc L 0 ;R)
| S_mov : forall (H:heap) (R:reg_file) (l:code_location)
                 (d:register) (o:operand),
    reg_app R ip = l -> fetch_instr l P = mov d o ->
    step P (H,R)
      (H, ip !->r next_cloc l; d !->r (operand_value o R); R)
| S_mov_sp_to_cont :
  forall (H_stk H_stk_ld H_stk_ed H_cont:stack_heap)
         (H_tup:tuple_heap) (R:reg_file) (l:code_location)
         (o:operand) (L:heap_loc) (lst:list word) (j k:nat),
    reg_app R ip = l -> fetch_instr l P = mov sp o
    -> operand_value o R = hloc L j
    -> H_stk = H_stk_ld ++ (L, stack lst) :: H_stk_ed
    -> List.length lst = k -> j <= k ->
    step P (H_stk ++ H_cont,H_tup,R)
      ((L,stack (skipn (k-j) lst)) :: H_stk_ed ++
        H_stk_ld ++ H_cont, H_tup,
        ip !->r next_cloc l; sp !->r hloc L j ; R)
| S_mov_sp_from_cont :
  forall (H_stk H_cont_ld H_cont' H_cont_ed H_cont:stack_heap)
         (H_tup H_ctup:tuple_heap) (R:reg_file) (l:code_location)
         (o:operand) (L:heap_loc) (lst:list word) (j k:nat),
    reg_app R ip = l -> fetch_instr l P = mov sp o
    -> operand_value o R = hloc L j
    -> H_cont = H_cont_ld ++
                  (L, stack lst) :: H_cont' ++ H_cont_ed
    -> List.length lst = k -> j <= k ->
    step P (H_stk ++ H_cont,H_tup,R)
      ((L,stack (skipn (k-j) lst)) :: H_cont' ++ H_stk
        ++ H_cont_ld ++ H_cont_ed, H_tup,
        ip !->r next_cloc l; sp !->r hloc L j ; R)
| S_mov_sp_del :
  forall (H_stk H_stk_ld H_stk_ed:stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (o:operand) (L L_fst:heap_loc)
         (lst s_fst:list word) (j k:nat),
    reg_app R ip = l -> fetch_instr l P = mov sp o
    -> operand_value o R = hloc L j
    -> H_stk = (L_fst,stack s_fst) :: H_stk_ld
                 ++ (L, stack lst) :: H_stk_ed
    -> List.length lst = k -> j <= k ->
    step P (H_stk,H_tup,R)
      ((L,stack (skipn (k-j) lst)) :: H_stk_ld ++ H_stk_ed,
        H_tup,
        ip !->r next_cloc l; sp !->r hloc L j ; R)
| S_load_stk :
  forall (H_stk H_stk_ld H_stk_ed:stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (s:register)
         (load_off reg_off:nat)
         (d:register) lst H,
    (* true means addition and false subtraction *)
    reg_app R ip = l -> fetch_instr l P = load d s false load_off
    -> reg_app R s = hloc L reg_off ->
    H = (H_stk,H_tup) ->
    H_stk = H_stk_ld ++ (L,stack lst) :: H_stk_ed ->
    step P (H,R)
      (H, ip !->r next_cloc l;
       d !->r nth (List.length lst - reg_off + load_off) lst ns; R)
| S_load_tup_v :
  forall (H_stk:stack_heap) (H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (s:register) (off:nat)
         (d:register) lst H,
    reg_app R ip = l -> fetch_instr l P = load d s true off
    -> reg_app R s = hloc L 0 ->
    H = (H_stk,th_comp H_vtup H_ctup) ->
    H_vtup L = tuple lst ->
    step P (H,R)
      (H, ip !->r next_cloc l;
       d !->r nth off lst ns; R)
| S_load_tup_c :
  forall (H_stk:stack_heap) (H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (s:register) (off:nat)
         (d:register) lst H,
    reg_app R ip = l -> fetch_instr l P = load d s true off
    -> reg_app R s = hloc L 0 ->
    H = (H_stk,th_comp H_vtup H_ctup) ->
    H_ctup L = tuple lst ->
    step P (H,R)
      (H, ip !->r next_cloc l;
       d !->r nth off lst ns; R)
| S_store_stk :
  forall (H_stk H_stk_ld H_stk_ed:stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (reg_off load_off:nat) (o:operand)
         (d:register) (lst:list word),
    reg_app R ip = l ->
    fetch_instr l P = store d false load_off o
    -> reg_app R d = hloc L reg_off ->
    H_stk = H_stk_ld ++ (L, stack lst) :: H_stk_ed ->
    load_off < List.length lst ->
    step P (H_stk,H_tup,R)
      (H_stk_ld ++
         (L, stack (update_nth
                      (List.length lst - reg_off + load_off)
                      lst (operand_value o R)))
         :: H_stk_ed, H_tup,
        ip !->r next_cloc l; R)
| S_store_v :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (j:nat) (o:operand)
         (d:register) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = store d true j o
    -> reg_app R d = hloc L 0 ->
    H_tup = th_comp H_vtup H_ctup ->
    H_vtup L = tuple lst ->
    j < List.length lst ->
    step P (H_stk,H_tup,R)
      (H_stk,th_comp
               (L !->t tuple (update_nth j lst (operand_value o R));
                H_vtup) H_ctup,
        ip !->r next_cloc l; R)
| S_store_c :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (j:nat) (o:operand)
         (d:register) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = store d true j o
    -> reg_app R d = hloc L 0 ->
    H_tup = th_comp H_vtup H_ctup ->
    H_ctup L = tuple lst ->
    j < List.length lst ->
    step P (H_stk,H_tup,R)
      (H_stk,th_comp H_vtup
               (L !->t tuple (update_nth j lst (operand_value o R));
                H_ctup),
        ip !->r next_cloc l; R)
| S_store_c_ns :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location)
         (L:heap_loc) (d:register) (v:word),
    reg_app R ip = l -> fetch_instr l P = store d true 0 ns
    -> reg_app R d = hloc L 0 ->
    H_tup = th_comp H_vtup H_ctup ->
    H_ctup L = tuple [v] ->
    step P (H_stk,H_tup,R)
      (H_stk,
        th_comp H_vtup
          (L !->t tuple [];H_ctup),
        ip !->r next_cloc l; R)
| S_call :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l l_dst:code_location)
         (lsp:heap_loc) (j:nat) (o:operand) (lst:list word),
    reg_app R ip = l -> fetch_instr l P = call o
    -> reg_app R sp = hloc lsp j -> H_stk = (lsp,stack lst) :: H_stk'
    -> List.length lst = j -> operand_value o R = l_dst ->
    step P (H_stk,H_tup,R)
      ((lsp,stack ((loc_w(next_cloc l)) :: lst)) :: H_stk',H_tup,
        ip !->r l_dst; sp !->r hloc lsp (S j); R)
| S_jmp :
  forall (H:heap) (R:reg_file) (l l':code_location)
         (o:operand),
    reg_app R ip = l -> fetch_instr l P = jmp o
    -> operand_value o R = l' ->
    step P (H,R) (H, ip !->r l' ; R)
| S_ret :
  forall (H_stk H_stk':stack_heap) (H_tup:tuple_heap)
         (R:reg_file) (l:code_location)
         (lst:list word) (pred_j:nat) (lsp:heap_loc),
    reg_app R ip = l -> fetch_instr l P = ret
    -> reg_app R sp = hloc lsp (S pred_j) ->
    H_stk = (lsp,stack lst) :: H_stk' ->
    List.length (tl lst) = pred_j ->
    lst <> [] ->
    step P (H_stk, H_tup,R)
      ((lsp,stack (tl lst))::H_stk',H_tup,
        ip !->r hd ns lst; sp !->r hloc lsp pred_j; R).
