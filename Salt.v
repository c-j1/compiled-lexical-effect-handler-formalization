Require Import Lists.List. Import ListNotations.
Require Import Strings.String.

(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
Inductive heap_loc := hloc_str : nat -> heap_loc.
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
Inductive stack_heap_val : Type :=
  | stack : list word -> stack_heap_val.
Inductive tuple_heap_val : Type :=
  | tuple : list word -> tuple_heap_val.
Definition heap_val := (stack_heap_val + tuple_heap_val)%type.
(* Compound Lists *)
Inductive instr_seq : Type :=
| ins_seq : list instr -> instr_seq
| ns_ins_seq.
Definition reg_file : Type := list (register * word).
Definition stack_heap : Type :=
  list (heap_loc * stack_heap_val).
Definition tuple_heap : Type := heap_loc -> tuple_heap_val.
(* K and E, continuations in heap, then tuples *)
Definition heap : Type :=
  (stack_heap * tuple_heap).
Definition code_mem : Type := code_loc -> instr_seq.
(* Coercions *)
Coercion hloc_str : nat >-> heap_loc.
Coercion cloc_str : string >-> code_loc.
Coercion h_loc : heap_location >-> location.
Coercion c_loc : code_location >-> location.
Coercion loc_w : location >-> word.
Coercion int_w : nat >-> word.
Coercion wd_o : word >-> operand.
Coercion reg_o : register >-> operand.
(* ------------ ------------ ------------
   ------------ ------------ ------------
   ------------- Interpreter -------------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)

(* --------------------------------------------
   initialization and update functions for maps
         (register and heap as functions)
   -------------------------------------------- *)
Definition reg_eqb a b :=
  match a,b with
  | nat_reg n, nat_reg n' => (Nat.eqb n n')
  | ip, ip => true
  | sp, sp => true
  | _,_ => false
  end.
(* register file is always an ordered list *)
Fixpoint reg_update (rf : reg_file) (x : register)
  (v : word) :=
  match x,rf with
  | _,nil => (x,v) :: nil
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
  | nil => ns
  end.
Notation "x '!->r' v ';' m" := (reg_update m x v)
  (at level 100, v at next level, right associativity).
Definition h_eqb a b :=
  match a,b with
  | hloc_str a', hloc_str b' => Nat.eqb a' b'
  end.
Definition sh_empty : stack_heap := nil.
Definition th_empty : tuple_heap := fun _ => tuple nil.
Definition h_empty : heap :=
  (sh_empty, th_empty).
Fixpoint sh_update (sh:stack_heap) (x:heap_loc)
  (v:stack_heap_val) :=
  match sh with
  | nil => (x,v) :: nil
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
(*Definition h_update (h : heap) (x : heap_loc) 
  (v : heap_val) :=
  match v, h with
  | inl (stack lst), (s_h,t_h) =>
    (sh_update s_h x (stack lst),t_h)
  | inr (tuple lst), (s_h,t_h) =>
    (s_h,th_update t_h x (tuple lst))
  (* undefined below *)
  | inl no_stacks, (s_h,t_h) => (s_h,t_h)
  end.
Notation "x '!->h' v ';' m" := (h_update m x v)
  (at level 100, v at next level, right associativity).*)
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
(* Fixpoint (*code_fetch*) (c: program) (lab: code_loc)
 : instr_seq :=
  match c with
  | (x,v) :: c' => if c_eqb x lab then v else 
    (*code_fetch*) c' lab
  | nil => empty_seq
  end.
*)
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
  | _, nil => nil
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
          Section for H hat of paper
   -------------------------------------------- *)
(* Fixpoint stk_heap_app (sh: stack_heap) (loc: heap_loc) :=
  match sh with
  | (x,v) :: sh' =>
    if h_eqb x loc then v else stk_heap_app sh' loc
  | [] => no_stacks
  end.
Definition fresh (h:heap) (loc:heap_loc) : bool :=
  match h with (s1,s2,t) =>
    match stk_heap_app s1 loc, stk_heap_app s2 loc, t loc with
    | no_stacks, no_stacks, tuple nil => true
    | _,_,_ => false
    end
  end.
returns word at given heap memory address
Definition heap_app (h: heap) (loc:heap_loc) :=
  match h with (s_h,t_h) =>
    match stk_heap_app s_h loc with
    | stack lst => inl (stack lst)
    | no_stacks => inr (t_h loc)
    end
  end.*)
(* Definition fetch_heap (loc:heap_loc) (i:nat) (h:heap) :=
  match h with (s_h1,s_h2,t_h) =>
    match stk_heap_app s_h1 loc,
      stk_heap_app s_h2 loc,t_h loc with
    | stack lst,no_stacks,tuple [] =>
      nth ((List.length lst)-i) lst ns
    | no_stacks,stack lst,tuple [] =>
      nth ((List.length lst)-i) lst ns
    | no_stacks,no_stacks,tuple lst => nth i lst ns
    | _,_,_ => ns
    end
  end.
*)
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
    -> (*fresh (H_stk,H_cont,H_tup) L = true ->*)
    step P (H_stk,H_tup,R)
      ((L,stack nil) :: H_stk,H_tup,
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
    (*fresh (H_stks,H_tup) L = true ->*)
      step P (H_stk,H_tup,R)
        (H_stk,th_comp (L !->t tuple (n_cons i ns nil) ; H_vtup)
          H_ctup,
           ip !->r next_cloc l ; d !->r hloc L 0 ;R)
| S_malloc_c :
  forall (H_stk:stack_heap) (H_tup H_vtup H_ctup:tuple_heap)
         (R:reg_file) (l:code_location) (i:nat)
         (d:register) (L:heap_loc),
    reg_app R ip = l -> fetch_instr l P = malloc d i ->
    H_tup = th_comp H_vtup H_ctup ->
    (*fresh (H_stks,H_tup) L = true ->*)
      step P (H_stk,H_tup,R)
        (H_stk,th_comp H_vtup
                 (L !->t tuple (n_cons i ns nil) ; H_ctup),
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
(*match sign with
  | true => reg_off + load_off
  | false => 
  end*)
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
(* Some properties and lemmas to be used later 
Lemma reg_eqb_refl : forall a, reg_eqb a a = true.
Proof with simpl;try reflexivity;auto.
  intros. unfold reg_eqb. induction a... induction n...
Qed.
Lemma leb_remov_SS : forall a b,
  Nat.leb (S a) (S b) = Nat.leb a b.
Proof with try reflexivity.
intros a. induction a;intros;induction b...
Qed.
Lemma leb_ab_Sab : forall a b,
  Nat.leb a b = false -> Nat.leb (S a) b = false.
Proof with try discriminate; try reflexivity.
  intros a. induction a;intros;induction b...
  rewrite leb_remov_SS. rewrite leb_remov_SS in H. auto.
Qed.
Lemma leb_not_eqb_means_ltb : forall a b,
  Nat.leb a b = true -> Nat.eqb a b = false ->
  Nat.ltb a b = true.
Proof with try reflexivity; try discriminate.
  unfold Nat.ltb. intros a. induction a;intros;induction b...
  rewrite leb_remov_SS. auto.
Qed.
Theorem reg_file_swap : forall R a b v1 v2,
  reg_eqb a b = false ->
  (a !->r v1; b !->r v2; R) = (b !->r v2; a !->r v1; R).
Proof with auto; try reflexivity.
  intros. induction R,a,b;inversion H;try reflexivity;
    try discriminate;simpl; try destruct a0,r.
  - rewrite H1. rewrite PeanoNat.Nat.eqb_sym in H1.
    rewrite H1. destruct Nat.ltb as []eqn:?;
    rewrite PeanoNat.Nat.ltb_antisym in Heqb;
    apply eq_sym in Heqb; apply Bool.negb_sym in Heqb;
    simpl in Heqb.
    + apply leb_ab_Sab in Heqb; unfold Nat.ltb.
    rewrite Heqb. reflexivity.
    + apply leb_not_eqb_means_ltb in Heqb... 
      rewrite Heqb...
  - 

Qed.
Theorem reg_file_front_update : forall R a v1 v2,
  (a !->r v1; a !->r v2; R) = (a !->r v1; R).
Proof.
  intros. induction a,R;simpl;
    try (rewrite nat_eqb_refl);try reflexivity;
    destruct p;induction r; try reflexivity.
  - 
Qed.
(n !->r v1;
 (let (r, w) := p in
  if
   match r with
   | nat_reg n' => Nat.eqb n n'
   | _ => false
   end
  then (n, v2) :: R
  else
   if
    match r with
    | nat_reg n' => Nat.ltb n n'
    | _ => false
    end
   then (n, v2) :: p :: R
   else (r, w) :: (n !->r v2; R))) =
(let (r, w) := p in
 if
  match r with
  | nat_reg n' => Nat.eqb n n'
  | _ => false
  end
 then (n, v1) :: R
 else
  if
   match r with
   | nat_reg n' => Nat.ltb n n'
   | _ => false
   end
  then (n, v1) :: p :: R
  else (r, w) :: (n !->r v1; R))
 *)


(*
raise abort's translation involves mov sp r1
label_handle involves mkstk sp, and mov sp r2 in the end.
  how handle works: make a new stack temporarily, call the function
  then ignore the new stack and go back to previous stack

label_raise
  sp now gets the location given by argument v1, translated to r1
  we then call the handler
label_resume
  similar, we also put content in r1 to sp

normally, sp points to top of first stack. When raising, sp points
to some middle stack, when resuming, sp go back to some stack
So we can view H_stack as two chuncks, 1 representing K of lexi,
the other representing heap of continuations.
 *)
(*
change sfree from r to sp in premise. Wrong register
for call and return, also increment and decrement stack pointer
    in principle we can also do it without changing stack pointer,
    but in practice that would require the offset of return to be
    j-1, so still we need to make some changes


load: used in 
  translating variables, 
  getting value/pi (load r1 r1 i): load from tuple,
    r1 always have offset 0, no need to special consider
  raise: load from stack, counting from bottom, also
    always offset 0
      nonono, these are also counting from top of stack
  raise general:
  resume:

raising handler has wrong offsets
 *)
