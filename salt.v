From Coq Require Import Lists.List.
(* ------------ ------------ ------------
   ------------ ------------ ------------
   ----------- Abstract Syntax -----------
   ------------ ------------ ------------
   ------------ ------------ ------------ *)
Definition heap_loc := nat.
Definition code_loc := nat.
(* Single Units *)
Inductive location : Type :=
  | h_loc : heap_loc -> location
  | c_loc : code_loc -> location
  | next : location -> location.
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
  | load : register -> register -> nat -> instr
  | store : register -> operand -> nat -> instr
  | push : operand -> instr
  | pop : register -> instr
  | call : operand -> instr
  | halt.
Inductive heap_val : Type :=
  | stack : list word -> heap_val
  | tuple : list word -> heap_val
  | empty_heap_val.
(* Compound Lists *)
Inductive instr_seq : Type :=
  | seq : instr -> instr_seq -> instr_seq
  | ret
  | jmp : operand -> instr_seq.
Definition reg_file : Type := register -> word.
Definition heap : Type := heap_loc -> heap_val.
Definition program : Type := code_loc -> instr_seq.

(* Coercions *)
Coercion h_loc : heap_loc >-> location.
Coercion c_loc : code_loc >-> location.
Coercion nat_reg : nat >-> register.
Coercion loc_w : location >-> word.
Coercion int_w : nat >-> word.
Coercion wd_o : word >-> operand.
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
Definition reg_empty (v : word) : reg_file := (fun _ => v).
Definition reg_update (m : reg_file) (x : register) (v : word) :=
  fun x' => if reg_eqb x x' then v else m x'.
Notation "'_' '!->r' v" := (reg_empty v)
  (at level 100, right associativity).
Notation "x '!->r' v ';' m" := (reg_update m x v)
  (at level 100, v at next level, right associativity).

Definition h_eqb (a b : heap_loc) := Nat.eqb a b.
Definition h_empty (v : heap_val) : heap := (fun _ => v).
Definition h_update (m : heap) (x : heap_loc) (v : heap_val) :=
  fun x' => if h_eqb x x' then v else m x'.
Notation "'_' '!->h' v" := (h_empty v)
  (at level 100, right associativity).
Notation "x '!->h' v ';' m" := (h_update m x v)
  (at level 100, v at next level, right associativity).

(* --------------------------------------------
                  Other helpers
   -------------------------------------------- *)
Fixpoint loc_to_nat (l : location) : nat :=
  match l with
  | h_loc h => h
  | c_loc c => c
  | next l' => S (loc_to_nat l')
  end.
Fixpoint incr_loc n (l : location) :=
  match n with
  | 0 => l
  | S n' => incr_loc n' (next l)
  end.
Definition add_wd (w1 w2 : word) : word :=
  match w1,w2 with
  | loc_w l, loc_w l' => int_w ((loc_to_nat l)+(loc_to_nat l'))
  | int_w n, int_w n' => int_w (n+n')
  | loc_w l, int_w n => int_w ((loc_to_nat l) + n)
  | int_w n, loc_w l => int_w ((loc_to_nat l) + n)
  | _,_ => ns
  end.
(* add n nonsenses to a list of words (for stacks) *)
Fixpoint n_ns n lst :=
  match n with
  | 0 => lst
  | S n' => n_ns n' (cons ns lst)
  end.
Fixpoint cdr_nth {A: Type} (n: nat) (lst: list A) :=
  match n, lst with
  | 0, lst' => lst'
  | S n', nil => nil
  | S n', cons x lst' => cdr_nth n' lst'
  end.
Fixpoint update_nth {A: Type} (n:nat) (lst:list A) (v:A) :=
  match n, lst with
  | 0, cons x lst' => cons v lst'
  | _, nil => nil
  | S n', cons x lst' => update_nth n' lst' v
  end.
(* --------------------------------------------
    Section for the cursive H hat of paper 
   -------------------------------------------- *)
Fixpoint nth_instr (is : instr_seq) (n : nat)
  : option (instr+instr_seq) :=
  match n,is with
  | 0, seq i is' => Some (inl i)
  | 0, ret => Some (inr ret)
  | 0, jmp o => Some (inr (jmp o))
  | S n', seq i is' => nth_instr is' n'
  | S n', _ => None
  end.
Fixpoint fetch_instr_h l (p : program) (acc : nat)
  : option (instr+instr_seq) :=
  match l with
  | next loc' => fetch_instr_h loc' p (1+acc)
  | c_loc c => nth_instr (p c) acc
  | h_loc h => None
  end.
(* returns instruction at given location *)
Definition fetch_instr l p := fetch_instr_h l p 0.
(* --------------------------------------------
          Section for R hat of paper
   -------------------------------------------- *)
(* returns word if given word,
   returns word in register if given register *)
Definition operand_value o r_file :=
  match o with
  | reg_o r => r_file r
  | wd_o w => w
  end.
(* --------------------------------------------
          Section for H hat of paper
   -------------------------------------------- *)
(* returns word at given heap memory address *)
Fixpoint next_counts_h loc n :=
  match loc with
  | next loc' => next_counts_h loc' (S n)
  | h_loc h => n
  | c_loc c => n
  end.
Definition next_counts loc := next_counts_h loc 0.
Definition fetch_heap (loc:heap_loc) (i:nat) (h:heap) :=
  match h loc with
  | stack lst => nth ((length lst)-i) lst ns
  | tuple lst => nth i lst ns
  | empty_heap_val => ns
  end.


(* --------------------------------------------
                      Interpreter
   -------------------------------------------- *)
Inductive step : program -> (heap * reg_file) ->
(heap * reg_file) -> Prop :=
  | S_add : forall P (H:heap) (R:reg_file) (l:location)
    (reg:register) (o:operand),
    R ip = l -> fetch_instr l P = Some (inl (add reg o)) ->
    step P (H,R)
      (H, ip !->r (next l); reg !->r (add_wd (R reg) (operand_value o R)) ; R)
  | S_mkstk : forall P (H:heap) (R:reg_file) (l:location)
    (reg:register) (L:heap_loc),
    R ip = l -> fetch_instr l P = Some (inl (mkstk reg))
    -> H L = empty_heap_val ->
    step P (H,R)
      (L !->h (stack nil) ; H,
      ip !->r (next l); reg !->r L; R)
  | S_salloc : forall P (H:heap) (R:reg_file) (l:location)
              (n j:nat) (lsp:heap_loc) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (salloc n))
    -> R sp =  (incr_loc j lsp) -> H lsp = stack lst -> length lst = j ->
    step P (H,R)
      (lsp !->h stack (n_ns n lst); H ,
      ip !->r (next l); sp !->r  (incr_loc (j+n) lsp); R)
  | S_push : forall P (H:heap) (R:reg_file) (l:location)
           (o:operand) (j:nat) (lsp:heap_loc) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (push o))
    -> R sp =  (j+(loc_to_nat lsp)) -> H lsp = stack lst
    -> H (1+j+(loc_to_nat lsp)) = empty_heap_val -> length lst = j ->
    step P (H,R)
      (lsp !->h stack (cons (operand_value o R) lst); H ,
      ip !->r (next l); sp !->r  (incr_loc (1+j) lsp); R)
  | S_sfree : forall P (H:heap) (R:reg_file) (l:location)
            (j n:nat) (reg:register) (lsp:heap_loc) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (sfree n))
    -> R reg =  (j+(loc_to_nat lsp)) -> H lsp = stack lst
    -> j >= n -> length lst = j ->
    step P (H,R)
      (lsp !->h stack (cdr_nth n lst); H,
      ip !->r (next l); sp !->r  (incr_loc (j-n) lsp); R)
  | S_pop : forall P (H:heap) (R:reg_file) (l:location)
          (j:nat) (reg:register) (lsp:heap_loc) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (pop reg))
    -> R sp =  (j+(loc_to_nat lsp)) -> H lsp = stack lst
    -> j > 0 -> length lst = j ->
    step P (H,R)
      (lsp !->h stack (cdr_nth 1 lst); H,
      ip !->r (next l); reg !->r (List.hd ns lst);
      sp !->r  (incr_loc (j-1) lsp); R)
  | S_malloc : forall P (H:heap) (R:reg_file) (l:location)
    (i d:nat) (L:heap_loc),
    R ip = l -> fetch_instr l P = Some (inl (malloc d i))
    -> H L = empty_heap_val ->
    step P (H,R)
      (L !->h tuple (n_ns i nil) ; H,
      ip !->r (next l) ; d !->r L ;R)
  | S_mov : forall P (H:heap) (R:reg_file) (l:location)
    (d:nat) (o:operand),
    R ip = l -> fetch_instr l P = Some (inl (mov d o)) ->
    step P (H,R)
      (H, ip !->r (next l); d !->r (operand_value o R); R)
  | S_mov_sp : forall P (H:heap) (R:reg_file) (l:location)
             (o:operand) (L:heap_loc) (lst:list word) (j k:nat),
    R ip = l -> fetch_instr l P = Some (inl (mov sp o))
    -> operand_value o R = (incr_loc j L) -> H L = stack lst
    -> length lst = k -> j <= k ->
    step P (H,R)
      (L !->h stack (cdr_nth (k-j) lst); H,
      ip !->r (next l); sp !->r (incr_loc j L) ; R)
  | S_load : forall P (H:heap) (R:reg_file) (l:location)
    (L:heap_loc) (d s j:nat),
    R ip = l -> fetch_instr l P = Some (inl (load d s j))
    -> R s = L ->
    step P (H,R)
      (H, ip !->r (next l); d !->r fetch_heap L j H ; R)
  | S_store : forall P (H:heap) (R:reg_file) (l:location)
    (L:heap_loc) (d j:nat) (o:operand) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (store d o j))
    -> R d = L -> H L = tuple lst -> j < length lst ->
    step P (H,R)
      (L !->h tuple (update_nth j lst (operand_value o R)); H,
      ip !->r (next l); R)
  | S_call : forall P (H:heap) (R:reg_file) (l l':location)
    (lsp:heap_loc) (j:nat) (o:operand) (lst:list word),
    R ip = l -> fetch_instr l P = Some (inl (call o))
    -> R sp = (incr_loc j lsp) -> H lsp = stack lst -> length lst = j
    -> operand_value o R = l' ->
    step P (H,R)
      (lsp !->h stack (cons (loc_w (next l)) lst) ; H,
      ip !->r l' ; R)
  | S_jmp : forall P (H:heap) (R:reg_file) (l l':location)
    (o:operand),
    R ip = l -> fetch_instr l P = Some (inr (jmp o))
    -> operand_value o R = l' ->
    step P (H,R) (H, ip !->r l' ; R)
  | S_ret : forall P (H:heap) (R:reg_file) (l l':location)
    (lst:list word) (j:nat) (lsp:heap_loc),
    R ip = l -> fetch_instr l P = Some (inr ret)
    -> R sp = (incr_loc j lsp) -> H lsp = stack (cons (loc_w l') lst)
    -> length lst = j-1 ->
    step P (H,R)
      (lsp !->h stack lst ; H, ip !->r l' ; R)
  | S_halt : forall P (H:heap) (R:reg_file) (l:location),
    R ip = l -> fetch_instr l P = Some (inl halt) ->
    step P (H,R) (H,R).
Definition normal_form_salt P H R : Prop := step P (H,R) (H,R).
Definition multi_step_salt (p:program) (h h':heap) (r r':reg_file)
 : Prop := Relation_Operators.clos_refl_trans_1n
  (heap * reg_file) (step p) (h,r) (h',r').
Definition interp p h h' r r' := 
  multi_step_salt p h h' r r' /\ normal_form_salt p h' r'.
