From LSEH Require Import Lexa.
Import Lists.List. Import ListNotations.
Import Strings.String.
From LSEH Require Import Salt.
Module L := Lexa. Module S := Salt. 
(* -------------- Helper Functions ----------------- *)
(* The iota of APL, when only taking 1 argument *)
Fixpoint iota i :=
  match i with
  | S n => i :: (iota n)
  | O => []
  end.
Fixpoint zip_map {A B C: Type} (func:A->B->C) lst1 lst2 :=
  match lst1,lst2 with
  | x1 :: lst1', x2 :: lst2' =>
    [func x1 x2] ++ (zip_map func lst1' lst2')
  | _,_ => []
  end.

Fixpoint zip {A: Type} (lst1 lst2 : list A) :=
  match lst1,lst2 with
  | x :: lst1', y :: lst2' => [x; y] ++ (zip lst1' lst2')
  | [], _ => lst2
  | _, [] => lst1
  end.
Definition r0 := nat_reg 0.
Definition r1 := nat_reg 1.
Definition r2 := nat_reg 2.
Definition r3 := nat_reg 3.
Definition r4 := nat_reg 4.
Definition r5 := nat_reg 5.
Definition r6 := nat_reg 6.

Definition annotation_trans (a:L.annotation) r : instr :=
  match a with
  | L.general => mov r 0
  end.
Definition static_const_trans (c:L.static_const)
  : S.word :=
  match c with
  | nat_const n => n
  | c_lab_const (c_lab c) => cloc c 0
  end.
Definition run_cst_trans (v:L.runtime_const) : word :=
  match v with
  | run_const st_c => static_const_trans st_c
  | obj_lab d => hloc d 0
  | hdl_lab d => hloc d 4
  | L.ns => S.ns
  end.
Definition val_direct_trans (v:L.value)
  (stk_lst:list word) : S.word :=
  match v with
  | L.ind_val (dbj_ind n) =>
    nth n stk_lst ns
  | L.const_val c => static_const_trans c
  end.
Definition val_trans r (v:value) : instr :=
  match v with
  | L.ind_val (dbj_ind n) => load r sp false n
  | _ => mov r (val_direct_trans v [])
  end.

Definition expr_trans exp : list instr :=
  match exp with
  | L.val_e v =>  [val_trans r1 v]
  | L.add v1 v2 =>
    [val_trans r1 v1; val_trans r2 v2; add r1 r2]
  | L.app v lst => 
    ([val_trans r0 v] ++
    (rev (zip_map (val_trans)
      (map nat_reg (iota (List.length lst)))
      lst))
    ++ [call r0])
  | L.newref h_v =>
    ([malloc r1 (List.length h_v)] ++
    zip (map (val_trans r2) h_v)
      (map (fun x => store r1 true (x-1) r2)
        (iota (List.length h_v))))
  | L.pi i v => [val_trans r1 v; load r1 r1 true i]
  | L.asgn v1 i v2 =>
    [val_trans r1 v2; val_trans r2 v1; store r2 true i r1]
  | L.handle (L.c_lab clab_body)
    (L.c_lab clab_op) A v_env =>
    [annotation_trans A r4; val_trans r3 v_env;
      mov r2 (cloc clab_op 0); mov r1 (cloc clab_body 0);
     call (cloc "handle"%string 0)]
  | L.raise L.general v1 v2 => [val_trans r2 v2; val_trans r1 v1;
    call (cloc "raise"%string 0)]
  | L.resume v1 v2 => [val_trans r2 v2 ; val_trans r1 v1;
    call (cloc "resume"%string 0)]
  end.
Fixpoint term_trans tm : list instr:=
  match tm with
  | L.val_term v => [val_trans r1 v]
  | L.bind exp t =>
    expr_trans exp
    ++ [push r1]
    ++ term_trans t
  (* special case, not needed for translating code,
     but needed for relating lexa and salt's config *)
  | L.halt => [S.halt]
  end.

Fixpoint num_let tm :=
  match tm with
  | L.val_term v => 0
  | L.bind e tm' => S (num_let tm')
  | L.halt => 0
  end.
Definition func_term_trans (n:nat) (t:L.term) : list instr :=
  term_trans t ++
  match last (term_trans t) ret with
  | S.halt => []
  | S.jmp o => []
  | _ => [sfree (n + (num_let t)); ret]
  end.
Definition func_trans (f:L.function) : instr_seq :=
  match f with
  | L.func n t =>
      ins_seq
        ((map (fun x => push (nat_reg x))
           (iota n))
           ++ func_term_trans n t)
  | L.ns_func => S.ns_ins_seq
  end.
Definition code_mem_trans (c:L.code_mem) : S.code_mem :=
  fun (x:code_loc) =>
  match x with cloc_str str => func_trans (c str) end.  

