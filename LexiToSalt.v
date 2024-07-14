From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
Module L := Lexi. Module S := Salt. 
(* -------------- Helper Functions ----------------- *)
Fixpoint iota i :=
  match i with
  | S n => cons i (iota n)
  | O => nil
  end.
Fixpoint zip_map {A B C: Type} (func:A->B->C) lst1 lst2 :=
  match lst1,lst2 with
  | cons x1 lst1', cons x2 lst2' =>
    [func x1 x2] ++ (zip_map func lst1' lst2')
  | _,_ => nil
  end.

Fixpoint zip {A: Type} (lst1 lst2 : list A) :=
  match lst1,lst2 with
  | cons x lst1', cons y lst2' => [x; y] ++ (zip lst1' lst2')
  | nil, _ => lst2
  | _, nil => lst1
  end.

(* -------------- Actual Translations ----------------- *)
Definition annotation_trans (a:L.annotation) r : instr :=
  match a with
  | L.tail => mov r 1
  | L.abort => mov r 2
  | L.general => mov r 0
  end.
Definition static_const_trans (c:L.static_const)
  : S.word :=
  match c with
  | nat_const n => n
  | c_lab_const (c_lab c) => cloc c 0
  end.
Definition val_direct_trans (v:L.value)
  (stk_lst:list word) : S.word :=
  match v with
  | L.var_val (dbjind_var n) =>
    nth n stk_lst ns
  | L.var_val (L.free_var _) => ns
  | L.const_val c => static_const_trans c
  end.
Definition val_trans r (v:value) : instr :=
  match v with
  | L.var_val (dbjind_var n) => load r sp false n
  | _ => mov r (val_direct_trans v [])
  end.

Definition expr_trans exp : list instr :=
  match exp with
  | L.val_e v =>  [val_trans 1 v]
  | L.add v1 v2 =>
    [val_trans 1 v1; val_trans 2 v2; add 1 (reg_o 2)]
  | L.app v lst => 
    ([val_trans 0 v] ++
    (rev (zip_map (val_trans)
      (map nat_reg (iota (List.length lst)))
      lst))
    ++ [call 0])
  | L.newref h_v =>
    ([malloc 2 (List.length h_v)] ++
    zip (map (val_trans 1) h_v)
      (map (fun x => store 2 (x-1) (reg_o 1))
        (iota (List.length h_v))))
  | L.pi i v => [val_trans 1 v; load 1 1 true i]
  | L.asgn v1 i v2 =>
    [val_trans 1 v2; val_trans 2 v1; store 2 i (reg_o 1)]
  | L.handle (L.c_lab clab_body)
    (L.c_lab clab_op) A v_env =>
    [annotation_trans A 4; val_trans 3 v_env;
      mov 2 (cloc clab_op 0); mov 1 (cloc clab_body 0);
      call (match A with 
      | L.general => (cloc "handle"%string 0)
      | _ => (cloc "handle_same_stack"%string 0) end)]
  | L.raise L.general v1 v2 => [val_trans 2 v2; val_trans 1 v1;
    call (cloc "raise"%string 0)]
  | L.raise L.tail v1 v2 => [val_trans 2 v2 ; val_trans 1 v1;
    load 3 1 false 3; load 1 1 false 2 ; call (reg_o 3)]
  | L.resume v1 v2 => [val_trans 2 v2 ; val_trans 1 v1;
    call (cloc "resume"%string 0)]
  (* Impossible case for newref continuation *)
  | _ => []
  end.
Fixpoint term_trans tm : list instr:=
  match tm with
  | L.val_term v => [val_trans 1 v]
  | L.bind (L.raise L.abort v1 v2) t =>
    [val_trans 2 v2 ; val_trans 1 v1;
    load 3 1 false 3; mov sp (reg_o 1); load 1 1 false 2;
    sfree 4; jmp (reg_o 3)]
  | L.bind (L.exit v) t =>
    [val_trans 1 v; halt]
  | L.bind exp t =>
    expr_trans exp
    ++ [push (reg_o 1)]
    ++ term_trans t
  (* special case, not needed for translating code,
     but needed for relating lexi and salt's config *)
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
  match last (term_trans t) S.halt with
  | S.halt => []
  | _ => [sfree (n + (num_let t)); ret]
  end.
Definition func_trans (f:L.function) : instr_seq :=
  match f with L.func n t =>
    ins_seq
    (map (fun (x:nat) => (push (reg_o x)))
      (List.rev (iota n))
    ++ func_term_trans n t)
  end.
Definition code_trans (c:L.code) : S.program :=
  fun (x:code_loc) =>
  match x with cloc_str str => func_trans (c str) end.

(*
All changes made
0. register 1 and register 2 are swapped in addition and assignment
*)
