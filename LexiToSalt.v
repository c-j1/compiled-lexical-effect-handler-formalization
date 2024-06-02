From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.

Module LexiSaltTrans.
(* -------------- Helper Functions ----------------- *)
Fixpoint iota i :=
  match i with
  | S n => cons i (iota n)
  | O => nil
  end.
Fixpoint ind_h lst str acc :=
  match lst with
  | cons y lst' => if L.var_eqb y str then acc else ind_h lst' str (S acc)
  | nil => 0
  end.
Definition ind lst str := ind_h lst str 0.
Fixpoint zip_map {A B C: Type} (func:A->B->C) lst1 lst2 :=
  match lst1,lst2 with
  | cons x1 lst1', cons x2 lst2' =>
    [func x1 x2] ++ (zip_map func lst1' lst2')
  | _,_ => nil
  end.

Fixpoint zip {A: Type} (lst1 lst2 : list A) :=
  match lst1,lst2 with
  | cons x lst1', cons y lst2' => [x; y] ++ (zip lst1' lst2')
  | nil, lst => lst2
  | lst, nil => lst1
  end.
(* Convert list of instructions to instruction sequences *)
Fixpoint concat_lst_seq lst s :=
  match lst with
  | cons istr lst' => seq istr (concat_lst_seq lst' s)
  | nil => s
  end.
(* -------------- Actual Translations ----------------- *)
Definition annotation_trans (a:L.annotation) r : instr :=
  match a with
  | L.tail => mov r 1
  | L.abort => mov r 2
  | L.general => mov r 0
  end.

Definition val_trans (env: list L.variable) r v : instr :=
  match v with
  | L.var_val str => load r sp (ind env str)
  | L.const_val (L.int_const i) => mov r i
  | L.const_val (L.c_lab_const (L.c_lab lab)) => mov r (c_loc lab)
  | _ => halt
  end.

Definition expr_trans env exp : list instr :=
  match exp with
  | L.val_e v =>  [val_trans env 1 v]
  | L.add v1 v2 =>
    [val_trans env 2 v1; val_trans env 1 v2; add 2 (reg_o 1)]
  | L.app v lst => 
    ([val_trans env 0 v] ++
    (rev (zip_map (val_trans env)
      (map nat_reg (iota (List.length lst)))
      lst))
    ++ [call 0])
  | L.newref (L.tuple h_v) =>
    ([malloc 2 (List.length h_v)] ++
    zip (map (val_trans env 1) h_v)
      (map (fun x => store 2 (x-1) (reg_o 1))
        (iota (List.length h_v))))
  | L.pi i v => [val_trans env 1 v; load 1 1 i]
  | L.asgn v1 i v2 =>
    [val_trans env 2 v2; val_trans env 1 v1; store 1 i (reg_o 2)]
  | L.handle (L.c_lab clab_body)
    (L.c_lab clab_op) A v_env =>
    [annotation_trans A 4; val_trans env 3 v_env;
      mov 2 (c_loc clab_op); mov 1 (c_loc clab_body);
      call (match A with 
      | L.general => (c_loc "handle"%string)
      | _ => (c_loc "handle_same_stack"%string) end)]
  | L.raise L.general v1 v2 => [val_trans env 2 v2; val_trans env 1 v1;
    call (c_loc "raise"%string)]
  | L.raise L.tail v1 v2 => [val_trans env 2 v2 ; val_trans env 1 v1;
    load 3 1 3; load 1 1 2 ; call (reg_o 3)]
  | L.resume v1 v2 => [val_trans env 2 v2 ; val_trans env 1 v1;
    call (c_loc "resume"%string)]
  (* Impossible case for newref continuation *)
  | _ => []
  end.
Fixpoint term_trans_h tm (env:list L.variable) : list instr:=
  match tm with
  | L.val_term v => [val_trans env 1 v]
  | L.bind var (L.raise L.abort v1 v2) t =>
    [val_trans env 2 v2 ; val_trans env 1 v1;
    load 3 1 3; mov sp (reg_o 1); load 1 1 2; sfree 4]
  | L.bind var (L.exit v) t =>
    [val_trans env 1 v; halt]
  | L.bind var exp t =>
    expr_trans env exp
    ++ [push (reg_o 
        match exp with 
        | L.add v1 v2 => 2
        | L.asgn v1 i v2 => 2
        | _ => 1 end )]
    ++ term_trans_h t (cons var env)
  (* Impossible case *)
  | L.halt v => []
  end.
Definition term_trans tm env : (list instr) + instr_seq :=
  match tm with
  | L.bind var (L.raise L.abort v1 v2) t =>
    inr (concat_lst_seq (term_trans_h tm env) (jmp (reg_o 3)))
  | tm' => inl (term_trans_h tm' env)
  end.
Fixpoint num_let tm :=
  match tm with
  | L.val_term v => 0
  | L.bind _ e tm' => S (num_let tm')
  | L.halt c => 0
  end.
Definition func_trans (f:L.function) : instr_seq :=
  match f with | L.func args t =>
    match List.length args with | n =>
      match term_trans t args with
      | inl t' => 
        concat_lst_seq
          (map (fun (x:nat) => (push (reg_o x))) (List.rev (iota n))
          ++ t' ++ [sfree (n + (num_let t))])
          ret
      | inr t' =>
        concat_lst_seq
          (map (fun (x:nat) => (push (reg_o x))) (List.rev (iota n)))
          t'
      end
    end
  end.
Definition code_trans (c:L.code) : program :=
  fun (x:code_loc) => func_trans (c (L.c_lab x)).
End LexiSaltTrans.