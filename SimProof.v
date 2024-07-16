Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
From TLC Require Import LibLN.
From LSEH Require Import Lexi.
From LSEH Require Import Salt.
From LSEH Require Import LexiToSalt.
From LSEH Require Import RelConfig.
From LSEH Require Import Infrastructure.
Module L := Lexi. Module S := Salt. Module LS := LexiToSalt.
Module R := RelConfig.
Delimit Scope Lexi_scope with L_scope.


(* ----------------------------------------------------------
                          Simulation 
   ---------------------------------------------------------- *)
Definition multi : forall A : Type, Relation_Definitions.relation A ->
  A -> A -> Prop := Relation_Operators.clos_refl_trans_1n.
Arguments multi {A}.
Inductive multi_plus {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | multi_one_step : forall (x y : X), R x y -> multi_plus R x y
  | multi_step : forall (x y z : X),
      R x y -> multi_plus R y z -> multi_plus R x z.
(* -----------------------------------------------------------------
    Theorem 2: translation from lexi to salt is semantic preserving
   ----------------------------------------------------------------- *)
(* By Theorem 1 already proven, this is reduced to proving LS_rel satisfying
  the 3 conditions *)


Theorem cond1 : forall C1 C2 M1 M2 main_lab init_lab,
  code_trans C1 = C2 ->
  init_L (c_lab init_lab) (letrec C1 (bind (app (c_lab main_lab) [])
    (bind (exit (var_val 0)) (val_term 0)))) M1
  -> init_S (cloc_str init_lab) (cloc_str main_lab) C2 M2 -> LS_rel M1 M2.
Proof with automate.
  intros. destruct M1 as [[[[LC LH] LK] LE] Lt], M2 as [[SC SH] SR].
  inversion H1... inversion H0...
  apply rel_LS with (len:=0) (Clab:=init_lab) (lst:=[])
    (SIlst:=[mov 0 (cloc main_lab 0); call 0;
    push (reg_o 1); load 1 sp false 0; halt])
    (Slsp:=hloc L_stack 0)...
  - destruct L_stack as [L_stack_str].
    apply rel_context with (Ks:=[]) (Flst:=[]) (E:=[])
      (s:=[]) (s':=[]) (s_out:=[]) (L_out:=L_stack_str) 
      (L_0:=L_stack_str)
      (H_stack:=sh_empty)...
  - intros. cbv in H. inversion H...
  - unfold c_update. rewrite c_eqb_refl...
  - repeat apply_fresh lc_bind...
Qed.

Theorem cond2 : forall M1 M2 i,
  LS_rel M1 M2 -> final_L M1 i -> final_S M2 i.
Proof with automate.
  intros. destruct M1 as [[[[LC LH] LK] LE] Lt], M2 as [[SC SH] SR].
  inversion H0... inversion H... inversion H10...
  simpl. rewrite H13. inversion H9... apply nth_middle.
Qed.

Definition un_tuple (tup:tuple_heap_val) : list word :=
  match tup with tuple lst => lst end.
Definition un_stack stk : list word :=
  match stk with
  | stack lst => lst
  | no_stacks => []
  end.
Lemma tuple_un_tuple : forall h_val,
    tuple (un_tuple h_val) = h_val.
Proof with automate. intros. destruct h_val... Qed.
Lemma stack_un_stack : forall lst,
    stack (un_stack (stack lst)) = stack lst.
Proof with automate. intros... Qed.
Lemma term_trans_not_nil : forall tm,
  term_trans tm <> [].
Proof with automate.
  intros. unfold not. destruct tm;simpl...
  destruct e;intros;simpl;apply eq_sym in H;
  generalize dependent H...
  - apply app_cons_not_nil.
  - destruct a...
Qed.



Theorem cond3 : forall LC SC H1 K1 E1 t1 R2 H2 H1' K1' E1' t1',
  LS_rel (LC, H1, K1, E1, t1)
    (SC, H2, R2) ->
  L.step LC (H1, K1, E1, t1) (H1', K1', E1', t1') ->
  (exists H2' R2',
    multi_plus (S.step SC)
      (H2, R2) (H2', R2') /\
    LS_rel (LC, H1', K1', E1', t1') (SC, H2', R2')).
Proof with super_a.
  intros. inversion H... inversion H12...
  inversion H0;automate;
  remember (List.map run_cst_trans E1 ++ s_out) as cur_stk_val;
  remember (cloc Clab (List.length lst)) as l;
  remember ((L_out,stack cur_stk_val)::H_stack) as cur_stkh.
  (* 14 stepping rules, prove the multi and rel for each *)
  4:
    { (* x = pi_i(v)*)
    destruct L as [L_str].
    exists ((L_out,
              stack (run_cst_trans (nth i lst0 L.ns) :: cur_stk_val))
              :: H_stack,SH_cont,SH_tup),
      ([(ip,loc_w (incr_cloc 3 l));
       (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
       (nat_reg 1,run_cst_trans (nth i lst0 L.ns));
       (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
        (nat_reg 5,o5);(nat_reg 6,o6)]). split.
    (* stepping salt code for loading from heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_cont,SH_tup),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 1,val_direct_trans v cur_stk_val);
               (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
               (nat_reg 5,o5);(nat_reg 6,o6)])).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (const_val cst) cur_stk_val) (l:=l)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
                 (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
            (H:=(cur_stkh,SH_cont,SH_tup)) (P:=SC)...
        - pose proof S_load_stk as Ins. specialize Ins with
          (d:=1) (s:=sp) (off:=ind)
          (L:=L_out) (H_stk:=cur_stkh) (H_cont:=SH_cont)
          (H_tup:=SH_tup) (sign:=false)
          (lst:=cur_stk_val) (i:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
                 (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
          (l:=l) (P:=SC). rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins;automate;cbn.
          + inversion H11. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val) (l:=l)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
                 (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
            (H:=(cur_stkh,SH_cont,SH_tup)) (P:=SC)... }
      apply multi_step with
        (y:=((cur_stkh,SH_cont,SH_tup),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 1,run_cst_trans (nth i lst0 L.ns));
               (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
               (nat_reg 5,o5);(nat_reg 6,o6)])).
      { pose proof S_load_tup as Temp. cbn in Temp.
        specialize Temp with
          (d:=1) (s:=nat_reg 1) (off:=i)
          (L:=L_str) (H_stk:=cur_stkh) (H_cont:=SH_cont)
          (H_tup:=SH_tup)
          (lst:=(List.map run_cst_trans lst0)) 
          (R:=[(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 1,val_direct_trans v cur_stk_val);
               (nat_reg 2,o2);(nat_reg 3,o3);
               (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
          (l:=next_cloc l) (P:=SC);automate;cbn.
        - rewrite H15. inversion H11. cbn. 
          assert (Temp:forall n, S n = n + 1).
          { intros. rewrite PeanoNat.Nat.add_comm... }
          rewrite Temp. apply app_nth2_plus with (n:=1) (l:=lst).
        - destruct v as [cst|[ind|str]]... cbn. inversion H17...
          inversion H5...
        - inversion H13...
          + inversion H2... specialize H1 with
              (L_tup:=L_str) (vs:=lst0)... rewrite H20.
          rewrite tuple_un_tuple... }
      constructor. cbn.
      apply S_push with (l:=incr_cloc 2 l) (lsp:=L_out)
      (o:=reg_o (nat_reg 1)) (lst:=cur_stk_val)
      (j:=List.length cur_stk_val) (H_stk:=cur_stkh) 
      (H_cont:=SH_cont) (H_tup:=SH_tup)
      (R:=[(ip,loc_w (incr_cloc 2 l));
           (sp,loc_w (hloc L_out (List.length cur_stk_val)));
           (nat_reg 1,nth i (un_tuple (SH_tup L_str)) ns);
           (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
           (nat_reg 5,o5);(nat_reg 6,o6)])... cbn.
      rewrite H15. assert (Temp:forall n, S (S n) = n + 2).
      { intros. rewrite PeanoNat.Nat.add_comm... } inversion H11.
      rewrite Temp. apply app_nth2_plus with (n:=2) (l:=lst).
    + (* prove LS_rel for L_get *)
      unfold incr_cloc...
      apply rel_LS with
      (lst:=lst ++ firstn 3 SIlst)
      (SIlst:= tl (tl (tl SIlst)));inversion H11...
      * cbn. pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=nth (S i) lst0 L.ns :: E1) (t:=t1').
      * apply rel_context with
          (s:=s) (s_out:=s_out) (L_0:=L_0)...
        rewrite <- map_nth with (d:=L.ns)...
        inversion H13...
        -- inversion H20... destruct i...
        -- 

          rewrite app_nth1...
        
        inversion H17... inversion H4...
      * rewrite H15. cbn. assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc_reverse...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
        
    - (* x = v1 + v2 *) exists
      ((L_out,stac  k ((int_w (i1+i2)) :: cur_stk_val))
        :: H_stack,SH_cont,SH_tup),
      ([(ip,loc_w (incr_cloc 4 l));(sp,loc_w (hloc L_out
        (1+(List.length cur_stk_val))));
        (nat_reg 1,int_w (i1+i2));(nat_reg 2,int_w i2);
        (nat_reg 3,o3);(nat_reg 4,o4);(nat_reg 5,o5);
        (nat_reg 6,o6)]). split.
    (* stepping translated salt code for addition *)
    + apply multi_step with (*y is 1 step after current*)
      (y:=((cur_stkh,SH_cont,SH_tup),
        [(ip,loc_w (next_cloc l));(sp,loc_w (hloc L_out
        (List.length cur_stk_val)));(nat_reg 1,int_w i1);
        (nat_reg 2,o2);(nat_reg 3,o3);
        (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])).
      { apply S_mov with (d:=1) (o:=i1)
        (l:=l) (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out
          (List.length cur_stk_val)));
          (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
          (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
        (H:=(cur_stkh,SH_cont,SH_tup)) (P:=SC)... inversion H10.
        simpl. rewrite H15... cbn. apply nth_middle. }
      apply multi_step with (y:=((cur_stkh, SH_cont,SH_tup),
      [(ip,loc_w (incr_cloc 2 l));(sp,loc_w (hloc L_out
      (List.length cur_stk_val)));(nat_reg 1,int_w i1);
      (nat_reg 2,int_w i2);(nat_reg 3,o3);
      (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])).
      { apply S_mov with (d:=2) (o:=i2)
        (l:=next_cloc l) (R:=[(ip,loc_w (next_cloc l));
          (sp,loc_w (hloc L_out (List.length cur_stk_val)));
          (nat_reg 1,int_w i1);(nat_reg 2,o2);(nat_reg 3,o3);
          (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
        (H:=(cur_stkh,SH_cont,SH_tup)) (P:=SC)... inversion H10.
        simpl. rewrite H15... rewrite <- last_length with (a:=mov 1 i1).
        cbn. assert (List_swp:forall lst', lst ++
        (mov 1 i1::mov 2 i2::lst')=
        lst ++ [mov 1 i1] ++ mov 2 i2::lst'). { intros... }
        rewrite List_swp, app_assoc.
        apply nth_middle with
          (a:=mov 2 i2)(l:=lst++[mov 1 i1])
          (l':=tl (tl(LS.func_term_trans (Datatypes.length E1)
            (L.bind (L.add 
            (L.st_cst_val i1)
            (L.st_cst_val i2)) t1')))). }
      apply multi_step with (y:=((cur_stkh,SH_cont,SH_tup),
      [(ip,loc_w (incr_cloc 3 l));(sp,loc_w (hloc L_out
      (List.length cur_stk_val)));(nat_reg 1,int_w (i1+i2));
      (nat_reg 2,int_w i2);(nat_reg 3,o3);
      (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])).
      { apply S_add with (w1:=i1) (w2:=i2) (reg:=nat_reg 1)
        (o:=reg_o (nat_reg 2)) (l:=incr_cloc 2 l)
        (H:=(cur_stkh,SH_cont,SH_tup)) (R:=[(ip,loc_w (incr_cloc 2 l));
          (sp,loc_w (hloc L_out (List.length cur_stk_val)));
          (nat_reg 1,int_w i1);(nat_reg 2,int_w i2);
          (nat_reg 3,o3);(nat_reg 4,o4);(nat_reg 5,o5);
          (nat_reg 6,o6)])... simpl. rewrite H15.
          inversion H10... cbn.
          assert (Temp:forall n, S (S n) = n + 2).
          { intros. rewrite PeanoNat.Nat.add_comm... }
          rewrite Temp.
          apply app_nth2_plus with (n:=2) (l:=lst). }
      constructor.
      apply S_push with (l:=incr_cloc 3 l) (lsp:=L_out)
      (o:=reg_o (nat_reg 1)) (lst:=cur_stk_val)
      (j:=List.length cur_stk_val) (H_stk:=cur_stkh) 
      (H_cont:=SH_cont) (H_tup:=SH_tup)
      (R:=[(ip,loc_w (incr_cloc 3 l));(sp,loc_w (hloc L_out
        (List.length cur_stk_val)));(nat_reg 1,int_w (i1+i2));
        (nat_reg 2,int_w i2);(nat_reg 3,o3);(nat_reg 4,o4);
        (nat_reg 5,o5);(nat_reg 6,o6)]);automate;simpl.
      rewrite H15. assert (Temp:forall n, S (S (S n)) = n + 3).
      { intros. rewrite PeanoNat.Nat.add_comm... } inversion H10...
      rewrite Temp. apply app_nth2_plus with (n:=3) (l:=lst).

    (* prove LS_rel for L_add *)
    + unfold h_update,incr_cloc,next_cloc... apply rel_LS with
      (lst:=lst ++ firstn 4 SIlst)
      (SIlst:= tl (tl (tl (tl SIlst))));inversion H10...
      * cbn. pose proof term_trans_not_nil as NN. specialize NN with
        (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?...
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=L.st_run_cst (i1 + i2) :: E1) (t:=t1').
      * apply rel_context with (s:=s) (s_out:=s_out)
        (L_0:=L_0)...
      * rewrite H15. cbn. assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc_reverse...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
  - (* x = v *) exists
      ((L_out,stack ((val_direct_trans v cur_stk_val) :: cur_stk_val))
        :: H_stack,SH_cont,SH_tup),
      ([(ip,loc_w (incr_cloc 2 l));(sp,loc_w (hloc L_out
        (1+(List.length cur_stk_val))));
        (nat_reg 1,val_direct_trans v cur_stk_val);(nat_reg 2,o2);
        (nat_reg 3,o3);(nat_reg 4,o4);(nat_reg 5,o5);
        (nat_reg 6,o6)]). split.
    + (* stepping translated salt code for single value *)
      apply multi_step with (*y is 1 step after current*)
      (y:=((cur_stkh,SH_cont,SH_tup),
        [(ip,loc_w (next_cloc l));(sp,loc_w (hloc L_out
        (List.length cur_stk_val)));(nat_reg 1,
          val_direct_trans v cur_stk_val);
        (nat_reg 2,o2);(nat_reg 3,o3);(nat_reg 4,o4);
        (nat_reg 5,o5);(nat_reg 6,o6)])).
      { destruct v as [cst|[ind]].
        - apply S_mov with (d:=1)
        (o:=val_direct_trans (st_cst_val cst) cur_stk_val)
        (l:=l) (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out
          (List.length cur_stk_val)));
          (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
          (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
        (H:=(cur_stkh,SH_cont,SH_tup)) (P:=SC)...
        inversion H10... cbn. rewrite H15...
        apply nth_middle.
        - pose proof S_load_stk as Ins. specialize Ins with
          (d:=1) (s:=sp) (off:=ind)
          (L:=L_out) (H_stk:=cur_stkh) (H_cont:=SH_cont)
          (H_tup:=SH_tup) (sign:=false)
          (lst:=cur_stk_val) (i:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out
          (List.length cur_stk_val)));
          (nat_reg 1,o1);(nat_reg 2,o2);(nat_reg 3,o3);
          (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])
          (l:=l) (P:=SC). rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins;automate;cbn.
          + inversion H10. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl... }
      constructor.
      apply S_push with (H_stk:=cur_stkh) (H_cont:=SH_cont)
      (H_tup:=SH_tup) (l:=next_cloc l) (o:=reg_o 1) (lsp:=L_out)
      (lst:=cur_stk_val) (j:=List.length cur_stk_val)
      (R:=[(ip,loc_w (next_cloc l));
      (sp,loc_w(hloc L_out (Datatypes.length cur_stk_val)));
      (nat_reg 1,val_direct_trans v cur_stk_val);
      (nat_reg 2,o2);(nat_reg 3,o3);
      (nat_reg 4,o4);(nat_reg 5,o5);(nat_reg 6,o6)])...
      cbn. rewrite H15. assert (Temp:forall n, S n = n + 1).
      { intros. rewrite PeanoNat.Nat.add_comm... }
      inversion H10... rewrite Temp.
      apply app_nth2_plus with (n:=1) (l:=lst).
    + (* prove LS_rel for x=v *)
      rewrite Heql. apply rel_LS with
        (lst:=lst ++ firstn 2 SIlst) (SIlst:= tl (tl SIlst))...
    
      * inversion H10. cbn. pose proof term_trans_not_nil as NN.
        specialize NN with (tm:=t1'). destruct
        (RelConfig.LS.term_trans t1')as []eqn:?... rewrite <- Heql.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=L.var_deref E1 v :: E1) (t:=t1').
      * apply rel_context with (s:=s) (s_out:=s_out)
        (L_0:=L_0)... destruct v as [cst|[ind]];cbn...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
(* need to guarantee that in programs entered by user,
   de brujin indices aren't out of range *)
      * rewrite H15. cbn. assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc_reverse...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...

(*other things
0. changes in lexi heaps e.g. assignment
1. handler related stuff
2. relating data heap
3. relating hdl-led-ctx*)

Qed.


(*
All changes made
*)




