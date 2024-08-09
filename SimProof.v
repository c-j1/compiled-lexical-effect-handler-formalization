Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
From TLC Require Import LibLN.
From LSEH Require Import Lexi.
From LSEH  Require Import Salt.
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
Proof with super_a.
  intros. destruct M1 as [[[[LC LH] LK] LE] Lt], M2 as [[SC SH] SR].
  inversion H1... inversion H0...
  apply rel_LS with
    (SIlst:=[mov 0 (cloc main_lab 0); call (reg_o 0);
             push (reg_o 1); load 1 sp false 0; halt])
    (lst:=[])...
  - destruct L_stack as [L_stack_str].
    apply rel_env_context with
      (s_out:=[ns_hloc;int_w 0; ns_hloc; ns_cloc])...
    apply rel_hdl_stk_lst with
      (H:=[]) (Ks:=[]) (K:=[h_f (handler_f ns_hdl_lab ns_hdl_lab ns_clab general)])
      (s:=[ns_hloc;int_w 0; ns_hloc; ns_cloc])...
    apply rel_hdl_stk_base with
      (Flst:=[]) (s:=[])...
    cbv. apply rel_hdl_general with
      (L:=""%string) (L_env:=""%string) (Clab_op:=""%string)
      (L_prev:=""%string) (s_prev:=[]).
  - intros... cbv in H. injection H. intros...
  - extensionality x. destruct x as [str]. 
    unfold c_update,L.c_update.
    unfold c_eqb,L.c_eqb.
    destruct (eqb init_lab str) as []eqn:?;cbn;rewrite Heqb...
  - intros. unfold wf_func_tm,L.c_update.
    destruct (L.c_eqb init_lab x)...
    specialize H12 with x. unfold wf_func_tm in H12...
  - unfold c_update... rewrite eqb_refl...
    (*- repeat apply_fresh lc_bind...*)
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
Lemma ins_verify : forall (A : Type) (l l' : list A) (d : A) (n : nat),
       nth (n + Datatypes.length l) (l ++ l') d = nth n l' d.
Proof.
  intros. rewrite PeanoNat.Nat.add_comm.
  apply app_nth2_plus.
Qed.
Lemma val_dir_trans_var_deref : forall E (v:value) lst,
    (forall ind:nat, v = var_val ind -> ind < List.length E) ->
    val_direct_trans v (List.map run_cst_trans E ++ lst)
    = run_cst_trans (L.var_deref E v).
Proof with super_a.
  intros. destruct v as [|[|]]...
  rewrite <- map_nth with (d:=L.ns)...
  rewrite app_nth1... specialize H with n.
  rewrite map_length...  
Qed.
(*Lemma update_nth_map: forall {A B:Type} ind (f:A->B) lst v,
    update_nth ind (List.map f lst) (f v)
    = (List.map f (L.update_nth ind lst v)).
Proof with super_a.
intros. Search (List.map _ _=_(List.map _ _)). Admitted.
  Lemma Sn_n1 : forall n m, S n = n + 1.
Proof. intros.  Qed.
Lemma SSn_n2 : forall n, S (S n) = n + 2.*)
  
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
    remember ((L_out,stack cur_stk_val)::H_stack) as cur_stkh;
    remember [(nat_reg 3,o3);(nat_reg 4,o4);(nat_reg 5,o5);
              (nat_reg 6,o6)] as R36.
  (* 14 stepping rules, prove the multi and rel for each *)
   - (* x = v1 + v2 *) exists
      ((L_out,stack ((int_w (i1+i2)) :: cur_stk_val))
        :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 4 l));(sp,loc_w (hloc L_out
        (1+(List.length cur_stk_val))));
        (nat_reg 0,o0);
        (nat_reg 1,int_w (i1+i2));(nat_reg 2,int_w i2)]
      ++ R36). split.
    (* stepping translated salt code for addition *)
    + apply multi_step with (*y is 1 step after current*)
      (y:=((cur_stkh,SH_tup,SH_conts),
            [(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);(nat_reg 1,int_w i1);
             (nat_reg 2,o2)] ++ R36)).
      { apply S_mov with
          (d:=1) (o:=i1)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,o1);
               (nat_reg 2,o2)] ++ R36)...
        inversion H11. rewrite H15... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,int_w i1);
               (nat_reg 2,int_w i2)] ++ R36)).
      { apply S_mov with
          (d:=2) (o:=i2)
          (R:=[(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,int_w i1);
               (nat_reg 2,o2)] ++ R36)...
        inversion H11. rewrite H15...
        apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,int_w (i1+i2));
               (nat_reg 2,int_w i2)] ++ R36)).
      { apply S_add with
          (reg:=nat_reg 1)
          (o:=reg_o (nat_reg 2))
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,int_w i1);
               (nat_reg 2,int_w i2)] ++ R36)... rewrite H15. inversion H11...
        apply ins_verify with (n:=2). }
      constructor.
      apply S_push with
        (o:=reg_o (nat_reg 1))
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);(nat_reg 1,int_w (i1+i2));
             (nat_reg 2,int_w i2)] ++ R36)...
      rewrite H15. inversion H11... apply ins_verify with (n:=3).
    (* prove LS_rel for L_add *)
    + unfold incr_cloc,next_cloc... apply rel_LS with
      (lst:=lst ++ firstn 4 SIlst)
      (SIlst:= tl (tl (tl (tl SIlst))));inversion H11...
      * pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). cbn. destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm...        
      * apply rel_env_context with (s_out:=s_out)...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
      * destruct t1';inversion H17...
  - (* x = v *) exists
      ((L_out,stack ((val_direct_trans v cur_stk_val) :: cur_stk_val))
        :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 2 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (nat_reg 0,o0);
        (nat_reg 1,val_direct_trans v cur_stk_val);
        (nat_reg 2,o2)] ++ R36). split.
    + (* stepping translated salt code for single value *)
      apply multi_step with (*y is 1 step after current*)
      (y:=((cur_stkh,SH_tup,SH_conts),
            [(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v cur_stk_val);
             (nat_reg 2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with (d:=1)
        (o:=val_direct_trans (const_val cst) cur_stk_val)
        (R:=[(ip,loc_w l);
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);(nat_reg 1,o1);
             (nat_reg 2,o2)] ++ R36)...
        inversion H11... rewrite H15... apply nth_middle.
        - pose proof S_load_stk as Ins. specialize Ins with
          (d:=1) (s:=sp) (off:=ind)
          (L:=L_out) (sign:=false)
          (lst:=cur_stk_val) (i:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,o1);
               (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          destruct SH_conts. apply Ins...
          + inversion H11. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)...
        inversion H11... rewrite H15... apply nth_middle. }
      constructor.
      apply S_push with
        (o:=reg_o 1)
        (R:=[(ip,loc_w (next_cloc l));
             (sp,loc_w(hloc L_out (Datatypes.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v cur_stk_val);
             (nat_reg 2,o2)] ++ R36)...
      rewrite H15. inversion H11...
      apply ins_verify with (n:=1).
    + (* prove LS_rel for x=v *)
      rewrite Heql. rewrite HeqR36. apply rel_LS with
        (lst:=lst ++ firstn 2 SIlst) (SIlst:= tl (tl SIlst))...
      * inversion H11... pose proof term_trans_not_nil as NN.
        specialize NN with (tm:=t1'). destruct
        (RelConfig.LS.term_trans t1')as []eqn:?;automate. rewrite <- Heql.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=L.var_deref E1 v :: E1) (t:=t1').
      * apply rel_env_context with (s_out:=s_out)...
        destruct v as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        inversion H17... inversion H4... inversion H2...
        rewrite List.map_length...
      * rewrite H15. destruct SIlst... destruct SIlst...
        rewrite <- app_assoc. assert (AssocIns: forall (x1:instr) x2 tl,
          [x1;x2] ++ tl = x1::x2::tl). { intros... }
        rewrite <- AssocIns...
      * destruct SIlst... destruct SIlst...
        rewrite app_length. rewrite PeanoNat.Nat.add_comm...
      * destruct t1';inversion H17...
        
  - (* x = newref<v> *)
    destruct L as [L_str].
    exists ((L_out,
              stack (loc_w (hloc L_str 0) :: cur_stk_val)) :: H_stack,
             hloc_str L_str !->t
               tuple ([val_direct_trans v cur_stk_val]); SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 4 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (nat_reg 0,o0);
        (nat_reg 1,loc_w (hloc L_str 0));
        (nat_reg 2,val_direct_trans v cur_stk_val)]
      ++ R36). split.
      (* stepping salt code for newref *)
    + apply multi_step with
        (y:=((cur_stkh,
                hloc_str L_str !->t
                  tuple ([ns]);SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,loc_w (hloc L_str 0));
               (nat_reg 2,o2)] ++ R36)).
      { apply S_malloc with
          (i:=1) (d:=1)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                (nat_reg 0,o0);
               (nat_reg 1,o1);(nat_reg 2,o2)] ++ R36)...
        - rewrite H15. inversion H11... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,
                hloc_str L_str !->t
                  tuple ([ns]);SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,loc_w (hloc L_str 0));
               (nat_reg 2,val_direct_trans v cur_stk_val)]
        ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=2) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);
                 (nat_reg 1,loc_w (hloc L_str 0));
                 (nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11...
          apply ins_verify with (n:=1).
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=2) (s:=sp) (off:=ind)
            (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);
                 (nat_reg 1,loc_w (hloc L_str 0));
                 (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          destruct SH_conts. apply Ins...
          + inversion H11. rewrite H15... apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=2) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);
                 (nat_reg 1,loc_w (hloc L_str 0));
                 (nat_reg 2,o2)] ++ R36)...
      rewrite H15. inversion H11... apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((cur_stkh,
                hloc_str L_str !->t
                  tuple ([val_direct_trans v cur_stk_val]);SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,loc_w (hloc L_str 0));
               (nat_reg 2,val_direct_trans v cur_stk_val)]
        ++ R36)).
      { pose proof S_store as Ins. specialize Ins with
          (d:=1) (o:=reg_o 2) (j:=0) (L:=hloc_str L_str)
          (H_tup:= L_str !->t tuple [ns]; SH_tup) (lst:=[ns])
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,loc_w (hloc L_str 0));
               (nat_reg 2,val_direct_trans v cur_stk_val)] ++ R36).
        rewrite heap_front_update in Ins. apply Ins...
        - rewrite H15. inversion H11.
          apply ins_verify with (n:=2).
        - unfold th_update. rewrite h_eqb_refl... }
      constructor.
      apply S_push with
        (o:=reg_o (nat_reg 1))
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,loc_w (hloc L_str 0));
             (nat_reg 2,val_direct_trans v cur_stk_val)] ++ R36)...
      rewrite H15. inversion H11... apply ins_verify with (n:=3).
    + (* Prove LS_rel for newref *)
      unfold incr_cloc,next_cloc... apply rel_LS with
      (lst:=lst ++ firstn 4 SIlst)
      (SIlst:= tl (tl (tl (tl SIlst))));inversion H11;automate.
      * pose proof term_trans_not_nil as NN. specialize NN with
        (tm:=t1'). cbn. destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=L.d_lab_const (L.obj_lab L_str) :: E1) (t:=t1').
      * apply rel_env_context with (s_out:=s_out)...
      * unfold th_update,L.th_update,L.h_eqb,h_eqb.
        intros. destruct (String.eqb L_str L_tup)...
        -- inversion H1... destruct v as [|[|]]...
           rewrite <- map_nth with (d:=L.ns)...
           rewrite app_nth1... inversion H17...
           inversion H7...
           specialize H3 with (v:=L.var_val n).
           assert (Temp:In (L.var_val n) [L.var_val (L.dbjind_var n)]).
           { super_a. } apply H3 in Temp. inversion Temp...
           rewrite List.map_length...
        -- inversion H13... inversion H3...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
      * destruct t1';inversion H17...
  - (* x = pi_i(v)*)
    destruct L as [L_str].
    exists ((L_out,
              stack ((nth i (List.map run_cst_trans lst0) ns) :: cur_stk_val))
              :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 3 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (nat_reg 0,o0);
        (nat_reg 1,nth i (List.map run_cst_trans lst0) ns);
        (nat_reg 2,o2)] ++ R36). split.
    (* stepping salt code for loading from heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v cur_stk_val);
               (nat_reg 2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (const_val cst) cur_stk_val) (l:=l)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)...
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=1) (s:=sp) (off:=ind) (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins. destruct SH_conts.
          apply Ins...
          + inversion H11. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)... }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,nth i (List.map run_cst_trans lst0) ns);
               (nat_reg 2,o2)] ++ R36)).
      { apply S_load_tup with
          (d:=1) (s:=nat_reg 1) (off:=i)
          (L:=L_str) (lst:=(List.map run_cst_trans lst0)) 
          (R:=[(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v cur_stk_val);
               (nat_reg 2,o2)] ++ R36)...
        - rewrite H15. inversion H11...
          apply ins_verify with (n:=1).
        - destruct v as [cst|[ind|str]]...
          inversion H4... rewrite app_nth1.
          rewrite map_nth with (d:=L.ns).
          rewrite H2... rewrite map_length.
          inversion H17... inversion H7... inversion H3...
        - inversion H13... inversion H2... }
      constructor. 
      apply S_push with
      (o:=reg_o (nat_reg 1)) 
      (R:=[(ip,loc_w (incr_cloc 2 l));
           (sp,loc_w (hloc L_out (List.length cur_stk_val)));
           (nat_reg 0,o0);
           (nat_reg 1,nth i (List.map run_cst_trans lst0) ns);
           (nat_reg 2,o2)] ++ R36)...
      rewrite H15. inversion H11. apply ins_verify with (n:=2).
    + (* prove LS_rel for L_get *)
      unfold incr_cloc...
      apply rel_LS with
        (lst:=lst ++ firstn 3 SIlst)
        (SIlst:= tl (tl (tl SIlst)));inversion H11...
      * pose proof term_trans_not_nil as NN. specialize NN with
        (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=nth i lst0 L.ns :: E1) (t:=t1').
      * apply rel_env_context with (s_out:=s_out)...
        rewrite <- map_nth with (d:=L.ns)...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 tl,
          [x1;x2;x3] ++ tl = x1::x2::x3::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
      * destruct t1';inversion H17...
  - (* x = v1[i] <- v2 *)
    destruct L as [L_str].
    exists ((L_out,
              stack (val_direct_trans v' cur_stk_val :: cur_stk_val))
              :: H_stack,
             hloc_str L_str !->t
               tuple (update_nth 0 (List.map run_cst_trans [c])
               (val_direct_trans v' cur_stk_val)); SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 4 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (nat_reg 0,o0);
        (nat_reg 1,val_direct_trans v' cur_stk_val);
        (nat_reg 2,loc_w (hloc L_str 0))] ++ R36). split.
    (* stepping salt code for storing to heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v' cur_stk_val);
               (nat_reg 2,o2)] ++ R36)).
      { destruct v' as [cst|[ind|str]].
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11... apply nth_middle.
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=1) (s:=sp) (off:=ind)
            (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          destruct SH_conts. apply Ins...
          + inversion H11. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v' cur_stk_val);
               (nat_reg 2,loc_w (hloc L_str 0))] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=2) (o:=loc_w (hloc L_str 0))
            (R:=[(ip,loc_w (next_cloc l));(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);
                 (nat_reg 1,val_direct_trans v' cur_stk_val);
                 (nat_reg 2,o2)] ++ R36)...
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=2) (s:=sp) (off:=ind) (l:=next_cloc l)
            (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);
                 (nat_reg 1,val_direct_trans v' cur_stk_val);
                 (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (hloc L_str 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H8... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H17... inversion H6...
            inversion H4... }
          destruct SH_conts. rewrite Temp. apply Ins...
          + inversion H11. rewrite H15... apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - inversion H5... }
      apply multi_step with
        (y:=((cur_stkh,
               hloc_str L_str !->t
                 tuple (update_nth 0 (List.map run_cst_trans [c])
                          (val_direct_trans v' cur_stk_val));
              SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v' cur_stk_val);
               (nat_reg 2,loc_w (hloc L_str 0))] ++ R36)).
      { apply S_store with
          (d:=2) (o:=reg_o 1) (j:=0) (L:=hloc_str L_str)
          (lst:=List.map run_cst_trans [c])
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);
               (nat_reg 1,val_direct_trans v' cur_stk_val);
               (nat_reg 2,loc_w (hloc L_str 0))] ++ R36)...
        - rewrite H15. inversion H19... inversion H11.
          apply ins_verify with (n:=2).
        - inversion H13... inversion H2...
          apply H1 with (vs:=[c])... }
      constructor.
      apply S_push with
        (o:=reg_o (nat_reg 1)) 
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v' cur_stk_val);
             (nat_reg 2,loc_w (hloc L_str 0))] ++ R36)...
      rewrite H15. inversion H11. apply ins_verify with (n:=3).
    + (* prove LS_rel for assignment *)
      unfold incr_cloc...
      apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst)
        (SIlst:= tl(tl (tl (tl SIlst))));inversion H11...
      * pose proof term_trans_not_nil as NN. specialize NN with
        (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_tm with (E:=L.var_deref E1 v' :: E1) (t:=t1').
      * apply rel_env_context with (s_out:=s_out)...
        destruct v'... destruct v0...
        rewrite <- map_nth with (d:=L.ns).
        rewrite app_nth1... inversion H17...
        inversion H4... rewrite map_length. inversion H9...
      * unfold th_update,L.th_update,L.h_eqb,h_eqb.
        inversion H19...
        intros. destruct (String.eqb L_str L_tup)...
        -- inversion H1... destruct v' as [|[|]]...
           rewrite <- map_nth with (d:=L.ns)...
           rewrite app_nth1... inversion H17... inversion H6...
           rewrite List.map_length... inversion H10...
        -- inversion H13... inversion H3...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
          [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
      * destruct t1';inversion H17...
          
  - (* x = v(v') *)
    destruct lab as [lab].
    exists ((L_out,stack ((val_direct_trans v' cur_stk_val)::
                            (loc_w (incr_cloc 3 l)) :: cur_stk_val))
                :: H_stack,SH_tup,SH_conts),
         ([(ip,loc_w (cloc lab 1));
           (sp,loc_w (hloc L_out (2 + (List.length cur_stk_val))));
           (nat_reg 0,loc_w (cloc lab 0));
           (nat_reg 1,val_direct_trans v' cur_stk_val);
           (nat_reg 2,o2)] ++ R36). split.
    + apply multi_step with
        (y:=(cur_stkh,SH_tup,SH_conts,
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,loc_w (cloc lab 0));
               (nat_reg 1,o1);(nat_reg 2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=0) (o:=loc_w (cloc lab 0))
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11... inversion H7...
          apply nth_middle.
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=0) (s:=sp) (off:=ind)
            (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,o0);(nat_reg 1,o1);
                 (nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (cloc lab 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H7... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H17... inversion H6... inversion H9... }
          destruct SH_conts. rewrite Temp. apply Ins...
          + inversion H11. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - inversion H7... }
      apply multi_step with
        (y:=(cur_stkh,SH_tup,SH_conts,
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,loc_w (cloc lab 0));
               (nat_reg 1,val_direct_trans v' cur_stk_val);
               (nat_reg 2,o2)] ++ R36)).
      { destruct v' as [cst|[ind|str]].
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,loc_w (cloc lab 0));
                 (nat_reg 1,o1);(nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11... inversion H7...
          apply ins_verify with (n:=1).
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=1) (s:=sp) (off:=ind)
            (L:=L_out) (sign:=false)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,loc_w (cloc lab 0));
                 (nat_reg 1,o1);(nat_reg 2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          destruct SH_conts. apply Ins...
          + inversion H11. rewrite H15... apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (nat_reg 0,loc_w (cloc lab 0));
                 (nat_reg 1,o1);(nat_reg 2,o2)] ++ R36)...
          rewrite H15. inversion H11... inversion H7...
          apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((L_out, stack (loc_w (incr_cloc 3 l) :: cur_stk_val)) :: H_stack,
           SH_tup, SH_conts,
           [(ip,loc_w (cloc lab 0));
            (sp,loc_w (hloc L_out (1 + List.length cur_stk_val)));
            (nat_reg 0,loc_w (cloc lab 0));
            (nat_reg 1,val_direct_trans v' cur_stk_val);
            (nat_reg 2,o2)] ++ R36)).
      { apply S_call with
        (o:=reg_o (nat_reg 0))
        (R:=[(ip,loc_w (incr_cloc 2 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,loc_w (cloc lab 0));
             (nat_reg 1,val_direct_trans v' cur_stk_val);
             (nat_reg 2,o2)] ++ R36)...
        rewrite H15. inversion H11...
        apply ins_verify with (n:=2). }
      constructor.
      apply S_push with
        (o:=reg_o (nat_reg 1)) (lst:=loc_w (incr_cloc 3 l) :: cur_stk_val)
        (l:=cloc lab 0)
        (R:=[(ip,loc_w (cloc lab 0));
             (sp,loc_w (hloc L_out (1 + (List.length cur_stk_val))));
             (nat_reg 0,loc_w (cloc lab 0));
             (nat_reg 1,val_direct_trans v' cur_stk_val);
             (nat_reg 2,o2)] ++ R36)...
      inversion H14;super_a;rewrite H19...
    + (* prove LS_rel for v(v') *)
      unfold incr_cloc,next_cloc... destruct (SC lab) as [newIns].
      apply rel_LS with
        (lst:=[push (reg_o 1)]) (SIlst:=func_term_trans 1 t1');
        inversion H11;automate.
      * apply rel_env_context with
          (s_out:=loc_w (cloc Clab (3 + (Datatypes.length lst)))
                    :: List.map run_cst_trans E1 ++ s_out).
        { inversion H5...
          - intros. inversion H1...
            assert (Temp:stk_points_to s_out s' L').
            { apply H2 with (L:=L) (H':=H')... }
            unfold stk_points_to in Temp.
            unfold stk_points_to. rewrite <- Temp.
            rewrite app_comm_cons. rewrite rev_app_distr.
            apply nth_error_app1. apply nth_error_Some.
            rewrite Temp. unfold not. intros...
          - inversion H3... rewrite app_comm_cons.
            apply rel_hdl_stk_lst... rewrite app_comm_cons.
            inversion H16...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk_base with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=SC)
                (lst:=lst ++ [val_trans 0 v;val_trans 1 v';
                              call (reg_o 0)])
                (Ilst:=push (reg_o 1) :: func_term_trans (S (List.length E1)) t)...
              rewrite H15. cbn. pose proof term_trans_not_nil as NN.
              specialize NN with (tm:=t).
              destruct (term_trans t) as []eqn:?;automate.
              rewrite <- Heql. unfold func_term_trans.
              rewrite <- PeanoNat.Nat.add_succ_comm.
              rewrite <- app_assoc...
              rewrite app_length... rewrite PeanoNat.Nat.add_comm...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=SC)
                (lst:=lst ++ [val_trans 0 v;val_trans 1 v';
                              call (reg_o 0)])
                (Ilst:=push (reg_o 1) :: func_term_trans (S (List.length E1)) t)...
              rewrite H15. cbn. pose proof term_trans_not_nil as NN.
              specialize NN with (tm:=t).
              destruct (term_trans t) as []eqn:?;automate.
              rewrite <- Heql. unfold func_term_trans.
              rewrite <- PeanoNat.Nat.add_succ_comm.
              rewrite <- app_assoc...
              rewrite app_length... rewrite PeanoNat.Nat.add_comm... }
        destruct v' as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        inversion H17... rewrite List.map_length... inversion H4...
        assert (Temp:wf_val (Datatypes.length E1) (var_val ind)).
        { apply H3... } inversion Temp...           
      * inversion H14... rewrite H19...
      * inversion H14... specialize H2 with (c_lab lab).
        unfold wf_func_tm in H2. rewrite H19 in H2.
        inversion H2... 
  - (* v end, return from function call *)
    (* move result to r1, chop stack via sfree
       (sp's label and Lsp changes accordingly)
     then return (ip changes, stack further chops *)
    exists ((L_out,stack (val_direct_trans v cur_stk_val :: (tl s_out)))
              :: H_stack,SH_tup,SH_conts),
    ([(ip,nth 0 s_out ns);
      (sp,loc_w (hloc L_out (List.length s_out))); (*remove l_dst, add v*)
      (nat_reg 0,o0);
      (nat_reg 1,val_direct_trans v cur_stk_val);(nat_reg 2,o2)] ++ R36).
    split.
    apply multi_step with
      (y:=((cur_stkh,SH_tup,SH_conts),
            [(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v cur_stk_val);
             (nat_reg 2,o2)] ++ R36)).
    { destruct v as [cst|[ind|str]].
      - apply S_mov with
          (d:=1) (o:=val_direct_trans (const_val cst) cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,o1);
               (nat_reg 2,o2)] ++ R36)...
        inversion H11... rewrite H15... apply nth_middle.
      - pose proof S_load_stk as Ins. specialize Ins with
          (d:=1) (s:=sp) (off:=ind)
          (L:=L_out) (sign:=false)
          (lst:=cur_stk_val) (i:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,o1);
               (nat_reg 2,o2)] ++ R36).
        rewrite PeanoNat.Nat.sub_diag in Ins.
        destruct SH_conts. apply Ins...
        + inversion H11. rewrite H15... apply nth_middle.
        + rewrite h_eqb_refl...
      - apply S_mov with
          (d:=1) (o:=val_direct_trans (var_val str) cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (nat_reg 0,o0);(nat_reg 1,o1);
               (nat_reg 2,o2)] ++ R36)...
        inversion H11... rewrite H15... apply nth_middle. }
    apply multi_step with
      (y:=((L_out,stack s_out) :: H_stack,SH_tup,SH_conts,
            [(ip,loc_w (incr_cloc 2 l));
             (sp,loc_w (hloc L_out (List.length s_out)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v cur_stk_val);
             (nat_reg 2,o2)] ++ R36)).
    { lemma on cdr_nth
      assert (cdr_nth (Datatypes.length E1) cur_stk_val) =  s_out.
      assert ((List.length - Datatypes.length E1) = length s_out
      apply S_sfree with
        (n:=List.length E1)
        (R:=[(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (nat_reg 0,o0);
             (nat_reg 1,val_direct_trans v cur_stk_val);
             (nat_reg 2,o2)] ++ R36)...

    4: { destruct (List.length l0). apply PeanoNat.Nat.lt_irrefl in H19;
         destruct H19. 
   

(*other things
0. changes in lexi heaps e.g. assignment
1. handler related stuff
2. relating data heap
3. relating hdl-led-ctx*)

Qed.


(*
All changes made
malloc rule's register should be r_d in resulting state
newref's translation s hould be malloc r2 n rather than i

simplifications can be done:
sfree after function call is just size of environment,
      no need to compute numlet
*)




