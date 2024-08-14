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


Theorem cond1 : forall C1 C2 M1 M2,
    code_mem_trans C1 = C2 -> init_L C1 M1 ->
    init_S C2 M2 -> LS_rel M1 M2.
Proof with super_a.
  intros. destruct M1 as [[[[LC LH] LK] LE] Lt], M2 as [[SC SH] SR].
  inversion H1... inversion H0...
  apply rel_LS with
    (SIlst:=func_term_trans 0 L_init_tm)
    (lst:=[])...
  - intros. destruct H...
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
    unfold c_comp,L.c_comp,code_mem_trans...
    destruct (L_init_func str)... 
  - intros. unfold L.c_comp.
    destruct (L_init_func x) as []eqn:?...
    unfold L_init_func in Heqf.
    unfold L.c_update in Heqf.
    destruct (L.c_eqb exit_lab x).
    + inversion Heqf...
    + destruct (L.c_eqb init_lab x).
      * inversion Heqf... intros. destruct H...
      * inversion Heqf...
        (*- repeat apply_fresh lc_bind...*)
Qed.

Theorem cond2 : forall M1 M2 i,
    LS_rel M1 M2 -> final_L M1 i -> final_S M2 i.
Proof with automate.
  intros. destruct M1 as [[[[LC LH] LK] LE] Lt], M2 as [[SC SH] SR].
  inversion H0... inversion H... inversion H10...
  cbn. rewrite H13. inversion H8... apply nth_middle.
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
    nth (n + List.length l) (l ++ l') d = nth n l' d.
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

(*Lemma push1_before_tm : forall ft lst Ilst E t,
          wf_func_tm ft ->
          func_trans ft = ins_seq (lst ++ Ilst) ->
          LS_rel_ins (E,t) (ins_seq (tl Ilst)) ->
          nth 0 Ilst ns_ins = push (reg_o 1).
Proof with super_a.
  intros. 

  Lemma update_nth_map: forall {A B:Type} ind (f:A->B) lst v,
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
    remember [(r3,o3);(r4,o4);(r5,o5);
              (r6,o6)] as R36.
  (* 14 stepping rules, prove the multi and rel for each *)
  - (* x = v1 + v2 *) exists
      ((L_out,stack ((int_w (i1+i2)) :: cur_stk_val))
         :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 4 l));(sp,loc_w (hloc L_out
                                                (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,int_w (i1+i2));(r2,int_w i2)]
         ++ R36). split.
    (* stepping translated salt code for addition *)
    + apply multi_step with (*y is 1 step after current*)
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,int_w i1);
               (r2,o2)] ++ R36)).
      { apply S_mov with
          (d:=r1) (o:=i1)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36)...
        rewrite H15. inversion H10... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,int_w i1);
               (r2,int_w i2)] ++ R36)).
      { apply S_mov with
          (d:=r2) (o:=i2)
          (R:=[(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,int_w i1);
               (r2,o2)] ++ R36)...
        inversion H10. rewrite H15...
        apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,int_w (i1+i2));
               (r2,int_w i2)] ++ R36)).
      { apply S_add with
          (reg:=r1)
          (o:=r2)
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,int_w i1);
               (r2,int_w i2)] ++ R36)... rewrite H15. inversion H10...
        apply ins_verify with (n:=2). }
      constructor.
      apply S_push with
        (o:=r1)
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);(r1,int_w (i1+i2));
             (r2,int_w i2)] ++ R36)...
      rewrite H15. inversion H10... apply ins_verify with (n:=3).
    (* prove LS_rel for L_add *)
    + unfold incr_cloc,next_cloc... apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst)
        (SIlst:= tl (tl (tl (tl SIlst))));inversion H10...
      * pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). cbn. destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm...
        inversion H2...
      * apply rel_env_context with (s_out:=s_out)...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
                                  [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
  - (* x = v *) exists
      ((L_out,stack ((val_direct_trans v cur_stk_val) :: cur_stk_val))
         :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 2 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,val_direct_trans v cur_stk_val);
        (r2,o2)] ++ R36). split.
    + (* stepping translated salt code for single value *)
      apply multi_step with (*y is 1 step after current*)
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v cur_stk_val);
               (r2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with (d:=r1)
                           (o:=val_direct_trans (const_val cst) cur_stk_val)
                           (R:=[(ip,loc_w l);
                                (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                                (r0,o0);(r1,o1);
                                (r2,o2)] ++ R36)...
          inversion H10... rewrite H15... apply nth_middle.
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r1) (off:=ind)
            (L:=L_out)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
          inversion H10... rewrite H15... apply nth_middle. }
      constructor.
      apply S_push with
        (o:=r1)
        (R:=[(ip,loc_w (next_cloc l));
             (sp,loc_w(hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36)...
      rewrite H15. inversion H10...
      apply ins_verify with (n:=1).
    + (* prove LS_rel for x=v *)
      rewrite Heql. rewrite HeqR36. apply rel_LS with
        (lst:=lst ++ firstn 2 SIlst) (SIlst:= tl (tl SIlst))...
      * inversion H10... pose proof term_trans_not_nil as NN.
        specialize NN with (tm:=t1'). destruct
          (RelConfig.LS.term_trans t1')as []eqn:?;automate. rewrite <- Heql.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_ins. inversion H2...
      * apply rel_env_context with (s_out:=s_out)...
        destruct v as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        rewrite map_length.
        inversion H10... inversion H2...
        inversion H6... inversion H3...
      * rewrite H15. destruct SIlst... destruct SIlst...
        rewrite <- app_assoc. assert (AssocIns: forall (x1:instr) x2 tl,
                                         [x1;x2] ++ tl = x1::x2::tl). { intros... }
        rewrite <- AssocIns...
      * destruct SIlst... destruct SIlst...
        rewrite app_length. rewrite PeanoNat.Nat.add_comm... 
  - (* x = newref<v> *)
    destruct L as [L_str].
    exists ((L_out,
              stack (loc_w (hloc L_str 0) :: cur_stk_val)) :: H_stack,
             hloc_str L_str !->t
               tuple ([val_direct_trans v cur_stk_val]); SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 4 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,loc_w (hloc L_str 0));
        (r2,val_direct_trans v cur_stk_val)]
         ++ R36). split.
    (* stepping salt code for newref *)
    + apply multi_step with
        (y:=((cur_stkh,
               hloc_str L_str !->t
                 tuple ([ns]);SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,o2)] ++ R36)).
      { apply S_malloc with
          (i:=1) (d:=r1)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,o1);(r2,o2)] ++ R36)...
        - rewrite H15. inversion H10... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,
               hloc_str L_str !->t
                 tuple ([ns]);SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,val_direct_trans v cur_stk_val)]
                ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=r2) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,loc_w (hloc L_str 0));
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10...
          apply ins_verify with (n:=1).
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r2) (off:=ind)
            (L:=L_out)
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,loc_w (hloc L_str 0));
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=r2) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,loc_w (hloc L_str 0));
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10... apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((cur_stkh,
               hloc_str L_str !->t
                 tuple ([val_direct_trans v cur_stk_val]);SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,val_direct_trans v cur_stk_val)]
                ++ R36)).
      { pose proof S_store as Ins. specialize Ins with
          (d:=r1) (o:=reg_o r2) (j:=0) (L:=hloc_str L_str)
          (H_tup:= L_str !->t tuple [ns]; SH_tup) (lst:=[ns])
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,val_direct_trans v cur_stk_val)] ++ R36).
        rewrite heap_front_update in Ins. apply Ins...
        - rewrite H15. inversion H10.
          apply ins_verify with (n:=2).
        - unfold th_update. rewrite h_eqb_refl... }
      constructor.
      apply S_push with
        (o:=r1)
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,loc_w (hloc L_str 0));
             (r2,val_direct_trans v cur_stk_val)] ++ R36)...
      rewrite H15. inversion H10... apply ins_verify with (n:=3).
    + (* Prove LS_rel for newref *)
      unfold incr_cloc,next_cloc... apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst)
        (SIlst:= tl (tl (tl (tl SIlst))));inversion H10;automate.
      * pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). cbn. destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_ins. inversion H10... inversion H3...
      * apply rel_env_context with (s_out:=s_out)...
      * unfold th_update,L.th_update,L.h_eqb,h_eqb.
        intros. destruct (String.eqb L_str L_tup)...
        -- inversion H1... destruct v as [|[|]]...
           rewrite <- map_nth with (d:=L.ns)...
           rewrite app_nth1... inversion H2...
           inversion H8...
           specialize H6 with (v:=L.var_val n).
           assert (Temp:In (L.var_val n) [L.var_val (L.dbjind_var n)]).
           { super_a. } apply H6 in Temp. inversion Temp...
           rewrite List.map_length...
        -- inversion H13... inversion H6...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
                                  [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
  - (* x = pi_i(v)*)
    destruct L as [L_str].
    exists ((L_out,
              stack ((nth i (List.map run_cst_trans lst0) ns) :: cur_stk_val))
              :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (incr_cloc 3 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,nth i (List.map run_cst_trans lst0) ns);
        (r2,o2)] ++ R36). split.
    (* stepping salt code for loading from heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v cur_stk_val);
               (r2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (const_val cst) cur_stk_val) (l:=l)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r1) (off:=ind) (L:=L_out) 
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins. 
          apply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)... }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,nth i (List.map run_cst_trans lst0) ns);
               (r2,o2)] ++ R36)).
      { apply S_load_tup with
          (d:=r1) (s:=r1) (off:=i)
          (L:=L_str) (lst:=(List.map run_cst_trans lst0)) 
          (R:=[(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v cur_stk_val);
               (r2,o2)] ++ R36)...
        - rewrite H15. inversion H10...
          apply ins_verify with (n:=1).
        - destruct v as [cst|[ind|str]]...
          inversion H4... rewrite app_nth1.
          rewrite map_nth with (d:=L.ns).
          rewrite H2... rewrite map_length.
          inversion H10... inversion H3... inversion H8...
          inversion H6...
        - inversion H13... inversion H2... }
      constructor. 
      apply S_push with
        (o:=r1) 
        (R:=[(ip,loc_w (incr_cloc 2 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,nth i (List.map run_cst_trans lst0) ns);
             (r2,o2)] ++ R36)...
      rewrite H15. inversion H10. apply ins_verify with (n:=2).
    + (* prove LS_rel for L_get *)
      unfold incr_cloc...
      apply rel_LS with
        (lst:=lst ++ firstn 3 SIlst)
        (SIlst:= tl (tl (tl SIlst)));inversion H10...
      * pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_ins. inversion H2...
      * apply rel_env_context with (s_out:=s_out)...
        rewrite <- map_nth with (d:=L.ns)...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 tl,
                                  [x1;x2;x3] ++ tl = x1::x2::x3::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
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
        (r0,o0);
        (r1,val_direct_trans v' cur_stk_val);
        (r2,loc_w (hloc L_str 0))] ++ R36). split.
    (* stepping salt code for storing to heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,o2)] ++ R36)).
      { destruct v' as [cst|[ind|str]].
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10... apply nth_middle.
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r1) (off:=ind)
            (L:=L_out) 
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,SH_tup,SH_conts),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,loc_w (hloc L_str 0))] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=r2) (o:=loc_w (hloc L_str 0))
            (R:=[(ip,loc_w (next_cloc l));(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,val_direct_trans v' cur_stk_val);
                 (r2,o2)] ++ R36)...
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r2) (off:=ind) (l:=next_cloc l)
            (L:=L_out) 
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,val_direct_trans v' cur_stk_val);
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (hloc L_str 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H8... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H10... inversion H3...
            inversion H7... inversion H6... }
          rewrite Temp. apply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
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
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,loc_w (hloc L_str 0))] ++ R36)).
      { apply S_store with
          (d:=r2) (o:=r1) (j:=0) (L:=hloc_str L_str)
          (lst:=List.map run_cst_trans [c])
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,loc_w (hloc L_str 0))] ++ R36)...
        - rewrite H15. inversion H18... inversion H10.
          apply ins_verify with (n:=2).
        - inversion H13... inversion H2...
          apply H1 with (vs:=[c])... }
      constructor.
      apply S_push with
        (o:=r1) 
        (R:=[(ip,loc_w (incr_cloc 3 l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,val_direct_trans v' cur_stk_val);
             (r2,loc_w (hloc L_str 0))] ++ R36)...
      rewrite H15. inversion H10. apply ins_verify with (n:=3).
    + (* prove LS_rel for assignment *)
      unfold incr_cloc...
      apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst)
        (SIlst:= tl(tl (tl (tl SIlst))));inversion H10...
      * pose proof term_trans_not_nil as NN. specialize NN with
          (tm:=t1'). destruct (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql. rewrite <- PeanoNat.Nat.add_succ_comm.
        apply rel_ins. inversion H2...
      * apply rel_env_context with (s_out:=s_out)...
        destruct v'... destruct v0...
        rewrite <- map_nth with (d:=L.ns).
        rewrite app_nth1... rewrite map_length.
        inversion H2... inversion H6...
        inversion H11...
      * unfold th_update,L.th_update,L.h_eqb,h_eqb.
        inversion H18...
        intros. destruct (String.eqb L_str L_tup)...
        -- inversion H1... destruct v' as [|[|]]...
           rewrite <- map_nth with (d:=L.ns)...
           rewrite app_nth1... inversion H2... inversion H7...
           rewrite List.map_length... inversion H16...
        -- inversion H13... inversion H4...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
                                  [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl). { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length. rewrite PeanoNat.Nat.add_comm...
  - (* x = v(v') *)
    destruct lab as [lab].
    exists ((L_out,stack ((val_direct_trans v' cur_stk_val)::
                            (loc_w (incr_cloc 3 l)) :: cur_stk_val))
              :: H_stack,SH_tup,SH_conts),
      ([(ip,loc_w (cloc lab 1));
        (sp,loc_w (hloc L_out (2 + (List.length cur_stk_val))));
        (r0,loc_w (cloc lab 0));
        (r1,val_direct_trans v' cur_stk_val);
        (r2,o2)] ++ R36). split.
    + apply multi_step with
        (y:=(cur_stkh,SH_tup,SH_conts,
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,loc_w (cloc lab 0));
               (r1,o1);(r2,o2)] ++ R36)).
      { destruct v as [cst|[ind|str]].
        - apply S_mov with
            (d:=r0) (o:=loc_w (cloc lab 0))
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10... inversion H7...
          apply nth_middle.
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r0) (off:=ind)
            (L:=L_out) 
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (cloc lab 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H7... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H10... inversion H3... inversion H8...
            inversion H11... }
          rewrite Temp. apply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
          + rewrite h_eqb_refl...
        - inversion H7... }
      apply multi_step with
        (y:=(cur_stkh,SH_tup,SH_conts,
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,loc_w (cloc lab 0));
               (r1,val_direct_trans v' cur_stk_val);
               (r2,o2)] ++ R36)).
      { destruct v' as [cst|[ind|str]].
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (const_val cst) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,loc_w (cloc lab 0));
                 (r1,o1);(r2,o2)] ++ R36)...
          rewrite H15. inversion H10... inversion H7...
          apply ins_verify with (n:=1).
        - pose proof S_load_sp as Ins. specialize Ins with
            (d:=r1) (off:=ind)
            (L:=L_out) 
            (lst:=cur_stk_val) (i:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,loc_w (cloc lab 0));
                 (r1,o1);(r2,o2)] ++ R36).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          apply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,loc_w (cloc lab 0));
                 (r1,o1);(r2,o2)] ++ R36)...
          rewrite H15. inversion H10... inversion H7...
          apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((L_out, stack (loc_w (incr_cloc 3 l) :: cur_stk_val)) :: H_stack,
              SH_tup, SH_conts,
              [(ip,loc_w (cloc lab 0));
               (sp,loc_w (hloc L_out (1 + List.length cur_stk_val)));
               (r0,loc_w (cloc lab 0));
               (r1,val_direct_trans v' cur_stk_val);
               (r2,o2)] ++ R36)).
      { apply S_call with
          (o:=r0)
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,loc_w (cloc lab 0));
               (r1,val_direct_trans v' cur_stk_val);
               (r2,o2)] ++ R36)...
        rewrite H15. inversion H10...
        apply ins_verify with (n:=2). }
      constructor.
      apply S_push with
        (o:=r1) (lst:=loc_w (incr_cloc 3 l) :: cur_stk_val)
        (l:=cloc lab 0)
        (R:=[(ip,loc_w (cloc lab 0));
             (sp,loc_w (hloc L_out (1 + (List.length cur_stk_val))));
             (r0,loc_w (cloc lab 0));
             (r1,val_direct_trans v' cur_stk_val);
             (r2,o2)] ++ R36)...
      inversion H14... inversion H18.
      apply H3 in H18. unfold c_comp.
      rewrite H18... rewrite H4...
    + (* prove LS_rel for v(v') *)
      unfold incr_cloc,next_cloc... destruct (SC0 lab) as [newIns|]eqn:?.
      apply rel_LS with
        (lst:=[push r1]) (SIlst:=func_term_trans 1 t1');
        inversion H10;automate.
      * inversion H14... specialize H3 with (c_lab lab).
        rewrite H18 in H3. inversion H3... 
      * apply rel_env_context with
          (s_out:=loc_w (cloc Clab (3 + (List.length lst)))
                    :: List.map run_cst_trans E1 ++ s_out).
        { inversion H5...
          - intros. inversion H1...
            assert (Temp:stk_points_to s_out s' L').
            { apply H3 with (L:=L) (H':=H')... }
            unfold stk_points_to in Temp.
            unfold stk_points_to. rewrite <- Temp.
            rewrite app_comm_cons. rewrite rev_app_distr.
            apply nth_error_app1. apply nth_error_Some.
            rewrite Temp. unfold not. intros...
          - inversion H4... rewrite app_comm_cons.
            apply rel_hdl_stk_lst... rewrite app_comm_cons.
            inversion H17...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk_base with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=c_comp S_builtin_ins SC0)
                (lst:=lst ++ [val_trans r0 v;val_trans r1 v';
                              call r0])
                (Ilst:=push r1 :: func_term_trans (S (List.length E1)) t)...
              * inversion H2...
              * rewrite H15. cbn. pose proof term_trans_not_nil as NN.
                specialize NN with (tm:=t).
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql. unfold func_term_trans.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                rewrite <- app_assoc...
              * rewrite app_length... rewrite PeanoNat.Nat.add_comm...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=c_comp S_builtin_ins SC0)
                (lst:=lst ++ [val_trans r0 v;val_trans r1 v';
                              call r0])
                (Ilst:=push r1 :: func_term_trans (S (List.length E1)) t)...
              * inversion H2...
              * rewrite H15. cbn. pose proof term_trans_not_nil as NN.
                specialize NN with (tm:=t).
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql. unfold func_term_trans.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                rewrite <- app_assoc...
              * rewrite app_length... rewrite PeanoNat.Nat.add_comm... }
        destruct v' as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        inversion H2... rewrite List.map_length...
        inversion H6...
        specialize H4 with (v':=L.var_val ind).
        assert (Temp:In (L.var_val ind) [L.var_val (L.dbjind_var ind)]).
        { super_a. } apply H4 in Temp. inversion Temp...
      * inversion H14... inversion H18.
        apply H4 in H6. unfold c_comp.
        rewrite H6. unfold code_mem_trans.
        rewrite H18...
      * inversion H14... unfold code_mem_trans in Heqi.
        rewrite H18 in Heqi...
  - (* v end, return from function call *)
    (* move result to r1, chop stack via sfree
       (sp's label and Lsp changes accordingly)
     then return (ip changes, stack further chops *)
    exists ((L_out,stack (val_direct_trans v cur_stk_val :: (tl s_out)))
              :: H_stack,SH_tup,SH_conts),
      ([(ip,match nth 0 s_out ns with
            | cloc Clab n => cloc Clab (S n)
            | _ => ns_cloc end);
        (sp,loc_w (hloc L_out (List.length s_out))); (*remove l_dst, add v*)
        (r0,o0);
        (r1,val_direct_trans v cur_stk_val);(r2,o2)] ++ R36).
    split.
    apply multi_step with
      (y:=((cur_stkh,SH_tup,SH_conts),
            [(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36)).
    { destruct v as [cst|[ind|str]].
      - apply S_mov with
          (d:=r1) (o:=val_direct_trans (const_val cst) cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36)...
        inversion H10... rewrite H15... apply nth_middle.
      - pose proof S_load_sp as Ins. specialize Ins with
          (d:=r1) (off:=ind)
          (L:=L_out)
          (lst:=cur_stk_val) (i:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36).
        rewrite PeanoNat.Nat.sub_diag in Ins.
        apply Ins...
        + inversion H10. rewrite H15... apply nth_middle.
        + rewrite h_eqb_refl...
      - apply S_mov with
          (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36)...
        inversion H10... rewrite H15... apply nth_middle. }
    apply multi_step with
      (y:=((L_out,stack s_out) :: H_stack,SH_tup,SH_conts,
            [(ip,loc_w (incr_cloc 2 l));
             (sp,loc_w (hloc L_out (List.length s_out)));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36)).
    { assert (Temp:skipn (List.length E1) cur_stk_val = s_out).
      { cbn... rewrite skipn_app, skipn_map, skipn_all...
        rewrite map_length, PeanoNat.Nat.sub_diag... }
      assert (Temp2:List.length cur_stk_val - List.length E1 = List.length s_out).
      { cbn... rewrite app_length, PeanoNat.Nat.add_comm,
          map_length. apply PeanoNat.Nat.add_sub. }
       pose proof S_sfree as Hyp. specialize Hyp with
        (n:=List.length E1) (lst:=cur_stk_val)
        (R:=[(ip,loc_w (next_cloc l));
             (sp,loc_w (hloc L_out (List.length cur_stk_val)));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36).
      rewrite Temp in Hyp. rewrite <- Temp2.
      apply Hyp...
      - rewrite H15. inversion H10...
        destruct v as [cst|[ind|str]];
          rewrite PeanoNat.Nat.add_comm;
          apply ins_verify with (n:=1).
      - rewrite app_length, PeanoNat.Nat.add_comm.
        destruct s_out;rewrite map_length...
        apply PeanoNat.Nat.le_add_l. }
    
    apply multi_step with
      (y:=((L_out,stack (tl s_out)) :: H_stack,SH_tup,SH_conts,
            [(ip,hd ns s_out);
             (sp,loc_w (hloc L_out (List.length (tl s_out))));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36)).
    { inversion H5... inversion H3...
      pose proof S_ret as Hyp. specialize Hyp with
        (l:=cloc Clab (2 + (List.length lst))).
      remember (fun (s_prev:list word) (lst0:list instr) C_lab =>
                   [(ip,loc_w (cloc Clab (2 + (List.length lst))));
                    (sp,loc_w (hloc L_out (S (List.length s_prev))));
                    (r0,o0);
                    (r1,
                      val_direct_trans v
                        (List.map run_cst_trans E1 ++
                           loc_w (cloc C_lab (List.length lst0)) :: s_prev));
                    (r2,o2);(r3,o3);
                    (r4,o4);(r5,o5);(r6,o6)])
        as newR.
      revert HeqnewR.
      inversion H11... 
      - inversion H1... inversion H16...
        remember ((s ++ s') ++ frm_stk) as s_prev.
        intros.
        specialize Hyp with
          (j:=S (List.length s_prev))
          (l':=cloc C_lab (List.length lst0))
          (R:=newR s_prev lst0 C_lab)...
        cbn in Hyp. rewrite PeanoNat.Nat.sub_0_r in Hyp.
        apply Hyp... rewrite H15. inversion H10...
        destruct v as [|[|]];rewrite PeanoNat.Nat.add_comm;
          apply ins_verify with (n:=2).
      - inversion H6... inversion H17...
        remember ((s ++ s') ++ frm_stk ++ slst) as s_prev.
        intros.
        specialize Hyp with
          (j:=S (List.length s_prev))
          (l':=cloc C_lab (List.length lst0))
          (R:=newR s_prev lst0 C_lab)...
        cbn in Hyp. rewrite PeanoNat.Nat.sub_0_r in Hyp.
        apply Hyp... rewrite H15. inversion H10...
        destruct v as [|[|]];rewrite PeanoNat.Nat.add_comm;
          apply ins_verify with (n:=2). }
    constructor.
    { pose proof S_push as Hyp. specialize Hyp with
        (o:=reg_o r1) (j:=List.length (tl s_out))
        (*l:=cloc C_lab (List.length lst0)*)
        (R:=[(ip,hd ns s_out);
             (sp,loc_w (hloc L_out (List.length (tl s_out))));
             (r0, o0);
             (r1, val_direct_trans v cur_stk_val);
             (r2, o2)] ++ R36).
      inversion H5... inversion H3... inversion H11...
      - inversion H1... inversion H16...
        specialize Hyp with (l:=cloc C_lab (List.length lst0)).
        cbn in Hyp. apply Hyp...
        rewrite H19.
        pose proof app_nth2_plus as Temp.
        specialize Temp with (l:=lst0) (l':=Ilst) (n:=0).
        rewrite PeanoNat.Nat.add_comm in Temp.
        rewrite Temp...
      - inversion H6... inversion H17...
        specialize Hyp with (l:=cloc C_lab (List.length lst0)).
        cbn in Hyp. apply Hyp...
        rewrite H20.
        pose proof app_nth2_plus as Temp.
        specialize Temp with (l:=lst0) (l':=Ilst) (n:=0).
        rewrite PeanoNat.Nat.add_comm in Temp.
        rewrite Temp... }
    + (* prove LS_rel for v end, end of function call *)
      unfold incr_cloc,next_cloc,ns_cloc...
      inversion H5... inversion H3...
      inversion H11...
      { inversion H1... inversion H16...
         inversion H4...
         apply rel_LS with
           (lst:=lst0 ++ [nth 0 Ilst halt])
           (SIlst:=tl Ilst)...
        - inversion H17...
        - apply rel_env_context with
            (s_out:=s' ++ frm_stk)...
          + intros. inversion H9...
            assert (stk_points_to
                      (loc_w (cloc C_lab (List.length lst0))
                         :: s ++ s' ++ frm_stk)
                      s'0 L').
            { apply H2 with (L:=L) (H':=H').
              repeat (rewrite <- app_assoc)... }
            unfold stk_points_to. unfold stk_points_to in H20.
            rewrite <- H20. rewrite app_comm_cons.
            rewrite rev_app_distr with (y:=s'++frm_stk).
            rewrite nth_error_app1...
            rewrite rev_length. rewrite app_length.
            rewrite PeanoNat.Nat.add_comm.
            inversion H6;cbn;apply PeanoNat.Nat.lt_add_pos_r with (m:=3);
              apply PeanoNat.Nat.lt_0_succ.
          + inversion H21... rewrite app_assoc. 
            destruct v as [cst|[ind|str]]...
            rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
            inversion H10... rewrite List.map_length... inversion H20...
            inversion H24...
        - rewrite H19... destruct Ilst... rewrite <- app_assoc...
        - rewrite H23, app_length, PeanoNat.Nat.add_comm... } 
      { inversion H6... inversion H17...
        inversion H4...
        apply rel_LS with
          (lst:=lst0 ++ [nth 0 Ilst halt])
          (SIlst:=tl Ilst)...
        - inversion H18...
        - apply rel_env_context with
            (s_out:=s' ++ frm_stk ++ slst)...
          + intros. inversion H16...
            assert (stk_points_to
                      (loc_w (cloc C_lab (List.length lst0))
                         :: s ++ s' ++ frm_stk ++ slst)
                      s'0 L').
            { apply H2 with (L:=L) (H':=H').
              repeat (rewrite <- app_assoc)... }
            unfold stk_points_to. unfold stk_points_to in H21.
            rewrite <- H21. rewrite app_comm_cons.
            rewrite rev_app_distr with (y:=s'++frm_stk++slst).
            rewrite nth_error_app1...
            rewrite rev_length. repeat (rewrite app_length).
            rewrite PeanoNat.Nat.add_comm.
            inversion H7;cbn;apply PeanoNat.Nat.lt_add_pos_r with (m:=3);
              apply PeanoNat.Nat.lt_0_succ.
          + inversion H22... repeat (rewrite app_assoc). 
            destruct v as [cst|[ind|str]]...
            rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
            inversion H10... rewrite List.map_length... inversion H21...
            inversion H25...
        - rewrite H20. destruct Ilst... rewrite <- app_assoc...
        - rewrite H24, app_length, PeanoNat.Nat.add_comm... }
  - (* handle P_body with A P_op under v_env in t*)
    destruct lab_op as [lab_op],lab_body as [lab_body],
          L as [L],(a_eqb general A) as [|]eqn:?.
    (* split cases for types of handlers *)
    *** assert (A = general). { destruct A... }
        exists
          ((hloc_str L,
             stack
               [val_direct_trans v_env cur_stk_val;
                loc_w (hloc L 4);loc_w (cloc handle_loc 10);
                loc_w (hloc L_out (S (List.length cur_stk_val)));
                int_w 0;
                val_direct_trans v_env cur_stk_val; 
                loc_w (cloc (cloc_str lab_op) 0)])
             :: (L_out, stack (loc_w (incr_cloc 5 l) :: cur_stk_val))
             :: H_stack, SH_tup, SH_conts),
          ([(ip,loc_w (cloc lab_body 2));
            (sp,loc_w (hloc L 7));(r0, o0);
            (r1,val_direct_trans v_env cur_stk_val);
            (r2,loc_w (hloc L 4));
            (r3,val_direct_trans v_env cur_stk_val);
            (r4,int_w 0);
            (r5,loc_w (hloc L_out (S (List.length cur_stk_val))));
            (r6,loc_w (cloc lab_body 0))]). split.
    + rewrite HeqR36. eapply multi_step.
      { eapply S_mov with (d:=r4) (o:=0)...
        inversion H10... rewrite H15...
        apply nth_middle. }
      eapply multi_step.
      { destruct v_env as [|[|]].
        - eapply S_mov with
            (d:=r3) (o:=val_direct_trans s cur_stk_val)...
        - pose proof S_load_sp as Temp.
          specialize Temp with
            (d:=r3) (off:=n) (lst:=cur_stk_val)
            (i:=List.length cur_stk_val).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          + rewrite H15. inversion H10...
            apply ins_verify with (n:=1).
          + rewrite h_eqb_refl...
        - eapply S_mov with
            (d:=r3) (o:=val_direct_trans (var_val v) cur_stk_val)... }
      eapply multi_step.
      { eapply S_mov with
          (d:=r2) (o:=wd_o (cloc lab_op 0))...
        inversion H10... rewrite H15...
        apply ins_verify with (n:=2). }
      eapply multi_step.
      { eapply S_mov with
          (d:=r1) (o:=wd_o (cloc lab_body 0))...
        inversion H10... rewrite H15...
        apply ins_verify with (n:=3). }
      eapply multi_step.
      { eapply S_call with
          (o:=wd_o (cloc handle_loc 0))...
        inversion H10... rewrite H15...
        apply ins_verify with (n:=4). }
      eapply multi_step.
      { eapply S_mov with
          (d:=r5) (o:=sp)... }
      eapply multi_step.
      { eapply S_mkstk with
          (reg:=sp) (L:=L)... }
      eapply multi_step.
      { eapply S_push with (o:=r2)... }
      eapply multi_step.
      { eapply S_push with (o:=r3)... }
      eapply multi_step.
      { eapply S_push with (o:=r4)... }
      eapply multi_step.
      { eapply S_push with (o:=r5)... }
      eapply multi_step.
      { eapply S_mov with
          (d:=r6) (o:=r1)... }
      eapply multi_step.
      { eapply S_mov with
          (d:=r2) (o:=sp)... }
      eapply multi_step.
      { eapply S_mov with
          (d:=r1) (o:=r3)... }
      eapply multi_step.
      { eapply S_call with (o:=r6)... }
      eapply multi_step.
      { eapply S_push with (o:=r2)...
        unfold c_comp. inversion H14...
        inversion H18... apply H3 in H4.
        rewrite H4,H18... }
      constructor.
      { cbn. repeat (rewrite <- Heqcur_stk_val).
        pose proof S_push as Temp.
        specialize Temp with
          (o:=reg_o r1) (l:=cloc lab_body 1)
          (lst:=[loc_w (hloc L 4);
                 loc_w (cloc handle_loc 10);
                 loc_w (hloc L_out (S (Datatypes.length cur_stk_val)));
                 int_w 0; val_direct_trans v_env cur_stk_val;
                 loc_w (cloc lab_op 0)])
          (R:=[(ip,loc_w (cloc lab_body 1));
               (sp,loc_w (hloc L 6)); (r0, o0);
               (r1,val_direct_trans v_env cur_stk_val);
               (r2,loc_w (hloc L 4));
               (r3,val_direct_trans v_env cur_stk_val);
               (r4,int_w 0);
               (r5,loc_w (hloc L_out (S (List.length cur_stk_val))));
               (r6,loc_w (cloc lab_body 0))]).
        cbn in Temp. apply Temp...
        unfold c_comp. inversion H14...
        inversion H18... apply H3 in H4.
        rewrite H4,H18... }
    + (* prove LS_rel for handler creation*)
      unfold incr_cloc,next_cloc... destruct (SC0 lab_body) as [newIns|]eqn:?.
      eapply rel_LS...
      * inversion H14... specialize H2 with (c_lab lab_body).
        rewrite H18 in H2. inversion H2... 
      * apply rel_env_context with
          (s_out:=
             [loc_w (cloc handle_loc 10);
              loc_w (hloc L_out
                       (S (List.length (List.map run_cst_trans E1 ++ s_out))));
              int_w 0; val_direct_trans v_env (List.map run_cst_trans E1 ++ s_out);
              loc_w (cloc lab_op 0)])...
        -- intros. inversion H1...
        -- inversion H5...


wrong here already







           apply rel_hdl_stk_lst with
             (K:=[L.h_f (L.handler_f (L.hdl_lab L)
                           L_env (L.c_lab lab_op) general)])...
           { inversion H3... rewrite app_comm_cons.
             apply rel_hdl_stk_lst... inversion H16;automate;
               repeat (rewrite app_comm_cons).
             - repeat (rewrite app_assoc).
               apply rel_hdl_stk_base... rewrite app_comm_cons.
               apply rel_frame_cons... apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               + pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H11...
               + rewrite H15...
                 rewrite <- app_assoc...
               + rewrite app_length...
                 rewrite PeanoNat.Nat.add_comm...
             - rewrite app_assoc with (m:=s). apply rel_hdl_stk...
               rewrite app_comm_cons.
               apply rel_frame_cons... apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               + pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H17...
               + rewrite H15...
                 rewrite <- app_assoc...
               + rewrite app_length...
                 rewrite PeanoNat.Nat.add_comm... }
           { apply rel_hdl_stk_base
               with (Flst:=[]) (s:=[])... destruct L_env.
             apply rel_hdl_general... rewrite app_comm_cons.
               apply rel_frame_cons... apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               + pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H11...
               + rewrite H15...
                 rewrite <- app_assoc...
               + rewrite app_length...
                 rewrite PeanoNat.Nat.add_comm...
             - rewrite app_assoc with (m:=s). apply rel_hdl_stk...
               rewrite app_comm_cons.
               apply rel_frame_cons... apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               + pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H17...
               + rewrite H15...
                 rewrite <- app_assoc...
               + rewrite app_length...
                 rewrite PeanoNat.Nat.add_comm... }





           
                 { inversion H5...
          - intros. inversion H1...
            assert (Temp:stk_points_to s_out s' L').
            { apply H3 with (L:=L) (H':=H')... }
            unfold stk_points_to in Temp.
            unfold stk_points_to. rewrite <- Temp.
            rewrite app_comm_cons. rewrite rev_app_distr.
            apply nth_error_app1. apply nth_error_Some.
            rewrite Temp. unfold not. intros...
          - inversion H4... rewrite app_comm_cons.
            apply rel_hdl_stk_lst... rewrite app_comm_cons.
            inversion H17...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk_base with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=c_comp S_builtin_ins SC0)
                (lst:=lst ++ [val_trans r0 v;val_trans r1 v';
                              call r0])
                (Ilst:=push r1 :: func_term_trans (S (List.length E1)) t)...
              * inversion H2...
              * rewrite H15. cbn. pose proof term_trans_not_nil as NN.
                specialize NN with (tm:=t).
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql. unfold func_term_trans.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                rewrite <- app_assoc...
              * rewrite app_length... rewrite PeanoNat.Nat.add_comm...
            + repeat (rewrite app_comm_cons).
              rewrite app_assoc.
              apply rel_hdl_stk with
                (frm:=frm) (frm_stk:=frm_stk)...
              rewrite app_comm_cons. constructor...
              apply rel_frame with
                (C_mem:=c_comp S_builtin_ins SC0)
                (lst:=lst ++ [val_trans r0 v;val_trans r1 v';
                              call r0])
                (Ilst:=push r1 :: func_term_trans (S (List.length E1)) t)...
              * inversion H2...
              * rewrite H15. cbn. pose proof term_trans_not_nil as NN.
                specialize NN with (tm:=t).
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql. unfold func_term_trans.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                rewrite <- app_assoc...
              * rewrite app_length... rewrite PeanoNat.Nat.add_comm... }
        destruct v' as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        inversion H2... rewrite List.map_length...
        inversion H6...
        specialize H4 with (v':=L.var_val ind).
        assert (Temp:In (L.var_val ind) [L.var_val (L.dbjind_var ind)]).
        { super_a. } apply H4 in Temp. inversion Temp...
      * inversion H14... inversion H18.
        apply H4 in H6. unfold c_comp.
        rewrite H6. unfold code_mem_trans.
        rewrite H18...
      * inversion H14... unfold code_mem_trans in Heqi.
        rewrite H18 in Heqi...
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
(* new changes after paper submitted
0. change definition of relating frames
1. passes parameter C_mem all the way down to frame relation
2. added well-formed ness for rel_ins rather than at LS_rel *)




