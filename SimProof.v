Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import PeanoNat.
Require Import Lia.
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
Definition multi :
  forall A : Type, Relation_Definitions.relation A ->
                   A -> A -> Prop :=
  Relation_Operators.clos_refl_trans_1n.
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
Lemma one_eval_ctx_rel :
  forall frm frm_lst C_mem L,
    (LS_rel_hdl L frm frm_lst
     /\ is_h_frm_general_hdl frm = true)
    <->
    LS_rel_eval_ctx C_mem [hdl_led_lst frm []]
      [(hloc_str L,stack frm_lst)].
Proof with super_a.
  intros. split.
  - intros.
    apply rel_eval_ctx_lst with
      (K:=hdl_led_lst frm [])...
    apply rel_hdl_stk_base with
      (Flst:=[]) (s:=[])...
  - intros. split;
      inversion H;subst;
      inversion H5;subst;
      inversion H7...
    inversion H3...
Qed.
Lemma length_ctx_stk :
  forall C_mem H K,
    LS_rel_eval_ctx C_mem K H ->
    List.length H <= List.length K.
Proof with super_a.
  intros C_mem H.
  induction H...
  intros. inversion H0;subst.
  apply IHlist in H4.
  apply le_n_S in H4.
  rewrite H4. cbn...
Qed.
Theorem cond1 : forall C1 C2 M1 M2,
    code_mem_trans C1 = C2 -> init_L C1 M1 ->
    init_S C2 M2 -> LS_rel M1 M2.
Proof with super_a.
  intros. destruct M2 as [[SC [SHs SH_t]] SR].
  remember SHs as SH_stk. revert HeqSH_stk.
  inversion H1... inversion H0... intros.
  pose proof rel_LS as Temp.
  specialize Temp with
    (SH_stack:=SHs)...
  eapply Temp...
  - intros. destruct H2...
  - econstructor.
    2:{ super_a. }
    apply one_eval_ctx_rel...
    apply rel_hdl_general with
      (s_prev:=[ns;ns;ns;ns]).    
  - intros... cbv in H2. injection H2. intros...
  - extensionality x. destruct x as [str]. 
    unfold c_comp,L.c_comp,
      code_mem_trans,S_init_ins,
      code_mem_trans...
    destruct (L_init_func str)... 
  - intros. unfold L.c_comp.
    destruct (L_init_func x) as []eqn:?...
    unfold L_init_func in Heqf.
    unfold L.c_update in Heqf.
    destruct (L.c_eqb exit_lab x).
    + inversion Heqf...
    + destruct (L.c_eqb init_lab x).
      * inversion Heqf... intros. destruct H2...
      * inversion Heqf...
        (*- repeat apply_fresh lc_bind...*)
Qed.

Theorem cond2 : forall M1 M2 i,
    LS_rel M1 M2 -> final_L M1 i -> final_S M2 i.
Proof with automate.
  intros. inversion H0...
  inversion H... inversion H8...
  cbn. rewrite H12. inversion H7...
  apply nth_middle.
Qed.

Definition un_tuple (tup:tuple_heap_val) : list word :=
  match tup with tuple lst => lst end.
Definition un_stack stk : list word :=
  match stk with
  | stack lst => lst
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

Lemma stk_points_to_preserves :
  forall s s' L' s_added,
    3 < List.length s ->
    stk_points_to s s' L' <->
    stk_points_to (s_added ++ s) s' L'.
Proof with super_a.
  unfold stk_points_to.
  intros. split;intros;
    rewrite <- H0;
    rewrite rev_app_distr with (y:=s);
    rewrite nth_error_app1;super_a;
    rewrite rev_length...    
Qed.
Check L_raise_past_stks.
(*Lemma last_eval_ctx_rel :
  forall s C_mem L L_env lab_op Ks H,
    LS_rel_eval_ctx C_mem
      (Ks ++ [h_f (handler_f (hdl_lab L)
                     (obj_lab L_env) lab_op general)])
      (H ++ [(hloc_str L,stack s)]) ->
    exists K',
      LS_rel_hdl_stk C_mem L
        (K' ++ [h_f (handler_f (hdl_lab L)
                       (obj_lab L_env) lab_op general)]) s.
Proof with super_a.
  intros. generalize dependent H.
  induction Ks.
  - intros. exists ([]:eval_context).
    destruct H.
    2:{ apply length_ctx_stk in H0.
        rewrite app_length in H0.
        rewrite Nat.add_comm in H0.
        cbn in H0... }
    inversion H0... inversion H5...
    rewrite app_nil_r in H1...
  - intros. inversion H0...
    inversion H5...
    inversion H7...
    + inversion H2...
      destruct H.
      { inversion H3...
        inversion H4...
        induction Ks... }
      inversion H3...
    + inversion H2...
      destruct H.
      * inversion H3...
        inversion H4...
        exists (a_f Fi :: Ks).
        cbn. rewrite <- H14,
          app_nil_r...
      * inversion H3...
        apply IHKs with
          (H:=(hloc_str L0, stack (s' ++ frm_stk)) :: H).
        rewrite <- H14.
        constructor...
        intros.
        rewrite stk_points_to_preserves with
          (s_added:=si). rewrite app_assoc.
        apply H6 with (H':=H')...
        rewrite app_length.
        inversion H8...       
Qed.
Lemma eval_ctx_app_split :
  forall C_mem H K1 K2 L L_env lab_op,
    LS_rel_eval_ctx C_mem
      (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)]
         ++ K2) H ->
    exists H_ld H_ed,
      LS_rel_eval_ctx C_mem
        (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)]) H_ld 
      /\ LS_rel_eval_ctx C_mem K2 H_ed
      /\ H = H_ld ++ H_ed.
Proof with super_a.
  intros. generalize dependent H.
  induction K1.
  { intros. inversion H0...
    inversion H4...
    inversion H... inversion H6...
    inversion H2...
    esplit. exists H1.
    split...
    apply rel_eval_ctx_lst with
      (K:=[h_f (handler_f (hdl_lab L)
                  (obj_lab L_env0) Clab_op general)])...
    cbn... }
  intros.
  cbn in IHK1.
  inversion H0...
  inversion H4...
  (* first chunk is
     general hdl led frames *)
  - inversion H...
    (*first frame is general hdl
      (activation frames empty)*)
    + inversion H6...
      inversion H2...
      destruct H1...
      { induction K1... }
      apply IHK1 in H3.
      destruct H3 as
        [H_ld' [H_ed [hyp1 [hyp2 hyp3]]]].
      esplit. exists H_ed.
      (*exists
        ((hloc_str L0,
          stack
            [loc_w (cloc handle_loc 10);
             loc_w (hloc L_prev (Datatypes.length s_prev));
             int_w 0; 
             loc_w (hloc L_env0 0);
             loc_w (cloc Clab_op 0)]) :: H_ld'),s,H_ed.*)
      split...
      * apply rel_eval_ctx_lst with
          (K:=[h_f (handler_f (hdl_lab L0) (obj_lab L_env0) Clab_op general)])
          (Ks:=K1 ++
                 [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)])...
        intros. apply H5 with (H':=H'++H_ed).
        rewrite hyp3,H3...
      * rewrite hyp3...
    (*first frame is activation frame
      (some activation frames following
      the general handler) *)
    + inversion H9... inversion H14...
      inversion H2...
      rewrite <- H15 in IHK1.
      assert (LS_rel_eval_ctx C_mem ((Flst0 ++ [h_f frm]) ++ Ks)
                ((hloc_str L0,stack (s' ++ frm_stk)) :: H1)).
      { super_a. intros. apply H5 in H8.
        rewrite <- app_assoc in H8.
        apply stk_points_to_preserves
          in H8...
        inversion H6;rewrite app_length... }
      apply IHK1 in H8.
      destruct H8 as [H_ld' [H_ed [hyp1 [hyp2 hyp3]]]].
      inversion hyp1...
      { destruct K1... }
      inversion hyp3...
      esplit. exists H_ed.
      (*inversion H17...
        inversion H22...
        exists
          sh_empty,(loc_w (cloc C_lab (Datatypes.length lst))
                      :: (run_cstlst_trans E) ++ s' ++ frm_stk),H_ed.
        rewrite <- app_assoc. *)
      rewrite <- app_assoc.
      split...
      * rewrite app_comm_cons.
        apply rel_eval_ctx_lst with
            (s:=loc_w (cloc C_lab (Datatypes.length lst))
                  :: (run_cstlst_trans E) ++ s' ++ frm_stk)...          
        -- inversion H18;
              repeat (rewrite app_comm_cons);
              rewrite app_assoc with (m:=s);
              constructor...
        -- intros. rewrite app_comm_cons.
            rewrite <- stk_points_to_preserves...
            inversion H6;rewrite app_length...
      * cbn...
Qed.
(* prove that last pair's
   label is indeed L,
   when we split *)

Lemma eval_ctx_last_label :
  forall C_mem H K1 L L_env lab_op,
    LS_rel_eval_ctx C_mem
      (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env
                       lab_op L.general)]) H ->
    exists H' s,
      H = H' ++ [(hloc_str L,stack s)]
      /\ 1 < List.length s.
Proof with super_a.
  intros. generalize dependent H.
  induction K1.
  { intros. exists sh_empty.
    inversion H0...
    apply length_ctx_stk in H0.
    inversion H0...
    destruct H1... exists s.
    inversion H3...
    - rewrite app_nil_r in H2...
      inversion H4...
      destruct Flst;inversion H...
      inversion H1...
      inversion H2...
    - inversion H4...
      rewrite app_length.
      inversion H1... }
  intros.
  inversion H0...
  inversion H4...
  inversion H...
  (* activation frames empty *)
  - inversion H6...
    inversion H2...
    destruct H1...
    { induction K1... }
    apply IHK1 in H3.
    destruct H3 as
      [H' [s [hyp1 hyp2]]].
    esplit. exists s.
    rewrite hyp1,app_comm_cons...
  (* some activation frames following
     the general handler *)
  - inversion H9... inversion H14...
    inversion H2...
    rewrite <- H15 in IHK1.
    assert (LS_rel_eval_ctx C_mem ((Flst0 ++ [h_f frm]) ++ Ks)
              ((hloc_str L0,stack (s' ++ frm_stk)) :: H1)).
    { super_a. intros. apply H5 in H8.
      rewrite <- app_assoc in H8.
      apply stk_points_to_preserves
        in H8...
      inversion H6;rewrite app_length... }
    apply IHK1 in H8.
    destruct H8 as [H' [s [hyp1 hyp2]]].
    destruct H'.
    + destruct H1.
      * exists sh_empty,
          (loc_w (cloc C_lab (Datatypes.length lst))
             :: (run_cstlst_trans E ++ s') ++ frm_stk).
        split.
        -- inversion hyp1...
        -- cbn. rewrite app_length.
           inversion H6...
      * inversion hyp1...
    + destruct H1.
      * inversion hyp1...
        induction H'...
      * inversion hyp1...
        exists
          (((hloc_str L0,
              stack (loc_w (cloc C_lab (Datatypes.length lst))
                       :: (run_cstlst_trans E ++ s') ++ frm_stk)))
             :: H'), s.
        rewrite H17...
Qed.
Lemma eval_ctx_app_middle :
  forall C_mem H K1 K2 L L_env lab_op,
    LS_rel_eval_ctx C_mem
      (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)]
         ++ K2) H ->
    exists s H_ld H_ed,
      LS_rel_eval_ctx C_mem
        (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)])
        (H_ld ++ [(hloc_str L,stack s)])
      /\ LS_rel_eval_ctx C_mem K2 H_ed
      /\ H = H_ld ++ [(hloc_str L,stack s)] ++ H_ed.
Proof with super_a.
  intros.
  apply eval_ctx_app_split in H0.
  destruct H0 as
    [H_ld' [H_ed [hyp1 [hyp2 hyp3]]]]...
  pose proof hyp1 as hyp3.
  apply eval_ctx_last_label in hyp1.
  destruct hyp1 as [H' [s [hyp1 hyp4]]]...
  rewrite <- app_assoc.
  exists s,H',H_ed.
  split...
Qed.
Check rel_env_context.
Lemma env_ctx_app_middle :
  forall C_mem (E:L.local_env) (K1 K2:L.eval_context) L L_env lab_op
         H (sp_loc:string) (sp_s:list word),
    LS_rel_env_context C_mem
      (K1 ++ [L.h_f (L.handler_f (hdl_lab L)
                       L_env lab_op L.general)] ++ K2,E)
      (H,hloc sp_loc (List.length sp_s)) ->
    exists s H_ld H_ed,
      LS_rel_env_context C_mem
        (K1 ++ [L.h_f (L.handler_f (hdl_lab L) L_env lab_op L.general)],E)
        (H_ld ++ [(hloc_str L,stack s)],
          hloc sp_loc (List.length sp_s))
      /\ LS_rel_eval_ctx C_mem K2 H_ed
      /\ H = H_ld ++ [(hloc_str L,stack s)] ++ H_ed
      /\ (H_ld = [] -> L = sp_loc /\ s = sp_s).
Proof with super_a.
  intros. inversion H0...
  apply eval_ctx_app_middle in H4.
  destruct H4 as [s [H_ld [H_ed [hyp1 [hyp2 hyp3]]]]].
Admitted.*)
Lemma app_inv_last :
  forall {A:Type} (l1:list A) l2 a b,
    l1 ++ [a] = l2 ++ [b] ->
    a = b
    /\ l1 = l2.
Proof with super_a.
  intros. generalize dependent l2.
  induction l1.
  - intros.
    induction l2...
    + inversion H...
    + inversion H...
      induction l2...
    + induction l2...
  - intros.
    induction l2.
    + induction l1...
    + split.
      * apply IHl1 with
          (l2:=l2).
        inversion H...
      * inversion H...
        apply IHl1 in H2.
        destruct H2.
        rewrite H1...
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
    remember (H_stack ++ SH_cont) as H_stks;
    remember ((L_out,stack cur_stk_val)::H_stks) as cur_stkh;
    remember (th_comp SH_tup SH_ctup) as SH_tups;
    remember [(r3,o3);(r4,o4);(r5,o5);
              (r6,o6)] as R36.
  (* 14 stepping rules, prove the multi and rel for each *)
  - (* x = v1 + v2 *) exists
      ((L_out,stack ((int_w (i1+i2)) :: cur_stk_val))
         :: H_stks,SH_tups),
      ([(ip,loc_w (incr_cloc 4 l));(sp,loc_w (hloc L_out
                                                (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,int_w (i1+i2));(r2,int_w i2)]
         ++ R36). split.
    (* stepping translated salt code for addition *)
    + apply multi_step with (*y is 1 step after current*)
        (y:=((cur_stkh,SH_tups),
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
        (y:=((cur_stkh,SH_tups),
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
        (y:=((cur_stkh,SH_tups),
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
    + unfold incr_cloc,next_cloc... rewrite app_comm_cons.
      apply rel_LS with
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
      * rewrite app_length...
  - (* x = v *) exists
      ((L_out,stack ((val_direct_trans v cur_stk_val) :: cur_stk_val))
         :: H_stks,SH_tups),
      ([(ip,loc_w (incr_cloc 2 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,val_direct_trans v cur_stk_val);
        (r2,o2)] ++ R36). split.
    + (* stepping translated salt code for single value *)
      apply multi_step with (*y is 1 step after current*)
        (y:=((cur_stkh,SH_tups),
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r1) (load_off:=ind)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          eapply Ins...
          inversion H10. rewrite H15... apply nth_middle.
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
      rewrite Heql. rewrite HeqR36... rewrite app_comm_cons.
      apply rel_LS with
        (lst:=lst ++ firstn 2 SIlst) (SIlst:= tl (tl SIlst))...
      * inversion H10... pose proof term_trans_not_nil as NN.
        specialize NN with (tm:=t1'). destruct
          (RelConfig.LS.term_trans t1')as []eqn:?;automate.
        rewrite <- Heql.
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
        rewrite app_length...
  - (* x = newref<v> *)
    destruct L as [L_str].
    exists ((L_out,
              stack (loc_w (hloc L_str 0) :: cur_stk_val)) :: H_stks,
             th_comp (hloc_str L_str !->t
                        tuple ([val_direct_trans v cur_stk_val]); SH_tup)
             SH_ctup),
      ([(ip,loc_w (incr_cloc 4 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,loc_w (hloc L_str 0));
        (r2,val_direct_trans v cur_stk_val)]
         ++ R36). split.
    (* stepping salt code for newref *)
    + apply multi_step with
        (y:=((cur_stkh,
               th_comp (hloc_str L_str !->t
                 tuple ([ns]);SH_tup) SH_ctup),
              [(ip,loc_w (next_cloc l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,o2)] ++ R36)).
      { apply S_malloc_v with
          (i:=1) (d:=r1)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,o1);(r2,o2)] ++ R36)...
        - rewrite H15. inversion H10... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,
               th_comp (hloc_str L_str !->t
                          tuple ([ns]);SH_tup) SH_ctup),
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r2) (load_off:=ind)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,loc_w (hloc L_str 0));
                 (r2,o2)] ++ R36) (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          eapply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
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
               th_comp (hloc_str L_str !->t
                 tuple ([val_direct_trans v cur_stk_val]);SH_tup) SH_ctup),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,loc_w (hloc L_str 0));
               (r2,val_direct_trans v cur_stk_val)]
                ++ R36)).
      { pose proof S_store_v as Ins. specialize Ins with
          (d:=r1) (o:=reg_o r2) (j:=0) (L:=hloc_str L_str)
          (H_vtup:=hloc_str L_str !->t
                 tuple ([ns]);SH_tup) (lst:=[ns])
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
      unfold incr_cloc,next_cloc... rewrite app_comm_cons.
      inversion H13;subst.
      apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst) (SH_cont:=SH_cont)
        (SIlst:= tl (tl (tl (tl SIlst))));inversion H10...
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
           inversion H16...
           specialize H6 with (v:=L.var_val n).
           assert (Temp:In (L.var_val n) [L.var_val (L.dbjind_var n)]).
           { super_a. } apply H6 in Temp. inversion Temp...
           rewrite List.map_length...
        -- inversion H7...
      * unfold th_update,L.th_update,h_eqb,L.h_eqb.
        intros. destruct (eqb L_str x)...
      * rewrite H15... assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
                                  [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl).
        { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length...
  - (* x = pi_i(v)*)
    destruct L as [L_str].
    exists ((L_out,
              stack ((nth i (List.map run_cst_trans lst0) ns) :: cur_stk_val))
              :: H_stks,SH_tups),
      ([(ip,loc_w (incr_cloc 3 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,nth i (List.map run_cst_trans lst0) ns);
        (r2,o2)] ++ R36). split.
    (* stepping salt code for loading from heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tups),
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r1) (load_off:=ind) (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36) (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins. 
          eapply Ins...
          inversion H10. rewrite H15... apply nth_middle.
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)... }
      apply multi_step with
        (y:=((cur_stkh,SH_tups),
              [(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,nth i (List.map run_cst_trans lst0) ns);
               (r2,o2)] ++ R36)).
      { eapply S_load_tup_v with
          (d:=r1) (s:=r1) (off:=i)
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
        - inversion H13... inversion H7... }
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
      unfold incr_cloc... rewrite app_comm_cons.
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
      * rewrite app_length...
  - (* x = v1[i] <- v2 *)
    destruct L as [L_str].
    exists ((L_out,
              stack (val_direct_trans v' cur_stk_val :: cur_stk_val))
              :: H_stks,
             th_comp (hloc_str L_str !->t
                        tuple (update_nth 0 (List.map run_cst_trans [c])
                                 (val_direct_trans v' cur_stk_val)); SH_tup) SH_ctup),
      ([(ip,loc_w (incr_cloc 4 l));
        (sp,loc_w (hloc L_out (1+(List.length cur_stk_val))));
        (r0,o0);
        (r1,val_direct_trans v' cur_stk_val);
        (r2,loc_w (hloc L_str 0))] ++ R36). split.
    (* stepping salt code for storing to heap *)
    + apply multi_step with
        (y:=((cur_stkh,SH_tups),
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r1) (load_off:=ind)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36) (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          eapply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w l);(sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)...
          rewrite H15. inversion H10... apply nth_middle. }
      apply multi_step with
        (y:=((cur_stkh,SH_tups),
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r2) (load_off:=ind) (l:=next_cloc l)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);
                 (r1,val_direct_trans v' cur_stk_val);
                 (r2,o2)] ++ R36)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (hloc L_str 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H8... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H10... inversion H3...
            inversion H7... inversion H6... }
          rewrite Temp. eapply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
        - inversion H5... }
      apply multi_step with
        (y:=((cur_stkh,
               th_comp (hloc_str L_str !->t
                          tuple (update_nth 0 (List.map run_cst_trans [c])
                                   (val_direct_trans v' cur_stk_val));
                        SH_tup) SH_ctup),
              [(ip,loc_w (incr_cloc 3 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,loc_w (hloc L_str 0))] ++ R36)).
      { apply S_store_v with
          (d:=r2) (o:=r1) (j:=0) (L:=hloc_str L_str)
          (lst:=List.map run_cst_trans [c])
          (R:=[(ip,loc_w (incr_cloc 2 l));
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);
               (r1,val_direct_trans v' cur_stk_val);
               (r2,loc_w (hloc L_str 0))] ++ R36)...
        - rewrite H15. inversion H18... inversion H10.
          apply ins_verify with (n:=2).
        - inversion H13... inversion H6...
          eapply H1 with (vs:=[c])... }
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
      unfold incr_cloc... rewrite app_comm_cons.
      apply rel_LS with
        (lst:=lst ++ firstn 4 SIlst)
        (SIlst:= tl(tl (tl (tl SIlst))));
        inversion H10;inversion H13...
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
           rewrite List.map_length.
           inversion H6... inversion H21...
        -- inversion H13... inversion H9...
      * unfold th_update,L.th_update,h_eqb,L.h_eqb.
        intros. destruct (eqb L_str x)...
      * rewrite H15...
        assert (AssocIns: forall (x1:instr) x2 x3 x4 tl,
                   [x1;x2;x3;x4] ++ tl = x1::x2::x3::x4::tl).
        { intros... }
        rewrite <- AssocIns,app_assoc...
      * rewrite app_length...
  - (* x = v(v') *)
    destruct lab as [lab].
    exists ((L_out,stack ((val_direct_trans v' cur_stk_val)::
                            (loc_w (incr_cloc 3 l)) :: cur_stk_val))
              :: H_stks,SH_tups),
      ([(ip,loc_w (cloc lab 1));
        (sp,loc_w (hloc L_out (2 + (List.length cur_stk_val))));
        (r0,loc_w (cloc lab 0));
        (r1,val_direct_trans v' cur_stk_val);
        (r2,o2)] ++ R36). split.
    + apply multi_step with
        (y:=(cur_stkh,SH_tups,
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r0) (load_off:=ind)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w l);
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,o0);(r1,o1);
                 (r2,o2)] ++ R36)(H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          assert (Temp:loc_w (cloc lab 0)
                       = nth (0 + ind) cur_stk_val ns).
          { inversion H7... rewrite app_nth1...
            rewrite map_nth with (d:=L.ns).
            rewrite H2... rewrite List.map_length...
            inversion H10... inversion H3... inversion H8...
            inversion H11... }
          rewrite Temp. eapply Ins...
          + inversion H10. rewrite H15... apply nth_middle.
        - inversion H7... }
      apply multi_step with
        (y:=(cur_stkh,SH_tups,
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
        - pose proof S_load_stk as Ins. specialize Ins with
            (d:=r1) (load_off:=ind)
            (L:=L_out) (s:=sp)
            (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,loc_w (cloc lab 0));
                 (r1,o1);(r2,o2)] ++ R36) (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Ins.
          eapply Ins...
          + inversion H10. rewrite H15... apply ins_verify with (n:=1).
        - apply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
            (R:=[(ip,loc_w (next_cloc l));
                 (sp,loc_w (hloc L_out (List.length cur_stk_val)));
                 (r0,loc_w (cloc lab 0));
                 (r1,o1);(r2,o2)] ++ R36)...
          rewrite H15. inversion H10... inversion H7...
          apply ins_verify with (n:=1). }
      apply multi_step with
        (y:=((L_out, stack (loc_w (incr_cloc 3 l) :: cur_stk_val)) :: H_stks,
              SH_tups,
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
      rewrite app_comm_cons.
      apply rel_LS with
        (lst:=[push r1]) (SIlst:=func_term_trans 1 t1');
        inversion H10;automate.
      * inversion H14... specialize H3 with (c_lab lab).
        rewrite H18 in H3. inversion H3... 
      * apply rel_env_context with
          (s_out:=loc_w (cloc Clab (3 + (List.length lst)))
                    :: List.map run_cst_trans E1 ++ s_out).
        { inversion H5...
          - inversion H16.
            rewrite app_comm_cons.
            rewrite app_assoc...
            apply rel_frame with
              (lst:=lst ++ [val_trans r0 v;val_trans r1 v';
                            call r0])
              (Ilst:=push r1 :: func_term_trans (S (List.length E1)) t)...
            + inversion H2...
            + rewrite H15;cbn;pose proof term_trans_not_nil as NN;
                specialize NN with (tm:=t);
                destruct (term_trans t) as []eqn:?;automate;
                rewrite <- Heql; unfold func_term_trans;
                rewrite <- PeanoNat.Nat.add_succ_comm;
                rewrite <- app_assoc...
            + rewrite app_length... 
          - intros. apply H17 with (s':=s') (L':=L') in H1.
            rewrite app_comm_cons.
            apply stk_points_to_preserves...
            inversion H16... inversion H11...
            rewrite app_length... }
        destruct v' as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
        inversion H2... rewrite List.map_length.
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
              :: H_stks,SH_tups),
      ([(ip,match nth 0 s_out ns with
            | cloc Clab n => cloc Clab (S n)
            | _ => ns_cloc end);
        (sp,loc_w (hloc L_out (List.length s_out))); (*remove l_dst, add v*)
        (r0,o0);
        (r1,val_direct_trans v cur_stk_val);(r2,o2)] ++ R36).
    split.
    apply multi_step with
      (y:=((cur_stkh,SH_tups),
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
      - pose proof S_load_stk as Ins. specialize Ins with
          (d:=r1) (load_off:=ind)
          (L:=L_out)(s:=sp)
          (lst:=cur_stk_val) (reg_off:=List.length cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36) (H_stk_ld:=[]).
        rewrite PeanoNat.Nat.sub_diag in Ins.
        eapply Ins...
        + inversion H10. rewrite H15... apply nth_middle.
      - apply S_mov with
          (d:=r1) (o:=val_direct_trans (var_val str) cur_stk_val)
          (R:=[(ip,loc_w l);
               (sp,loc_w (hloc L_out (List.length cur_stk_val)));
               (r0,o0);(r1,o1);
               (r2,o2)] ++ R36)...
        inversion H10... rewrite H15... apply nth_middle. }
    apply multi_step with
      (y:=((L_out,stack s_out) :: H_stks,SH_tups,
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
          map_length... }
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
        destruct s_out;rewrite map_length... }
    eapply multi_step.
    { subst. cbn.
      assert (s_out <> []).
      { inversion H5... inversion H9...
        inversion H6. induction s... }
      eapply S_ret...
      - rewrite H15. inversion H10...
        destruct v as [|[|]];
          apply ins_verify with (n:=2).
      - induction s_out... }
     
    (* apply multi_step with
      (y:=((L_out,stack (tl s_out)) :: H_stks,SH_tups,
            [(ip,hd ns s_out);
             (sp,loc_w (hloc L_out (List.length (tl s_out))));
             (r0,o0);
             (r1,val_direct_trans v cur_stk_val);
             (r2,o2)] ++ R36)).
    
    { inversion H5;subst.
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
      inversion H8... 
      - inversion H1... inversion H11...
        remember ((s ++ s') ++ frm_stk) as s_prev.
        intros.
        specialize Hyp with
          (pred_j:=List.length s_prev)
          (*l':=cloc C_lab (List.length lst0)*)
          (lst:=loc_w (cloc C_lab (Datatypes.length lst0))
                  :: (s ++ s') ++ frm_stk)
          (R:=newR s_prev lst0 C_lab)...
        cbn in Hyp. apply Hyp...
        rewrite H15. inversion H10...
        destruct v as [|[|]];rewrite PeanoNat.Nat.add_comm;
          apply ins_verify with (n:=2).
      - inversion H3... inversion H16...
        remember ((s ++ s') ++ frm_stk ++ slst) as s_prev.
        intros.
        specialize Hyp with
          (pred_j:=List.length s_prev)
          (lst:=loc_w (cloc C_lab (List.length lst0)) :: s_prev)
          (R:=newR s_prev lst0 C_lab)...
        cbn in Hyp. apply Hyp...
        rewrite H15. inversion H10...
        destruct v as [|[|]];rewrite PeanoNat.Nat.add_comm;
          apply ins_verify with (n:=2). }*)
    constructor.
    { revert Heqcur_stk_val.
      revert HeqR36.
      inversion H5... inversion H9...
      inversion H4... inversion H16...
      pose proof S_push as Hyp.
      specialize Hyp with
        (o:=reg_o r1) (j:=List.length ((s ++ s') ++ frm_stk))
        (l:=cloc C_lab (List.length lst0))
        (R:=[(ip,loc_w (cloc C_lab (S (List.length lst0))));
             (sp,loc_w (hloc L (List.length ((s ++ s') ++ frm_stk))));
             (r0, o0);
             (r1, val_direct_trans v
                    cur_stk_val);
             (r2, o2)] ++ R36).
      intros... cbn in Hyp.

???????

      apply Hyp...
      rewrite H18.
      pose proof app_nth2_plus as Temp.
      specialize Temp with (l:=lst0) (l':=Ilst) (n:=0).
      rewrite PeanoNat.Nat.add_comm in Temp.
      rewrite Temp... }
    + (* prove LS_rel for v end, end of function call *)
      unfold incr_cloc,next_cloc,ns_cloc...
      inversion H5... inversion H8...
      { inversion H1... inversion H11...
         inversion H4... rewrite app_comm_cons.
         apply rel_LS with
           (lst:=lst0 ++ [nth 0 Ilst halt])
           (SIlst:=tl Ilst)...
        - inversion H2... inversion H16...
        - inversion H2...
          apply rel_env_context with
            (s_out:=s' ++ frm_stk)...
          + intros. apply H9 with (s':=s'0) (L':=L') in H6.
            rewrite <- app_assoc in H6.
            apply <- stk_points_to_preserves. apply H6.
            rewrite app_length. inversion H3... 
          + rewrite app_assoc.
            inversion H20...
            destruct v as [cst|[ind|str]]...
            rewrite <- map_nth with (d:=L.ns). rewrite app_nth1...
            inversion H10... rewrite List.map_length... inversion H21...
            inversion H24...
        - rewrite H18... destruct Ilst... rewrite <- app_assoc...
        - rewrite H22, app_length... }
     
  - (* handle P_body with A P_op under v_env in t*)
    destruct lab_op as [lab_op],
        lab_body as [lab_body], L as [L].
    (*exists
      ((hloc_str L,
         stack
           [val_direct_trans v_env cur_stk_val;
            loc_w (hloc L 4);loc_w (cloc handle_loc 10);
            loc_w (hloc L_out (S (List.length cur_stk_val)));
            int_w 0;
            val_direct_trans v_env cur_stk_val; 
            loc_w (cloc (cloc_str lab_op) 0)])
         :: (L_out, stack (loc_w (incr_cloc 5 l) :: cur_stk_val))
         :: H_stks, SH_tups, SH_conts),
      ([(ip,loc_w (cloc lab_body 2));
        (sp,loc_w (hloc L 7));(r0, o0);
        (r1,val_direct_trans v_env cur_stk_val);
        (r2,loc_w (hloc L 4));
        (r3,val_direct_trans v_env cur_stk_val);
        (r4,int_w 0);
        (r5,loc_w (hloc L_out (S (List.length cur_stk_val))));
        (r6,loc_w (cloc lab_body 0))]).*) esplit. esplit.
    split.
    + rewrite HeqR36. eapply multi_step.
      { eapply S_mov with (d:=r4) (o:=0)...
        inversion H10... rewrite H15...
        apply nth_middle. }
      eapply multi_step.
      { destruct v_env as [|[|]].
        - eapply S_mov with
            (d:=r3) (o:=val_direct_trans s cur_stk_val)...
        - pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r3) (load_off:=n) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)
            (s:=sp) (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          + rewrite H15. inversion H10...
            apply ins_verify with (n:=1).
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
      { eapply S_push with (o:=r1)...
        unfold c_comp. inversion H14...
        inversion H18... apply H3 in H4.
        rewrite H4,H18... }
    + (* prove LS_rel for handler creation*)
      unfold incr_cloc,next_cloc...
      destruct (SC0 lab_body) as [newIns|]eqn:?.
      repeat (rewrite app_comm_cons).
      eapply rel_LS with
        (lst:=[push r2;push r1]) (SIlst:=func_term_trans 2 t1')...
      * inversion H14... specialize H2 with (c_lab lab_body).
        rewrite H18 in H2. inversion H2... 
      * apply rel_env_context with
          (s_out:=
             [loc_w (cloc handle_loc 10);
              loc_w (hloc L_out
                       (S (List.length (List.map run_cst_trans E1 ++ s_out))));
              int_w 0; val_direct_trans v_env (List.map run_cst_trans E1 ++ s_out);
              loc_w (cloc lab_op 0)])...
        -- inversion H5...
           eapply rel_eval_ctx_lst with
             (K:=[L.h_f (L.handler_f (L.hdl_lab L)
                           L_env (L.c_lab lab_op) general)])...
           { rewrite app_comm_cons.
             apply rel_eval_ctx_lst... inversion H9;automate;
               repeat (rewrite app_comm_cons).
             - repeat (rewrite app_assoc).
               apply rel_hdl_stk_base...
               apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               + pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H7...
               + rewrite H15...
                 rewrite <- app_assoc...
               + rewrite app_length...
             - intros. apply H11 with (L':=L') (s':=s') in H1.
               rewrite app_comm_cons.
               apply stk_points_to_preserves...
               inversion H9;subst;repeat (rewrite app_length).
               + inversion H3... }
           { apply rel_hdl_stk_base
               with (Flst:=[]) (s:=[])...
             destruct L_env,v_env as [|[]]...
             inversion H6... rewrite app_nth1.
             rewrite map_nth with (d:=L.ns).
             rewrite H2...
             apply rel_hdl_general with
               (s_prev:=loc_w (cloc Clab (5+(Datatypes.length lst)))
                          :: List.map run_cst_trans E1 ++ s_out)...
             rewrite map_length.
             inversion H10... inversion H3...
             inversion H16... inversion H4... }
           { intros. inversion H1... }
        -- destruct v_env as [|[|]],L_env...
           rewrite app_nth1. rewrite map_nth with (d:=L.ns).
           inversion H6... rewrite H2...
           rewrite map_length.
           inversion H10... inversion H2...
           inversion H7... inversion H3...
      * inversion H14... inversion H18.
        apply H3 in H4. unfold c_comp.
        rewrite H4. unfold code_mem_trans.
        rewrite H18...
      * inversion H14... unfold code_mem_trans in Heqi.
        rewrite H18 in Heqi...
  - (* v end, leaving from handler *)
    inversion H5...
    inversion H8...
    inversion H1...
    inversion H3...
    inversion H7...
    inversion H2...
    specialize H9 with
      (L':=hloc_str L1) (s':=s) (H':=H6).
    assert (Temp:(hloc_str L1, stack s) :: H6
                 = (hloc_str L1, stack s) :: H6)...
    apply H9 in Temp.
    unfold stk_points_to in Temp.
    cbn in Temp. inversion Temp.
    destruct Temp.
    assert (exists str num,
               loc_w (cloc str num) = hd ns s).
    { inversion H16...
      - inversion H18...
        inversion H24...}
    destruct H18 as [C_lab [num s_ret_addr]].
    remember ([loc_w (cloc handle_loc 10);
               loc_w (hloc L1 (Datatypes.length s_prev));
               int_w 0; 
               loc_w (hloc L_env0 0);
               loc_w (cloc Clab_op 0)])
      as s_out.
    remember (List.map run_cst_trans E1 ++ s_out)
        as cur_stk_val.
    esplit. esplit. split.
    + eapply multi_step.
      { destruct v as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans cst cur_stk_val)...
          cbn. rewrite H15. inversion H10... apply nth_middle.
        - pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r1) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val) (s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          + rewrite H15. inversion H10...
            apply nth_middle.
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val var) cur_stk_val)...
          rewrite H15. inversion H10... apply nth_middle. }
      eapply multi_step.
      { eapply S_sfree with
          (n:=List.length (List.map run_cst_trans E1))...
        - cbn. rewrite H15. inversion H10...
          destruct v as [|[|]];
            rewrite Nat.add_comm,map_length;
            apply ins_verify with (n:=1).
        - rewrite app_length... }
      eapply multi_step.
      { subst. cbn. rewrite skipn_app,
          skipn_all, Nat.sub_diag,
          app_length,Nat.add_comm,Nat.add_sub.
        cbn. eapply S_ret with
          (lst:=[loc_w (cloc handle_loc 10);
                 loc_w (hloc L1 (Datatypes.length s_prev));
                 int_w 0; 
                 loc_w (hloc L_env0 0);
                 loc_w (cloc Clab_op 0)])
          (lsp:=L0) (pred_j:=4)...
        rewrite H15. inversion H10...
        destruct v as [|[|]];
          apply ins_verify with (n:=2). }
      eapply multi_step.
      { eapply S_pop with (reg:=r2)... }
      eapply multi_step.
      { eapply S_sfree with (n:=3)... }
      eapply multi_step.
      { eapply S_mov_sp_del with
          (H_stk_ed:=H6 ++ SH_cont)
          (H_stk_ld:=[]) (lst:=s)... }
      eapply multi_step.
      { assert (Tmp:s <> []).
        { subst. inversion H16...
          - inversion H19;subst;
              rewrite app_length in H20;
              rewrite Nat.add_comm in H20;
              cbn in H20;destruct s0... }     
        eapply S_ret with
          (lst:=s)
          (H_stk':=H6 ++ SH_cont)...
        - rewrite H20. destruct s...
        - rewrite H20. rewrite Nat.sub_diag... }
      constructor.
      { rewrite <- s_ret_addr.
        apply S_push with (o:=reg_o r1)...
        inversion H14... inversion H16...
        - inversion H18...
          inversion H26...
          inversion s_ret_addr...
          rewrite H29. destruct Ilst...
          cbn in H33...
          apply nth_middle. }
    + (* prove LS_rel for v end, leaving handler *)
      inversion H16...
      * inversion H18...
        inversion H24...
        inversion H2...
        rewrite app_comm_cons.
        { eapply rel_LS with
            (lst:=lst0 ++ firstn 1 Ilst)...
          - inversion H25...
          - apply rel_env_context with
              (s_out:=s' ++ frm_stk)...
            + intros. apply H17 with (s':=s'0) (L':=L') in H19.
              rewrite <- app_assoc in H19.
              apply <- stk_points_to_preserves. apply H19.
              rewrite app_length. inversion H21... 
            + rewrite <- app_assoc.
              inversion H29...
              destruct v as [cst|[ind|str]]...
              rewrite <- map_nth with (d:=L.ns).
              rewrite app_nth1.
              inversion H10...
              rewrite List.map_length.
              inversion H10...
              inversion H28... inversion H32...
          - inversion s_ret_addr.
            rewrite H27. inversion H25.
            rewrite H34. destruct Ilst...
            rewrite <- app_assoc...
          - inversion s_ret_addr...
            destruct Ilst...
            rewrite app_length... }
  (* x = raise v1 v2, raising handler*)
  - destruct L as [L_str].
    inversion H5.
    inversion H9. inversion H3.
    apply eval_ctx_app_middle in H5.
    destruct H5 as
      [s_cont [H_ld [H_ed [hyp1 [hyp2 hyp3]]]]].
    pose proof hyp1 as hyp4.
    destruct L_env as [L_env].
    apply last_eval_ctx_rel in hyp4.
    destruct hyp4 as [K0 hyp4].
    inversion hyp4. inversion H25.
    esplit. esplit. split.
    + eapply multi_step.
      { destruct v2 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans cst cur_stk_val)...
          cbn. rewrite H15. inversion H10... apply nth_middle.
        - pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r2) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          + rewrite H15. inversion H10...
            apply nth_middle.
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans (var_val var) cur_stk_val)...
          rewrite H15. inversion H10... apply nth_middle. }
      eapply multi_step.
      { destruct v1 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans cst cur_stk_val)...
        - pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r1) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          + rewrite H15. inversion H10...
            apply ins_verify with (n:=1).
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val var) cur_stk_val)... }
      eapply multi_step.
      { eapply S_call
          with (o:=wd_o (cloc raise_loc 0))...
        rewrite H15. inversion H10...
        apply ins_verify with (n:=2). }
      cbn.
      apply multi_step with
        (y:=((hloc_str L,
               stack (loc_w (cloc Clab
                               (S (S (S (Datatypes.length lst)))))
                         :: cur_stk_val))
              :: H_stack ++ SH_cont, th_comp SH_tup SH_ctup,
           [(ip,loc_w (cloc raise_loc 1));
            (sp,loc_w (hloc L (S (Datatypes.length cur_stk_val))));
            (r0,o0); (r1,val_direct_trans v1 cur_stk_val);
            (r2,val_direct_trans v2 cur_stk_val);
            (r3,o3);
            (r4,nth (List.length
                       (match H_ld with
                        | [] => loc_w (cloc Clab
                                         (3 + List.length lst))
                                  :: cur_stk_val
                        | _ :: _ => s_cont
                        end) - 4 + 0)
                  (match H_ld with
                   | [] => loc_w (cloc Clab
                                    (3 + List.length lst))
                             :: cur_stk_val
                   | _ :: _ => s_cont
                   end) ns);
            (r5,o5);(r6,o6)])).
      { destruct H_ld.
        - (*inversion hyp3.
          fold (nth (List.length (loc_w (cloc Clab
                                    (3 + Datatypes.length lst))
                                    :: List.map run_cst_trans E1
                                    ++ s0 ++ frm_stk) - 4 + 0)
                  (loc_w (cloc Clab (3 + List.length lst))
                     :: List.map run_cst_trans E1
                     ++ s0 ++ frm_stk) ns*)
          subst. unfold next_cloc.
          inversion hyp3.
          eapply S_load_stk with
            (d:=r4) (s:=r1) (load_off:=0)
            (l:=cloc raise_loc 0)
            (R:=[(ip,loc_w (cloc raise_loc 0));
                 (sp,loc_w (hloc L_str (S (List.length
                                             (List.map run_cst_trans E1
                                                ++ s0 ++ frm_stk)))));
                 (r0,o0);
                 (r1,val_direct_trans v1
                       (List.map run_cst_trans E1 ++ s0 ++ frm_stk));
                 (r2,val_direct_trans v2
                       (List.map run_cst_trans E1 ++ s0 ++ frm_stk));
                 (r3,o3);
                 (r4,o4);
                 (r5,o5);(r6,o6)])
            (H_stk_ld:=[])
            (lst:=loc_w (cloc Clab (3 + List.length lst))
                    :: List.map run_cst_trans E1 ++ s0 ++ frm_stk)
            (H_stk_ed:=H_ed ++ SH_cont)...
          + destruct v1 as [|[|]]...
            inversion H17... rewrite app_nth1,
              map_nth with (d:=L.ns),H3...
            rewrite map_length.
            inversion H10... inversion H6...
            inversion H27... inversion H22...
        - inversion hyp3. subst.
          unfold next_cloc.
          Check S_load_stk.
          eapply S_load_stk with
            (d:=r4) (s:=r1) (load_off:=0)
            (l:=cloc raise_loc 0)
            (R:=[(ip,loc_w (cloc raise_loc 0));
                 (sp,loc_w (hloc L (S (Datatypes.length (List.map run_cst_trans E1
                                         ++ s0 ++ frm_stk)))));
                 (r0,o0); (r1,val_direct_trans v1 (List.map run_cst_trans E1
                                ++ s0 ++ frm_stk));
                 (r2,val_direct_trans v2 (List.map run_cst_trans E1
                       ++ s0 ++ frm_stk));
                 (r3,o3);
                 (r4,o4);
                 (r5,o5);(r6,o6)])
            (H_stk_ld:=
               (hloc_str L,
                 stack (loc_w (cloc Clab (3 + List.length lst))
                          :: List.map run_cst_trans E1
                          ++ s0 ++ frm_stk))
                 :: H_ld)
            (*lst:=s1 ++
                     [loc_w (cloc handle_loc 10);
                      loc_w (hloc L_prev (Datatypes.length s_prev));
                      int_w 0; 
                      loc_w (hloc L_env0 0);
                      loc_w (cloc Clab_op 0)]*)
            (H_stk_ed:=H_ed ++ SH_cont)...
          + destruct v1 as [|[|]]...
            inversion H17... rewrite app_nth1,
              map_nth with (d:=L.ns),H3...
            rewrite map_length.
            inversion H10... inversion H4...
            inversion H22... inversion H21...
          + inversion hyp3...
            rewrite <- app_assoc,
              <- app_comm_cons... }
      eapply multi_step.
      { eapply S_store_stk with
          (d:=r1) (load_off:=0) (o:=sp)
          (H_stk_ld:=match H_ld with
                     | [] => []
                     | _::H_ld' =>
                         (hloc_str L,
                           stack (loc_w (cloc Clab (3 + List.length lst))
                                    :: cur_stk_val))
                           :: H_ld'
                     end)
          (lst:=match H_ld with
                | [] =>
                    loc_w (cloc Clab (3 + List.length lst))
                      :: cur_stk_val
                | _ :: _ => s_cont
                end)
          (H_stk_ed:=H_ed ++ SH_cont)...
        - destruct v1 as [|[|]]...
          inversion H17... rewrite app_nth1,
            map_nth with (d:=L.ns),H3...
          rewrite map_length.
          inversion H10... inversion H4...
          inversion H22... inversion H21...
        - destruct H_ld.
          + inversion hyp3...
          + inversion hyp3...
            rewrite <- app_assoc,
              <- app_comm_cons...
        - destruct H_ld.
          + inversion H9. cbn.
            repeat (rewrite app_length).
            inversion H3...
          + apply eval_ctx_last_label in hyp1.
            destruct hyp1 as [H' [s [hyp1 hyp5]]].
            apply app_inv_last in hyp1.
            inversion hyp1... }
      inversion H18.
      eapply multi_step.
      { Check S_mov_sp_to_cont.
        eapply S_mov_sp_to_cont with
          (o:=r4) (H_cont:=SH_cont) (H_stk_ed:=H_ed)
          (H_stk_ld:=match H_ld with
                     | [] => []
                     | _ :: H_ld' =>
                         (hloc_str L,
                           stack (loc_w (cloc Clab (3 + Datatypes.length lst))
                                    :: cur_stk_val)) :: H_ld'
                     end)
          (L:=match H_ld with
              | [] => L_prev0
              | _::_ => L_prev
              end)
          (lst:=match H_ld with
                | [] => s_prev0
                | _::_ => s_prev
                end)...
        - destruct H_ld.
          + rewrite app_comm_cons,Nat.add_0_r.
            rewrite <- rev_nth with (n:=3),
                rev_app_distr,rev_app_distr.
            2:{ repeat (rewrite app_length).
                rewrite Nat.add_comm... }
            cbn...
          + rewrite Nat.add_0_r.
            rewrite <- rev_nth with (n:=3),
                rev_app_distr.
            2:{ rewrite app_length.
                rewrite Nat.add_comm... }
            cbn...
            super_a.
        - destruct H_ld.
          + inversion hyp3... }
      eapply multi_step.
      { eapply S_load_stk with
          (d:=r5) (s:=r1) (load_off:=3)...
        destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H4...
        inversion H16... inversion H6... }
      eapply multi_step.
      { apply S_malloc_c with
          (d:=r3) (i:=1) (L:=L_str)... }
      eapply multi_step.
      { eapply S_store_c with
          (d:=r3) (o:=r1) (j:=0)...
        - unfold th_update.
          rewrite h_eqb_refl...
        - super_a. }
      eapply multi_step.
      { eapply S_load_stk with
          (d:=r1) (s:=r1) (load_off:=2)...
        destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H4...
        inversion H16... inversion H6... }
     
      eapply multi_step.
      { cbn. 
        eapply S_call with
          (o:=r5) (lsp:=match H_ld with
                        | [] => L_prev
                        | _::_ => L_prev0
                        end)
          (lst:=match H_ld with
                        | [] => s_prev
                        | _::_ => s_prev0
                        end)...       
        - destruct H_ld.
          + rewrite app_comm_cons,Nat.add_0_r.
            rewrite <- rev_nth with (n:=3),
                rev_app_distr,rev_app_distr.
            2:{ repeat (rewrite app_length).
                inversion H3. cbn.
                rewrite Nat.add_comm... }
            inversion H3...
          + rewrite Nat.add_0_r.
            rewrite <- rev_nth with (n:=3),
                rev_app_distr.
            2:{ rewrite app_length.
                inversion H3. cbn.
                rewrite Nat.add_comm... }
            inversion H3...
        - destruct H_ld.
          + Check S_call. inversion hyp3...
          + inversion hyp3...
            rewrite <- app_assoc,
              <- app_comm_cons...
        - destruct H_ld.
          +
            
            rewrite app_length. inversion H3.
            rewrite <- rev_nth.
        - destruct v1 as [|[|]]...
          destruct H_ld.
          + inversion H17.
          + inversion H17... rewrite app_nth1,
              map_nth with (d:=L.ns),H3...
            rewrite map_length.
            inversion H10... inversion H4...
            inversion H16... inversion H6...
        
        - destruct H_ld.
          + inversion H9. cbn.
            repeat (rewrite app_length).
            inversion H3...
          + apply eval_ctx_last_label in hyp1.
            destruct hyp1 as [H' [s0 [hyp1 hyp4]]].
            apply app_inv_last in hyp1.
            inversion hyp1...
      }
(*
rewrite app_comm_cons,
              Nat.sub_add_distr with
              (m:=3) (p:=1). ,Nat.sub_add with
                (n:=1).
            2:{ inversion H9...
                repeat (rewrite app_length).
                inversion H3... }
            Search (rev (_++_)).


 should write another lemma
             to compose two lists back 
::
tl H_ld*)

          (*inversion H1...
    inversion H3...
    2:{ destruct H16... }
    inversion H7...
    inversion H2...
    specialize H9 with
      (L':=L1) (s':=s) (H':=H6).
    assert (Temp:(L1, stack s) :: H6
                 = (L1, stack s) :: H6).
    { reflexivity. }
    apply H9 in Temp.
    unfold stk_points_to in Temp.
    cbn in Temp. inversion Temp.
    destruct Temp.
    assert (exists str num,
               loc_w (cloc str num) = hd ns s).
    { inversion H16...
      - inversion H18...
        inversion H24... eauto.
      - inversion H21...
        inversion H25... eauto. }
    destruct H18 as [C_lab [num s_ret_addr]].*)
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
2. added well-formed ness for rel_ins rather than at LS_rel
3. handler relation should also store return location
4. handler rule for lexi should swap order of env and L
   (this actually doesn't matter for paper proof since
    paper proof uses named variables)*)




