Require Import Lists.List. Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import PeanoNat.
Require Import Lia.
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
Lemma last_eval_ctx_rel :
  forall s C_mem L L_env lab_op Ks H alst,
    LS_rel_eval_ctx C_mem
      (Ks ++ [hdl_led_lst
                (handler_f (hdl_lab L)
                   (obj_lab L_env) lab_op general) alst])
      (H ++ [(hloc_str L,stack s)]) ->
      LS_rel_hdl_stk C_mem L
        (hdl_led_lst (handler_f (hdl_lab L)
                        (obj_lab L_env) lab_op general) alst)
        (stack s).
Proof with super_a.
  intros. generalize dependent H.
  induction Ks.
  - intros.
    destruct H.
    2:{ apply length_ctx_stk in H0.
        rewrite app_length in H0.
        rewrite Nat.add_comm in H0.
        cbn in H0... }
    inversion H0...
  - intros. inversion H0...
    destruct H;inversion H4...
    { inversion H5...
      induction Ks... }
Qed.
Lemma eval_ctx_app_split :
  forall C_mem K' K H,
    LS_rel_eval_ctx C_mem
      (K' ++ K) H ->
    exists H_ld H_ed,
      LS_rel_eval_ctx C_mem K' H_ld
      /\ LS_rel_eval_ctx C_mem K H_ed
      /\ H = H_ld ++ H_ed.
Proof with super_a.
  intros. generalize dependent H.
  induction K'.
  { intros.
    exists sh_empty,H... }
  intros. inversion H0...
  apply IHK' in H4.
  destruct H4 as
    [H_ld [H_ed [hyp1 [hyp2 hyp3]]]].
  exists ((hloc_str L,stack s)
            :: H_ld),H_ed...
  intros. eapply H7...
Qed.
Lemma eval_ctx_last_label :
  forall C_mem H K' L L_env lab_op alst,
    LS_rel_eval_ctx C_mem
      (K' ++
         [hdl_led_lst
            (L.handler_f (L.hdl_lab L)
               L_env lab_op L.general)
            alst]) H ->
    exists H' s,
      H = H' ++ [(hloc_str L,
                   stack s)]
      /\ 1 < List.length s.
Proof with super_a.
  intros. generalize dependent H.
  induction K'.
  { intros. 
    inversion H0...
    exists sh_empty,s.
    apply length_ctx_stk in H0.
    destruct H1;super_a;
      inversion H5;
      inversion H6...
    rewrite app_length... }
  intros. inversion H0...
  apply IHK' in H4.
  destruct H4 as [H' [s' [h1 h2]]].
  exists ((hloc_str L0, stack s) :: H'),s'...
Qed.
Definition get_hdl_lab (hdl_frm_lst:hdl_led_frm_lst) : string :=
  match hdl_frm_lst with
  | hdl_led_lst (handler_f (hdl_lab L) _ _ _) _ => L
  end.
Definition frm_to_hloc frm :=
  hloc_str (get_hdl_lab frm).
Definition is_hdllst_general hdl_lst:=
  match hdl_lst with
  | hdl_led_lst frm alst =>
      is_h_frm_general_hdl frm
  end.
Lemma eval_ctx_app_comp :
  forall C_mem K' K H_ld H_ed,
    LS_rel_eval_ctx C_mem K' H_ld ->
    LS_rel_eval_ctx C_mem K H_ed ->
    (forall H_ld' H_ed' L s L' s',
        H_ld = H_ld' ++ [(L,stack s)] ->
        H_ed = (L',stack s') :: H_ed' ->
        stk_points_to s s' L') ->
    LS_rel_eval_ctx C_mem
      (K' ++ K) (H_ld ++ H_ed).
Proof with super_a.
  intros. generalize dependent H_ld.
  induction K'.
  { intros. inversion H... }
  destruct H_ed as [|b H_ed']eqn:?.
  { intros. inversion H0...
    repeat (rewrite app_nil_r)... }
  intros. inversion H;subst.
  pose proof H5 as H5_backup.
  apply IHK' in H5.
  { constructor...
    intros.
    destruct H2.
    - (*destructing it means we prove the first of H_ed
        is the s_pr ev of Hld*)
      inversion H5_backup...
      inversion H3...
      specialize H1 with
        (H_ld':=[]) (H_ed':=H')
        (L:=hloc_str L) (s:=s).
      assert (Tmp:[(L, stack s)] = [(L, stack s)])...
    - inversion H3... }
  (*also use H1 here *)
  intros. inversion H4...
  apply H1 with
    (H_ld':=(hloc_str L,stack s)
              :: H_ld')
    (H_ed':=H_ed'0) (L:=L0)...
Qed.
(*Lemma eval_ctx_split_already :
  forall C_mem K' K H_ld H_ed,
    LS_rel_eval_ctx C_mem
      (K' ++ K) (H_ld ++ H_ed) ->
    LS_rel_eval_ctx C_mem K' H_ld
    /\ LS_rel_eval_ctx C_mem K H_ed.
Proof with super_a.
  intros. generalize dependent H_ld.
  induction K'.
  { intros. split...
Qed.
Lemma eval_ctx_recompose :
  forall C_mem K' K H_ld H_ed frm a,
    LS_rel_eval_ctx C_mem K' H_ld ->
    LS_rel_eval_ctx C_mem (frm :: K) (a :: H_ed) ->
    LS_rel_eval_ctx C_mem
      (K' ++ frm :: K) (H_ld ++ a :: H_ed) ->
    LS_rel_eval_ctx C_mem (K' ++ [frm]) (H_ld ++ [a])
    /\ LS_rel_eval_ctx C_mem K H_ed.
Proof with super_a.
  intros. split;inversion H0...
  assert (K' ++ frm :: K
          = K' ++ [frm] ++ K)...
  rewrite H2 in H1.
  assert (H_ld ++ (hloc_str L,stack s)
            :: H_ed
          = H_ld ++ [(hloc_str L,stack s)]
              ++ H_ed)...
  rewrite H3 in H1.
  repeat (rewrite app_assoc in H1).
  apply eval_ctx_app_split in H1.
  destruct H1 as
    [Hld [Hed [hyp1 [hyp2 hyp3]]]].
  assert (Hed = H_ed).
  { generalize dependent H_ed.
    generalize dependent Hed.
    induction K.
    - intros.
      inversion H7...
      inversion hyp2...
    - intros.
      apply IHK...
      + 
      3:{
      +
      + inversion H7...
      super_a.}
  apply eval_ctx_last_label in hyp1.
Qed.*)

(*what I really need is just to prove that frm1 points
to frm2, so that the s_prev and L_prev that we obtain
is indeed what we have for frm2*)
Lemma eval_ctx_app_2_middle :
  forall C_mem K K' frm1 frm2 H,
    LS_rel_eval_ctx C_mem
      (K' ++ frm1 :: frm2 :: K) H ->
    is_hdllst_general frm1 = true ->
    is_hdllst_general frm2 = true ->
    exists s1 s2 H_ld H_ed,
      LS_rel_eval_ctx C_mem (K' ++ [frm1])
        (H_ld ++ [(frm_to_hloc frm1,stack s1)])
      /\ LS_rel_eval_ctx C_mem (frm2 :: K)
           ((frm_to_hloc frm2,stack s2) :: H_ed)
      /\ H = H_ld ++ (frm_to_hloc frm1,stack s1)
               :: (frm_to_hloc frm2,stack s2) :: H_ed
      /\ stk_points_to s1 s2 (frm_to_hloc frm2).
Proof with super_a.
  intros. generalize dependent H.
  induction K'.
  { intros. inversion H0...
    inversion H6...
    exists s,s0,sh_empty,H.
    inversion H7;subst;
    inversion H5;subst;
    inversion H10;subst;
    inversion H14... }
  intros. inversion H0...
  apply IHK' in H6.
  destruct H6 as
    [s1 [s2 [H_ld [H_ed hyp]]]].
  destruct hyp as [hyp1 [hyp2 [hyp3 hyp4]]].
  exists s1,s2,((hloc_str L,stack s)
                  :: H_ld),H_ed...
  intros. destruct H_ld;inversion H...
  - eapply H9...
  - eapply H9...
Qed.
 (* intros.
  apply eval_ctx_app_split in H0.
  destruct H0 as
    [H_ld [H_ed [hyp1 [hyp2 hyp3]]]].
  
  (* get s1 and H_ld *)
  destruct frm1 as
    [[[L] L_env lab_op A] alst].
  destruct A...
  pose proof hyp1 as hyp4.
  apply eval_ctx_last_label in hyp4.
  destruct hyp4 as
    [H_ld' [s1 [hyp4 hyp5]]].
  (* get s2 and H_ed *)
  inversion hyp2...
  exists s1,s,H_ld',H;
    inversion H5;
    inversion H6...
  - rewrite <- app_assoc...
  - apply eval_ctx_app_split in H0_backup.
    destruct H0_backup as
      [H_ld'' [H_ed'' [_ [hy1 hy2]]]]...
    inversion hy1...
    inversion H11...
    (**88888888888888888888*)
    assert (Tmp:K' ++ frm1 :: frm2 :: K
                = (K' ++ [frm1]) ++ frm2 :: K).
  { rewrite <- app_assoc... }
  pose proof H0 as H0_backup.
  rewrite Tmp in H0.
  apply eval_ctx_app_split in H0.
  destruct Tmp.
  destruct H0 as
    [H_ld [H_ed [hyp1 [hyp2 hyp3]]]].
  (* get s1 and H_ld *)
  destruct frm1 as
    [[[L] L_env lab_op A] alst].
  destruct A...
  pose proof hyp1 as hyp4.
  apply eval_ctx_last_label in hyp4.
  destruct hyp4 as
    [H_ld' [s1 [hyp4 hyp5]]].
  (* get s2 and H_ed *)
  inversion hyp2...
  exists s1,s,H_ld',H;
    inversion H5;
    inversion H6...
  - rewrite <- app_assoc...
  - apply eval_ctx_app_split in H0_backup.
    destruct H0_backup as
      [H_ld'' [H_ed'' [_ [hy1 hy2]]]]...
    inversion hy1...
    assert (H0 = (L
    inversion H11...
    
Qed.*)
(*
Lemma eval_ctx_app_middle :
  forall C_mem K' K H L L_env lab_op alst,
    LS_rel_eval_ctx C_mem
      ((K' ++
          [hdl_led_lst
             (L.handler_f (L.hdl_lab L)
                L_env lab_op L.general)
             alst]) ++ K) H ->
    exists s H_ld H_ed,
      LS_rel_eval_ctx C_mem K'
        (H_ld ++ [(hloc_str L,stack s)])
      /\ LS_rel_eval_ctx C_mem K H_ed
      /\ H = H_ld ++ [(hloc_str L,
                        stack s)] ++ H_ed.
Proof with super_a.
  intros. apply eval_ctx_app_split in H0.
  destruct H0 as
    [H_ld [H_ed [h1 [h2 h3]]]]...
    generalize dependent H.
  induction K'.
  { intros.
    exists sh_empty,H... }
  intros. inversion H0...
  apply IHK' in H4.
  destruct H4 as
    [H_ld [H_ed [hyp1 [hyp2 hyp3]]]].
  exists ((hloc_str L,stack s)
            :: H_ld),H_ed...
  intros. eapply H7...
Qed.

Lemma eval_ctx_app_middle :
  forall C_mem hf_top hf alst_top alst_mid alst
         K' K H L L_env lab_op,
    LS_rel_eval_ctx C_mem
      (K' ++
         L.hdl_led_lst (L.handler_f (L.hdl_lab L)
                          L_env lab_op L.general) alst_mid
          :: K) H ->
    exists s H_ld H_ed,
      LS_rel_eval_ctx C_mem
        (K' ++
           [L.hdl_led_lst (L.handler_f (L.hdl_lab L)
                             L_env lab_op L.general) alst_mid])
        (H_ld ++ [(hloc_str L,stack s)])
      /\ LS_rel_eval_ctx C_mem K H_ed
      /\ H = H_ld ++ [(hloc_str L,stack s)] ++ H_ed.
Proof with super_a.
  intros. generalize dependent H.
  induction K'.
  { intros. inversion H0...
    inversion H4...
    assert (L1 = L).
    { inversion H8...
      inversion H11... }(*
    inversion H... inversion H6...
    inversion H2...*)
    exists s0,[(hloc_str L0,stack s)],H.
    split... intros. inversion H1... }
  intros.
  cbn in IHK'.
  inversion H0...
  inversion H4...
  invresion H.
  inversion H6...
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
Admitted.
*)
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
Lemma update_nth_one_iter :
  forall {A} n a lst (v:A),
    update_nth (S n) (a :: lst) v = a :: update_nth n lst v.
Proof. intros. super_a. Qed.
(*Lemma update_nth_one_off :
  forall {A} n a lst (v:a),
    update_nth (S n) (a :: lst) v = a :: update_nth n lst *)
Lemma update_nth_split :
  forall {A} l1 l2 n (v:A),
    n <= Datatypes.length l2 ->
    update_nth (List.length (l1 ++ l2) - n) (l1 ++ l2) v
    = l1 ++ update_nth (List.length l2 - n) l2 v.
Proof with super_a.
  intros. induction l1;automate.
  assert (List.length ((a :: l1) ++ l2)
            = S (List.length (l1 ++ l2)));
    automate. rewrite H0.
  rewrite Nat.sub_succ_l.
  2:{ rewrite app_length... }
  rewrite <- app_comm_cons.
  rewrite update_nth_one_iter...
Qed.

(*Lemma rel_frame_inv :
   forall C_mem F s s',
    LS_rel_frame C_mem F s -> LS_rel_frame C_mem F s' ->
    s = s'.
Proof with super_a.
  intros.
  (* expand s *)
  inversion H...
  inversion H4...
  inversion H1...
  (* expand s' *)
  inversion H0...
  inversion H12...
  inversion H9...
  rewrite H8 in H13.
  rewrite H2 in H10
  - intros. inversion H. inversion H0...
  - intros. inversion H... inversion H0...
    specialize IHF with (s:=s'0) (s':=s'1).
    apply IHF in H5. inversion H3...
    inversion H4...
Qed.
Lemma rel_frames_inv :
  forall C_mem F s s',
    LS_rel_frames C_mem F s -> LS_rel_frames C_mem F s' ->
    s = s'.
Proof with super_a.
  intros C_mem F. induction F.
  - intros. inversion H. inversion H0...
  - intros. inversion H... inversion H0...
    specialize IHF with (s:=s'0) (s':=s'1).
    apply IHF in H5. inversion H3...
    inversion H4...
Qed.
Lemma push1_before_tm : forall ft lst Ilst E t,
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
      inversion H4... inversion H3...
      pose proof S_push as Hyp.
      specialize Hyp with
        (o:=reg_o r1) (j:=List.length ((s ++ s') ++ frm_stk))
        (l:=cloc C_lab (List.length lst0))
        (R:=[(ip,loc_w (cloc C_lab (List.length lst0)));
             (sp,loc_w (hloc L (List.length ((s ++ s') ++ frm_stk))));
             (r0, o0);
             (r1, val_direct_trans v
                    cur_stk_val);
             (r2, o2)] ++ R36).
      intros... cbn in Hyp.
      apply Hyp...
      rewrite H18.
      pose proof app_nth2_plus as Temp.
      specialize Temp with (l:=lst0) (l':=Ilst) (n:=0).
      rewrite PeanoNat.Nat.add_comm in Temp.
      rewrite Temp... }
    + (* prove LS_rel for v end, end of function call *)
      unfold incr_cloc,next_cloc,ns_cloc...
      inversion H5... inversion H9...
      inversion H4... inversion H3...
      rewrite app_comm_cons.
      { apply rel_LS with
          (lst:=lst0 ++ [nth 0 Ilst halt])
          (SIlst:=tl Ilst)...
        - inversion H16...
        - apply rel_env_context with
            (s_out:=s' ++ frm_stk)...
          + intros. apply H11 with (s':=s'0) (L':=L') in H1.
            rewrite <- app_assoc in H1.
            apply <- stk_points_to_preserves. apply H1.
            rewrite app_length. inversion H6... 
          + rewrite app_assoc.
            inversion H20...
            destruct v as [cst|[ind|str]]...
            rewrite <- map_nth with (d:=L.ns).
            rewrite app_nth1... inversion H10...
            rewrite List.map_length.
            inversion H2... inversion H21...
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
                       (List.length (ns :: List.map run_cst_trans E1 ++ s_out)));
              int_w 0; val_direct_trans v_env (List.map run_cst_trans E1 ++ s_out);
              loc_w (cloc lab_op 0)])...
        -- inversion H5;super_a;inversion H11...
           2:{ intros. apply H16 with (L':=L') (s':=s') in H1.
               rewrite app_comm_cons.
               apply stk_points_to_preserves...
               inversion H7...
               rewrite app_length... }
           rewrite app_comm_cons,app_assoc.
           apply rel_hdl_stk_base...
           { apply rel_frame with
                 (lst:=lst ++ firstn 5 SIlst) (Ilst:=skipn 5 SIlst);
                 inversion H10;automate.
               - pose proof term_trans_not_nil...
                 destruct (term_trans t) as []eqn:?;automate.
                 rewrite <- Heql.
                 rewrite <- PeanoNat.Nat.add_succ_comm.
                 apply rel_ins. inversion H2...
               - rewrite H15,
                   <- app_assoc...
               - rewrite app_length... }
        -- destruct v_env as [|[|]],L_env...
           rewrite app_nth1. rewrite map_nth with (d:=L.ns).
           inversion H6... rewrite H2...
           apply rel_hdl_stk_base with
             (Flst:=[]) (s:=[])...
           apply rel_hdl_general with
           (s_prev:=ns :: map run_cst_trans E1 ++ s_out).
           rewrite map_length.
           inversion H10... inversion H2...
           inversion H7... inversion H3...
        -- intros. inversion H1...
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
    inversion H9...
    inversion H4...
    inversion H7...
    inversion H6...
    specialize H11 with
      (L':=hloc_str L1) (s':=s) (H':=H1).
    assert (Temp:(hloc_str L1, stack s) :: H1
                 = (hloc_str L1, stack s) :: H1)...
    apply H11 in Temp.
    unfold stk_points_to in Temp.
    inversion Temp...
    assert (exists str num,
               loc_w (cloc str num) = hd ns s).
    { inversion H17...
      inversion H21...
      inversion H20... }
    destruct H2 as [C_lab [num s_ret_addr]].
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
        - destruct Temp.
          pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r1) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val) (s:=sp)
            (H_stk_ld:=[]) (L:=hloc_str L0)
            (H_stk_ed:=(hloc_str L1, stack s) :: H1 ++ SH_cont).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          rewrite H15. inversion H10...
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
          (H_stk_ed:= H1 ++ SH_cont)
          (H_stk_ld:=[]) (lst:=s)
          (s_fst:=[]) (L_fst:=L0)... }
      eapply multi_step.
      { assert (Tmp:s <> []).
        { induction s... } 
        eapply S_ret with
          (lst:=s)
          (H_stk':=H1 ++ SH_cont)...
        - rewrite H18. destruct s...
        - rewrite H18. rewrite Nat.sub_diag... }
      constructor.
      { rewrite <- s_ret_addr.
        apply S_push with (o:=reg_o r1)...
        inversion H17... inversion H21...
        inversion H20...
        inversion s_ret_addr...
        rewrite H26. destruct Ilst...
        rewrite nth_middle.
        cbn in H30... }
    + (* prove LS_rel for v end, leaving handler *)
      inversion H17...
      inversion H21...
      inversion H20...
      rewrite app_comm_cons.
      { eapply rel_LS with
          (lst:=lst0 ++ firstn 1 Ilst)...
        - inversion H24...
        - apply rel_env_context with
            (s_out:=s' ++ frm_stk)...
          + intros. apply H19 with (s':=s'0) (L':=L') in H2.
            rewrite <- app_assoc in H2.
            apply <- stk_points_to_preserves. apply H2.
            rewrite app_length. inversion H22... 
          + rewrite <- app_assoc.
            inversion H28...
            destruct v as [cst|[ind|str]]...
            rewrite <- map_nth with (d:=L.ns).
            rewrite app_nth1.
            inversion H10...
            rewrite List.map_length.
            inversion H10...
            inversion H3... inversion H29...
        - inversion s_ret_addr...
          inversion H24...
          destruct Ilst...
          rewrite H26. rewrite H29.
          rewrite <- app_assoc...
        - inversion s_ret_addr...
          destruct Ilst...
          rewrite app_length... }
  (* x = raise v1 v2, raising handler of current stack*)
  - destruct L as [L_str].
    destruct L_k as [L_k_str].
    inversion H5...
    inversion H11...
    inversion H6...
    inversion H7...
    specialize H16 with
      (L':=hloc_str L) (s':=s0) (H':=H1).
    assert (Temp:(hloc_str L, stack s0) :: H1
                 = (hloc_str L, stack s0) :: H1)...
    apply H16 in Temp.
    unfold stk_points_to in Temp.
    rewrite rev_app_distr in Temp.
    inversion Temp...
    remember (s ++
                [loc_w (cloc handle_loc 10);
                 loc_w (hloc L (Datatypes.length s_prev));
                 int_w 0; 
                 loc_w (hloc L_env0 0);
                 loc_w (cloc Clab_op 0)])
      as s_out.
    remember (List.map run_cst_trans E1 ++ s_out)
        as cur_stk_val.
    esplit. esplit. split.
    + eapply multi_step.
      { destruct v2 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans cst cur_stk_val)...
          cbn. rewrite H15. inversion H10... apply nth_middle.
        - destruct Temp.
          pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r2) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]) (L:=hloc_str L_str)
            (H_stk_ed:=(hloc_str L, stack s0)
                         :: H1 ++ SH_cont).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          rewrite H15. inversion H10...
          apply nth_middle.
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans (var_val var) cur_stk_val)...
          rewrite H15. inversion H10... apply nth_middle. }
      eapply multi_step.
      { destruct v1 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans cst cur_stk_val)...
        - destruct Temp.
          pose proof S_load_stk as Temp.
          specialize Temp with
            (d:=r1) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Temp.
          eapply Temp...
          rewrite H15. inversion H10...
          apply ins_verify with (n:=1).
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val var) cur_stk_val)... }
      eapply multi_step.
      { eapply S_call
          with (o:=wd_o (cloc raise_loc 0))...
        rewrite H15. inversion H10...
        apply ins_verify with (n:=2). }
      eapply multi_step.
      { eapply S_load_stk with
            (d:=r4) (s:=r1) (load_off:=0)
            (l:=cloc raise_loc 0)
            (H_stk_ld:=[])
            (lst:=loc_w (cloc Clab (3 + List.length lst))
                    :: cur_stk_val)
            (H_stk_ed:=(hloc_str L, stack s0) ::
                         H1 ++ SH_cont)...
        destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H23...
        inversion H26... inversion H25... }
      eapply multi_step.
      { eapply S_store_stk with
          (d:=r1) (load_off:=0) (o:=sp)
          (H_stk_ld:=[])
          (lst:=loc_w (cloc Clab (3 + List.length lst))
                  :: cur_stk_val)
          (H_stk_ed:=(hloc_str L, stack s0)
                       :: H1 ++ SH_cont).
        5:{ subst. rewrite app_comm_cons.
            repeat (rewrite app_length).
            rewrite Nat.add_comm... }
        super_a. super_a.
        2:{ super_a. }
        destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H23...
        inversion H26... inversion H25... }
      eapply multi_step.
      { rewrite Heqcur_stk_val,
          Heqs_out.
        repeat (rewrite app_comm_cons;
                rewrite app_assoc).
        rewrite Nat.add_0_r.
        rewrite update_nth_split with
          (l2:=[loc_w (cloc handle_loc 10);
                loc_w (hloc L (List.length s_prev));
                int_w 0;
                loc_w (hloc L_env0 0); 
                loc_w (cloc Clab_op 0)]).
        2:{ super_a. }
        apply S_mov_sp_to_cont with
          (o:=r4) (H_cont:=SH_cont) (H_stk_ed:=H1)
          (l:=cloc raise_loc 2)
          (H_stk_ld:=
             [(hloc_str L_str,
                stack (loc_w (cloc Clab (3 + Datatypes.length lst))
                         :: map run_cst_trans E1 ++ s ++
                         [loc_w (cloc handle_loc 10);
                          loc_w (hloc L_str
                                   (6 + (List.length (map run_cst_trans E1 ++ s))));
                          int_w 0;
                          loc_w (hloc L_env0 0); 
                          loc_w (cloc Clab_op 0)]))])
          (L:=L) (j:=List.length s0)
          (lst:=s0);automate.
        - (*rewrite app_comm_cons,Nat.add_0_r.*)
          rewrite <- rev_nth with (n:=3),
              rev_app_distr,rev_app_distr.
          2:{ repeat (rewrite app_length).
              rewrite Nat.add_comm... }
          cbn...
        - cbn. rewrite app_length,app_assoc,
            Nat.add_comm... }
      rewrite Nat.sub_diag,
        <-app_assoc.
      eapply multi_step.
      { eapply S_load_stk with
          (d:=r5) (s:=r1) (load_off:=3)
          (H_stk_ld:=(hloc_str L, stack s0) :: H1)
          (H_stk_ed:=SH_cont)...
        destruct v1 as [|[|]]...
        inversion H17... rewrite
          app_nth1, map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H23...
        inversion H26... inversion H25... }
      eapply multi_step.
      { apply S_malloc_c with
          (d:=r3) (i:=1) (L:=L_k_str)... }
      eapply multi_step.
      { eapply S_store_c with
          (d:=r3) (o:=r1) (j:=0)...
        - unfold th_update.
          rewrite h_eqb_refl...
        - super_a. }
      eapply multi_step.
      { eapply S_load_stk with
          (d:=r1) (s:=r1) (load_off:=2)
          (H_stk_ld:=(hloc_str L, stack (skipn 0 s0)) :: H1)
          (H_stk_ed:=SH_cont)...
        destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        rewrite map_length.
        inversion H10... inversion H23...
        inversion H26... inversion H25... }
      eapply multi_step.
      { eapply S_jmp with
          (o:=r5) (l':=cloc Clab_op 0);automate.
        repeat (rewrite Nat.sub_add_distr with
                 (m:=1) (p:=3)).
        rewrite Nat.sub_add;
          repeat (rewrite app_comm_cons).
        2:{ repeat (rewrite app_length)... }
        rewrite <- rev_nth with (n:=0),
            rev_app_distr,rev_app_distr.
        2:{ repeat (rewrite app_length).
            rewrite Nat.add_comm... }
        cbn... }
      eapply multi_step.
      { eapply S_push with (o:=r3)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
      eapply multi_step.
      { eapply S_push with (o:=r2)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
      constructor.
      { eapply S_push with (o:=r1)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
    (* prove LS_rel for raise, to handler of current stack*)
    + rewrite app_comm_cons.
      apply rel_LS with
        (lst:=[push r3;push r2;push r1])
        (SIlst:=func_term_trans 3 t1')
        (SH_cont:=
           (hloc_str L_str,
             stack (loc_w (cloc Clab (3 + Datatypes.length lst))
                      :: map run_cst_trans E1 ++ s ++
                      [loc_w (cloc handle_loc 10);
                       loc_w (hloc L_str
                                (6 + (List.length (map run_cst_trans E1 ++ s))));
                       int_w 0;
                       loc_w (hloc L_env0 0); 
                       loc_w (cloc Clab_op 0)]))
             :: SH_cont);automate.
      * inversion H14... specialize H3 with
          (x:=c_lab Clab_op).
        inversion H3... rewrite H19 in H2.
        inversion H2...        
      * repeat (rewrite Nat.sub_add_distr with
                 (m:=2) (p:=2)).
        rewrite Nat.sub_add;
          repeat (rewrite app_comm_cons).
        2:{ repeat (rewrite app_length)... }
        rewrite <- rev_nth with (n:=1),
            rev_app_distr,rev_app_distr.
        2:{ repeat (rewrite app_length).
            rewrite Nat.add_comm... }
        cbn.
        apply rel_env_context with
          (s_out:=s0)...
        destruct v2 as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns).
        rewrite app_nth1... inversion H10...
        rewrite List.map_length.
        inversion H3... inversion H25...
        inversion H28...
      * intros. inversion H13...
        inversion H26...
      * cbn. destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        2:{ rewrite map_length.
            inversion H10... inversion H23...
            inversion H26... inversion H25... }
        rewrite heap_front_update.
        assert (forall a (l : list (heap_loc * stack_heap_val)),
                   a :: l = [a] ++ l)...
        inversion H13...
        rewrite H2 with (l:=SH_cont).
        eapply rel_cont_heap with
          (SH_cont:=SH_cont)
          (H_one_cont_ld:=[])...
        { apply rel_cont_stks with (stks:=[])...
          - rewrite app_comm_cons,
             app_assoc...
            + apply rel_frame with
                (lst:=lst ++ firstn 3 SIlst)
                (Ilst:=skipn 3 SIlst);inversion H10...
              * pose proof term_trans_not_nil...
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                apply rel_ins. inversion H24...
              * rewrite H15,
                   <- app_assoc...
              * rewrite app_length...
            + assert (S (S (S (S (S (S (List.length (map run_cst_trans E1 ++ s)))))))
                      = List.length (map run_cst_trans E1 ++
                                       s ++ [ns;ns;ns;ns;ns;ns])).
              { repeat (rewrite app_length)... }
              rewrite H23.
              constructor.
          - intros. inversion H23...
            unfold stk_points_to.
            rewrite app_comm_cons,
              app_assoc,rev_app_distr...
            rewrite app_length with
              (l:=map run_cst_trans E1 ++ s),
                Nat.add_comm... }
      * inversion H13...
      * inversion H14... inversion H19.
        unfold c_comp. apply H23 in H19.
        rewrite H19... rewrite H24...
  (* x = raise v1 v2, raising handler of past stacks*)
  - destruct L as [L_str].
    destruct L_k as [L_k_str].
    destruct L_new as [L_new].
    inversion H5.
    inversion H9. inversion H3.
    (*assert (Temp:forall {A} a b (l l': list A),
               l' ++ a :: b :: l = l' ++ [a] ++ b :: l). {super_a.}
    rewrite Temp, app_assoc in H7.*)
    apply eval_ctx_app_2_middle in H7.
    2:{super_a.} 2:{ super_a. }
    (*rewrite app_comm_cons,Temp,app_assoc in H5.
    apply eval_ctx_app_split in H5.*)
    destruct H7 as
      [s1 [s2 [H_ld [H_ed hyp]]]].
    destruct hyp as [hyp1 [hyp2 [hyp3 hyp4]]].
    destruct L_env as [L_env].
    apply last_eval_ctx_rel in hyp1.
    inversion hyp1. inversion H24.
    esplit. esplit. split.
    + eapply multi_step.
      { destruct v2 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans cst cur_stk_val)...
          cbn. rewrite H15. inversion H10... apply nth_middle.
        - pose proof S_load_stk as Tmp.
          specialize Tmp with
            (d:=r2) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Tmp.
          eapply Tmp...
          + rewrite H15. inversion H10...
            apply nth_middle.
        - eapply S_mov with
            (d:=r2) (o:=val_direct_trans (var_val var) cur_stk_val)...
          rewrite H15. inversion H10... apply nth_middle. }
      eapply multi_step.
      { destruct v1 as [cst|[ind|var]].
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans cst cur_stk_val)...
        - pose proof S_load_stk as Tmp.
          specialize Tmp with
            (d:=r1) (load_off:=ind) (lst:=cur_stk_val)
            (reg_off:=List.length cur_stk_val)(s:=sp)
            (H_stk_ld:=[]).
          rewrite PeanoNat.Nat.sub_diag in Tmp.
          eapply Tmp...
          + rewrite H15. inversion H10...
            apply ins_verify with (n:=1).
        - eapply S_mov with
            (d:=r1) (o:=val_direct_trans (var_val var) cur_stk_val)... }
      eapply multi_step.
      { eapply S_call
          with (o:=wd_o (cloc raise_loc 0))...
        rewrite H15. inversion H10...
        apply ins_verify with (n:=2). }
      eapply multi_step.
      { inversion hyp3. subst.
        unfold next_cloc.
        Check S_load_stk.
        eapply S_load_stk with
          (d:=r4) (s:=r1) (load_off:=0)
          (l:=cloc raise_loc 0)
          (*R:=[(ip,loc_w (cloc raise_loc 0));
               (sp,
                 loc_w (hloc L (S (List.length
                                     cur_stk_val))));
               (r0,o0);
               (r1,val_direct_trans v1
                     (List.map run_cst_trans E1
                        ++ s0 ++
                        [loc_w (cloc handle_loc 10);
                         loc_w (hloc L_prev (Datatypes.length s_prev));
                         int_w 0; 
                         loc_w (hloc L_env 0);
                         loc_w (cloc Clab_op 0)]));
               (r2,val_direct_trans v2
                     (List.map run_cst_trans E1
                        ++ s0 ++
                        [loc_w (cloc handle_loc 10);
                         loc_w (hloc L_prev (Datatypes.length s_prev));
                         int_w 0; 
                         loc_w (hloc L_env 0);
                         loc_w (cloc Clab_op 0)]));
               (r3,o3);
               (r4,o4);
               (r5,o5);(r6,o6)]*)
          (H_stk_ld:=
             (hloc_str L,
               stack (loc_w (cloc Clab (3 + List.length lst))
                        :: map run_cst_trans E1 ++ s_out))
               :: H_ld(* ++
               [(hloc_str L_str,
                  stack
                    (s0 ++
                       [loc_w (cloc handle_loc 10);
                        loc_w (hloc L_prev (Datatypes.length s_prev));
                        int_w 0; 
                        loc_w (hloc L_env 0);
                        loc_w (cloc Clab_op 0)]))]*))
          (lst:=s0 ++
                  [loc_w (cloc handle_loc 10);
                   loc_w (hloc L_prev (List.length s_prev));
                   int_w 0; 
                   loc_w (hloc L_env 0);
                   loc_w (cloc Clab_op 0)])
          (*H_stk_ed:=H_ed ++ SH_cont*)...
        - destruct v1 as [|[|]]...
          inversion H17... rewrite app_nth1,
            map_nth with (d:=L.ns),H2...
          rewrite map_length.
          inversion H10... inversion H3...
          inversion H7... inversion H6...
        - repeat (rewrite <- app_assoc)... }      
      eapply multi_step.
      { eapply S_store_stk with
          (d:=r1) (load_off:=0) (o:=sp)
          (H_stk_ld:=
             (hloc_str L,
               stack (loc_w (cloc Clab (3 + List.length lst))
                        :: map run_cst_trans E1 ++ s_out))
               :: H_ld)
          (L:=L_str)
          (*lst:=s_md)
          (H_stk_ed:=H_ed ++ SH_cont*)...
        - destruct v1 as [|[|]]...
          inversion H17... rewrite app_nth1,
            map_nth with (d:=L.ns),H2...
          rewrite map_length.
          inversion H10... inversion H3...
          inversion H7... inversion H6...
        - repeat (rewrite <- app_assoc)...
        - rewrite app_length... }
      rewrite <- H22.
      rewrite Nat.add_0_r.
      rewrite update_nth_split with
        (l2:=frm_stk).
      2:{ super_a. } rewrite <- H26.
      inversion hyp2.
      (*assert (hloc_str L0 = L_prev /\
             s1 = s_prev).
      { 

        rewrite app_comm_cons in H5.
        apply eval_ctx_app_split in H5.
        destruct H5 as
          [H_ld'' [H_ed' [hy1 [hy2 hy3]]]].
        subst. inversion hy2;subst.
        inversion H4;subst.
        assert ((hloc_str L2,stack s2) :: H2
                = (hloc_str L2,stack s2) :: H2);trysolve.
        apply H7 in H1. unfold stk_points_to in H1.
      }*)
      
      eapply multi_step.
      { repeat (rewrite app_comm_cons).
        rewrite app_assoc.

        Check S_mov_sp_to_cont.
        
        
        eapply S_mov_sp_to_cont with
          (o:=r4) (H_cont:=SH_cont) (H_stk_ed:=H_ed)
          (l:=cloc raise_loc 2)
          (H_stk_ld:=(*what we put to cont*)
             (hloc_str L,
               stack (loc_w (cloc Clab (3 + List.length lst))
                        :: map run_cst_trans E1 ++ s_out))
               :: H_ld ++
               [(hloc_str L_str,
                  stack (s0 ++ [loc_w (cloc handle_loc 10);
                                loc_w (hloc L_out
                                         (S (List.length (map run_cst_trans E1 ++ s))));
                                int_w 0;
                                loc_w (hloc L_env 0); 
                                loc_w (cloc Clab_op 0)]))])
          (*top stack not in cont*)
          (L:=L_new)
          (lst:=s2)...
        
          (*H_stk_ld:=
             [(hloc_str L_str,
                stack (loc_w (cloc Clab (3 + Datatypes.length lst))
                         :: map run_cst_trans E1 ++ s ++
                         [loc_w (cloc handle_loc 10);
                          loc_w (hloc L_str
                                   (6 + (List.length (map run_cst_trans E1 ++ s))));
                          int_w 0;
                          loc_w (hloc L_env0 0); 
                          loc_w (cloc Clab_op 0)]))])
          (L:=L) (j:=List.length s0)
          (lst:=s0*)
        - (*we placed L_prev s_prev in r4*)
          (*rewrite app_comm_cons,Nat.add_0_r.*)
          rewrite <- rev_nth with (n:=3),
              rev_app_distr.
          2:{ repeat (rewrite app_length).
              rewrite Nat.add_comm... }
          unfold stk_points_to in hyp4.
          rewrite rev_app_distr in hyp4.
          inversion hyp4...
        - unfold stk_points_to in hyp4.
          rewrite rev_app_distr in hyp4.
          inversion hyp4...
          rewrite <- app_assoc... }
      rewrite Nat.sub_diag.
      eapply multi_step.
      { Check S_load_stk.
        eapply S_load_stk with
          (d:=r5) (s:=r1) (load_off:=3)
          (H_stk_ld:=
             (hloc_str L_new, stack s2) :: H_ed
               ++ (hloc_str L,
                 stack (loc_w (cloc Clab (3 + List.length lst))
                          :: map run_cst_trans E1 ++ s_out))
               :: H_ld)
          (L:=L_str)
          (H_stk_ed:=SH_cont)...
        - destruct v1 as [|[|]]...
          inversion H17...
          rewrite app_nth1,
            map_nth with (d:=L.ns),H2...
          rewrite map_length.
          inversion H10... inversion H3...
          inversion H7... inversion H6...
        - repeat (rewrite <- app_assoc)... }
      eapply multi_step.
      { apply S_malloc_c with
          (d:=r3) (i:=1) (L:=L_k_str)... }
      eapply multi_step.
      { eapply S_store_c with
          (d:=r3) (o:=r1) (j:=0)...
        - unfold th_update.
          rewrite h_eqb_refl...
        - super_a. }
      eapply multi_step.
      { cbn. eapply S_load_stk with
          (d:=r1) (s:=r1) (load_off:=2)
           (H_stk_ld:=
             (hloc_str L_new, stack s2) :: H_ed
               ++ (hloc_str L,
                 stack (loc_w (cloc Clab (3 + List.length lst))
                          :: map run_cst_trans E1 ++ s_out))
               :: H_ld)
          (H_stk_ed:=SH_cont)...
        - destruct v1 as [|[|]]...
          inversion H17... rewrite app_nth1,
            map_nth with (d:=L.ns),H2...
          rewrite map_length.
          inversion H10... inversion H3...
          inversion H7... inversion H6...
        - repeat (rewrite <-app_assoc)... }
      (* finish up till here, ??????!!!!!!---<<<>>>>>>><<<<

copy and paste both versions (no need for call, only jump)
 (o:=r5) (lsp:=match H_ld with
                        | [] => L_prev
                        | _::_ => L_prev0
                        end)
          (lst:=match H_ld with
                        | [] => s_prev
                        | _::_ => s_prev0
                        end).*)
      eapply multi_step.
      { eapply S_jmp with
          (o:=r5) (l':=cloc Clab_op 0);automate.
        repeat (rewrite Nat.sub_add_distr with
                 (m:=1) (p:=3)).
        rewrite Nat.sub_add;
          repeat (rewrite app_comm_cons).
        2:{ repeat (rewrite app_length)... }
        rewrite <- rev_nth with (n:=0),
            rev_app_distr,rev_app_distr.
        2:{ repeat (rewrite app_length).
            rewrite Nat.add_comm... }
        cbn... }
      
    (*inversion H7...
    specialize H16 with
      (L':=hloc_str L) (s':=s0) (H':=H1).
    assert (Temp:(hloc_str L, stack s0) :: H1
                 = (hloc_str L, stack s0) :: H1)...
    apply H16 in Temp.
    unfold stk_points_to in Temp.
    rewrite rev_app_distr in Temp.
    inversion Temp...*)
    
      
      eapply multi_step.
      { eapply S_push with (o:=r3)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
      eapply multi_step.
      { eapply S_push with (o:=r2)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
      constructor.
      { eapply S_push with (o:=r1)...
        unfold c_comp. inversion H14...
        inversion H19.
        apply H23 in H19.
        rewrite H19,H24... }
    (* prove LS_rel for raise, to handler of current stack*)
    + rewrite app_comm_cons.
      apply rel_LS with
        (lst:=[push r3;push r2;push r1])
        (SIlst:=func_term_trans 3 t1')
        (SH_cont:=
           (hloc_str L_str,
             stack (loc_w (cloc Clab (3 + Datatypes.length lst))
                      :: map run_cst_trans E1 ++ s ++
                      [loc_w (cloc handle_loc 10);
                       loc_w (hloc L_str
                                (6 + (List.length (map run_cst_trans E1 ++ s))));
                       int_w 0;
                       loc_w (hloc L_env0 0); 
                       loc_w (cloc Clab_op 0)]))
             :: SH_cont);automate.
      * inversion H14... specialize H3 with
          (x:=c_lab Clab_op).
        inversion H3... rewrite H19 in H2.
        inversion H2...        
      * repeat (rewrite Nat.sub_add_distr with
                 (m:=2) (p:=2)).
        rewrite Nat.sub_add;
          repeat (rewrite app_comm_cons).
        2:{ repeat (rewrite app_length)... }
        rewrite <- rev_nth with (n:=1),
            rev_app_distr,rev_app_distr.
        2:{ repeat (rewrite app_length).
            rewrite Nat.add_comm... }
        cbn.
        apply rel_env_context with
          (s_out:=s0)...
        destruct v2 as [cst|[ind|str]]...
        rewrite <- map_nth with (d:=L.ns).
        rewrite app_nth1... inversion H10...
        rewrite List.map_length.
        inversion H3... inversion H25...
        inversion H28...
      * intros. inversion H13...
        inversion H26...
      * cbn. destruct v1 as [|[|]]...
        inversion H17... rewrite app_nth1,
          map_nth with (d:=L.ns),H3...
        2:{ rewrite map_length.
            inversion H10... inversion H23...
            inversion H26... inversion H25... }
        rewrite heap_front_update.
        assert (forall a (l : list (heap_loc * stack_heap_val)),
                   a :: l = [a] ++ l)...
        inversion H13...
        rewrite H2 with (l:=SH_cont).
        eapply rel_cont_heap with
          (SH_cont:=SH_cont)
          (H_one_cont_ld:=[])...
        { apply rel_cont_stks with (stks:=[])...
          - rewrite app_comm_cons,
             app_assoc...
            + apply rel_frame with
                (lst:=lst ++ firstn 3 SIlst)
                (Ilst:=skipn 3 SIlst);inversion H10...
              * pose proof term_trans_not_nil...
                destruct (term_trans t) as []eqn:?;automate.
                rewrite <- Heql.
                rewrite <- PeanoNat.Nat.add_succ_comm.
                apply rel_ins. inversion H24...
              * rewrite H15,
                   <- app_assoc...
              * rewrite app_length...
            + assert (S (S (S (S (S (S (List.length (map run_cst_trans E1 ++ s)))))))
                      = List.length (map run_cst_trans E1 ++
                                       s ++ [ns;ns;ns;ns;ns;ns])).
              { repeat (rewrite app_length)... }
              rewrite H23.
              constructor.
          - intros. inversion H23...
            unfold stk_points_to.
            rewrite app_comm_cons,
              app_assoc,rev_app_distr...
            rewrite app_length with
              (l:=map run_cst_trans E1 ++ s),
                Nat.add_comm... }
      * inversion H13...
      * inversion H14... inversion H19.
        unfold c_comp. apply H23 in H19.
        rewrite H19... rewrite H24...



-----!!!???

  
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



      ---------------------------------------
           (*H_one_cont:=
             [(hloc_str L_str,
                stack
                  (loc_w (hloc L_str
                     (S (Datatypes.length
                           (map run_cst_trans E1 ++ s ++
                              [loc_w (cloc handle_loc 10);
                               loc_w (hloc L (List.length s_prev));
                               int_w 0;
                               loc_w (hloc L_env0 0); 
                               loc_w (cloc Clab_op 0)]))))
                     :: map run_cst_trans E1 ++ s ++
                     [loc_w (cloc handle_loc 10);
                      loc_w (hloc L (List.length s_prev));
                      int_w 0;
                      loc_w (hloc L_env0 0); 
                      loc_w (cloc Clab_op 0)]))]*)
        

        intros. exists [],SH_cont. split.
        -- inversion H2... unfold ch_update in H24.
           { destruct (L.h_eqb (obj_lab L_k_str)
                         (obj_lab L_rsp)) as []eqn:?.
             - inversion H24... inversion H25...
               inversion H30...
               destruct H_one_cont_ld;
                 inversion H29...
               2:{ destruct H_one_cont_ld... }
               inversion H31... inversion H34...
               inversion H33...
               assert (s = s').
               { inversion H37...
                 - inversion H4...
                 -  inversion H4...
                   (* alst_to_cont is s, and alst_to_cont is s', we prove*)
           cbn.
        rewrite H18... destruct Ilst... rewrite <- app_assoc...
      * rewrite H22, app_length... 
        --
        -- intros. apply H11 with (s':=s'0) (L':=L') in H1.
           rewrite <- app_assoc in H1.
           apply <- stk_points_to_preserves. apply H1.
           rewrite app_length. inversion H6... 
        
   

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




