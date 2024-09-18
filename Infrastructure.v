Require Import Logic.FunctionalExtensionality.
Require Import Lia.
Require Import PeanoNat.
From LSEH Require Import RelConfig.
Import Lists.List. Import ListNotations.
Import Strings.String. Import LexaToSalt.
Import Lexa. Import Salt.
Ltac trysolve :=
  try easy;try discriminate;
  try congruence;try tauto;
  try lia;auto;eauto.
Ltac automate :=
  repeat (trysolve;try constructor;trysolve;subst).
Ltac super_a :=
  repeat (automate;cbn).

(* ---------------------------------------------------------
   ------------------ Lemmas for Salt ----------------------
   --------------------------------------------------------- *)
Lemma h_eqb_refl : forall (a:heap_loc), a = a -> h_eqb a a = true.
Proof. intros. unfold h_eqb. destruct a. apply PeanoNat.Nat.eqb_refl. Qed.
Lemma c_eqb_refl : forall (a:code_loc), a = a -> c_eqb a a = true.
Proof. intros. unfold h_eqb. destruct a. apply eqb_refl. Qed.

Theorem heap_front_update : forall H a v1 v2,
  (a !->t v1; a !->t v2; H) = (a !->t v1; H).
Proof with super_a.
  intros. unfold th_update. extensionality x. destruct (h_eqb a x)...
Qed.

(* ---------------------------------------------------------
                       Some Useful Lemmas for
                     Proving Condition 1 and 3
   --------------------------------------------------------- *)
Lemma one_eval_ctx_rel :
  forall frm frm_lst C_mem L,
    (LS_rel_hdl L frm frm_lst
     /\ is_h_frm_general_hdl frm = true)
    <->
    LS_rel_eval_ctx C_mem [hdl_led_lst frm []]
      [(hloc_num L,stack frm_lst)].
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
(* ---------------------------------------------------------
   ------ Some Basic Lemmas for Proving Condition 3 --------
   --------------------------------------------------------- *)
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
    (forall ind:nat, v = ind_val ind -> ind < List.length E) ->
    val_direct_trans v (List.map run_cst_trans E ++ lst)
    = run_cst_trans (L.var_deref E v).
Proof with super_a.
  intros. destruct v as [|[]]...
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

(* ---------------------------------------------------------
                   Lemmas for Working with 
            Evaluation Context and Continuations
   --------------------------------------------------------- *)
Definition get_hdl_lab (hdl_frm_lst:hdl_led_frm_lst) : nat :=
  match hdl_frm_lst with
  | hdl_led_lst (hdl_f (hdl_lab L) _ _ _) _ => L
  end.
Definition frm_to_hloc frm :=
  hloc_num (get_hdl_lab frm).
Definition is_hdllst_general hdl_lst:=
  match hdl_lst with
  | hdl_led_lst frm alst =>
      is_h_frm_general_hdl frm
  end.
Lemma last_eval_ctx_rel :
  forall s L frm C_mem Ks H,
    LS_rel_eval_ctx C_mem
      (Ks ++ [frm])
      (H ++ [(hloc_num L,stack s)]) ->
    is_hdllst_general frm = true ->
    LS_rel_hdl_stk C_mem L
      frm (stack s)
    /\ L = get_hdl_lab frm.
Proof with super_a.
  intros.
  destruct frm as
    [[[L_h] L_env lab_op []] alst];
    trysolve.
  generalize dependent H.
  induction Ks.
  - intros.
    destruct H.
    2:{ apply length_ctx_stk in H0.
        rewrite app_length in H0.
        rewrite Nat.add_comm in H0.
        cbn in H0... }
    inversion H0...
    inversion H8...
    inversion H5...
  - intros. inversion H0;subst.
    destruct H;inversion H5;
      subst;trysolve.
    inversion H6.
    destruct Ks...
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
  exists ((hloc_num L,stack s)
            :: H_ld),H_ed...
  intros. eapply H7...
Qed.
Lemma eval_ctx_last_label :
  forall C_mem H K' L frm,
    LS_rel_eval_ctx C_mem
      (K' ++ [frm]) H ->
    is_hdllst_general frm = true ->
    L = get_hdl_lab frm ->
    exists H' s,
      H = H' ++ [(hloc_num L,
                   stack s)]
      /\ 1 < List.length s.
Proof with super_a.
  intros.
  destruct frm as
    [[[L_h] L_env lab_op []] alst]...
  generalize dependent H.
  induction K'.
  { intros. 
    inversion H0...
    exists sh_empty,s.
    apply length_ctx_stk in H0.
    inversion H5;inversion H6;
    inversion H10...
    rewrite app_length... }
  intros. inversion H0...
  apply IHK' in H5.
  destruct H5 as [H' [s' [h1 h2]]].
  exists ((hloc_num L, stack s) :: H'),s'...
Qed.

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
        (L:=hloc_num L) (s:=s).
      assert (Tmp:[(L, stack s)] = [(L, stack s)])...
    - inversion H3... }
  (*also use H1 here *)
  intros. inversion H4...
  apply H1 with
    (H_ld':=(hloc_num L,stack s)
              :: H_ld')
    (H_ed':=H_ed'0) (L:=L0)...
Qed.
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
  exists s1,s2,((hloc_num L,stack s)
                  :: H_ld),H_ed...
  intros. destruct H_ld;inversion H...
  - eapply H9...
  - eapply H9...
Qed.
Lemma app_inv_length_ld :
  forall {A:Type} (l1 l2 l3 l4:list A),
    l1 ++ l2 = l3 ++ l4 ->
    List.length l2 = 5 ->
    List.length l4 = 5->
    l1 = l3.
Proof with super_a.
  intros.
  assert (forall {A:Type} (l1 l2:list A),
             l1 = l2 -> List.length l1
                        = List.length l2)...
  pose proof H as H3.
  apply H2 in H3.
  apply app_inv_tail with (l:=l2).
  repeat (rewrite app_length in H3).
  repeat (destruct l2 as [|];super_a).
  repeat (destruct l4 as [|];super_a).
  rewrite H. generalize dependent l1.
  induction l3...
  - destruct l1...
  - intros. destruct l1.
    + inversion H3...
    + rewrite IHl3 with
        (l1:=l1)...
      inversion H...
Qed.
Lemma app_inv_length_ed :
  forall {A:Type} (l1 l2 l3 l4:list A),
    l1 ++ l2 = l3 ++ l4 ->
    List.length l2 = 5 ->
    List.length l4 = 5->
    l2 = l4.
Proof with super_a.
  intros.
  pose proof H.
  apply app_inv_length_ld in H...
  eapply app_inv_head...
Qed.
Lemma eval_ctx_last_points_to_preserves :
  forall C_mem K H L s frmlst1 frmlst2 frm alst,
    LS_rel_eval_ctx C_mem
      (K ++ [hdl_led_lst frm alst])  
      (H ++ [(hloc_num L, stack (s ++ frmlst1))]) ->
    LS_rel_hdl L frm frmlst1 ->
    LS_rel_hdl L frm frmlst2 ->
    LS_rel_eval_ctx C_mem
      (K ++ [hdl_led_lst frm alst])  
      (H ++ [(hloc_num L, stack (s ++ frmlst2))]).
Proof with super_a.
  intros. inversion H1...
  inversion H2...
  generalize dependent K.
  induction H...
  - intros.
    inversion H0...
    inversion H8...
    inversion H5...
    + apply app_inv_length_ld
        in H...
    + inversion H5...
      apply app_inv_length_ed
        in H...
  - intros.
    destruct K;
      inversion H0;subst.
    { inversion H8.
      destruct H... }
    apply IHlist in H8.
    constructor...
    destruct H. 
    + intros. 
      inversion H...
      unfold stk_points_to.
      rewrite app_length.
      assert (stk_points_to s0
                (s ++
                   [loc_w (cloc handle_loc 10);
                    loc_w (hloc L_prev (Datatypes.length s_prev));
                    int_w 0; 
                    loc_w (hloc L_env 0);
                    loc_w (cloc Clab_op 0)]) L).
      { apply H10 with (H':=[])... }
      unfold stk_points_to in H3.
      rewrite app_length in H3...
    + intros. inversion H3...
      apply H10 with
        (H':=H ++
               [(hloc_num L,
                  stack (s ++
                           [loc_w (cloc handle_loc 10);
                            loc_w (hloc L_prev (Datatypes.length s_prev));
                            int_w 0; 
                            loc_w (hloc L_env 0);
                            loc_w (cloc Clab_op 0)]))])...
Qed.

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
Lemma update_nth_length :
  forall {A} n l (v:A),
    List.length (update_nth n l v)
    = List.length l.
Proof with super_a.
  intros. generalize dependent n.
  induction l;destruct n...
Qed.
Lemma tup_heap_nil_split :
  forall H1 H2 L,
    th_comp H1 H2 L = tuple [] ->
    H1 L = tuple [] /\ H2 L = tuple [].
Proof with super_a.
  intros. split;
    unfold th_comp in H;
    destruct (H1 L) as []eqn:?;
                         destruct l...
Qed.
Lemma th_comp_comm_th_update :
  forall x v H1 H2,
    H2 x = tuple [] ->
    th_comp (x !->t v; H1) H2 =
      (x !->t v; th_comp H1 H2).
Proof with super_a.
  intros. extensionality x'.
  unfold th_comp,th_update,
    h_eqb. destruct x as [x],x' as [x'].
  destruct (x =? x') as []eqn:?...
  rewrite Nat.eqb_eq in Heqb.
  destruct v as [[|]]...
Qed.
Lemma cont_heap_split :
  forall C_mem LH_cont_ld LH_cont_ed
         SH_cont SH_ctup,
    (*L_last is label of last stack
      in the Ks*)
    LS_rel_cont_heap C_mem
      (LH_cont_ld ++ LH_cont_ed)
      (SH_cont,SH_ctup) ->
    exists SH_cont_ld SH_cont_ed
           SH_ctup_ld SH_ctup_ed,
      LS_rel_cont_heap C_mem LH_cont_ld
        (SH_cont_ld,SH_ctup_ld)
      /\ LS_rel_cont_heap C_mem LH_cont_ed
           (SH_cont_ed,SH_ctup_ed)
      /\ SH_cont = SH_cont_ld ++ SH_cont_ed
      /\ SH_ctup = th_comp SH_ctup_ld SH_ctup_ed
      /\ (forall L,
             SH_ctup_ed L = tuple []
             \/ SH_ctup_ld L = tuple []).
(*can't both be non nil.
if ed not nil then ld is nil
if ld not nil then ed nil
at least one is nil*)
Proof with super_a.
  intros.
  generalize dependent SH_cont.
  generalize dependent SH_ctup.
  induction LH_cont_ld.
  - intros.
    exists sh_empty,SH_cont,
      th_empty,SH_ctup...
  - intros. inversion H...
    apply IHLH_cont_ld in H4.
    destruct H4 as
      [SH_cont_ld' [SH_cont_ed' [SH_ctup_ld' [SH_ctup_ed' hyp]]]].
    destruct hyp as
      [hyp1 [hyp2 [hyp3 [hyp4 hyp5]]]].
    exists
      ((H_one_cont_ld ++ [(L_last,stack s_last)]) ++ SH_cont_ld'),
      SH_cont_ed',
      (L_rsp !->t tuple [loc_w (hloc L_last 4)];
       SH_ctup_ld'),
      SH_ctup_ed'.
    repeat split;trysolve.
    + econstructor...
      apply tup_heap_nil_split in H7...
    + super_a. rewrite app_assoc...
    + extensionality x.
      unfold th_update,th_comp.
      destruct (h_eqb L_rsp x)...
    + intros.
      destruct (h_eqb L_rsp L) as []eqn:?.
      * left...
        apply tup_heap_nil_split in H7...
        destruct L as [L].
        inversion Heqb.
        apply Nat.eqb_eq in H1...
      * destruct hyp5 with (L:=L).
        -- left...
        -- right... unfold th_update.
           rewrite Heqb...
Qed.
Lemma cont_heap_app :
  forall C_mem LH_cont_ld LH_cont_ed
         SH_cont_ld SH_cont_ed
         SH_ctup_ld SH_ctup_ed,
    (*L_last is label of last stack
      in the Ks*)
    LS_rel_cont_heap C_mem LH_cont_ld
      (SH_cont_ld,SH_ctup_ld) ->
    LS_rel_cont_heap C_mem LH_cont_ed
      (SH_cont_ed,SH_ctup_ed) ->
    (forall L,
        SH_ctup_ed L = tuple []
        \/ SH_ctup_ld L = tuple []) ->
    LS_rel_cont_heap C_mem
      (LH_cont_ld ++ LH_cont_ed)
      (SH_cont_ld ++ SH_cont_ed,
        th_comp SH_ctup_ld SH_ctup_ed).
Proof with super_a.
  intros.
  generalize dependent SH_cont_ld.
  generalize dependent SH_ctup_ld.
  induction LH_cont_ld;
    intros;inversion H...
  apply IHLH_cont_ld in H6.
  2:{ intros. specialize H1 with L.
      destruct H1.
      - left...
      - right. unfold th_update in H1.
        destruct (h_eqb L_rsp L)
          as []eqn:?... }
  rewrite <- app_assoc.
  specialize H1 with (hloc_num L_rsp).
  destruct H1.
  - rewrite th_comp_comm_th_update...
    econstructor...
    unfold th_comp.
    rewrite H9...
  - unfold th_update in H1.
    rewrite h_eqb_refl in H1...
Qed.
Lemma update_comp_cancel :
  forall L lst H1 H2,
    H1 L = tuple [] -> H2 L = tuple [] ->
    (L !->t tuple []; th_comp H1 (L !->t tuple lst; H2))
    = th_comp H1 H2.
Proof with super_a.
  intros. extensionality x.
  unfold th_update,th_comp.
  destruct L as [L],x as [x].
  destruct (h_eqb L x) as []eqn:?...
  unfold h_eqb in Heqb.
  rewrite Nat.eqb_eq in Heqb...
  rewrite H0,H...
Qed.
Lemma fresh_cont_lab_rel :
  forall L LH_cont C_mem SH_cont SH_ctup,
    fresh_cont_lab (obj_lab L) LH_cont = true ->
    LS_rel_cont_heap C_mem
      LH_cont (SH_cont,SH_ctup) ->
    SH_ctup L = tuple [].
Proof with super_a.
  intros.
  generalize dependent SH_ctup.
  generalize dependent SH_cont.
  induction LH_cont;intros;
    inversion H0...
  specialize IHLH_cont with
    (SH_cont:=SH_cont0)
    (SH_ctup:=SH_ctup0).
  unfold th_update.
  inversion H.
  destruct (L_rsp =? L) as []eqn:?...
  rewrite Heqb.
  apply IHLH_cont...
Qed.
