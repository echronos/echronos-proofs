(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_contexts_stack_inv

imports
  EChronos_arm_sched_prop_base
  EChronos_arm_sched_prop_tactic
begin

definition
  schedule
where
  "schedule \<equiv>
    \<lbrace>True\<rbrace>
    \<acute>nextT := None;;
    \<lbrace>\<acute>nextT = None\<rbrace>
    WHILE \<acute>nextT = None
    INV \<lbrace>\<acute>nextT=None \<or> ((\<exists>n. \<acute>nextT=Some n \<and> n\<in>U))\<rbrace>
    DO
      \<lbrace>True\<rbrace>
      \<acute>E_tmp := \<acute>E;;
      \<lbrace>True\<rbrace>
      \<acute>R := handle_events \<acute>E_tmp \<acute>R;;
      \<lbrace>True\<rbrace>
      \<acute>E := \<acute>E - \<acute>E_tmp;;
      \<lbrace>True\<rbrace>
      \<acute>nextT := sched_policy(\<acute>R)
    OD"

definition
  context_switch
where
  "context_switch preempt_enabled \<equiv>
    \<lbrace>\<exists>n. \<acute>nextT = Some n \<and> n \<in> U \<and> last \<acute>ATStack = \<acute>curUser\<rbrace>
    \<acute>contexts := \<acute>contexts (\<acute>curUser \<mapsto> (preempt_enabled, \<acute>ATStack));;
    \<lbrace>\<exists>n. \<acute>nextT = Some n \<and> n \<in> U\<rbrace>
    \<acute>curUser := the \<acute>nextT;;
    \<lbrace>\<acute>curUser \<in> U\<rbrace>
    \<acute>ATStack := snd (the (\<acute>contexts (\<acute>curUser)));;
    \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace>
    IF fst (the (\<acute>contexts (\<acute>curUser)))
      THEN \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace> \<langle>svc\<^sub>aEnable\<rangle>
      ELSE \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace> \<langle>svc\<^sub>aDisable\<rangle> FI"

definition
  eChronos_arm_sched_prop_contexts_stack_inv_prog
where
  "eChronos_arm_sched_prop_contexts_stack_inv_prog \<equiv>
  (hardware_init,,
   eChronos_init,,
  (COBEGIN
    (* svc\<^sub>a_take *)
    \<lbrace>svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack) \<and> svc\<^sub>s \<notin> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> (last (\<acute>AT # \<acute>ATStack) = \<acute>curUser)\<rbrace>
    WHILE True INV \<lbrace>svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack) \<and> svc\<^sub>s \<notin> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> (last (\<acute>AT # \<acute>ATStack) = \<acute>curUser)\<rbrace>
    DO
      \<lbrace>svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack) \<and> svc\<^sub>s \<notin> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> (last (\<acute>AT # \<acute>ATStack) = \<acute>curUser)\<rbrace> svc\<^sub>aTake
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    (* svc\<^sub>a *)
    \<lbrace>svc\<^sub>a \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
    WHILE True INV \<lbrace>svc\<^sub>a \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
    DO
      add_await_routine svc\<^sub>a (
      \<lbrace>svc\<^sub>a \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
      \<acute>ghostP := True;;
      add_inv_assn_com \<lbrace>\<acute>ghostP\<rbrace> (
      add_inv_assn_com \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace> (
      schedule);;
      context_switch True;;
      \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace>
       \<langle>\<acute>ghostP := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    (* svc\<^sub>s *)
    \<lbrace>svc\<^sub>s \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
    WHILE True INV \<lbrace>svc\<^sub>s \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
    DO
      add_await_routine svc\<^sub>s (
      \<lbrace>svc\<^sub>s \<in> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> last \<acute>ATStack = \<acute>curUser\<rbrace>
      \<acute>ghostS := True;;
      add_inv_assn_com \<lbrace>\<acute>ghostS\<rbrace> (
      add_inv_assn_com \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace> (
      schedule);;
      context_switch False;;
      \<lbrace>last \<acute>ATStack = \<acute>curUser\<rbrace>
       \<langle>\<acute>ghostS := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    SCHEME [user0 \<le> i < user0 + nbRoutines]
    add_inv_assn_com
     \<lbrace>svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack) \<and> svc\<^sub>s \<notin> set (\<acute>AT # \<acute>ATStack) \<longrightarrow> (last (\<acute>AT # \<acute>ATStack) = \<acute>curUser)\<rbrace> (
    \<lbrace>\<acute>ghostU i = User\<rbrace> IF (i\<in>I) THEN

    (* Interrupts *)
    \<lbrace>i\<in>I\<rbrace>
    WHILE True INV \<lbrace>i\<in>I\<rbrace>
    DO
      \<lbrace>i\<in>I\<rbrace>
      ITake i;;

      (add_await_routine i (
      add_inv_assn_com
       \<lbrace>i\<in>I\<rbrace> (
      \<lbrace>True\<rbrace>
      \<acute>E :\<in> {E'. \<acute>E \<subseteq> E'};;

      \<lbrace>True\<rbrace>
      svc\<^sub>aRequest;;

      \<lbrace>True\<rbrace>
      \<langle>IRet\<rangle>)))
    OD

    ELSE
    (* Users *)
    add_inv_assn_com
     \<lbrace>i \<in> U\<rbrace> (
    \<lbrace>\<acute>ghostU i = User\<rbrace>
    WHILE True INV \<lbrace>\<acute>ghostU i = User\<rbrace>
    DO
      (add_await_routine i (
      \<lbrace>\<acute>ghostU i = User\<rbrace>
      \<acute>userSyscall :\<in> {SignalSend, Block};;

      \<lbrace>\<acute>ghostU i = User\<rbrace>
      IF \<acute>userSyscall = SignalSend
      THEN
        \<lbrace>\<acute>ghostU i = User\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        add_inv_assn_com
          \<lbrace>\<acute>ghostU i = Syscall\<rbrace> (
        \<lbrace>True\<rbrace>
        \<acute>R :\<in> {R'. \<forall>i. \<acute>R i = Some True \<longrightarrow> R' i = Some True};;

        \<lbrace>True\<rbrace>
        svc\<^sub>aRequest;;

        \<lbrace>True\<rbrace>
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>);;
        \<lbrace>\<acute>ghostU i = User\<rbrace>
        WHILE \<acute>svc\<^sub>aReq INV \<lbrace>\<acute>ghostU i = User\<rbrace>
        DO
          \<lbrace>\<acute>ghostU i = User\<rbrace> SKIP
        OD
      ELSE \<lbrace>\<acute>ghostU i = User\<rbrace> IF \<acute>userSyscall = Block
      THEN
        \<lbrace>\<acute>ghostU i = User\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<acute>R := \<acute>R (i := Some False);;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Yield),, SVC\<^sub>s_now\<rangle>;;

        \<lbrace>\<acute>ghostU i = Yield\<rbrace>
        \<acute>ghostU := \<acute>ghostU (i := Syscall);;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>;;
        \<lbrace>\<acute>ghostU i = User\<rbrace>
        WHILE \<acute>svc\<^sub>aReq INV \<lbrace>\<acute>ghostU i = User\<rbrace>
        DO
          \<lbrace>\<acute>ghostU i = User\<rbrace> SKIP
        OD
      FI FI))
    OD)
    FI)
    \<lbrace>False\<rbrace>
  COEND))"

(*--------------------------------------------------------------------------*)
subsection \<open>The proof\<close>

lemmas eChronos_arm_sched_prop_contexts_stack_inv_prog_defs =
                    eChronos_arm_sched_prop_base_defs
                    eChronos_arm_sched_prop_contexts_stack_inv_prog_def
                    schedule_def context_switch_def

lemma eChronos_arm_sched_prop_contexts_stack_inv_proof:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and>
   (\<forall>i \<in> U. \<exists>j \<in> U. snd (the (\<acute>contexts i)) = [j]) \<and>
   \<acute>ghostP_S_stack_inv\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>contexts_stack_inv\<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_contexts_stack_inv_prog
  \<lbrace>False\<rbrace>"
(*<*)
  unfolding eChronos_arm_sched_prop_contexts_stack_inv_prog_defs
  unfolding inv_defs oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
             cong: Collect_cong
              del: last.simps butlast.simps (*upt_Suc*))
  apply oghoare
(*768*)

apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)
  subgoal
(* invariant is true initially *)
apply clarify
apply (erule notE)
apply clarsimp
apply (rule conjI)
 apply (case_tac "nbRoutines - Suc (Suc 0)=0")
  apply (clarsimp simp: handle_events_empty user0_is_highest)
 apply (clarsimp simp: handle_events_empty user0_is_highest)
apply clarsimp
apply (case_tac "i=0")
 apply (clarsimp simp: handle_events_empty user0_is_highest)
apply (case_tac "i=Suc 0")
 apply (clarsimp simp: handle_events_empty user0_is_highest)
apply (case_tac "i=Suc (Suc 0)")
 apply (clarsimp simp: handle_events_empty user0_is_highest)
apply (clarsimp simp: handle_events_empty user0_is_highest)
done

  apply (tactic \<open>fn thm => if Thm.nprems_of thm > 0 then
        let val simp_ctxt = (clear_simpset @{context})
          addsimps @{thms eChronos_state_upd_simps HOL.simp_thms HOL.all_simps HOL.ex_simps
                          option.inject pre.simps snd_conv option.sel last_single
                          U_simps neq_Nil_conv svc\<^sub>a_commute
                          handle_events_empty
                          }
            val simp_ctxt =  simp_ctxt
                            |> Splitter.add_split @{thm split_if_asm}
                            |> Splitter.add_split @{thm split_if}

            val clarsimp_ctxt = (@{context}
                addsimps @{thms Int_Diff card_insert_if
                                insert_Diff_if Un_Diff interrupt_policy_I
                                sched_picks_user handle_events_empty helper16
                                helper18 interrupt_policy_self
                                user0_is_highest svc\<^sub>a_commute
                                interrupt_policy_mono sorted_by_policy_svc\<^sub>a
                                helper21 helper22 helper25
                                sorted_by_policy_U' sorted_by_policy_svc\<^sub>s_hd_svc\<^sub>a
                                sorted_by_policy_svc\<^sub>a_hd_svc\<^sub>s}
                delsimps @{thms disj_not1}
                addSIs @{thms last_tl'}
                addSDs @{thms helper28' helper27'})

            val clarsimp_ctxt2 = (@{context}
                addsimps @{thms neq_Nil_conv
                                interrupt_policy_svc\<^sub>a'
                                interrupt_policy_svc\<^sub>s'
                                interrupt_policy_U helper25
                                svc\<^sub>a_commute
                                handle_events_empty}
                delsimps @{thms disj_not1}
                addDs @{thms })
                           |> Splitter.add_split @{thm split_if_asm}
                           |> Splitter.add_split @{thm split_if}

            val fastforce_ctxt = (@{context}
                addsimps @{thms sorted_by_policy_svc\<^sub>s_svc\<^sub>a sched_policy_Some_U
                                interrupt_policy_U last_tl svc\<^sub>a_commute
                                helper26 sorted_by_policy_svc\<^sub>a''}
                addDs @{thms })
                           |> Splitter.add_split @{thm split_if_asm}
                           |> Splitter.add_split @{thm split_if}

                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 10 ((TRY' o SOLVED' o DETERM') (
        (((fn i => DETERM (REPEAT_ALL_NEW (resolve_tac @{context}
                  @{thms subset_eqI subsetI ballI CollectI IntI conjI disjCI impI
                         union_negI_drop}
                ORELSE' DETERM o dresolve_tac @{context} @{thms CollectD Set.singletonD
                                                      ComplD CollectNotD
                                                      Meson.not_conjD
                                                      Meson.not_exD
                                                      set_ConsD}
                ORELSE' DETERM o eresolve_tac @{context} @{thms IntE conjE exE insertE}
                ORELSE' CHANGED o safe_asm_full_simp_tac simp_ctxt
                ORELSE' CHANGED o Classical.clarify_tac (Clasimp.addSss simp_ctxt)) i))
        THEN_ALL_NEW (
           ((TRY' o REPEAT_ALL_NEW) ((EqSubst.eqsubst_tac @{context} [0] @{thms svc\<^sub>a_commute})
            ORELSE' (EqSubst.eqsubst_asm_tac @{context} [0] @{thms svc\<^sub>a_commute})))
            THEN' ((TRY' o REPEAT_ALL_NEW) ((EqSubst.eqsubst_tac @{context} [0] @{thms svc\<^sub>s_commute})
            ORELSE' (EqSubst.eqsubst_asm_tac @{context} [0] @{thms svc\<^sub>s_commute}))))
        THEN_ALL_NEW (((fn tac => fn i => DETERM (tac i))
                        (TRY_EVERY_FORWARD' @{context}
                                            @{thms helper29 helper30
                                            sorted_by_policy_U
                                            sorted_by_policy_svc\<^sub>a_single
                                            sorted_by_policy_svc\<^sub>s_single
                                            sorted_by_policy_U_single
                                            sched_policy_Some_U
                                            list.set_sel(2)
                                            sorted_by_policy_empty'})
                         THEN'
                         ((TRY' o REPEAT_ALL_NEW)
                             (FORWARD (dresolve_tac @{context}
                                  @{thms helper21' helper27' helper28'})
                                  @{context})))
                THEN_ALL_NEW (TRY' (
                        SOLVED' (fn i => fn st => timed_tac 40 clarsimp_ctxt st (clarsimp_tac clarsimp_ctxt i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 40 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac (@{context} delsimps @{thms disj_not1}
                           |> Splitter.add_split @{thm split_if_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 30 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 5 @{context} st
                                    (Metis_Tactic.metis_tac [] ATP_Proof_Reconstruct.default_metis_lam_trans @{context} [] i st))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
(*0*)(*381.599s elapsed time, 1325.540s cpu time, 106.568s GC time*)
(*this now takes much longer after updating to Isabelle2016*)
(*643.336s elapsed time, 2265.148s cpu time, 210.252s GC time*)

(*>*)
done

end