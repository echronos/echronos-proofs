(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_EIT_inv

imports
  "EChronos_arm_sched_prop_tactic"
begin

  
definition
  schedule
where
  "schedule \<equiv>
    \<lbrace>True\<rbrace>
    \<acute>nextT := None;;
    \<lbrace>True (*\<acute>nextT = None*)\<rbrace>
    WHILE \<acute>nextT = None
    INV \<lbrace>True\<rbrace>
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
    \<lbrace>True\<rbrace>
    \<acute>contexts := \<acute>contexts (\<acute>curUser \<mapsto> (preempt_enabled, \<acute>ATStack));;
    \<lbrace>True\<rbrace>
    \<acute>curUser := the \<acute>nextT;;
    \<lbrace>True\<rbrace>
    \<acute>ATStack := snd (the (\<acute>contexts (\<acute>curUser)));;
    \<lbrace>True\<rbrace>
    IF fst (the (\<acute>contexts (\<acute>curUser)))
      THEN \<lbrace>True\<rbrace> \<langle>svc\<^sub>aEnable\<rangle>
      ELSE \<lbrace>True\<rbrace> \<langle>svc\<^sub>aDisable\<rangle> FI"

definition
  eChronos_arm_sched_prop_EIT_prog
where
  "eChronos_arm_sched_prop_EIT_prog \<equiv>
  (hardware_init,,
   eChronos_init,,
  (COBEGIN
    (* svc\<^sub>a_take *)
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      \<lbrace>True\<rbrace> svc\<^sub>aTake
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    (* svc\<^sub>a *)
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      add_await_routine svc\<^sub>a (
      \<lbrace>True\<rbrace>
      \<acute>ghostP := True;;
      add_inv_assn_com \<lbrace>True\<rbrace> (
      schedule;;
      context_switch True;;
      \<lbrace>True\<rbrace>
       \<langle>\<acute>ghostP := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    (* svc\<^sub>s *)
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      add_await_routine svc\<^sub>s (
      \<lbrace>True\<rbrace>
      \<acute>ghostS := True;;
      add_inv_assn_com \<lbrace>True\<rbrace> (
      schedule;;
      context_switch False;;
      \<lbrace>True\<rbrace>
       \<langle>\<acute>ghostS := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    SCHEME [user0 \<le> i < user0 + nbRoutines]
    \<lbrace>True\<rbrace> IF (i\<in>I) THEN

    (* Interrupts *)
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      \<lbrace>True\<rbrace>
      ITake i;;

      (add_await_routine i (
      add_inv_assn_com
       \<lbrace>True\<rbrace> (
      \<lbrace>True\<rbrace>
      \<acute>E :\<in> {E'. \<acute>E \<subseteq> E'};;

      \<lbrace>True\<rbrace>
      svc\<^sub>aRequest;;

      \<lbrace>True (*\<acute>svc\<^sub>aReq*)\<rbrace>
      \<langle>IRet\<rangle>)))
    OD

    ELSE
    (* Users *)
    add_inv_assn_com
     \<lbrace>True\<rbrace> (
    \<lbrace>True\<rbrace>
    WHILE True INV \<lbrace>True\<rbrace>
    DO
      (add_await_routine i (
      \<lbrace>True\<rbrace>
      \<acute>userSyscall :\<in> {SignalSend, Block};;

      \<lbrace>True\<rbrace>
      IF \<acute>userSyscall = SignalSend
      THEN
        \<lbrace>True\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        add_inv_assn_com
          \<lbrace>True\<rbrace> (
        \<lbrace>True\<rbrace>
        \<acute>R :\<in> {R'. \<forall>i. \<acute>R i = Some True \<longrightarrow> R' i = Some True};;

        \<lbrace>True\<rbrace>
        svc\<^sub>aRequest;;

        \<lbrace>True\<rbrace>
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>);;
        \<lbrace>True\<rbrace>
        WHILE \<acute>svc\<^sub>aReq INV \<lbrace>True\<rbrace>
        DO
          \<lbrace>True\<rbrace> SKIP
        OD
      ELSE \<lbrace>True\<rbrace> IF \<acute>userSyscall = Block
      THEN
        \<lbrace>True\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        \<lbrace>True\<rbrace>
        \<acute>R := \<acute>R (i := Some False);;

        \<lbrace>True\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Yield),, SVC\<^sub>s_now\<rangle>;;
        \<lbrace>True\<rbrace>
        \<acute>ghostU := \<acute>ghostU (i := Syscall);;

        \<lbrace>True\<rbrace>
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>;;
        \<lbrace>True\<rbrace>
        WHILE \<acute>svc\<^sub>aReq INV \<lbrace>True\<rbrace>
        DO
          \<lbrace>True\<rbrace> SKIP
        OD
      FI FI))
    OD)
    FI
    \<lbrace>False\<rbrace>
  COEND))"

lemmas eChronos_arm_sched_prop_EIT_prog_defs =
                    eChronos_arm_sched_prop_base_defs
                    eChronos_arm_sched_prop_EIT_prog_def
                    schedule_def context_switch_def

lemma rtos_EIT_inv_holds:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>True\<rbrace> \<parallel>-\<^sub>i \<lbrace>\<acute>EIT_inv \<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_EIT_prog
  \<lbrace>False\<rbrace>" 

  unfolding eChronos_arm_sched_prop_EIT_prog_defs
  unfolding oghoare_inv_def EIT_inv_def
  apply (simp add: add_inv_aux_def o_def)
  apply oghoare
  apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)
  subgoal
  apply (clarify)
  apply (erule notE)
  apply (simp add: handle_events_empty user0_is_highest)
  apply (rule conjI)
   apply (case_tac "nbRoutines - Suc (Suc 0)=0")
    apply (clarsimp simp:  handle_events_empty user0_is_highest)
   apply (clarsimp simp: handle_events_empty user0_is_highest)
  apply clarsimp
  apply (case_tac "i=0")
   apply (clarsimp simp: handle_events_empty user0_is_highest)
  apply (case_tac "i=Suc 0")
   apply (clarsimp simp: handle_events_empty user0_is_highest user0_def)
  apply (case_tac "i=Suc (Suc 0)")
   apply (clarsimp simp: handle_events_empty user0_is_highest user0_def)
  apply (clarsimp simp: handle_events_empty user0_is_highest)
  done

  by (tactic \<open>fn thm =>
        let val simp_ctxt = (clear_simpset @{context})
          addsimps @{thms eChronos_state_upd_simps HOL.simp_thms HOL.all_simps HOL.ex_simps
                          option.inject pre.simps snd_conv option.sel last_single
                          U_simps neq_Nil_conv svc\<^sub>a_commute (*svc\<^sub>s_commute*)
                          handle_events_empty sorted_by_policy_svc\<^sub>a_single
                          }
            val simp_ctxt =  simp_ctxt
                            |> Splitter.add_split @{thm split_if_asm}
                            |> Splitter.add_split @{thm split_if}

            val clarsimp_ctxt = (@{context}
                addsimps @{thms Int_Diff card_insert_if 
                                insert_Diff_if Un_Diff interrupt_policy_I
                                (*interrupt_policy_U*)
                                (*sched_picks_user *) handle_events_empty helper16
                                helper18 interrupt_policy_self
                                user0_is_highest svc\<^sub>a_commute (*svc\<^sub>s_commute*)
                                interrupt_policy_mono sorted_by_policy_svc\<^sub>a
                                helper21 helper22 helper25
                                sorted_by_policy_U'
                                sorted_by_policy_svc\<^sub>a_single})

            val clarsimp_ctxt2 = (@{context}
                addsimps @{thms neq_Nil_conv
                                interrupt_policy_svc\<^sub>a'
                                interrupt_policy_svc\<^sub>s'
                                interrupt_policy_U helper25
                                svc\<^sub>a_commute (*svc\<^sub>s_commute*)
                                handle_events_empty
                                sorted_by_policy_svc\<^sub>a_single}


                addDs @{thms sched_policy_Some_U})
                           |> Splitter.add_split @{thm split_if_asm}
                           |> Splitter.add_split @{thm split_if}

            val fastforce_ctxt = (@{context}
                addsimps @{thms sorted_by_policy_svc\<^sub>s_svc\<^sub>a sched_policy_Some_U}
                addDs @{thms sorted_by_policy_svc\<^sub>s_single})
                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 21 ((TRY o  SOLVE o DETERM) (
        (REPEAT_ALL_NEW (resolve_tac @{context}
                  @{thms subset_eqI subsetI ballI CollectI IntI conjI disjCI impI
                         union_negI_drop}
                ORELSE' DETERM o dresolve_tac @{context} @{thms CollectD Set.singletonD
                                                      ComplD CollectNotD
                                                      Meson.not_conjD
                                                      Meson.not_exD}
                ORELSE' DETERM o eresolve_tac @{context} @{thms IntE conjE exE insertE}
                ORELSE' CHANGED o safe_asm_full_simp_tac simp_ctxt
                ORELSE' CHANGED o Classical.clarify_tac (Clasimp.addSss simp_ctxt)
                ORELSE' SOLVED' (clarsimp_tac clarsimp_ctxt)
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac @{context} THEN'
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )
                ) 1))
                thm |> Seq.pull |> the |> fst |> Seq.single) end\<close>)

end