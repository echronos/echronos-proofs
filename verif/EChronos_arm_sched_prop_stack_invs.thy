(*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *

 * @TAG(DATA61_BSD)
 *)

theory EChronos_arm_sched_prop_stack_invs

imports
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
    \<lbrace>\<exists>n. \<acute>nextT = Some n \<and> n \<in> U\<rbrace>
    \<acute>contexts := \<acute>contexts (\<acute>curUser \<mapsto> (preempt_enabled, \<acute>ATStack));;
    \<lbrace>\<exists>n. \<acute>nextT = Some n \<and> n \<in> U\<rbrace>
    \<acute>curUser := the \<acute>nextT;;
    \<lbrace>\<acute>curUser \<in> U\<rbrace>
    \<acute>ATStack := snd (the (\<acute>contexts (\<acute>curUser)));;
    \<lbrace>True\<rbrace>
    IF fst (the (\<acute>contexts (\<acute>curUser)))
      THEN \<lbrace>True\<rbrace> \<langle>svc\<^sub>aEnable\<rangle>
      ELSE \<lbrace>True\<rbrace> \<langle>svc\<^sub>aDisable\<rangle> FI"

definition
  eChronos_arm_sched_prop_stack_invs_prog
where
  "eChronos_arm_sched_prop_stack_invs_prog \<equiv>
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
      add_inv_assn_com \<lbrace>\<acute>ghostP \<and> svc\<^sub>a \<in> set (\<acute>AT # \<acute>ATStack)\<rbrace> (
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
      add_inv_assn_com \<lbrace>\<acute>ghostS \<and> svc\<^sub>s \<in> set (\<acute>AT # \<acute>ATStack)\<rbrace> (
      schedule;;
      context_switch False;;
      \<lbrace>True\<rbrace>
       \<langle>\<acute>ghostS := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    SCHEME [user0 \<le> i < user0 + nbRoutines]
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
    FI
    \<lbrace>False\<rbrace>
  COEND))"

(*--------------------------------------------------------------------------*)
subsection \<open>The proof\<close>

lemmas eChronos_arm_sched_prop_stack_invs_prog_defs =
                    eChronos_arm_sched_prop_base_defs
                    eChronos_arm_sched_prop_stack_invs_prog_def
                    schedule_def context_switch_def

lemma eChronos_arm_sched_prop_stack_invs_proof:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>True\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and>
      (\<forall>i \<in> U. \<exists>j \<in> U. snd (the (\<acute>contexts i)) = [j])\<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_stack_invs_prog
  \<lbrace>False\<rbrace>"
  unfolding eChronos_arm_sched_prop_stack_invs_prog_defs
  unfolding inv_defs oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
             cong: Collect_cong
              del: last.simps butlast.simps (*upt_Suc*))
  apply oghoare
(*661*)

apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)
  subgoal
(* invariant is true initially *)
apply clarify
apply (erule notE)
(*the next line takes about 10 minutes*)
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
        let val ctxt = @{context}
            val clarsimp_ctxt = (ctxt
                addsimps @{thms Int_Diff card_insert_if
                                insert_Diff_if Un_Diff interrupt_policy_I
                                handle_events_empty helper16
                                helper18 interrupt_policy_self
                                user0_is_highest
                                interrupt_policy_mono sorted_by_policy_svc\<^sub>a
                                helper21 helper22 helper25}
                delsimps @{thms disj_not1}
                addSIs @{thms last_tl'})

            val clarsimp_ctxt2 = (ctxt
                addsimps @{thms neq_Nil_conv
                                interrupt_policy_svc\<^sub>a'
                                interrupt_policy_svc\<^sub>s'
                                interrupt_policy_U helper25
                                handle_events_empty}
                delsimps @{thms disj_not1}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

            val clarsimp_ctxt3 = (put_simpset HOL_basic_ss ctxt)

            val fastforce_ctxt = (ctxt
                addsimps @{thms sorted_by_policy_svc\<^sub>s_svc\<^sub>a sched_policy_Some_U
                                interrupt_policy_U last_tl
                                helper26 sorted_by_policy_svc\<^sub>a''}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 51 ((TRY' o SOLVED' o DETERM') (
        ((set_to_logic ctxt
        THEN_ALL_NEW svc_commute ctxt
        THEN_ALL_NEW (((fn tac => fn i => DETERM (tac i))
                        (TRY_EVERY_FORWARD' ctxt
                                            @{thms helper29 helper30
                                            sorted_by_policy_U
                                            sorted_by_policy_svc\<^sub>a_single
                                            sorted_by_policy_svc\<^sub>s_single
                                            sorted_by_policy_U_single
                                            sched_picks_user
                                            set_tl
                                            sorted_by_policy_empty'})
                         THEN'
                         ((TRY' o REPEAT_ALL_NEW)
                             (FORWARD (dresolve_tac ctxt
                                  @{thms helper21' helper27' helper28'})
                                  ctxt)))
                THEN' (TRY' (clarsimp_tac clarsimp_ctxt3))
                THEN' (TRY' (
                        SOLVED' (fn i => fn st => timed_tac 5 ctxt st
                                    (Blast.depth_tac ctxt 3 i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt st (clarsimp_tac clarsimp_ctxt i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac (ctxt delsimps @{thms disj_not1}
                           |> Splitter.add_split @{thm if_split_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
  (*221.173s elapsed time, 491.464s cpu time, 50.760s GC time*)
done

lemma eChronos_arm_sched_prop_ghostP_S_stack_inv_proof:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and>
   (\<forall>i \<in> U. \<exists>j \<in> U. snd (the (\<acute>contexts i)) = [j])\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>ghostP_S_stack_inv\<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_stack_invs_prog
  \<lbrace>False\<rbrace>"
  unfolding eChronos_arm_sched_prop_stack_invs_prog_defs
  unfolding inv_defs oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
             cong: Collect_cong
              del: last.simps butlast.simps (*upt_Suc*))
  apply oghoare
(*661*)

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
        let val ctxt = @{context}
            val clarsimp_ctxt = (ctxt
                addsimps @{thms Int_Diff card_insert_if
                                insert_Diff_if Un_Diff interrupt_policy_I
                                handle_events_empty helper16
                                helper18 interrupt_policy_self
                                user0_is_highest
                                interrupt_policy_mono sorted_by_policy_svc\<^sub>a
                                helper21 helper22 helper25}
                delsimps @{thms disj_not1}
                addSIs @{thms last_tl'})

            val clarsimp_ctxt2 = (ctxt
                addsimps @{thms neq_Nil_conv
                                interrupt_policy_svc\<^sub>a'
                                interrupt_policy_svc\<^sub>s'
                                interrupt_policy_U helper25
                                handle_events_empty}
                delsimps @{thms disj_not1}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

            val clarsimp_ctxt3 = (put_simpset HOL_basic_ss ctxt)

            val fastforce_ctxt = (ctxt
                addsimps @{thms sorted_by_policy_svc\<^sub>s_svc\<^sub>a sched_policy_Some_U
                                interrupt_policy_U last_tl
                                helper26 sorted_by_policy_svc\<^sub>a''}
                addDs @{thms })
                           |> Splitter.add_split @{thm if_split_asm}
                           |> Splitter.add_split @{thm if_split}

                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 61 ((TRY' o SOLVED' o DETERM') (
        ((set_to_logic ctxt
        THEN_ALL_NEW svc_commute ctxt
        THEN_ALL_NEW (((fn tac => fn i => DETERM (tac i))
                        (TRY_EVERY_FORWARD' ctxt
                                            @{thms helper29 helper30
                                            sorted_by_policy_U
                                            sorted_by_policy_svc\<^sub>a_single
                                            sorted_by_policy_svc\<^sub>s_single
                                            sorted_by_policy_U_single
                                            sched_picks_user
                                            set_tl
                                            sorted_by_policy_empty'})
                         THEN'
                         ((TRY' o REPEAT_ALL_NEW)
                             (FORWARD (dresolve_tac ctxt
                                  @{thms helper21' helper27' helper28'})
                                  ctxt)))
                THEN' (TRY' (clarsimp_tac clarsimp_ctxt3))
                THEN' (TRY' (
                        SOLVED' (fn i => fn st => timed_tac 5 ctxt st
                                    (Blast.depth_tac ctxt 3 i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt st (clarsimp_tac clarsimp_ctxt i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac (ctxt delsimps @{thms disj_not1}
                           |> Splitter.add_split @{thm if_split_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
  (*149.959s elapsed time, 414.808s cpu time, 60.468s GC time*)
done

end
