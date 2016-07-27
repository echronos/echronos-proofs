(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_ghostP_inv

imports
  EChronos_arm_sched_prop_tactic
begin

definition
  schedule
where
  "schedule \<equiv>
    \<lbrace>True\<rbrace>
    \<acute>nextT := None;;
    \<lbrace>True\<rbrace>
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
  eChronos_arm_sched_prop_ghostP_prog
where
  "eChronos_arm_sched_prop_ghostP_prog \<equiv>
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
      add_inv_assn_com \<lbrace>\<acute>ghostP\<rbrace> (
      schedule;;
      context_switch True;;
      \<lbrace>True\<rbrace>
       \<langle>\<acute>ghostP := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    (* svc\<^sub>s *)
    \<lbrace>\<acute>AT = svc\<^sub>s \<longrightarrow> svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
    WHILE True INV \<lbrace>\<acute>AT = svc\<^sub>s \<longrightarrow> svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
    DO
      add_await_routine svc\<^sub>s (
      \<lbrace>\<acute>AT = svc\<^sub>s \<longrightarrow> svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
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
    \<lbrace>True\<rbrace> IF (i\<in>I) THEN

    (* Interrupts *)
    \<lbrace>i\<in>I\<rbrace>
    WHILE True INV \<lbrace>i\<in>I\<rbrace>
    DO
      \<lbrace>i\<in>I\<rbrace>
      ITake i;;

      (add_await_routine i (
      add_inv_assn_com
       \<lbrace>i\<in>I  \<and> \<acute>ATStack \<noteq> []  \<and> i \<in> set (\<acute>AT # \<acute>ATStack)
       \<and> (\<acute>AT = i \<longrightarrow> i \<in> interrupt_policy (hd (\<acute>ATStack)))\<rbrace> (
      \<lbrace>True\<rbrace>
      \<acute>E :\<in> {E'. \<acute>E \<subseteq> E'};;

      \<lbrace>True\<rbrace>
      svc\<^sub>aRequest;;

      \<lbrace>\<acute>svc\<^sub>aReq\<rbrace>
      \<langle>IRet\<rangle>)))
    OD

    ELSE
    (* Users *)
    add_inv_assn_com
     \<lbrace>i \<in> U\<rbrace> (
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
          \<lbrace>\<acute>ghostU i = Syscall\<rbrace> (
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

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<acute>R := \<acute>R (i := Some False);;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Yield),, SVC\<^sub>s_now\<rangle>;;
        \<lbrace>\<acute>ghostU i = Yield\<rbrace>
        \<acute>ghostU := \<acute>ghostU (i := Syscall);;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
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

lemmas eChronos_arm_sched_prop_ghostP_prog_defs =
                    eChronos_arm_sched_prop_base_defs
                    eChronos_arm_sched_prop_ghostP_prog_def
                    schedule_def context_switch_def

lemma rtos_ghostP_inv_holds:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>\<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostS_ghostP_inv 
    \<and> \<acute>priority_inv \<and> \<acute>last_stack_inv \<and> \<acute>EIT_inv \<and> \<acute>ghostP_S_stack_inv\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>ghostP_inv \<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_ghostP_prog
  \<lbrace>False\<rbrace>" 

  unfolding eChronos_arm_sched_prop_ghostP_prog_defs
  unfolding inv_defs oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
              del: last.simps butlast.simps (*upt_Suc*))
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
                           |> Splitter.add_split @{thm split_if_asm}
                           |> Splitter.add_split @{thm split_if}

            val clarsimp_ctxt3 = (put_simpset HOL_basic_ss ctxt)

            val fastforce_ctxt = (ctxt
                addsimps @{thms sorted_by_policy_svc\<^sub>s_svc\<^sub>a sched_policy_Some_U
                                interrupt_policy_U last_tl
                                helper26 sorted_by_policy_svc\<^sub>a''}
                addDs @{thms })
                           |> Splitter.add_split @{thm split_if_asm}
                           |> Splitter.add_split @{thm split_if}

                          in
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 31 ((TRY' o SOLVED' o DETERM') (
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
                        SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt st (clarsimp_tac clarsimp_ctxt i st))
                ORELSE' SOLVED' (fn i => fn st => timed_tac 30 clarsimp_ctxt2 st (clarsimp_tac clarsimp_ctxt2 i st))
                ORELSE' SOLVED' (clarsimp_tac (ctxt delsimps @{thms disj_not1}
                           |> Splitter.add_split @{thm split_if_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
  (*12*)(*193.585s elapsed time, 681.808s cpu time, 67.180s GC time*)
             apply (clarsimp simp: interrupt_policy_svc\<^sub>a' svc\<^sub>a_interrupt_empty)
            apply clarsimp
            apply (rule conjI; clarsimp)
            apply (metis interrupt_policy_U last_in_set sorted_by_policy_Cons
                         sorted_by_policy_hd)
           apply clarsimp
           apply (metis hd_in_set helper19 insert_iff list.set(2) sorted_by_policy_svc\<^sub>a sorted_by_policy_svc\<^sub>a_not_svc\<^sub>s)
          apply clarsimp
          apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
         apply clarsimp
         apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
        apply clarsimp
        apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
       apply clarsimp
       apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
      apply clarsimp
      apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
     apply clarsimp
    apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
    apply clarsimp 
    apply (metis (no_types, lifting) I_sub_I' helper21 interrupt_policy_U 
                 list.collapse sorted_by_policy_Cons sorted_by_policy_Cons_hd 
                 sorted_by_policy_hd' sorted_by_policy_svc\<^sub>a 
                 sorted_by_policy_svc\<^sub>a' subsetCE)
   apply clarsimp
   apply (metis (no_types, lifting) I_sub_I' helper21 interrupt_policy_U 
                 list.collapse sorted_by_policy_Cons sorted_by_policy_Cons_hd 
                 sorted_by_policy_hd' sorted_by_policy_svc\<^sub>a 
                 sorted_by_policy_svc\<^sub>a' subsetCE)
  apply clarsimp
  apply (metis helper9 order_refl sorted_by_policy_svc\<^sub>a)
  done

end