(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_proof

imports
  EChronos_arm_sched_prop_tactic
begin

section \<open>Proof of the scheduler property, assuming invariants\<close>

subsection \<open>The program\<close>

text \<open>
The eChronos OS uses $SVC_s$ and $svc_a$ interrupt handlers to
implement scheduling. The scheduler function chooses a new task to run
by first updating the runnable mapping $R$ before using
whichever scheduler policy is in place to pick a task from among the
runnable ones. To update the runnable mapping, the function
$handle\_events$ is used, with this function being left
non-deterministic. After the execution of this function, the variable
$E$ needs to be cleared to indicate that the events have been
processed. However, the scheduler may itself be interrupted. If an
interrupt occurs between the execution of $handle\_events$ and the
reset of $E$, the interrupt handler might have modified
$E$ with new events to be processed (and flagged a request
for the scheduler to run). On return from interrupt, because the
scheduler is itself an interrupt and is not re-entrant, its execution
resumes, and so $E$ should not be cleared. Instead we save
its value before running $handle\_events$, and only remove those saved
events that have indeed been processed. When the scheduler will
return, the hardware will check if there are still any pending
requests for the scheduler to run, and re-run it if required.
\<close>

definition
  schedule
where
  "schedule \<equiv>
    \<lbrace>True\<rbrace>
    \<acute>nextT := None;;
    \<lbrace>\<acute>nextT = None\<rbrace>
    WHILE \<acute>nextT = None
    INV \<lbrace>(\<acute>nextT=None \<or> ((\<exists>n. \<acute>nextT=Some n \<and> n\<in>U) \<and>
           sched_policy \<acute>R = \<acute>nextT)) \<and>
           (\<acute>nextT \<noteq> None \<longrightarrow> \<acute>svc\<^sub>aReq \<or> \<acute>E = {} \<or> \<acute>AT \<in> I)\<rbrace>
    DO
      \<lbrace>True\<rbrace>
      \<acute>E_tmp := \<acute>E;;
      \<lbrace>\<acute>svc\<^sub>aReq \<or> \<acute>E=\<acute>E_tmp \<or> \<acute>AT \<in> I\<rbrace>
      \<acute>R := handle_events \<acute>E_tmp \<acute>R;;
      \<lbrace>\<acute>svc\<^sub>aReq \<or> \<acute>E=\<acute>E_tmp \<or> \<acute>AT \<in> I\<rbrace>
      \<acute>E := \<acute>E - \<acute>E_tmp;;
      \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I)\<rbrace>
      \<acute>nextT := sched_policy(\<acute>R)
    OD"

text \<open>
\noindent
Once the schedule functions has executed, the $context\_switch$
function is called. This function, as the name suggests, saves the
context of the old user task that was previously on the hardware
stack, and then replaces it with the context of the task chosen by the
scheduler. To do this the function first stores whether the previous
user task had $svc_a$ enabled,\footnote{This is identified by the
boolean passed to context\_switch. If $context\_switch$ is being
called by $svc_a$ then clearly $svc_a$ was previously enabled, while
by design we know that $SVC_s$ is only called when $svc_a$ is
disabled.} along with the current value of $ATStack$. It then loads
the stack that existed when the new task was last executing. Lastly,
$svc_a$ is enabled or disabled as required by the new task.
\<close>

definition
  context_switch
where
  "context_switch preempt_enabled \<equiv>
    \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I)
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT\<rbrace>
    \<acute>contexts := \<acute>contexts (\<acute>curUser \<mapsto> (preempt_enabled, \<acute>ATStack));;
    \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I)
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT\<rbrace>
    \<acute>curUser := the \<acute>nextT;;
    \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> \<acute>curUser = the \<acute>nextT
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT\<rbrace>
    \<acute>ATStack := snd (the (\<acute>contexts (\<acute>curUser)));;
    \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> last \<acute>ATStack = the \<acute>nextT
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT\<rbrace>
    IF fst (the (\<acute>contexts (\<acute>curUser)))
      THEN
        \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> last \<acute>ATStack = the \<acute>nextT
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT
           \<and> fst (the (\<acute>contexts (\<acute>curUser)))\<rbrace>
        \<langle>svc\<^sub>aEnable\<rangle>
      ELSE
        \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> last \<acute>ATStack = the \<acute>nextT
           \<and> (\<exists>n. \<acute>nextT = Some n \<and> n\<in>U) \<and> sched_policy \<acute>R = \<acute>nextT
           \<and> \<not> fst (the (\<acute>contexts (\<acute>curUser)))\<rbrace>
        \<langle>svc\<^sub>aDisable\<rangle> FI"

definition
  eChronos_arm_sched_prop_prog
where
  "eChronos_arm_sched_prop_prog \<equiv>
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
      \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> sched_policy \<acute>R = Some (last \<acute>ATStack)\<rbrace>
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
      add_inv_assn_com \<lbrace>\<acute>ghostS \<and> svc\<^sub>s \<in> set (\<acute>AT # \<acute>ATStack) \<and>
                        svc\<^sub>a \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace> (
      schedule;;
      context_switch False;;
      \<lbrace>(\<acute>svc\<^sub>aReq \<or> \<acute>E={} \<or> \<acute>AT \<in> I) \<and> sched_policy \<acute>R = Some (last \<acute>ATStack)\<rbrace>
      \<langle>\<acute>ghostS := False,, IRet\<rangle>))
    OD
    \<lbrace>False\<rbrace>

    \<parallel>

    SCHEME [user0 \<le> i < user0 + nbRoutines]
    \<lbrace>(i \<in> I \<longrightarrow> i \<notin> set (\<acute>AT # \<acute>ATStack)) \<and>
     (i \<in> U \<longrightarrow> (\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq) \<and>
                (\<acute>AT = i \<longrightarrow> \<acute>svc\<^sub>aReq \<or> \<acute>E = {}))\<rbrace> IF (i\<in>I) THEN

    (* Interrupts *)
    \<lbrace>i\<in>I \<and> i \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
    WHILE True INV \<lbrace>i\<in>I \<and> i \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
    DO
      \<lbrace>i\<in>I \<and> i \<notin> set (\<acute>AT # \<acute>ATStack)\<rbrace>
      ITake i;;

      (add_await_routine i (
      add_inv_assn_com
       \<lbrace>i\<in>I \<and> i \<in> set (\<acute>AT # \<acute>ATStack) \<and> \<acute>ATStack \<noteq> []\<rbrace> (
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
     \<lbrace>i \<in> U \<and> (\<acute>AT = i \<longrightarrow> \<acute>svc\<^sub>aReq \<or> \<acute>E = {})\<rbrace> (
    \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
    WHILE True INV \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
    DO
      (add_await_routine i (
      \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
      \<acute>userSyscall :\<in> {SignalSend, Block};;

      \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
      IF \<acute>userSyscall = SignalSend
      THEN
        \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        add_inv_assn_com
          \<lbrace>\<acute>ghostU i = Syscall\<rbrace> (
        \<lbrace>True\<rbrace>
        \<acute>R :\<in> {R'. \<forall>i. \<acute>R i = Some True \<longrightarrow> R' i = Some True};;

        \<lbrace>True\<rbrace>
        svc\<^sub>aRequest;;

        \<lbrace>\<acute>svc\<^sub>aReq\<rbrace>
        \<langle>svc\<^sub>aEnable,, \<acute>ghostU := \<acute>ghostU (i := User)\<rangle>);;
        \<lbrace>True\<rbrace>
        WHILE \<acute>svc\<^sub>aReq INV \<lbrace>True\<rbrace>
        DO
          \<lbrace>True\<rbrace> SKIP
        OD
      ELSE
      \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
      IF \<acute>userSyscall = Block
      THEN
        \<lbrace>(\<acute>AT = i \<and> svc\<^sub>a \<in> \<acute>EIT \<longrightarrow> \<not> \<acute>svc\<^sub>aReq)\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Syscall),, svc\<^sub>aDisable\<rangle>;;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<acute>R := \<acute>R (i := Some False);;

        \<lbrace>\<acute>ghostU i = Syscall\<rbrace>
        \<langle>\<acute>ghostU := \<acute>ghostU (i := Yield),, SVC\<^sub>s_now\<rangle>;;

        \<lbrace>\<acute>ghostU i = Yield \<and>
         (\<acute>AT = i \<and> \<not>\<acute>svc\<^sub>aReq \<longrightarrow> sched_policy \<acute>R = Some i)\<rbrace>
        \<acute>ghostU := \<acute>ghostU (i := Syscall);;

        \<lbrace>\<acute>ghostU i = Syscall \<and>
         (\<acute>AT = i \<and> \<not>\<acute>svc\<^sub>aReq \<longrightarrow> sched_policy \<acute>R = Some i)\<rbrace>
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

(*--------------------------------------------------------------------------*)
subsection \<open>The proof\<close>
(*
declare [[simp_trace_new mode=normal ]]
*)

lemmas eChronos_arm_sched_prop_prog_defs =
                    eChronos_arm_sched_prop_base_defs
                    eChronos_arm_sched_prop_prog_def
                    schedule_def context_switch_def

lemma eChronos_arm_sched_prop_proof:
  "0<nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace> \<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostP_inv \<and>
   \<acute>stack_distinct_inv \<and> \<acute>last_stack_inv \<and>
   \<acute>butlast_stack_inv \<and> \<acute>contexts_stack_inv \<and> \<acute>priority_inv \<and>
   \<acute>ghostS_ghostP_inv\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>scheduler_invariant\<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_prog
  \<lbrace>False\<rbrace>"
  unfolding eChronos_arm_sched_prop_prog_defs
  unfolding inv_defs oghoare_inv_def
  apply (simp add: add_inv_aux_def o_def
              del: last.simps butlast.simps (*upt_Suc*))
  apply oghoare
(*1229*)

apply (find_goal \<open>succeeds \<open>rule subsetI[where A=UNIV]\<close>\<close>)
  subgoal
(* invariant is true initially *)
apply clarify
apply (erule notE)
apply (simp add: handle_events_empty user0_is_highest)
apply (rule conjI, clarsimp simp: helper20)
apply (rule conjI, clarsimp simp: helper20)
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
        timeit (fn _ => Cache_Tactics.PARALLEL_GOALS_CACHE 1 ((TRY' o SOLVED' o DETERM') (
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
                           |> Splitter.add_split @{thm if_split_asm}) THEN_ALL_NEW
                                (fn i => fn st => timed_tac 20 fastforce_ctxt st (fast_force_tac fastforce_ctxt i st)))
                )))
                ))) 1)
                thm |> Seq.pull |> the |> fst |> Seq.single) end
        else Seq.empty\<close>)
  (*244.296s elapsed time, 854.684s cpu time, 81.168s GC time*)
done

end