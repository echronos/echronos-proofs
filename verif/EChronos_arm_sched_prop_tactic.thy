(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_tactic

imports
  EChronos_arm_sched_prop_base
begin

ML \<open>
fun timed_tac i ctxt st seq =
  let
    fun str_of_goal th = Pretty.string_of (Goal_Display.pretty_goal ctxt th)

    fun limit f x = TimeLimit.timeLimit (Time.fromSeconds i) f x
      handle TimeLimit.TimeOut =>
        let val _ = warning ("Method timed out:\n"(* ^ (str_of_goal st)*))
        in SOME (st, Seq.empty) end
  in
    Seq.make (limit (fn () => Option.map (apsnd (timed_tac i ctxt st))
      (Seq.pull seq)))
  end
\<close>

ML \<open>
(*Apply second tactic to all subgoals emerging from the first,
  but not the last one --
  following usual convention for subgoal-based tactics.*)
infix 1 THEN_ALL_NEW_BUT_1;

fun (tac1 THEN_ALL_NEW_BUT_1 tac2) i st =
  st |> (tac1 i THEN (fn st' =>
    Seq.INTERVAL tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st - 1) st'));

fun DETERM' tac i = DETERM (tac i)

fun TRY' tac i = TRY (tac i)

fun TRY_EVERY' tacs i = EVERY' (map (fn tac => TRY' tac) tacs) i

fun FORWARD tac ctxt = tac THEN_ALL_NEW_BUT_1 (SOLVED' (assume_tac ctxt))

fun TRY_EVERY_FORWARD' ctxt thms i =
  TRY_EVERY' (map (fn thm => FORWARD (forward_tac ctxt [thm]) ctxt) thms) i
\<close>

ML \<open>
fun set_to_logic ctxt i =
  let val simp_ctxt = ((clear_simpset ctxt)
          addsimps @{thms eChronos_state_upd_simps HOL.simp_thms HOL.all_simps HOL.ex_simps
                          option.inject pre.simps snd_conv option.sel last_single
                          U_simps neq_Nil_conv svc\<^sub>a_commute
                          handle_events_empty
                          })
                  |> Splitter.add_split @{thm split_if_asm}
                  |> Splitter.add_split @{thm split_if}
  in DETERM (REPEAT_ALL_NEW (resolve_tac ctxt
                  @{thms subset_eqI subsetI ballI CollectI IntI conjI disjCI impI
                         union_negI_drop}
         ORELSE' DETERM o dresolve_tac ctxt @{thms CollectD Set.singletonD
                                                   ComplD CollectNotD
                                                   Meson.not_conjD
                                                   Meson.not_exD
                                                   set_ConsD}
         ORELSE' DETERM o eresolve_tac ctxt @{thms IntE conjE exE insertE}
         ORELSE' CHANGED o safe_asm_full_simp_tac simp_ctxt
         ORELSE' CHANGED o Classical.clarify_tac (Clasimp.addSss simp_ctxt)) i)
  end

fun svc_commute ctxt =
  ((TRY' o REPEAT_ALL_NEW) ((EqSubst.eqsubst_tac ctxt [0] @{thms svc\<^sub>a_commute})
                ORELSE' (EqSubst.eqsubst_asm_tac ctxt [0] @{thms svc\<^sub>a_commute})))
  THEN'
  ((TRY' o REPEAT_ALL_NEW) ((EqSubst.eqsubst_tac ctxt [0] @{thms svc\<^sub>s_commute})
                ORELSE' (EqSubst.eqsubst_asm_tac ctxt [0] @{thms svc\<^sub>s_commute})))
\<close>

end