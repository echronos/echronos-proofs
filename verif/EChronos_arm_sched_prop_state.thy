(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*<*)
theory EChronos_arm_sched_prop_state

imports
  "../lib/Rule_By_Method"
begin
(*>*)

section \<open>Model\<close>

text \<open>
We present here a model of the ARM Cortex-M4 version of the eChronos
OS scheduling behaviour, formalised in Isabelle/HOL. It is based on
Leonor Prensa's formalisation of Owicki-Gries in Isabelle/HOL.
\<close>

subsection\<open>State\<close>

text \<open>
A routine is just a natural number; we add routines for the $svc_a$
and $svc_s$ handlers, user routines have numbers from @{text 2} to @{text
"nbUsers+2"}(excluded) and interrupt routines have numbers from @{text
"nbUsers+2"} to @{text "nbUsers+nbInts+2"} (excluded). The first user
to run is arbitrarily chosen to be the first one.
\<close>
    
type_synonym routine = nat

consts nbUsers :: nat
consts nbInts :: nat

abbreviation "nbRoutines \<equiv> nbUsers+nbInts"

definition "svc\<^sub>a \<equiv> 0 :: routine"
definition "svc\<^sub>s \<equiv> 1 :: routine"
definition "user0 \<equiv> 2 :: routine"
definition "U \<equiv> {user0..<user0 + nbUsers}"
definition "I \<equiv> {user0 + nbUsers..< user0 + nbRoutines}"
definition "I' \<equiv> I \<union> {svc\<^sub>a, svc\<^sub>s}"

(*<*)
lemma [simp]: "nbUsers >0 \<Longrightarrow> nbInts > 0 \<Longrightarrow> user0 \<notin> I"
  by (auto simp: I_def user0_def)

lemma [simp]: "\<lbrakk>user0 \<le> i; i < nbRoutines; i \<notin> I\<rbrakk> \<Longrightarrow> i \<in> U"
  by (simp add: I_def U_def)

lemma [simp]:
  "svc\<^sub>a \<notin> I"
  "svc\<^sub>s \<notin> I"
  by (auto simp: svc\<^sub>a_def svc\<^sub>s_def I_def user0_def)

lemma [simp]:
  "svc\<^sub>a \<in> I'"
  "svc\<^sub>s \<in> I'"
  by (auto simp: I'_def)

lemma I_sub_I'[simp]: "I \<subseteq> I'"
  by (auto simp: I_def I'_def)

lemma [simp]:
  "x \<in> I \<Longrightarrow> x \<noteq> svc\<^sub>a"
  "x \<in> I \<Longrightarrow> x \<noteq> svc\<^sub>s"
  by auto

lemma [dest]:
  "x \<in> I' \<Longrightarrow> x \<noteq> svc\<^sub>a \<Longrightarrow> x \<noteq> svc\<^sub>s \<Longrightarrow> x \<in> I"
  by (auto simp: I'_def)

lemma [simp]:
  "svc\<^sub>s \<noteq> svc\<^sub>a"
  "svc\<^sub>a \<noteq> svc\<^sub>s"
  "svc\<^sub>a \<noteq> user0"
  "svc\<^sub>s \<noteq> user0"
  by (auto simp: svc\<^sub>s_def svc\<^sub>a_def user0_def)

lemmas subset_trans[OF _ I_sub_I', simp, intro]

lemma [simp]: "\<lbrakk>user0 \<le> x; x < user0 + nbRoutines; x \<notin> I\<rbrakk> \<Longrightarrow> x \<notin> I'"
  by (simp add: I_def I'_def svc\<^sub>a_def svc\<^sub>s_def user0_def)

lemma [simp]: "\<lbrakk>user0 \<le> x; x < user0 + nbRoutines; x \<notin> I\<rbrakk> \<Longrightarrow> x \<in> U"
  by (simp add: I_def I'_def svc\<^sub>a_def user0_def U_def)

lemma [simp]:
  "user0 \<le> x \<Longrightarrow> x < user0 + nbRoutines \<Longrightarrow> (x \<notin> I') = (x \<in> U)"
  by (auto simp: I_def I'_def U_def svc\<^sub>a_def svc\<^sub>s_def user0_def)

lemma [simp]:
  "x \<in> I \<Longrightarrow> x \<notin> U"
  by (auto simp: I_def U_def)

lemma [simp]:
  "x \<in> I' \<Longrightarrow> x \<notin> U"
  by (auto simp: I'_def I_def U_def svc\<^sub>a_def svc\<^sub>s_def user0_def)

lemma [simp]:
  "svc\<^sub>a \<notin> U"
  "svc\<^sub>s \<notin> U"
  by (auto simp: svc\<^sub>a_def svc\<^sub>s_def user0_def U_def)

lemma [simp]:
  "x \<in> U \<Longrightarrow> x \<noteq> svc\<^sub>a"
  "x \<in> U \<Longrightarrow> x \<noteq> svc\<^sub>s"
  by auto

lemma [simp]:
  "nbUsers >0 \<Longrightarrow> nbInts > 0 \<Longrightarrow> user0 \<le> nbRoutines"
  by (simp add: user0_def)

lemmas [simp] = set_rev_mp[where A=I and B=I', simplified]
(*>*)

datatype ghostU = User | Syscall | Yield
datatype syscall = SignalSend | Block

text\<open>
\noindent
A state is composed of all the hardware variables, the program
variables that the targeted invariant or property relies on, plus
potential ghost variables used for reasoning.
\<close>

record state =
  EIT :: "routine set"                                                        \<comment> "the set of enabled interrupt tasks"
  svc\<^sub>aReq :: bool                                                         \<comment> "the $svc_a$ requested bit"
  AT :: routine                                                               \<comment> "the active routine"
  ATStack :: "routine list"                                                 \<comment> "the stack of suspended routines"

record eChronos_state = state +
  curUser :: routine                                                       \<comment> "current user task"
  contexts :: "routine \<Rightarrow> (bool \<times> routine list) option"     \<comment> "stored contexts"
  R :: "routine \<Rightarrow> bool option"                                         \<comment> "Runnable threads"
  E :: "nat set"                                                                  \<comment> "Events set (current)"
  E_tmp :: "nat set"                                                           \<comment> "Temporary events set"
  nextT :: "routine option"                                                \<comment> "the next Task"
  userSyscall :: syscall

  ghostP :: bool                     \<comment> "ghost var saying if $svc_a$ routine is executing"
  ghostS :: bool                     \<comment> "ghost var saying if $svc_s$ routine is executing"
  ghostU :: "routine \<Rightarrow> ghostU"      \<comment> "ghost var tracking the program counter of user routines"

locale foo
  =
  fixes Rec :: "'a eChronos_state_scheme"
  begin
  
lemmas r_surj = eChronos_state.surjective[of Rec,symmetric]

lemmas foo = state.update_convs[of "\<lambda>_. X" for X, @ (schematic) \<open>subst (asm) r_surj\<close>,symmetric]
             eChronos_state.update_convs[of "\<lambda>_. X" for X, @ (schematic) \<open>subst (asm) r_surj\<close>,symmetric]

lemmas foo' = state.select_convs(1) state.select_convs(2) state.select_convs(3)
              state.select_convs(4) select_convs

lemmas foos =  foo'[@ (schematic) \<open>subst (asm) foo(1)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(2)\<close>] 
               foo'[@ (schematic) \<open>subst (asm) foo(3)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(4)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(6)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(7)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(8)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(9)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(10)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(11)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(12)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(13)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(14)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(15)\<close>]
               foo'[@ (schematic) \<open>subst (asm) foo(16)\<close>]
               

end

lemmas eChronos_state_upd_simps = foo.foos 

(*--------------------------------------------------------------------------*)

subsection \<open>Generic scheduling policy, handling of events and interrupt policy\<close>

text\<open>
The scheduling policy (picking the next thread, given the list of
runnable threads) is left unspecified here; as well as the updating of
this runnable list, given a list of events. The interrupt policy
(which interrupts are allowed to run, given the currently running
routine) is also left unspecified. We have several assumptions about
these functions.
FIXME: these should be assumptions of the lemma, or in a locale
(context) for the lemma.
\<close>

consts sched_policy :: "(routine \<Rightarrow> bool option) \<Rightarrow> routine option"
consts handle_events :: "nat set \<Rightarrow> (routine \<Rightarrow> bool option) \<Rightarrow> routine \<Rightarrow> bool option"
consts interrupt_policy :: "routine \<Rightarrow> routine set"
(* definition "interrupt_policy i \<equiv> {i..<Suc nbRoutines} \<inter> {nbUsers..<Suc nbRoutines}" *)

text\<open>The scheduler picks a user task (not an interrupt).\<close>
lemma sched_picks_user:
  "sched_policy xs = t \<Longrightarrow> t= None \<or> (\<exists>n. t=Some n \<and> n \<in> U)"
sorry

text \<open>Running @{text handle_events} when the irq events set is empty returns the
        runnable set taken as input.\<close>
lemma handle_events_empty:
  "handle_events {} runn = runn "
sorry

text\<open>user0 is the highest priority task. This is for the invariant to 
   be true initially, where user0 is picked to run first.\<close>
lemma user0_is_highest:
  "sched_policy (\<lambda>n. if n\<in>U then Some True else None) = Some user0"
sorry

lemma interrupt_policy_svc\<^sub>a:
  "interrupt_policy svc\<^sub>a = I"
sorry

lemma interrupt_policy_svc\<^sub>a':
  "x \<in> I' \<Longrightarrow> svc\<^sub>a \<notin> interrupt_policy x"
sorry

lemma interrupt_policy_svc\<^sub>s:
  "interrupt_policy svc\<^sub>s = I"
sorry

lemma interrupt_policy_svc\<^sub>s':
  "x \<in> I' \<Longrightarrow> svc\<^sub>s \<notin> interrupt_policy x"
sorry

lemma interrupt_policy_self:
  "x \<notin> interrupt_policy x"
sorry

lemma interrupt_policy_I:
  "x \<in> I \<Longrightarrow> interrupt_policy x \<subseteq> I"
sorry

lemma interrupt_policy_I':
  "interrupt_policy x \<subseteq> I'"
sorry

lemma interrupt_policy_U:
  "x \<in> U \<Longrightarrow> interrupt_policy x = I'"
sorry

lemma interrupt_policy_mono:
  "y \<in> interrupt_policy x \<Longrightarrow> interrupt_policy y \<subseteq> interrupt_policy x"
sorry

lemma interrupt_policy_trans:
  "y \<in> interrupt_policy x \<Longrightarrow> z \<in> interrupt_policy y \<Longrightarrow> z \<in> interrupt_policy x"
  apply (rule basic_trans_rules(30), simp)
  apply (erule interrupt_policy_mono)
  done

lemma interrupt_policy_not_refl:
  "x \<in> interrupt_policy y \<Longrightarrow> y \<notin> interrupt_policy x"
  apply clarsimp
  apply (drule (1) interrupt_policy_trans)
  apply (simp add: interrupt_policy_self)
  done

lemma svc\<^sub>a_svc\<^sub>s_priority[simp]:
  "svc\<^sub>a \<notin> interrupt_policy svc\<^sub>s"
  "svc\<^sub>s \<notin> interrupt_policy svc\<^sub>a"
  by (auto simp: interrupt_policy_svc\<^sub>s interrupt_policy_svc\<^sub>a)

(*--------------------------------------------------------------------------*)

subsection \<open>The scheduler invariant\<close>

text \<open>
The scheduler invariant states that the running user is the one with
highest priority. In other words, if the active routine is a user, and
if preemption is on (we're not in an rtos call, and the user hasn't
turned off preemption), then if we were to update the list of runnable
threads from occurred events, and compute which thread should be
running, we would find the currently running user thread.
\<close>

definition
  "sched_inv x i \<equiv>
    i \<in> U \<and> svc\<^sub>a \<in> EIT x \<and> \<not> svc\<^sub>aReq x
        \<longrightarrow> sched_policy (handle_events (E x) (R x)) = Some i"

definition
  "scheduler_invariant x \<equiv> sched_inv x (AT x)"

(*--------------------------------------------------------------------------*)

subsection \<open>The assumed invariants\<close>

text \<open>
The invariants that we assume while proving that the scheduler
invariant holds. The aim is to then prove that these invariants hold
independently.
\<close>

definition
  "EIT_inv x \<equiv> (*finite (EIT x) \<and>*) EIT x \<subseteq> I'"

text \<open>If a user is making an rtos call then preemption is disabled\<close>
definition
  "ghostU_inv x \<equiv> (\<exists>i. (ghostU x) i = Syscall) \<longrightarrow> svc\<^sub>a \<notin> EIT x"

text \<open>Only one user can be making an rtos call\<close>
definition
  "ghostU_inv2 x \<equiv> (\<forall>j. j \<noteq> last (AT x # ATStack x)\<longrightarrow> (ghostU x) j \<noteq> Syscall)"

text \<open>If a user routine has yielded its context is stored correctly\<close>
definition
  "ghostU_inv3 x \<equiv>
    (\<forall>i. i \<in> U \<and> (ghostU x) i = Yield \<longrightarrow>
      curUser x = i \<or> fst (the ((contexts x) i)) = False)"

text \<open>If the $svc_a$ handler is running then only interrupts can be active\<close>
definition
  "ghostP_inv x \<equiv> ghostP x \<longrightarrow> AT x \<in> I'"

text \<open>If ghostP or ghostS is true then the respective task is in the
  ATStack\<close>
definition
  "ghostP_S_stack_inv x \<equiv> (ghostP x \<longrightarrow> svc\<^sub>a \<in> set (AT x # ATStack x)) \<and>
      (ghostS x \<longrightarrow> svc\<^sub>s \<in> set (AT x # ATStack x))"

definition
  "stack_distinct_inv x \<equiv> distinct (AT x # ATStack x)"

text \<open>The last element of the stack is a user\<close>
definition
  "last_stack_inv x \<equiv> last (AT x # ATStack x) \<in> U"

text \<open>Everything but the last of the stack is an interrupt\<close>
definition
  "butlast_stack_inv x \<equiv> set (butlast (AT x # ATStack x)) \<subseteq> I'"

text \<open>The saved stack for every user is the singleton list of just that user.\<close>
definition
  "contexts_stack_inv x \<equiv> \<forall>i \<in> U. snd (the ((contexts x) i)) = [i]"

text \<open>The $svc_s$ and $svc_a$ handlers cannot be executing at the same time.\<close>
definition
  "ghostS_ghostP_inv x \<equiv> \<not> ghostS x \<or> \<not> ghostP x"

fun sorted_by_policy where
  "sorted_by_policy [] = True"
| "sorted_by_policy [x] = True"
| "sorted_by_policy (x # xs) = (x \<in> interrupt_policy (hd xs) \<and> sorted_by_policy xs)"

text \<open>The stack is ordered by the interrupt\_policy\<close>
definition
  "priority_inv x \<equiv> sorted_by_policy (AT x # ATStack x)"

(*<*)

lemmas inv_defs = scheduler_invariant_def
                  sched_inv_def EIT_inv_def ghostU_inv_def
                  ghostU_inv2_def ghostU_inv3_def ghostP_inv_def
                  stack_distinct_inv_def last_stack_inv_def
                  contexts_stack_inv_def butlast_stack_inv_def
                  priority_inv_def ghostS_ghostP_inv_def
                  ghostP_S_stack_inv_def

lemma sorted_by_policy_hd:
  "sorted_by_policy xs \<Longrightarrow> x \<in> set (tl xs) \<Longrightarrow> (hd xs) \<in> interrupt_policy x"
  apply (induct rule: sorted_by_policy.induct)
    apply simp
   apply simp
  apply (fastforce simp: interrupt_policy_self interrupt_policy_trans)
  done

lemma sorted_by_policy_tl[simp]:
  "sorted_by_policy xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> sorted_by_policy (tl xs)"
  by (rule sorted_by_policy.cases) auto

lemma sorted_by_policy_Cons[simp]:
  "sorted_by_policy (x # xs) \<Longrightarrow> sorted_by_policy xs"
  by (cases xs) auto

lemma sorted_by_policy_hd':
  "\<lbrakk>sorted_by_policy xs; x \<in> set xs \<rbrakk> \<Longrightarrow> x \<notin> interrupt_policy (hd xs)"
  apply (cases xs, simp)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: interrupt_policy_self)
  apply (frule sorted_by_policy_hd, simp)
  apply (clarsimp dest!: interrupt_policy_not_refl)
  done

lemma sorted_by_policy_Cons_hd:
  "sorted_by_policy (x # xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> interrupt_policy (hd xs)"
  by (cases xs) auto
(*>*)

end