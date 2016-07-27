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
theory EChronos_arm_sched_prop_base

imports
  "OG_More"
  EChronos_arm_sched_prop_state
  "../lib/Hoare_Parallel/OG_Syntax"
  "../lib/subgoal_focus/Subgoal_Methods"
  "../lib/Eisbach_Methods"

begin
(*>*)

subsection\<open>Controlled Owicki-Gries reasoning\<close>

text \<open>
The model of parallel composition allows more interleaving than the
real execution, where only enabled routines can run. To model this we
extend the OG formalisation with our controlled concurrency mechanism;
we use the @{text AT} variable and wrap every instruction of routine
@{text r} in an @{text "AWAIT \<lbrace>\<acute>AT = r\<rbrace>"} statement. The function
@{text add_await_ann_com} performs this process. It uses the given
property to construct an @{text AWAIT} statement which is then added
to every instruction in the given command. The full definition of
@{text add_await_ann_com} is not shown here.
\<close>

definition add_await_routine
where
  "add_await_routine r c \<equiv> add_await_ann_com \<lbrace>\<acute>AT = r\<rbrace> c"

(*--------------------------------------------------------------------------*)

subsection\<open>Few helper lemmas\<close>

text\<open>These lemmas sound trivial but help Isabelle's automated methods.\<close>

(*<*)
       (*
lemma helper:
  "\<lbrakk> x \<in> xs; x \<in> ys; xs \<subseteq> ys\<rbrakk> \<Longrightarrow> insert x (xs - ys) = {x} "
  by (force simp: double_diff)

lemma helper2:
  "\<lbrakk> x \<in> xs; x \<in> ys; xs \<subseteq> ys\<rbrakk> \<Longrightarrow> xs-ys = {}"
 by clarsimp

lemma helper3:
  "\<lbrakk> x \<in> xs; x \<in> ys; xs \<subseteq> ys\<rbrakk> \<Longrightarrow> insert x (xs - ys) \<subseteq> ys "
  by (force simp: double_diff)
*)

(*
lemma helper4:
  "n\<notin>I' \<Longrightarrow> (insert n (xs \<inter> I) - I') = {n}"
  by (auto simp: I_def I'_def)
*)

lemma helper':
    "  Some n = s \<Longrightarrow>
       Some(the s) = s "
     by auto

(*  
lemma helper5:
    "  Some n = sched_policy (handle_events {} (R x)) \<Longrightarrow>
       Some ( the (sched_policy  (R x))) = sched_policy (R x) "
  apply (case_tac "sched_policy (R x)")
  by (simp add: handle_events_empty)+
*)

lemma helper6:
  " \<lbrakk> Some n = a; n \<notin> I \<rbrakk> \<Longrightarrow> the a \<notin> I"
  by auto

lemma helper7:
  "\<lbrakk> A - B = {u}; x \<in> A; x \<notin> B\<rbrakk> \<Longrightarrow> x = u"
  by auto

lemma helper8:
  "card A \<le> Suc 0 \<Longrightarrow> A = {} \<or> (\<exists>u. A = {u}) \<or> \<not> finite A"
  by (auto simp: le_eq_less_or_eq dest: card_eq_SucD)

lemma helper9:
  "svc\<^sub>a \<in> A \<Longrightarrow> \<not> A \<subseteq> I "
  by auto

(*
lemma helper10:
  "n\<notin>I' \<Longrightarrow> (insert n (insert svc\<^sub>a (xs \<inter> I)) - I') = {n}"
  by (auto simp: I_def I'_def)
*)

(*
lemma helper11:
  "x \<notin> A \<Longrightarrow> insert x A - A = {x}"
  by (simp add: insert_Diff_if)
*)

(*
lemma helper12:
  "A \<subseteq> I' \<Longrightarrow> A - I \<subseteq> {svc\<^sub>a}"
  by (auto simp: I_def I'_def)
*)

lemma helper13:
  "x \<in> (if b then c else {}) \<Longrightarrow> b"
  by (case_tac b, auto)

lemma helper14:
  "\<lbrakk>j \<in> A; A \<subseteq> interrupt_policy i\<rbrakk> \<Longrightarrow> j \<in> interrupt_policy i"
  by auto

(* lemma helper15: *)
(*   "\<lbrakk>hd xs \<in> set xs; xs = [hd xs]\<rbrakk> \<Longrightarrow> tl xs = []" *)
(*   by (cases xs) auto *)

lemma helper15:
  "x \<in> set xs \<Longrightarrow> xs \<noteq> []"
  by auto

(* lemma helper16: *)
(*   "tl xs \<noteq> [] \<Longrightarrow> xs \<noteq> [hd xs]" *)
(*   by (cases xs) auto *)

lemma helper16:
  "\<lbrakk>distinct xs; tl xs \<noteq> []\<rbrakk> \<Longrightarrow> last xs \<noteq> hd xs"
  by (cases xs) auto

lemma helper17:
  "\<lbrakk>distinct xs; xs \<noteq> []; last xs = hd xs\<rbrakk> \<Longrightarrow> tl xs = []"
  apply (clarsimp simp: last_conv_nth hd_conv_nth nth_eq_iff_index_eq)
  apply (cases xs, simp+)
  done

lemma helper18:
  "distinct xs \<Longrightarrow> hd xs \<notin> set (tl xs)"
  by (cases xs) auto

lemma helper19[simp]:
  "x \<notin> set xs \<Longrightarrow> x \<notin> set (tl xs)"
  by (cases xs) auto

  lemma helper20:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow> user0 \<notin> I"
  by (auto simp: user0_def I_def)

(*
lemma helper20:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow> nbRoutines - Suc svc\<^sub>a \<noteq> user0"
  by (auto simp: user0_def )
*)

lemma helper21:
  "x \<in> set xs \<Longrightarrow> x = hd xs \<or> x \<in> set (tl xs)"
  by (cases xs) auto

lemma helper21':
  "hd xs \<noteq> x \<Longrightarrow> x \<notin> set (tl xs) \<Longrightarrow> x \<notin> set xs"
  by (cases xs) auto

lemma helper22:
  "xs \<noteq> [] \<Longrightarrow> x \<notin> set xs \<Longrightarrow> x \<noteq> hd xs \<and> x \<notin> set (tl xs)"
  by (cases xs) auto

lemma helper23:
  "\<lbrakk>x \<in> A; x \<in> set xs; last xs \<notin> A \<rbrakk> \<Longrightarrow> tl xs \<noteq> []"
  by (cases xs) auto

lemma helper23':
  "\<lbrakk>x \<notin> A; x \<in> set xs; last xs \<in> A \<rbrakk> \<Longrightarrow> tl xs \<noteq> []"
  by (cases xs) auto

lemma helper24:
  "i \<in> U \<Longrightarrow> i \<notin> interrupt_policy j"
  apply clarsimp
  apply (drule subsetD[OF interrupt_policy_I'])
  apply simp
  done

lemma helper25:
  "i \<notin> I \<Longrightarrow> user0 \<le> i \<Longrightarrow> i < user0 + nbRoutines \<Longrightarrow> i \<in> U"
  by (simp add: I_def U_def)

lemma helper26:
  "y \<in> set xs \<Longrightarrow> last xs \<in> U \<Longrightarrow> y \<notin> U \<Longrightarrow> last xs = x
    \<Longrightarrow> last (tl xs) = x"
  by (auto simp: List.last_tl helper23')

lemma helper27:
  "x = y \<or> P \<Longrightarrow> x \<in> I \<Longrightarrow> y \<notin> I \<Longrightarrow> P"
  by auto

lemmas helper27' = helper27[where y=svc\<^sub>a, simplified]
                   helper27[where y=svc\<^sub>s, simplified]

lemma helper28:
  "x = y \<or> P \<Longrightarrow> x \<in> U \<Longrightarrow> y \<notin> U \<Longrightarrow> P"
  by auto

lemmas helper28' = helper28[where y=svc\<^sub>a, simplified]
                   helper28[where y=svc\<^sub>s, simplified]

lemma helper29:
  "last (x # xs) \<in> U \<Longrightarrow> x \<in> I \<Longrightarrow> xs \<noteq> []"
  by auto

lemma helper30:
  "P \<or> P' \<Longrightarrow> P \<longrightarrow> Q \<Longrightarrow> P' \<longrightarrow> Q \<Longrightarrow> Q"
  by auto

lemma last_in_set_tl:
  "last as \<noteq> hd as \<Longrightarrow> last as \<in> set (tl as)"
  apply (cases as)
   apply (simp add: last_def hd_def)
  apply clarsimp
  done

lemma last_tl_hd:
  "last as \<noteq> hd as \<Longrightarrow> last (tl as) = last as"
  by (cases as) auto

lemmas last_tl' = last_tl[symmetric, THEN subst, rotated]

lemmas set_tl = list.set_sel(2)[rotated]

lemma AT_U_ATStack:
  "AT x \<in> U \<Longrightarrow> set (butlast (AT x # ATStack x)) \<subseteq> I'
  \<Longrightarrow> ATStack x = []"
  by (auto split: split_if_asm)

lemma sorted_by_policy_svc\<^sub>a:
  "sorted_by_policy (x # xs) \<Longrightarrow> svc\<^sub>a \<in> set xs \<Longrightarrow> hd xs \<in> I'"
  apply (drule_tac sorted_by_policy_tl, clarsimp)
  apply (cases xs, simp, clarsimp)
  apply (erule disjE, clarsimp)
  apply (drule_tac x=svc\<^sub>a in sorted_by_policy_hd)
   apply (auto simp: interrupt_policy_svc\<^sub>a)
  done

lemma sorted_by_policy_svc\<^sub>s:
  "sorted_by_policy (x # xs) \<Longrightarrow> svc\<^sub>s \<in> set xs \<Longrightarrow> hd xs \<in> I'"
  apply (drule_tac sorted_by_policy_tl, clarsimp)
  apply (cases xs, simp, clarsimp)
  apply (erule disjE, clarsimp)
  apply (drule_tac x=svc\<^sub>s in sorted_by_policy_hd)
   apply (auto simp: interrupt_policy_svc\<^sub>s)
  done

lemma sorted_by_policy_svc\<^sub>a_single:
  "sorted_by_policy (svc\<^sub>a # xs) \<Longrightarrow> last (svc\<^sub>a # xs) \<in> U
   \<Longrightarrow> \<exists>x. xs = [x]"
  apply (cases xs)
   apply clarsimp
  apply clarsimp
  apply (case_tac list)
   apply clarsimp
  apply (drule_tac x="last xs" in sorted_by_policy_hd)
   apply simp
  apply (clarsimp simp: interrupt_policy_U interrupt_policy_svc\<^sub>a')
  done

lemma sorted_by_policy_svc\<^sub>s_single:
  "sorted_by_policy (svc\<^sub>s # xs) \<Longrightarrow> last (svc\<^sub>s # xs) \<in> U
   (*\<Longrightarrow> svc\<^sub>a \<notin> set xs *)\<Longrightarrow> \<exists>x. xs = [x]"
  apply (cases xs)
   apply clarsimp
  apply clarsimp
  apply (case_tac list)
   apply clarsimp
  apply (drule_tac x="last xs" in sorted_by_policy_hd)
   apply simp
  apply (clarsimp simp: interrupt_policy_U interrupt_policy_svc\<^sub>s')
  done

lemma sorted_by_policy_U_single:
  "sorted_by_policy (x # xs) \<Longrightarrow> x \<in> I \<Longrightarrow> last (x # xs) \<in> U \<Longrightarrow>
   hd xs \<in> U \<Longrightarrow> \<exists>x. xs = [x]"
  apply (cases xs)
   apply clarsimp
  apply (clarsimp split: split_if_asm)
  apply (drule_tac x="last xs" in sorted_by_policy_hd)
   apply simp
  apply (clarsimp simp: interrupt_policy_U)
  done

lemma sorted_by_policy_svc\<^sub>a':
  "\<lbrakk>i \<in> I'; i \<in> set xs; sorted_by_policy xs\<rbrakk>
    \<Longrightarrow> svc\<^sub>a \<notin> interrupt_policy (hd xs)"
  apply (cases xs)
   apply clarsimp
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: interrupt_policy_svc\<^sub>a')
  apply (drule sorted_by_policy_hd, simp)
  apply clarsimp
  apply (drule (1) interrupt_policy_trans)
  apply (clarsimp simp: interrupt_policy_svc\<^sub>a')
  done

lemmas sorted_by_policy_svc\<^sub>a'' =
  sorted_by_policy_svc\<^sub>a'[where i=svc\<^sub>a, simplified]
  sorted_by_policy_svc\<^sub>a'[where i=svc\<^sub>s, simplified]

lemma sorted_by_policy_svc\<^sub>s_svc\<^sub>a:
  "sorted_by_policy (x # xs) \<Longrightarrow> svc\<^sub>s \<in> set xs
    \<Longrightarrow> svc\<^sub>a \<notin> interrupt_policy x"
  apply (cases xs)
   apply clarsimp
  apply clarsimp
  apply (erule disjE)
   apply (drule (1) interrupt_policy_trans, clarsimp)
  apply (drule sorted_by_policy_hd, simp)
  apply clarsimp
  apply (drule (1) interrupt_policy_trans)
  apply (drule (1) interrupt_policy_trans, clarsimp)
  done

lemma sorted_by_policy_U:
  "\<lbrakk>sorted_by_policy (x # xs); x \<in> U\<rbrakk> \<Longrightarrow> xs = []"
  apply (rule ccontr)
  apply (drule_tac x="hd xs" in sorted_by_policy_hd)
   apply simp
  apply (simp add: helper24)
  done

lemma sorted_by_policy_svc\<^sub>s_hd_svc\<^sub>a:
  "sorted_by_policy (svc\<^sub>s # xs) \<Longrightarrow> svc\<^sub>a \<notin> set xs"
  by (auto dest: sorted_by_policy_hd)

lemma sorted_by_policy_svc\<^sub>a_hd_svc\<^sub>s:
  "sorted_by_policy (svc\<^sub>a # xs) \<Longrightarrow> svc\<^sub>s \<notin> set xs"
  by (auto dest: sorted_by_policy_hd)

lemma svc\<^sub>a_interrupt_empty:
  "svc\<^sub>a \<in> interrupt_policy x \<Longrightarrow> sorted_by_policy (x # xs)
   \<Longrightarrow> xs = []"
  apply (cases xs)
   apply clarsimp
  apply clarsimp
  by (drule subsetD[OF interrupt_policy_I'],
      clarsimp simp: interrupt_policy_svc\<^sub>a')

lemma sorted_by_policy_empty':
  "\<lbrakk>svc\<^sub>a \<in> interrupt_policy (hd xs); sorted_by_policy (x # xs); xs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>i. xs = [i]"
  apply (cases xs)
   apply clarsimp
  apply (clarsimp simp: svc\<^sub>a_interrupt_empty split: split_if_asm)
  done

lemma CollectNotD: "a \<notin> {x. P x} \<Longrightarrow> \<not> P a"
  by simp

lemmas Collect_conj_eq_rev = Collect_conj_eq[symmetric]
lemmas subset_eqI = subset_eq[THEN iffD2]

lemma
  union_negI: 
  "(x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> x \<in> A \<union> -B"
  by blast

lemma
  union_negI_drop: 
  "x \<in> A \<Longrightarrow> x \<in> A \<union> -B"
  by blast

lemma
  last_single: 
  "last [x] = x"
  by simp

lemma
   sched_policy_Some_U: 
  "sched_policy xs = (Some n) \<Longrightarrow> n \<in> U"
  using sched_picks_user
  by blast

lemma 
  U_simps:
  "svc\<^sub>a \<notin> U"
  "svc\<^sub>s \<notin> U"
  by (simp add: U_def svc\<^sub>a_def svc\<^sub>s_def user0_def)+

lemmas svc\<^sub>a_commute = eq_commute[where a=svc\<^sub>a]
lemmas svc\<^sub>s_commute = eq_commute[where a=svc\<^sub>s]
lemmas sorted_by_policy_U' = sorted_by_policy_U[THEN arg_cong, THEN eqset_imp_iff]


(* implied invariants *)

lemma sorted_by_policy_distinct: "sorted_by_policy l \<Longrightarrow> distinct l"
  by (induct l, simp) 
     (metis distinct.simps(2) helper15 sorted_by_policy_Cons 
            sorted_by_policy_Cons_hd sorted_by_policy_hd')

lemma priority_stack_distinct: 
  "priority_inv x \<Longrightarrow> stack_distinct_inv x"
  unfolding priority_inv_def stack_distinct_inv_def
  by (rule sorted_by_policy_distinct)

lemma sorted_by_policy_svc\<^sub>a_not_svc\<^sub>s:
  "\<lbrakk>sorted_by_policy l; svc\<^sub>a \<in> set l \<rbrakk> \<Longrightarrow> svc\<^sub>s \<notin> set l"
  by (induct l, simp)
     (metis One_nat_def helper15 insert_iff interrupt_policy_svc\<^sub>a' 
            interrupt_policy_svc\<^sub>s' list.set(2) old.nat.distinct(2)  
            sorted_by_policy_Cons sorted_by_policy_Cons_hd svc\<^sub>a_def
            sorted_by_policy_svc\<^sub>a sorted_by_policy_svc\<^sub>s svc\<^sub>s_def) 

lemma stack_priority_implies_ghostS_ghostP:
  "priority_inv x \<Longrightarrow> ghostP_S_stack_inv x \<Longrightarrow> ghostS_ghostP_inv x"
  by (fastforce 
             simp: priority_inv_def ghostP_S_stack_inv_def 
                   ghostS_ghostP_inv_def svc\<^sub>a_def svc\<^sub>s_def 
             dest: sorted_by_policy_svc\<^sub>a_hd_svc\<^sub>s 
                   sorted_by_policy_svc\<^sub>s_hd_svc\<^sub>a 
                   sorted_by_policy_svc\<^sub>a_not_svc\<^sub>s sorted_by_policy_Cons)

lemma sorted_by_policy_last_U_butlast_I':
  "\<lbrakk>sorted_by_policy l; last l \<in> U\<rbrakk> \<Longrightarrow> set (butlast l) \<subseteq> I'"
  by (induct l, simp_all)
     (metis contra_subsetD interrupt_policy_I' sorted_by_policy_Cons_hd)

  

lemma priority_last_stack_butlast_stack:
  "priority_inv x \<Longrightarrow> last_stack_inv x \<Longrightarrow> butlast_stack_inv x"
  unfolding priority_inv_def last_stack_inv_def butlast_stack_inv_def
  by (drule(2) sorted_by_policy_last_U_butlast_I')

(*--------------------------------------------------------------------------*)

subsection \<open>A model of  hardware interface\<close>

text\<open>
The following two functions are used to enable and disable the
$svc_a$ interrupt. They do this by either adding or removing $svc_a$
from the $EIT$ set.
\<close>

definition
  svc\<^sub>aEnable
where
  "svc\<^sub>aEnable \<equiv> \<acute>EIT := \<acute>EIT \<union> {svc\<^sub>a}"

definition
  svc\<^sub>aDisable
where
  "svc\<^sub>aDisable \<equiv> \<acute>EIT := \<acute>EIT - {svc\<^sub>a}"

text\<open>
\noindent

$\mathitbf{ITake}\ i$ models the hardware mechanism that traps to the
handler for interrupt $i$. First it checks whether the interrupt is
enabled, is not already being handled and is a higher priority than
the current routine. When these conditions are satisfied then the
context\footnote{We only model the part of the context relevant to
controlling the interleaving. Here that is just the previous value of
$AT$, which can be thought of as corresponding to the program counter.
} of the previous task is saved on a stack and $AT$ is set to $i$.

\<close>

definition
  ITake ("_ //ITake _"  [90,0] 61)
where
  "r ITake i \<equiv>
    r
    AWAIT i \<in> \<acute>EIT - set \<acute>ATStack \<and> i \<in> interrupt_policy \<acute>AT
    THEN
     \<acute>ATStack := \<acute>AT # \<acute>ATStack,, \<acute>AT := i
    END"

text\<open>
\noindent
Similarly to above, $\mathitbf{svc_aTake}$ models the hardware
mechanism that traps to the $\mathrm{svc_a}$ handler. It is almost
exactly the same as $\mathitbf{ITake}\ i$, but because we can observe
when $\mathrm{svc_a}$ is requested we now also require that $svc_aReq$
is True before it can begin executing. It also sets $svc_aReq$ to
False while setting $AT$ to $\mathrm{svc_a}$.
\<close>

definition
  svc\<^sub>aTake ("_ //svc\<^sub>aTake"  [90] 61)
where
  "r svc\<^sub>aTake \<equiv>
    r
    AWAIT \<acute>svc\<^sub>aReq \<and> svc\<^sub>a \<in> \<acute>EIT - set \<acute>ATStack \<and>
          svc\<^sub>a \<in> interrupt_policy \<acute>AT
    THEN
      \<acute>ATStack := \<acute>AT # \<acute>ATStack,,
      \<acute>AT := svc\<^sub>a,, \<acute>svc\<^sub>aReq := False
    END"

text\<open>
\noindent
$\mathitbf{IRet}$ models the hardware mechanism used to return from an
interrupt. The main action it performs is to restore the context of
the interrupted routine. It does this by setting $AT$ to the head
$ATStack$, which is then removed from the stack. However, if there is
a pending interrupt that is now allowed to run then $\mathitbf{IRet}$
will transfer control directly to this interrupt instead of restoring
the stored context. Due to the construction of our model we only need
to ensure that this happens for $\mathrm{svc_a}$, as it is the only
interrupt that we can observe has occured.
\<close>

definition
  IRet
where
  "IRet \<equiv>
    IF \<acute>svc\<^sub>aReq \<and> svc\<^sub>a \<in> \<acute>EIT - set \<acute>ATStack \<and> svc\<^sub>a \<in> interrupt_policy (hd \<acute>ATStack)
      THEN \<acute>AT := svc\<^sub>a,, \<acute>svc\<^sub>aReq := False
      ELSE \<acute>AT := hd \<acute>ATStack,, \<acute>ATStack := tl \<acute>ATStack
    FI"

text\<open>
\noindent
When $SVC_s\_now$ is called it triggers an $\mathrm{svc_s}$
interrupt to occur, which is then immediately handled. The effect of
this function is similar to that of $\mathitbf{ITake}$, the active
task is saved on the stack and then $AT$ is set to $svc_s$. We
implicitly assume that $\mathrm{svc_s}$ is enabled when
$SVC_s\_now$ is called, as if this was not true in reality then the
hardware would trigger an abort exception.
\<close>

definition
  SVC\<^sub>s_now
where
  "SVC\<^sub>s_now \<equiv> \<acute>ATStack := \<acute>AT # \<acute>ATStack,, \<acute>AT := svc\<^sub>s"

text\<open>
\noindent
$svc_aRequest$ is used to request that $\mathrm{svc_a}$
occurs as soon as it is next possible.
\<close>

definition
  svc\<^sub>aRequest ("_ //svc\<^sub>aRequest"  [90] 61)
where
  "r svc\<^sub>aRequest \<equiv> r \<acute>svc\<^sub>aReq := True"

definition
  hardware_init
where
  "hardware_init \<equiv>
   \<acute>EIT := I',,
   \<acute>svc\<^sub>aReq := False,,
   \<acute>AT := user0,,
   \<acute>ATStack := []"

definition 
  eChronos_init
where
  "eChronos_init \<equiv>
   \<acute>curUser := user0,,
   \<acute>contexts := (\<lambda>n. if n\<in>U then Some (True, [n]) else None),,
   \<acute>R := (\<lambda>n. if n\<in>U then Some True else None),,
   \<acute>E := {},,
   \<acute>E_tmp := {},,
   \<acute>nextT := None,,
   \<acute>ghostP := False,,
   \<acute>ghostS := False,,
   \<acute>ghostU := (\<lambda>_. User)"

lemmas eChronos_arm_sched_prop_base_defs =
                    add_await_routine_def
                    svc\<^sub>aEnable_def svc\<^sub>aDisable_def ITake_def
                    IRet_def svc\<^sub>aTake_def svc\<^sub>aRequest_def
                    SVC\<^sub>s_now_def hardware_init_def eChronos_init_def

(*<*)
end
(*>*)
