(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory EChronos_arm_sched_prop_proof_final

imports
  EChronos_arm_sched_prop_proof
  EChronos_arm_sched_prop_stack_invs
  EChronos_arm_sched_prop_contexts_stack_inv
  EChronos_arm_sched_prop_ghostU_inv
  EChronos_arm_sched_prop_ghostP_inv
  OG_Composition
begin

lemma oghoare_assumed_inv_cong:
  "J = J' \<Longrightarrow> oghoare_inv J Inv p c q = oghoare_inv J' Inv p c q"
  by simp

lemma oghoare_assumed_inv_cong':
  "oghoare_inv J Inv p c q \<Longrightarrow> J = J' \<Longrightarrow> oghoare_inv J' Inv p c q"
  by simp

lemma oghoare_inv_cong:
  "Inv = Inv' \<Longrightarrow> oghoare_inv J Inv p c q = oghoare_inv J Inv' p c q"
  by simp

lemma oghoare_inv_cong':
  "oghoare_inv J Inv p c q \<Longrightarrow> Inv = Inv' \<Longrightarrow> oghoare_inv J Inv' p c q"
  by simp

theorem oghoare_inv_strengthen_assm:
  "oghoare_inv J  In p  c  q  \<Longrightarrow>  
   oghoare_inv (J\<inter>J') In p c q"
  unfolding oghoare_inv_def
  by (erule oghoare_strengthen_assm)

lemma eChronos_arm_sched_prop_proof':
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
  \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and> \<acute>ghostP_S_stack_inv \<and>
   \<acute>contexts_stack_inv \<and> \<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostU_inv3 \<and>
   \<acute>EIT_inv \<and> \<acute>ghostP_inv\<rbrace>
  \<parallel>-\<^sub>i \<lbrace>\<acute>scheduler_invariant\<rbrace> \<lbrace>True\<rbrace>
  eChronos_arm_sched_prop_prog
  \<lbrace>False\<rbrace>"
  apply (subst oghoare_assumed_inv_cong)
   prefer 2
   apply (erule eChronos_arm_sched_prop_proof[THEN oghoare_inv_strengthen_assm,
                   where J' = "\<lbrace>\<acute>ghostP_S_stack_inv \<and> \<acute>ghostU_inv3 \<and>
                                \<acute>EIT_inv\<rbrace>"])
  apply (subst Collect_conj_eq_rev)
  apply (rule Collect_cong)
  apply (rule iffI[rotated], simp)
  apply (clarsimp simp: priority_stack_distinct
                        stack_priority_implies_ghostS_ghostP
                        priority_last_stack_butlast_stack)
  done

(*TODO: move to compositionality theory *)
theorem oghoare_composition_mergeI:
  " Inv' \<parallel>-\<^sub>i Inv  p  c  q  \<Longrightarrow>
       \<parallel>-\<^sub>i Inv' p' c'  q'  \<Longrightarrow> 
    Inv''=Inv'\<inter>Inv \<Longrightarrow>
    p''=p\<inter>p' \<Longrightarrow>
    q''=q\<inter>q' \<Longrightarrow>
    merge_prog_com c c' = Some c'' \<Longrightarrow>   
       \<parallel>-\<^sub>i Inv'' p'' c'' q''"
 by (simp add: oghoare_composition_merge)

lemma oghoare_inv_IntI: 
  assumes Inv: "\<parallel>-\<^sub>i Inv p c q"
  and Inv': "\<parallel>-\<^sub>i Inv' p c' q"
  and merge: " merge_prog_com c c' = Some c''"
  shows "\<parallel>-\<^sub>i (Inv \<inter> Inv') p c'' q"
  apply (rule oghoare_composition_mergeI)
       apply (rule Inv[THEN oghoare_inv_strengthen_assm])
      apply clarsimp
      apply (rule Inv')
     apply blast+
  apply (rule merge)
  done

lemma [simp]:
  "\<lbrace>True\<rbrace> = UNIV"
  by simp

lemma will_not_fail_merge_same_prog_com: 
  "same_prog_com cs cs' \<Longrightarrow> merge_prog_com cs cs' = Some (the (merge_prog_com cs cs'))"
  apply (subst option.collapse)
   apply (rule ccontr)
   apply (clarsimp simp: no_merge_imp_not_same_prog_com)
  apply simp
  done

lemma same_prog_ann_com_refl:
  "uses_all_pres c \<Longrightarrow> same_prog_ann_com c c"
  by (induct c) auto

lemma same_prog_list_aux_refl_helper:
  "\<forall>i<length (a # Ts).
           (\<exists>y. OG_Tran.com ((a # Ts) ! i) = Some y) \<longrightarrow>
           uses_all_pres (the (OG_Tran.com ((a # Ts) ! i))) \<Longrightarrow>
   \<forall>i<length Ts.
           (\<exists>y. OG_Tran.com (Ts ! i) = Some y) \<longrightarrow>
           uses_all_pres (the (OG_Tran.com (Ts ! i)))"
  by auto

lemma same_prog_list_aux_refl:
  "(\<forall>i<length Ts. (\<exists>y. OG_Tran.com(Ts ! i) = Some y) \<longrightarrow> uses_all_pres (the(OG_Tran.com(Ts ! i))))
    \<Longrightarrow> same_prog_list_aux Ts Ts"
  apply (simp add: same_prog_list_aux_def same_prog_aux_def)
  apply (induct Ts, simp)
  apply (simp add: same_prog_list_aux_refl_helper)
  apply (drule_tac x=0 in spec)
  apply (clarsimp split: option.splits)
  apply (clarsimp simp: same_prog_ann_com_refl split: option.splits)
  done

lemma same_prog_com_refl:
  "uses_all_pres' c \<Longrightarrow> same_prog_com c c"
  apply (induct c)
  apply (auto simp: same_prog_list_aux_refl)
  done

lemma merge_ann_com_refl:
  "uses_all_pres c \<Longrightarrow> merge_ann_com c c = Some c"
  apply (induct c)
  by auto

lemma merge_prog_list_aux_refl:
  "\<forall>i<length Ts.
              (\<exists>y. OG_Tran.com (Ts ! i) = Some y) \<longrightarrow>
              uses_all_pres (the (OG_Tran.com (Ts ! i)))
    \<Longrightarrow> merge_prog_list_aux Ts Ts = Some Ts"
  apply (simp add: merge_prog_list_aux_def merge_prog_aux_def)
  apply (induct Ts, simp)
  apply (simp add: same_prog_list_aux_refl_helper)
  apply (drule_tac x=0 in spec)
  apply (clarsimp split: option.splits)
  apply (auto simp: merge_ann_com_refl split: option.splits)
  done

lemma merge_prog_com_refl:
  "uses_all_pres' c \<Longrightarrow> merge_prog_com c c = Some c"
  apply (induct c)
  apply (auto simp: merge_prog_list_aux_refl split: option.splits)
  done
    
lemma same_prog_aux_add_await[intro!]:
  "same_prog_ann_com c c'\<Longrightarrow>
  same_prog_aux (Some c, aa)
                (Some c', aa')"
  by (auto simp: same_prog_aux_def)

lemma same_prog_merge''':
  "same_prog_ann_com p1 p2 \<Longrightarrow>
   same_prog_ann_com p2 p3 \<Longrightarrow>
   merge_ann_com p2 p3 = Some p4 \<Longrightarrow>
   same_prog_ann_com p1 p4"
  apply (induct p1 p2 arbitrary: p3 p4
                           rule: same_prog_ann_com.induct; clarsimp)
       apply (erule same_prog_ann_com.elims; fastforce split: option.splits)+
  done

lemma same_prog_merge'':
  "\<lbrakk>same_prog_aux (a, b) (aa, ba); same_prog_aux (aa, ba) (ab, bb);
        merge_prog_aux (aa, ba) (ab, bb) = Some (ac, bc)\<rbrakk>
       \<Longrightarrow> same_prog_aux (a, b) (ac, bc)"
  apply (clarsimp simp: same_prog_aux_def merge_prog_aux_def)
  apply (clarsimp split: option.splits)
  apply (drule_tac s="Some _" in sym)
  apply clarsimp
  apply (rule same_prog_merge'''; simp)
  done

lemma same_prog_merge':
  "\<lbrakk>same_prog_list_aux Ts Ts'; same_prog_list_aux Ts' Ts'';
        merge_prog_list_aux Ts' Ts'' = Some Ts'''\<rbrakk>
       \<Longrightarrow> same_prog_list_aux Ts Ts'''"
  apply (clarsimp simp: same_prog_list_aux_def merge_prog_list_aux_def)
  apply (induct Ts arbitrary: Ts' Ts'' Ts'''; simp)
  apply (clarsimp simp: zip_Cons1 split: list.splits option.splits)
  apply (rule same_prog_merge''; simp)
  done

lemma same_prog_merge:
  "same_prog_com p1 p2 \<Longrightarrow>
   same_prog_com p2 p3 \<Longrightarrow>
   same_prog_com p1 (the (merge_prog_com p2 p3))"
  apply (frule will_not_fail_merge_same_prog_com)
  apply (frule_tac cs=p2 in will_not_fail_merge_same_prog_com)
  apply (induct p1 p2 arbitrary: p3 rule: same_prog_com.induct; simp)
      apply (erule same_prog_com.elims; clarsimp split: option.splits)
      apply (rule same_prog_merge'; simp)
     apply (erule same_prog_com.elims; fastforce split: option.splits)+
  done

lemma uses_all_pres_stack_invs:
  "uses_all_pres' eChronos_arm_sched_prop_stack_invs_prog"
  unfolding eChronos_arm_sched_prop_stack_invs_prog_defs
  apply clarsimp
  apply (case_tac "i=0")
   apply clarsimp
  apply (case_tac "i=Suc 0")
   apply clarsimp
  apply (case_tac "i=Suc (Suc 0)")
   apply clarsimp
  apply clarsimp
  done

lemma same_prog_com_stack_invs:
  "same_prog_com
     eChronos_arm_sched_prop_contexts_stack_inv_prog
     eChronos_arm_sched_prop_stack_invs_prog"
  unfolding eChronos_arm_sched_prop_contexts_stack_inv_prog_defs
            eChronos_arm_sched_prop_stack_invs_prog_defs
  by auto

schematic_goal stack_invs[simplified]:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
   \<parallel>-\<^sub>i \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and> 
        \<acute>ghostP_S_stack_inv \<and> \<acute>contexts_stack_inv\<rbrace>
        ?p
        ?c
        ?q"
  apply (rule oghoare_inv_cong')
   apply (rule oghoare_composition_merge)
     apply (erule eChronos_arm_sched_prop_contexts_stack_inv_proof)
    apply (rule oghoare_inv_cong')
     apply (rule oghoare_composition_merge)
       apply (erule eChronos_arm_sched_prop_ghostP_S_stack_inv_proof)
      apply (erule eChronos_arm_sched_prop_stack_invs_proof[simplified])
     apply (rule will_not_fail_merge_same_prog_com)
     apply (rule same_prog_com_refl)
     apply (rule uses_all_pres_stack_invs)
    apply (subst Collect_conj_eq_rev)+
    apply (rule Collect_cong)
    apply clarsimp
   apply (simp add: merge_prog_com_refl uses_all_pres_stack_invs)
   apply (rule will_not_fail_merge_same_prog_com)
   apply (rule same_prog_com_stack_invs)
  apply (subst Collect_conj_eq_rev)+
  apply (rule Collect_cong)
  apply (fastforce simp: contexts_stack_inv_def)
  done

lemma same_prog_contexts_stack_ghostU_invs:
  "same_prog_com
     eChronos_arm_sched_prop_ghostU_inv_prog
     eChronos_arm_sched_prop_contexts_stack_inv_prog"
  unfolding eChronos_arm_sched_prop_contexts_stack_inv_prog_defs
            eChronos_arm_sched_prop_ghostU_inv_prog_defs
  by auto

lemmas same_prog_stack_ghostU_invs =
   same_prog_merge[OF same_prog_contexts_stack_ghostU_invs
                      same_prog_com_stack_invs]

schematic_goal stack_ghostU_invs[simplified]:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
   \<parallel>-\<^sub>i \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and> 
        \<acute>ghostP_S_stack_inv \<and> \<acute>contexts_stack_inv \<and>
        \<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostU_inv3\<rbrace>
        ?p
        ?c
        ?q"
  apply (rule oghoare_inv_cong')
   apply (rule oghoare_composition_merge)
     apply (erule eChronos_arm_sched_prop_ghostU_inv_proof)
    apply (erule stack_invs)
   apply (rule will_not_fail_merge_same_prog_com)
   apply (rule same_prog_stack_ghostU_invs)
  apply (subst Collect_conj_eq_rev)+
  apply (rule Collect_cong)
  apply (fastforce simp: contexts_stack_inv_def)
  done

lemma same_prog_EIT_ghostU_invs:
  "same_prog_com
     eChronos_arm_sched_prop_EIT_prog
     eChronos_arm_sched_prop_ghostU_inv_prog"
  unfolding eChronos_arm_sched_prop_EIT_prog_defs
            eChronos_arm_sched_prop_ghostU_inv_prog_defs
  by auto

lemmas same_prog_stack_ghostU_EIT_invs =
   same_prog_merge[OF same_prog_EIT_ghostU_invs
                      same_prog_stack_ghostU_invs]

lemma same_prog_ghostP_EIT_invs:
  "same_prog_com
     eChronos_arm_sched_prop_ghostP_prog
     eChronos_arm_sched_prop_EIT_prog"
  unfolding eChronos_arm_sched_prop_EIT_prog_defs
            eChronos_arm_sched_prop_ghostP_prog_defs
  by auto

lemmas same_prog_all_helper_invs =
   same_prog_merge[OF same_prog_ghostP_EIT_invs
                      same_prog_stack_ghostU_EIT_invs]

schematic_goal all_helper_invs[simplified]:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
   \<parallel>-\<^sub>i \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and> 
        \<acute>ghostP_S_stack_inv \<and> \<acute>contexts_stack_inv \<and>
        \<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostU_inv3 \<and>
        \<acute>EIT_inv \<and> \<acute>ghostP_inv\<rbrace>
        ?p
        ?c
        ?q"
  apply (rule oghoare_inv_cong')
   apply (rule oghoare_composition_merge)
     apply (erule rtos_ghostP_inv_holds[THEN oghoare_inv_strengthen_assm,
                   where J' = "\<lbrace>\<acute>J\<rbrace>" for J])
    apply (rule oghoare_inv_cong')
     apply (rule oghoare_inv_IntI)
       apply (erule rtos_EIT_inv_holds[simplified])
      apply (erule stack_ghostU_invs)
     apply (rule will_not_fail_merge_same_prog_com)
     apply (rule same_prog_stack_ghostU_EIT_invs)
    apply (subst Collect_conj_eq_rev)+
    apply (rule Collect_cong)
    apply (rule iffI[rotated])
     apply clarsimp
     apply simp
    apply (clarsimp simp: stack_priority_implies_ghostS_ghostP)
   apply (rule will_not_fail_merge_same_prog_com)
   apply (rule same_prog_all_helper_invs)
  apply (subst Collect_conj_eq_rev)+
  apply (rule Collect_cong)
  apply (fastforce simp: stack_priority_implies_ghostS_ghostP)
  done

lemma same_prog_sched_EIT_invs:
  "same_prog_com
     eChronos_arm_sched_prop_prog
     eChronos_arm_sched_prop_ghostP_prog"
  unfolding eChronos_arm_sched_prop_prog_defs
            eChronos_arm_sched_prop_ghostP_prog_defs
  by auto

lemmas same_prog_all_invs =
   same_prog_merge[OF same_prog_sched_EIT_invs
                      same_prog_all_helper_invs]

schematic_goal all_invs[simplified]:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
   \<parallel>-\<^sub>i (\<lbrace>\<acute>scheduler_invariant\<rbrace> \<inter>
        \<lbrace>\<acute>priority_inv \<and> \<acute>last_stack_inv \<and>
         \<acute>ghostP_S_stack_inv \<and> \<acute>contexts_stack_inv \<and>
         \<acute>ghostU_inv \<and> \<acute>ghostU_inv2 \<and> \<acute>ghostU_inv3 \<and>
         \<acute>EIT_inv \<and> \<acute>ghostP_inv\<rbrace>)
        ?p
        ?c
        ?q"
  apply (rule oghoare_inv_cong')
   apply (rule oghoare_composition_merge)
     apply (erule eChronos_arm_sched_prop_proof')
    apply (erule all_helper_invs)
   apply (rule will_not_fail_merge_same_prog_com)
   apply (rule same_prog_all_invs)
  apply (subst Collect_conj_eq_rev)+
  apply (rule Collect_cong)
  apply fastforce
  done

end