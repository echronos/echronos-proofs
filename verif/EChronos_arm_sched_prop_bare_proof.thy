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

theory EChronos_arm_sched_prop_bare_proof

imports
  EChronos_arm_sched_prop_proof_final
  EChronos_arm_sched_prop_bare

begin

lemma will_not_fail_merge_prog_list_aux:
  "same_prog_list_aux TS TS' \<Longrightarrow> merge_prog_list_aux TS TS' = Some (the (merge_prog_list_aux TS TS'))"
  apply (subst option.collapse)
   apply (rule ccontr)
   apply (clarsimp simp: no_merge_imp_not_same_prog_list_aux)
  apply simp
  done

lemma map_eq_conv_length:
  "length xs = length ys \<Longrightarrow>
     (map f xs = map f ys) = (\<forall>i<length xs. f (xs ! i) = f (ys ! i))"
  apply (induct rule: list_induct2)
   apply simp
  apply (auto simp add: less_Suc_eq_0_disj)
  done

lemma extract_ann_prg_merge_prog:
  "merge_ann_com c c' = Some c'' \<Longrightarrow>
    extract_ann_prg c'' = extract_ann_prg c"
  apply (induct c c' arbitrary: c'' rule: merge_ann_com.induct; clarsimp)
       apply (clarsimp split: if_splits
            | simp(no_asm_use) split: option.splits)+
  done

lemma extract_prg_merge_progI:
  "same_prog_com c c' \<Longrightarrow>
   extract_prg c = c'' \<Longrightarrow>
    extract_prg (the (merge_prog_com c c')) = c''"
  apply (induct c c' arbitrary: c'' rule: same_prog_com.induct; clarsimp)
     apply (drule will_not_fail_merge_prog_list_aux)
     apply (clarsimp split: option.splits, rule conjI, clarsimp)
     apply clarsimp
     apply (clarsimp simp: merge_prog_list_aux_def merge_prog_aux_def
                    split: if_split_asm option.splits)
     apply (frule those_length[symmetric], drule those_some, clarsimp)
     apply (clarsimp simp: map_eq_conv_length)
     apply (drule_tac x=i in spec)
     apply (clarsimp split: option.splits simp:split_def)[1]
     apply (erule extract_ann_prg_merge_prog)
    apply (auto dest: will_not_fail_merge_same_prog_com
               split: option.splits)
  done

lemma same_prog_sched_bare:
  "extract_prg eChronos_arm_sched_prop_prog
     = eChronos_sys"
  unfolding eChronos_arm_sched_prop_prog_defs
            eChronos_sys_defs
  by auto

lemmas same_prog_sched_bare' =
          extract_prg_merge_progI[OF same_prog_all_invs same_prog_sched_bare]

lemma eChronos_scheduler_inv:
  "0 < nbUsers \<and> 0 < nbInts \<Longrightarrow>
    \<parallel>-\<^sub>b \<lbrace>\<acute>scheduler_invariant\<rbrace> \<lbrace>True\<rbrace> eChronos_sys \<lbrace>False\<rbrace>"
  apply (rule oghoare_bareI)
  apply (rule exI, rule conjI, rule same_prog_sched_bare')
  apply simp
  apply (erule all_invs)
  done

end
