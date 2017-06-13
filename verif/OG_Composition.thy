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

(*<*)
theory OG_Composition
imports
  OG_More
  "../lib/Hoare_Parallel/OG_Syntax"
begin
(*>*)

section \<open>Compositionality theorem\<close>

text\<open>
When proving that a given invariant @{term I} is preserved during
the execution of a parallel, annotated program @{term c} (i.e. 
when proving @{text "\<parallel>- I  p  c  q"}), it is often needed to
prove that another invariant @{term I'} is also preserved by @{term c}
(i.e. it is often needed to actually prove @{text  "\<parallel>- (I'\<inter>I) p c q"}).

However, @{term I'} often does not need @{term I} and can be 
proved independently (i.e.  @{text "\<parallel>- I' p' c  q'"} can be proved). 
In that case, we would like the proof of @{term I} to {\emph assume} 
@{text I'} (we will denote this @{text  " I' \<parallel>- I  p  c  q"}) and we would
like to get for free that @{text "\<parallel>- (I'\<inter>I) (p\<inter>p') c (q\<inter>q')"}.

We want the following theorem:\<close>
theorem
  "\<lbrakk>I' \<parallel>-\<^sub>i I  p  c  q ; \<parallel>-\<^sub>i I' p' c  q'\<rbrakk> \<Longrightarrow>
   \<parallel>-\<^sub>i (I'\<inter>I) (p\<inter>p') c (q\<inter>q')"
(*<*) oops (*>*)

text \<open>
In practice, c is an annotated program where the annotations
depend a lot of the property being proved. So the annotations
to prove @{term I'} are going to be different from the ones
needed to prove @{term I}. The program text (without annotations)
should be the same, but the annotations for the final
theorem of @{term "I'\<inter>I"} should be the conjunction of the annotations
used to prove @{term I'} and the ones used to proved @{term I} 
assuming @{term I'}.

We want the following theorem:\<close>
theorem
  "\<lbrakk> I' \<parallel>-\<^sub>i I  p  c  q ; \<parallel>-\<^sub>i I' p' c'  q' ; merge_prog_com c c' = Some c''\<rbrakk> \<Longrightarrow>   
   \<parallel>-\<^sub>i (I'\<inter>I) (p\<inter>p') c'' (q\<inter>q')"
(*<*) oops (*>*)

text \<open>
This theorem allows the proof of invariants to be compositional 
and performed by different people.
\<close> 

(* -------------------------------------------------------------- *)

subsection\<open>Checking programs are the same (up to annotations)\<close>

text \<open>Here we define a predicates that tells if 2 annotated 
        programs are the same up to their annotations; i.e. the 
        commands are the same, but the annotations may defer.\<close>
        
text \<open>For annotated commands, the command text must be equal, but 
        differences in annotations are discarded.
        
        Note : cruft booleans, denoted by x, x', y, y' here,
               are also discarded and required to be all True.\<close>
fun 
  same_prog_ann_com :: "'a ann_com \<Rightarrow> 'a ann_com \<Rightarrow> bool" 
where
  "same_prog_ann_com (AnnBasic (x, _) f) (AnnBasic(x', _) f') 
      = (f = f' \<and> x \<and> x')"
| "same_prog_ann_com (AnnSeq c1 c2) (AnnSeq c1' c2')
      = (same_prog_ann_com c1 c1' \<and> same_prog_ann_com c2 c2')"
| "same_prog_ann_com (AnnCond1(x, _) bb c1 c2) (AnnCond1(x', _) bb' c1' c2') 
      = (bb = bb' \<and> x \<and> x' \<and> 
         same_prog_ann_com c1 c1' \<and> same_prog_ann_com c2 c2')" 
| "same_prog_ann_com (AnnCond2(x, _) bb c) (AnnCond2(x', _) bb' c') 
      = (bb = bb' \<and> x \<and> x' \<and> same_prog_ann_com c c')"
| "same_prog_ann_com (AnnWhile(x, _) bb (y, _) c) (AnnWhile(x', _) bb' (y', _) c') 
      = (bb = bb' \<and> x \<and> x' \<and> y \<and> y' \<and> same_prog_ann_com c c')"
| "same_prog_ann_com (AnnAwait(x, _) bb c) (AnnAwait(x', _) bb' c')
      = (bb = bb' \<and> c = c' \<and> x \<and> x')"
| "same_prog_ann_com _ _ 
      = False"

text \<open>For a given program in a parallel composition,
        the program is a list of pairs, where the first element
        is an option of annotated command and the second element
        is the assertion. 
        Two lists are the same-up-to-annotations if their elements 
        are pairwise the same-up-to-annotations.
        Two elements are the same-up-to-annotations if their first 
        elements are either both None, or both Some of annotated commands 
        that are the same-up-to-annotations.
\<close>
        
        
definition
  same_prog_aux:: "('a ann_com option \<times> 'a assn) \<Rightarrow> 
                   ('a ann_com option \<times> 'a assn) \<Rightarrow> bool" 
where
  "same_prog_aux c1 c2 =
     (case (fst c1, fst c2) of
        (Some ac1, Some ac2) \<Rightarrow>  (same_prog_ann_com ac1 ac2)
       |(None, None) \<Rightarrow> True
       |_ \<Rightarrow> False)"

definition 
  same_prog_list_aux:: "('a ann_com option \<times> 'a assn) list \<Rightarrow>
                        ('a ann_com option \<times> 'a assn) list \<Rightarrow> bool"
where
  "same_prog_list_aux Ts Ts' =
      ((length Ts = length Ts') \<and>
       (foldr (op \<and>) (map (\<lambda>p. same_prog_aux (fst p) (snd p)) (zip Ts Ts')) True))"
    (*  
        What this does:
        same_prog_list_aux [..., xi, ...] [... yi, ...] 
        = (foldr (op \<and>) (map (\<lambda>p. same_prog_aux (fst p) (snd p)) [...,(xi,yi),...) True))
        = (foldr (op \<and>) (..., same_prog_aux xi yi, ...) True)
        = (same_prog_aux x0 y0 \<and> (same_prog_aux x1 y1 \<and> ( ... \<and> True)))
      *)

lemma same_prog_list_aux_cons [intro!]:
  "same_prog_list_aux xs xs' \<Longrightarrow>  
   same_prog_aux x x' \<Longrightarrow> 
   same_prog_list_aux (x#xs) (x'#xs') " 
  unfolding same_prog_list_aux_def same_prog_aux_def
  by (auto split: prod.split_sel_asm option.split_sel_asm  prod.split_sel option.split_sel)

text \<open>
  Two parallel programs are the same-up-to-annotations if their
  sequential parts are identical (no annotations), and the list of their
  parallel programs are the same-up-to-annotations.
\<close>

fun 
  same_prog_com :: "'a com \<Rightarrow> 'a com \<Rightarrow> bool" 
where 
  "same_prog_com (Parallel Ts) (Parallel Ts') 
    = same_prog_list_aux Ts Ts'"
| "same_prog_com (Basic f) (Basic f') 
    = (f = f')" 
| "same_prog_com (Seq c1 c2) (Seq c1' c2') 
    = (same_prog_com c1 c1' \<and> same_prog_com c2 c2')" 
| "same_prog_com (Cond bb c1 c2) (Cond bb' c1' c2') 
    = (bb = bb' \<and> same_prog_com c1 c1' \<and> same_prog_com c2 c2')"
| "same_prog_com (While bb _ c) (While bb' _ c')
    = (bb = bb' \<and> same_prog_com c c')"
| "same_prog_com _ _ 
    = False"

text \<open>
  Two parametrized parallel programs are the same-up-to-annotations if their
  parametrized codes are the same-up-to-annotations.
\<close>

lemma same_prog_scheme [intro!]:
  "\<forall>i \<in> {j..<k} . same_prog_ann_com (c i) (c' i) \<Longrightarrow> 
  same_prog_list_aux (map (\<lambda>i. (Some (c i), q)) [j..<k])
                      (map (\<lambda>i. (Some (c' i), q')) [j..<k])"
  unfolding same_prog_list_aux_def same_prog_aux_def
  by (induct k, simp_all)
 
lemma same_prog_scheme' [intro!]:
  "\<forall>i \<in> {j..<k} . same_prog_ann_com (c i) (c' i) \<Longrightarrow>
  (*same_prog_list_aux (SCHEME [j \<le> i < k] c i q) (SCHEME [j \<le> i < k] c' i q')*)
  same_prog_com (COBEGIN SCHEME [j \<le> i < k] c i q COEND)
                (COBEGIN SCHEME [j \<le> i < k] c' i q' COEND)"
  by clarsimp

(* -------------------------------------------------------------- *)

subsection\<open>Merging annotations of a same program\<close>

text \<open>Here we define the merge of 2 annotated programs. This is a
        partial function (returning an option type), which returns
        @{term None} if the programs are not the same up to annotations.
        If the programs are the same up to annotations, then
        the output annotated program is the same program where
        the annotations are the conjunction of the annotations
        of the 2 input programs.\<close>

subsubsection \<open>Definition of the merge\<close>        

(* Discards cruft booleans, denoted by x, x', y, y' here, and requires all to be True *)
fun merge_ann_com:: "'a ann_com \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com option"
where
  "merge_ann_com (AnnBasic (x, r) f) (AnnBasic(x', r') f') =
        (if f \<noteq> f' \<or> \<not> x \<or> \<not> x' then None else Some (AnnBasic(True, r \<inter> r') f))"
| "merge_ann_com (AnnSeq c1 c2) (AnnSeq c1' c2') =
        (case (merge_ann_com c1 c1') of None \<Rightarrow> None
         | Some c1'' \<Rightarrow>
         (case (merge_ann_com c2 c2') of None \<Rightarrow> None
          | Some c2'' \<Rightarrow> Some (AnnSeq c1'' c2'')))"
| "merge_ann_com (AnnCond1(x, r) bb c1 c2) (AnnCond1(x', r') bb' c1' c2') =
        (if bb \<noteq> bb' \<or> \<not> x \<or> \<not> x' then None else
         (case merge_ann_com c1 c1' of None \<Rightarrow> None
          | Some c1'' \<Rightarrow>
          (case merge_ann_com c2 c2' of None \<Rightarrow> None
           | Some c2'' \<Rightarrow> Some (AnnCond1(True, r \<inter> r') bb c1'' c2''))))"
| "merge_ann_com (AnnCond2(x, r) bb c) (AnnCond2(x', r') bb' c') =
        (if bb \<noteq> bb' \<or> \<not> x \<or> \<not> x' then None else
         (case merge_ann_com c c' of None \<Rightarrow> None
          | Some c'' \<Rightarrow> Some (AnnCond2(True, r \<inter> r') bb c'')))"
| "merge_ann_com (AnnWhile(x, r) bb (y, i) c) (AnnWhile(x', r') bb' (y', i') c') =
        (if bb \<noteq> bb' \<or> \<not> x \<or> \<not> x' \<or> \<not> y \<or> \<not> y' then None else
         (case merge_ann_com c c' of None \<Rightarrow> None
          | Some c'' \<Rightarrow> Some (AnnWhile(True, r \<inter> r') bb (True, i \<inter> i') c'')))"
| "merge_ann_com (AnnAwait(x, r) bb c) (AnnAwait(x', r') bb' c') =
        (* Assume here that c, c' are non-looping and contain no annotations to merge. *)
        (if bb \<noteq> bb' \<or> c \<noteq> c' \<or> \<not> x \<or> \<not> x'
         then None
         else Some (AnnAwait(True, r \<inter> r') bb c))"
| "merge_ann_com _ _ = None"

definition 
  merge_prog_aux:: "('a ann_com option \<times> 'a assn) \<Rightarrow> 
                    ('a ann_com option \<times> 'a assn) \<Rightarrow>
                    ('a ann_com option \<times> 'a assn) option"
where
  "merge_prog_aux c c' \<equiv>
      (case (c,c') of 
         ((Some ac, aa), (Some ac', aa')) \<Rightarrow> 
             (case (merge_ann_com ac ac') of 
                  None \<Rightarrow> None
                 |Some ac'' \<Rightarrow> Some (Some ac'', aa\<inter>aa'))
        |((None,aa),(None,aa')) \<Rightarrow> Some (None, aa\<inter>aa')
        | _ \<Rightarrow> None)"

definition
  merge_prog_list_aux:: "('a ann_com option \<times> 'a assn) list \<Rightarrow>
                         ('a ann_com option \<times> 'a assn) list \<Rightarrow>
                         ('a ann_com option \<times> 'a assn) list option"
where
  "merge_prog_list_aux Ts Ts' =
      (if (length Ts \<noteq> length Ts') then None 
       else those (map (\<lambda>p. merge_prog_aux (fst p) (snd p)) (zip Ts Ts')))"


fun merge_prog_com :: "'a com \<Rightarrow> 'a com \<Rightarrow> 'a com option"
where
  "merge_prog_com (Parallel Ts) (Parallel Ts') =
      (case merge_prog_list_aux Ts Ts' of None \<Rightarrow> None
        | Some Ts'' \<Rightarrow> Some (Parallel Ts''))"
| "merge_prog_com (Basic f) (Basic f') =
      (if (f = f') then Some (Basic f) else None)" 
| "merge_prog_com (Seq c1 c2) (Seq c1' c2') =
      (case merge_prog_com c1 c1' of None \<Rightarrow> None
       | Some c1'' \<Rightarrow>
       (case merge_prog_com c2 c2' of None \<Rightarrow> None
        | Some c2'' \<Rightarrow> Some (Seq c1'' c2'')))"
| "merge_prog_com (Cond bb c1 c2) (Cond bb' c1' c2') =
      (if (bb \<noteq> bb') then None else
       (case merge_prog_com c1 c1' of None \<Rightarrow> None
        | Some c1'' \<Rightarrow> 
        (case merge_prog_com c2 c2' of None \<Rightarrow> None
         | Some c2'' \<Rightarrow> Some (Cond bb c1'' c2''))))"
| "merge_prog_com (While bb i c) (While bb' i' c') =
      (if (bb \<noteq> bb') then None else
        (case merge_prog_com c c' of None \<Rightarrow> None
         | Some c'' \<Rightarrow> Some (While bb (i \<inter> i') c'')))"
| "merge_prog_com _ _ = None"

subsubsection \<open>Lemmas about merge\<close>  

(* FIXME: check which ones are really used, redundant, etc *)

lemma not_same_wont_merge_ann_com: 
  "\<not> same_prog_ann_com c c' \<Longrightarrow> merge_ann_com c c' = None"
  apply (induct rule:same_prog_ann_com.induct)
  by (auto  split:option.split)

lemma no_merge_imp_not_same_ann_com: 
  "merge_ann_com c c' = None \<Longrightarrow> \<not> same_prog_ann_com c c'"
  apply (induct rule:merge_ann_com.induct)
  by (auto split:option.splits if_splits)

lemma no_merge_iff_not_same_ann_com: 
  "merge_ann_com c c' = None = (\<not> same_prog_ann_com c c')"
  by (auto simp: not_same_wont_merge_ann_com no_merge_imp_not_same_ann_com)

lemma will_not_fail_merge_same_ann_com:
  "same_prog_ann_com c c' \<Longrightarrow> merge_ann_com c c' \<noteq> None"
  by (auto simp:no_merge_iff_not_same_ann_com)

lemma will_merge_same_ann_com:
  "same_prog_ann_com c c' \<Longrightarrow> \<exists> c''. merge_ann_com c c' = Some c''"
  by (drule will_not_fail_merge_same_ann_com, simp)
 
lemma merged_imp_same_ann_com: 
  "merge_ann_com c c' = Some c'' \<Longrightarrow> same_prog_ann_com c c'"
  apply (rule ccontr)
  apply (frule not_same_wont_merge_ann_com)
  apply simp
  done

lemma not_same_wont_merge_prog_aux: 
  "\<not> same_prog_aux cs cs' \<Longrightarrow> merge_prog_aux cs cs' = None"
  unfolding same_prog_aux_def merge_prog_aux_def
  by (auto split: option.splits prod.splits simp: merged_imp_same_ann_com) 
  
lemma no_merge_imp_not_same_prog_aux: 
  "merge_prog_aux cs cs' = None \<Longrightarrow> \<not> same_prog_aux cs cs'"
  unfolding same_prog_aux_def merge_prog_aux_def
  by (auto split: option.splits prod.splits simp: no_merge_iff_not_same_ann_com)

lemma no_merge_iff_not_same_prog_aux: 
  "merge_prog_aux cs cs' = None = (\<not> same_prog_aux cs cs')"
  by (auto simp: no_merge_imp_not_same_prog_aux not_same_wont_merge_prog_aux)

lemma will_not_fail_merge_same_prog_aux: 
  "same_prog_aux cs cs' \<Longrightarrow> merge_prog_aux cs cs' \<noteq> None"
  by (auto simp:no_merge_iff_not_same_prog_aux)
  
lemma will_merge_same_prog_aux: 
  "same_prog_aux cs cs' \<Longrightarrow> \<exists> cs''. merge_prog_aux cs cs' = Some cs''"
  by (drule will_not_fail_merge_same_prog_aux, simp)

lemma merged_imp_same_prog_aux: 
  "merge_prog_aux cs cs' = Some cs'' \<Longrightarrow> same_prog_aux cs cs'"
  apply (rule ccontr)
  apply (frule not_same_wont_merge_prog_aux, simp)
  done

lemma not_same_wont_merge_prog_list_aux: 
  "\<not> same_prog_list_aux Ts Ts' \<Longrightarrow>
   merge_prog_list_aux Ts Ts' = None"
  apply (simp add: same_prog_list_aux_def merge_prog_list_aux_def)
  apply (induct Ts arbitrary: Ts'; clarsimp)
  apply (simp add: merged_imp_same_prog_aux zip_Cons1 split: list.splits option.splits)
  done

lemma no_merge_imp_not_same_prog_list_aux: 
  "merge_prog_list_aux Ts Ts' = None \<Longrightarrow> \<not> same_prog_list_aux Ts Ts'"
  apply (simp add: same_prog_list_aux_def merge_prog_list_aux_def)
  apply (induct Ts arbitrary: Ts'; clarsimp)
  apply (simp add: zip_Cons1 split: list.splits option.splits)
  apply (drule will_merge_same_prog_aux, clarsimp)
  done

lemma no_merge_iff_not_same_prog_list_aux: 
  "merge_prog_list_aux Ts Ts' = None = (\<not> same_prog_list_aux Ts Ts')"
  by (auto simp: no_merge_imp_not_same_prog_list_aux
                 not_same_wont_merge_prog_list_aux)

lemma not_same_wont_merge_prog_com:
  "\<not> same_prog_com c c' \<Longrightarrow> merge_prog_com c c' = None"
  by (induct c c' rule:same_prog_com.induct; 
         auto split: option.splits simp: no_merge_iff_not_same_prog_list_aux) 

lemma no_merge_imp_not_same_prog_com:
  "merge_prog_com c c' = None \<Longrightarrow> \<not> same_prog_com c c'"
  by (induct c c' rule:same_prog_com.induct, 
         auto split: if_split_asm option.splits 
                simp: no_merge_imp_not_same_prog_list_aux )

lemma no_merge_iff_not_same_prog_com:
  "merge_prog_com c c' = None = (\<not> same_prog_com c c')"
  by (auto simp: no_merge_imp_not_same_prog_com not_same_wont_merge_prog_com)

lemma merged_imp_same_prog_com:
  "merge_prog_com c c' = Some c'' \<Longrightarrow> same_prog_com c c'"
  apply (rule ccontr)
  apply (frule not_same_wont_merge_prog_com, simp)
  done

lemma merge_ann_com_pre:
  "merge_ann_com x1 x2 = Some x3 \<Longrightarrow>
   pre x1 \<inter> pre x2 = pre x3"
  apply (induct x1 arbitrary:x2 x3, simp_all)
       apply (clarsimp, drule merge_ann_com.elims,
              simp_all add: if_split)
      apply (drule merge_ann_com.elims,
             simp_all add: if_split,
             clarsimp split: option.splits)+
  apply (drule merge_ann_com.elims,
               simp_all add: if_split)       
  done

(*<*)
lemma those_length:
  "those xs = Some ys \<Longrightarrow> length ys = length xs"
  by (induct xs arbitrary: ys; clarsimp split: option.splits)
  
lemma those_some:
  "those xs = Some ys \<Longrightarrow> 
    \<forall>i<length xs. \<exists>x. xs!i=Some x \<and> ys!i = x" 
  by (induct xs arbitrary: ys, 
         auto split:option.splits nat.splits simp:nth_Cons)
  
lemma merge_prog_list_aux_length:
  "merge_prog_list_aux Ts Ts' = Some Ts'' \<Longrightarrow>
   length Ts = length Ts'"
  by (clarsimp  split: if_splits simp: merge_prog_list_aux_def)
  
lemma merge_prog_list_aux_some_length:
  "merge_prog_list_aux Ts Ts' = Some Ts'' \<Longrightarrow>
   length Ts'' = length Ts"
  by (clarsimp  split: if_splits simp: merge_prog_list_aux_def those_length)

lemma pre_merge_ann_com:
  "merge_ann_com a1 a2 = Some a \<Longrightarrow>
   pre (add_inv_assn_com (I1 \<inter> I2) a) =
   pre (add_inv_assn_com I1 a1) \<inter> pre (add_inv_assn_com I2 a2)" 
  by (induct a1 a2 arbitrary: a rule: merge_ann_com.induct;
         clarsimp split: if_splits option.splits; blast) 
  
lemma pre_merge_prog_aux:
  "(merge_prog_aux c1 c2) = Some c \<Longrightarrow>
   pre (the (OG_Hoare.com (add_inv_aux (I1\<inter>I2) c))) =
   pre (the (OG_Hoare.com (add_inv_aux I1 c1))) \<inter> 
   pre (the (OG_Hoare.com (add_inv_aux I2 c2)))"
   unfolding merge_prog_aux_def
   by (auto split:prod.splits option.splits
               simp: add_inv_aux_def pre_merge_ann_com)
   
lemma post_merge_prog_list_aux:
  "merge_prog_list_aux Ts Ts' = Some Ts'' \<Longrightarrow> 
   length Ts = length Ts' \<Longrightarrow>
   \<forall>i < length Ts.
   OG_Hoare.post (add_inv_aux (I' \<inter> I) (Ts'' ! i)) =
   OG_Hoare.post (add_inv_aux I (Ts ! i)) \<inter>
   OG_Hoare.post (add_inv_aux I' (Ts' ! i))"
  unfolding merge_prog_list_aux_def merge_prog_aux_def 
            add_inv_aux_def
  apply (clarsimp split: if_splits)
  apply (drule those_some, clarsimp)
  apply (elim allE impE, assumption)
  apply (auto split: prod.splits option.splits)
  done

lemma merge_prog_list_aux_D:
  "merge_prog_list_aux Ts Ts' = Some Ts'' \<Longrightarrow>
  \<forall>i<length Ts'. merge_prog_aux (Ts!i) (Ts'!i) = Some (Ts''!i)"
  unfolding merge_prog_aux_def merge_prog_list_aux_def
  apply (clarsimp split: if_splits)
  by (drule those_some, auto)

lemma merge_prog_com_Parallel_D:
  "merge_prog_com c c' = Some c'' \<Longrightarrow> 
   c = Parallel Ts \<Longrightarrow>
        (\<exists>Ts' Ts''. 
          c' = Parallel Ts'
        \<and> length Ts = length Ts'
        \<and>  merge_prog_list_aux Ts Ts' = Some Ts''
        \<and>  c'' = Parallel Ts'')"
  by (induct c c' rule: merge_prog_com.induct; 
         clarsimp split: option.splits simp: merge_prog_list_aux_length)  

lemma merge_prog_com_Basic_D:
  "merge_prog_com c c' = Some c'' \<Longrightarrow>
  c = Basic f \<Longrightarrow>
  c' = Basic f \<and>  c'' = Basic f"
  by (induct c c' rule: merge_prog_com.induct; 
         clarsimp split: option.splits if_splits)

lemma merge_prog_com_Seq_D:
  "merge_prog_com c c' = Some c'' \<Longrightarrow>
  c = Seq c1 c2 \<Longrightarrow>
        (\<exists>c1' c2' c1'' c2''. 
          c' = Seq c1' c2'
        \<and>  merge_prog_com c1 c1' = Some c1''
        \<and>  merge_prog_com c2 c2' = Some c2''
        \<and>  c'' = Seq c1'' c2'')"
  by (induct c c' rule: merge_prog_com.induct; 
         clarsimp split: option.splits if_splits)

lemma merge_prog_com_Cond_D:
  "merge_prog_com c c' = Some c'' \<Longrightarrow>
  c = Cond bb c1 c2 \<Longrightarrow>
       (\<exists> c1' c2' c1'' c2''. 
          c' = Cond bb c1' c2'
        \<and>  merge_prog_com c1 c1' = Some c1''
        \<and>  merge_prog_com c2 c2' = Some c2''
        \<and>  c'' = Cond bb c1'' c2'')"
  by (induct c c' rule: merge_prog_com.induct; 
         clarsimp split: option.splits if_splits)

lemma merge_prog_com_While_D:
  "merge_prog_com c c' = Some c'' \<Longrightarrow>
   c = While bb i c1 \<Longrightarrow>
        (\<exists> c1' i' c1'' i''. 
          c' = While bb i' c1'
        \<and>  merge_prog_com c1 c1' = Some c1''
        \<and>  c'' = While bb (i\<inter>i') c1'')"
  by (induct c c' rule: merge_prog_com.induct; 
         clarsimp split: option.splits if_splits)

lemma merge_ann_com_add_inv_assn_com:
  "merge_ann_com ac ac' = Some ac'' \<Longrightarrow>
   merge_ann_com (add_inv_assn_com I ac) (add_inv_assn_com I' ac') =
   Some (add_inv_assn_com (I' \<inter> I) ac'')"
  by (induct ac ac' arbitrary: ac'' rule: merge_ann_com.induct;
         clarsimp split: if_splits option.splits; auto)

lemma merge_prog_aux_add_inv_aux:
  "merge_prog_aux (Ts!i) (Ts'!i) = Some (Ts''!i) \<Longrightarrow>
   length Ts' = length Ts \<Longrightarrow>
   length Ts'' = length Ts \<Longrightarrow> 
   i < length Ts \<Longrightarrow>
   add_inv_aux I (Ts ! i) = (Some c, q) \<Longrightarrow>
   add_inv_aux I' (Ts' ! i) = (Some c', q') \<Longrightarrow>
   \<exists>c''. merge_ann_com c c' = Some c''\<and>
   add_inv_aux (I' \<inter> I) (Ts'' ! i) = (Some c'', q\<inter>q')"
   unfolding merge_prog_aux_def
   by (auto split: prod.splits option.splits 
               simp: add_inv_aux_def merge_ann_com_add_inv_assn_com)
  
lemma atomics_merge:
  "merge_ann_com acj acj' = Some acj''\<Longrightarrow>
  (r'',a) \<in> atomics acj'' \<Longrightarrow>
  (\<exists>r r'. r''=r\<inter>r' \<and> (r,a) \<in> atomics acj \<and> (r',a)\<in>atomics acj')" 
  apply (induct acj acj' arbitrary: acj'' r'' a rule: merge_ann_com.induct; 
         clarsimp split: if_splits option.splits; (meson?; auto))
  done   

lemma assertions_merge:
  "merge_ann_com acj acj' = Some acj'' \<Longrightarrow>
  p'' \<in> assertions acj'' \<Longrightarrow>
  (\<exists>p p'. p''=p\<inter>p' \<and> p \<in> assertions acj \<and> p' \<in>assertions acj')" 
  apply (induct acj acj' arbitrary: acj'' p'' rule: merge_ann_com.induct; 
         clarsimp split: if_splits option.splits; (meson?; auto))
  done
(*>*)

subsubsection \<open>Simple example of merge\<close> 

text \<open>A simple test that doesn't exercise all language features.\<close>

lemma "merge_prog_com
     (COBEGIN
     \<lbrace>a\<rbrace> \<langle>disable_interrupts_p None\<rangle>;;
     \<lbrace>b\<rbrace> \<acute>runnable := handle_events \<acute>irqEvents \<acute>runnable;;
     \<lbrace>c\<rbrace> \<acute>irqEvents := {};;
     \<lbrace>d\<rbrace> \<langle>enable_interrupts_p\<rangle>
     \<lbrace>e\<rbrace> COEND)
     (COBEGIN
     \<lbrace>a'\<rbrace> \<langle>disable_interrupts_p None\<rangle>;;
     \<lbrace>b'\<rbrace> \<acute>runnable := handle_events \<acute>irqEvents \<acute>runnable;;
     \<lbrace>c'\<rbrace> \<acute>irqEvents := {};;
     \<lbrace>d'\<rbrace> \<langle>enable_interrupts_p\<rangle>
     \<lbrace>e'\<rbrace> COEND)
     =
     Some (COBEGIN
     \<lbrace>a \<and> a'\<rbrace> \<langle>disable_interrupts_p None\<rangle>;;
     \<lbrace>b \<and> b'\<rbrace> \<acute>runnable := handle_events \<acute>irqEvents \<acute>runnable;;
     \<lbrace>c \<and> c'\<rbrace> \<acute>irqEvents := {};;
     \<lbrace>d \<and> d'\<rbrace> \<langle>enable_interrupts_p\<rangle>
     \<lbrace>e \<and> e'\<rbrace> COEND)" 
  apply ( clarsimp simp add: merge_prog_list_aux_def merge_prog_aux_def) 
  done



(* -------------------------------------------------------------- *)
 
subsection \<open>Compositionality theorem for identical program\<close>

(*<*)
lemma oghoare_inter [rule_format]:
  " I \<parallel>- p c q \<longrightarrow> (\<forall>p' q' . I \<parallel>- p' c q' \<longrightarrow> I \<parallel>- (p\<inter>p') c (q\<inter>q'))"
  apply (induct  rule:oghoare_induct, (rule TrueI)+)
       \<comment> \<open>Parallel\<close>
       apply clarsimp
       apply (drule Parallel', simp) 
       apply clarsimp  
       apply (rule ParallelConseqRule)
         apply blast
        apply (rule Parallel, auto)[1]
       apply auto[1]
      \<comment> \<open>Basic\<close>
      apply clarsimp
      apply (drule Basic', simp)
      apply (rule Conseq[rotated])
        apply (rule Basic)
       apply (rule subset_refl)
      apply auto[1]
     \<comment> \<open>Seq\<close>
     apply clarsimp 
     apply (drule_tac p=p' in Seq', simp)
     apply clarsimp
     apply (rule Seq, auto)[1]
    \<comment> \<open>Cond\<close>
    apply clarsimp
    apply (drule Cond', simp)
    apply clarsimp
    apply (rule Cond)
     apply (rule Conseq[OF _ _ subset_refl, rotated], fastforce+)[1]
    apply (rule Conseq[OF _ _ subset_refl, rotated], fastforce+)[1]
   \<comment> \<open>While\<close>
    subgoal
    apply clarsimp
    apply (drule While', simp)
    apply clarsimp
    apply (rule Conseq[rotated])
      apply (rule While)
      apply (rule Conseq[OF _ _ subset_refl, rotated])
       by (elim allE, erule (1) mp, fastforce+)
  \<comment> \<open>Conseq\<close>
  apply clarsimp
  apply (rule Conseq[rotated])
    by (elim allE, erule (1) mp, auto)
(*>*)  

lemma oghoare_inter_conseq:
  "\<lbrakk>I \<parallel>- p c q; I \<parallel>- p' c q'; p''\<subseteq>(p\<inter>p'); (q\<inter>q')\<subseteq>q''\<rbrakk> \<Longrightarrow>
   I \<parallel>- p'' c q''" 
  by (drule oghoare_inter, simp, rule Conseq, auto)
  
lemma ann_hoare_composition:
  " I' \<turnstile> (add_inv_assn_com I c)  (q\<inter>I)  \<Longrightarrow>
       \<turnstile> (add_inv_assn_com I' c) (q\<inter>I') \<Longrightarrow>  
       I''=I'\<inter>I \<Longrightarrow> 
       \<turnstile> (add_inv_assn_com I'' c) (q\<inter>I'\<inter>I)"
  \<comment>\<open>Proof\<close>
  apply (induct c  arbitrary: q, simp_all)
       apply (clarsimp split: prod.splits)
       apply (drule AnnBasic', simp)+
       apply (rule AnnBasic) 
       apply blast
      apply (drule AnnSeq', simp)+
      apply clarsimp
      apply (rule AnnSeq, simp add: pre_add_inv_assn_com inf_assoc)
      apply auto[1]
     apply clarsimp
     apply (drule AnnCond1', simp)+
     apply clarsimp 
     apply (rule AnnCond1, auto simp add: pre_add_inv_assn_com)[1]
    apply clarsimp
    apply (drule AnnCond2', simp)+
    apply clarsimp 
    apply (rule AnnCond2, auto simp add: pre_add_inv_assn_com)[1]
   apply clarsimp
   apply (drule AnnWhile', simp)+
   apply (clarsimp simp: pre_add_inv_assn_com)
   apply (rule AnnWhile)
      apply blast
     apply (auto simp add: pre_add_inv_assn_com)[1]
    apply (simp add: inf_assoc)
   apply blast
  apply clarsimp
  apply (drule AnnAwait', simp)+
  apply clarsimp
  apply (rule AnnAwait, simp)
  apply clarsimp
  apply (rule oghoare_inter_conseq, assumption, assumption, blast, blast)
  done           
  (*>*)

(*<*)
lemma com_validity_weaker:
  "\<lbrakk> \<parallel>= p a q; p'\<subseteq>p; q\<subseteq>q' \<rbrakk> \<Longrightarrow> \<parallel>= p' a q'" 
  by (auto simp: com_validity_def SEM_def)

lemma com_validity_inter:
  "\<lbrakk> \<parallel>= p a q; \<parallel>= p' a q' \<rbrakk> \<Longrightarrow> \<parallel>= (p\<inter>p') a (q\<inter>q')" 
  by (auto simp: com_validity_def SEM_def)
(*>*)

lemma interfree_composition:
  "interfree I' (map (add_inv_aux I) xs) \<Longrightarrow>
   interfree UNIV (map (add_inv_aux I') xs) \<Longrightarrow> 
   interfree UNIV (map (add_inv_aux (I' \<inter> I)) xs)"   
  \<comment>\<open>Proof\<close>
  (*<*)
  apply (clarsimp simp: interfree_def)
  apply (rename_tac i j)
  apply (erule_tac x=i in allE, erule_tac x=i in allE)
  apply (erule_tac x=j in allE, erule_tac x=j in allE)   
  apply (erule impE, simp)+
  apply (clarsimp simp: post_add_inv_aux)
  
  apply (simp add: interfree_aux_def)
  
  apply (case_tac "xs!j", clarsimp, rename_tac acj_o aaj r a co'')
  apply (case_tac acj_o, simp add: add_inv_aux_def, clarsimp)
  apply (rename_tac aaj r a co'' acj)
  apply (clarsimp simp: add_inv_aux_def)
  
  apply (clarsimp simp: atomics_add_assn_com)
  apply (rename_tac a acj rr)
  apply (erule_tac x="rr\<inter>I" in allE, erule_tac x=a in allE, erule impE, blast)
  apply (erule_tac x="rr\<inter>I'" in allE, erule_tac x=a in allE, erule impE, blast)
  apply clarsimp
  
  apply (rule conjI)
   apply (auto simp: com_validity_def SEM_def)[1]
  apply clarsimp
    
  apply (case_tac "xs!i", simp_all, rename_tac aci_o aai)   
  apply (case_tac aci_o, simp_all, clarsimp, rename_tac aci)
   
  apply (clarsimp simp: assertions_add_assn_com, rename_tac rrp)
  apply (erule_tac x="rrp\<inter>I" in allE, erule impE, blast)
  apply (erule_tac x="rrp\<inter>I'" in allE, erule impE, blast)
  apply (auto simp: com_validity_def SEM_def)[1] 
  apply fastforce 
  done
  (*>*)  

lemmas While_helper = Conseq[OF _ While, rotated, OF Conseq[rotated], OF _ subset_refl]
  
theorem oghoare_composition:
  " I' \<parallel>-\<^sub>i I  p  c  q  \<Longrightarrow>
       \<parallel>-\<^sub>i I' p' c  q'  \<Longrightarrow> 
       \<parallel>-\<^sub>i (I'\<inter>I) (p\<inter>p') c (q\<inter>q')"
  \<comment>\<open>Proof\<close>
  (*<*)
  apply (induct c arbitrary: p p' q q', simp_all add:oghoare_inv_def)
      \<comment> \<open>Parallel\<close>
      apply (drule Parallel', simp)+
      apply clarsimp 
      apply (rule ParallelConseqRule) 
        apply (simp add: length_map)
        apply (drule Int_mono, assumption)             
        apply (rule subset_trans, assumption)
        apply (simp only: INT_extend_simps(6))
        apply (simp only: INT_Int_distrib[symmetric])
        apply (rule INT_anti_mono, simp)
        apply (simp add: Int_commute)
        apply (clarsimp simp: add_inv_aux_def pre_add_inv_assn_com
                        split:prod.split option.splits)
        apply blast
        
       apply (rule Parallel)
        apply (clarsimp simp:map_ann_hoare_def )
        apply (erule allE, erule impE, assumption)+
        apply clarsimp
        apply (simp add:add_inv_aux_def)
        apply (rename_tac x p p' q q' i c ca qa qb)
        apply (case_tac "x ! i")
        apply (rename_tac a b)
        apply (case_tac a, clarsimp)
        apply clarsimp
        apply (simp add: inf_assoc[symmetric])
        apply (drule ann_hoare_composition, assumption, auto)[1]
       apply (clarsimp simp:map_ann_hoare_def interfree_composition) 
      apply (rule Int_greatest)+
        apply (erule subset_trans[rotated])
        apply (rule INT_anti_mono, auto)[1] 
        apply (simp add: post_add_inv_aux)  
       apply (erule subset_trans[rotated])
       apply (rule INT_anti_mono, auto)[1] 
       apply (simp add: post_add_inv_aux)
     \<comment> \<open>Basic\<close>
     apply (drule Basic', simp)+
     apply (rule BasicRule, auto)[1]
    \<comment> \<open>Seq\<close>
    apply (drule Seq', simp)+
    apply clarsimp  
    apply (blast intro:Seq)
   \<comment> \<open>Cond\<close>
   apply (drule Cond', simp)+
   apply clarsimp
   apply (rule Cond) 
    apply (rule Conseq[rotated], fastforce+)[1]
   apply (rule Conseq[rotated], fastforce+)[1]
  \<comment> \<open>While\<close>
  apply (drule While', simp)+
  apply clarsimp
  apply (rule While_helper)
     by auto
  (*>*)


(* -------------------------------------------------------------- *)
 
subsection \<open>Compositionality theorem for merged program\<close>
  
text \<open>
In practice, when proving different invariants about the same
program, the annotations used are different. This means that
effectively the annotated programs are different. What we want
is to be able to show invariants about a program and automatically
get the conjunctions of the invariants for the merged programs 
(same program with merged annotations).\<close>

(*<*)  
lemma pre_add_inv_assn_com_inter_merge:
   "merge_ann_com (add_inv_assn_com I c) (add_inv_assn_com I' c') = 
      Some (add_inv_assn_com (I'\<inter>I) c'') \<Longrightarrow>
    pre (add_inv_assn_com (I'\<inter>I) c'') =  
    pre (add_inv_assn_com I c) \<inter> pre (add_inv_assn_com I' c')" 
  apply (drule_tac pre_merge_ann_com) 
  apply (rule_tac I1=I in subst[OF add_inv_assn_com_idempotent])
  apply (rule_tac I1=I' in subst[OF add_inv_assn_com_idempotent])
  apply (rule_tac I1="I'\<inter>I" in subst[OF add_inv_assn_com_idempotent])
  apply (simp add: Int_commute)
  done

lemma ann_hoare_composition_merge:
  "I' \<turnstile> (add_inv_assn_com I c) (q \<inter> I) \<Longrightarrow>
      \<turnstile> (add_inv_assn_com I' c') (q' \<inter> I')  \<Longrightarrow>
   merge_ann_com (add_inv_assn_com I c) (add_inv_assn_com I' c') = 
        Some (add_inv_assn_com (I' \<inter> I) c'') \<Longrightarrow>
     \<turnstile> (add_inv_assn_com (I'\<inter>I) c'') (q\<inter>I \<inter> (q'\<inter>I'))"
  apply (induct c arbitrary: I q c' I' q' c'', simp_all)
       \<comment> \<open>AnnBasic\<close>
       apply clarsimp
       apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits)
       apply (drule add_inv_assn_com.elims, simp_all, clarsimp)
       apply (drule AnnBasic', simp)+      
       apply (rule AnnBasic)
       apply blast
      \<comment> \<open>AnnSeq\<close>
      apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits option.splits)
      apply (drule add_inv_assn_com.elims, simp_all, clarsimp)+
      apply (drule AnnSeq', simp)+
      apply (rule AnnSeq) 
       apply (frule_tac c=c1 in pre_add_inv_assn_com_inter_merge)
       apply (frule_tac c=c2 in pre_add_inv_assn_com_inter_merge)
       apply (simp add: pre_add_inv_assn_com) 
       apply auto[1]
      apply auto[1]
     \<comment> \<open>AnnCond1\<close>
     apply (clarsimp split:prod.splits)
     apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits option.splits)
     apply (drule add_inv_assn_com.elims, simp_all, clarsimp)+
     apply (drule AnnCond1', simp)+
     apply clarsimp 
     apply (rule AnnCond1, auto simp add: pre_add_inv_assn_com_inter_merge)[1]
    \<comment> \<open>AnnCond2\<close>
    apply (clarsimp split:prod.splits)
    apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits option.splits)
    apply (drule add_inv_assn_com.elims, simp_all, clarsimp)+
    apply (drule AnnCond2', simp)+
    apply clarsimp 
    apply (rule AnnCond2, auto simp add: pre_add_inv_assn_com_inter_merge)[1]
   \<comment> \<open>AnnWhile\<close> 
   apply (clarsimp split:prod.splits)
   apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits option.splits)
   apply (drule add_inv_assn_com.elims, simp_all, clarsimp)+
   apply (drule AnnWhile', simp)+
   apply clarsimp 
   apply (rule AnnWhile) 
      apply blast
     apply (auto simp add: pre_add_inv_assn_com_inter_merge)[1]
     (* FIXME: try to avoid the rename_tac!*)
    apply (rename_tac a b aa i c I qI qI' x y xb' yb' I' x' r' y' i' c' x'' r'' bb'' y'' i'' c'')
    apply (subgoal_tac "i'' \<inter> (I' \<inter> I) = (i \<inter> I) \<inter> (i' \<inter>I')", simp+)
   apply blast
  \<comment> \<open>AnnAwait\<close>
  apply (clarsimp split:prod.splits)
  apply (erule merge_ann_com.elims, simp_all, clarsimp split: if_splits option.splits)
  apply (drule add_inv_assn_com.elims, simp_all, clarsimp)+
  apply (drule AnnAwait', simp)+
  apply clarsimp
  apply (rule AnnAwait, simp, clarsimp) 
  (* FIXME: try to avoid the rename_tac!*)
  apply (rename_tac a b I qI qI' x x' I' xa r xb r' b' c')
  apply (drule oghoare_inter, simp)
  apply (rule_tac p="(b \<inter> I \<inter> b' \<inter> I' \<inter> (r \<inter> I' \<inter> b'))" in Conseq)
    apply auto
  done

lemma interfree_aux_composition_merge:
  "interfree_aux I'
         (OG_Hoare.com (add_inv_aux I xsi), 
          OG_Hoare.post xsi \<inter> I,
          OG_Hoare.com (add_inv_aux I xsj)) \<Longrightarrow>
   interfree_aux UNIV
         (OG_Hoare.com (add_inv_aux I' xsi'),
          OG_Hoare.post xsi' \<inter> I',
          OG_Hoare.com (add_inv_aux I' xsj')) \<Longrightarrow>
   merge_prog_aux xsi xsi' = Some xsi'' \<Longrightarrow>
   merge_prog_aux xsj xsj' = Some xsj'' \<Longrightarrow>
   interfree_aux UNIV
         (OG_Hoare.com (add_inv_aux (I' \<inter> I) xsi''),
          OG_Hoare.post xsi'' \<inter> (I' \<inter> I),
          OG_Hoare.com (add_inv_aux (I' \<inter> I) xsj''))"
  apply (clarsimp simp: interfree_aux_def merge_prog_aux_def com_add_inv_aux 
                        atomics_add_assn_com
                  split: prod.splits option.splits)
   apply (drule atomics_merge, assumption, clarsimp) 
   apply (erule allE, erule allE, erule impE, rule exI, rule conjI, assumption, rule refl)+
   apply (rename_tac aaj aaj' aai aai' acj' acj acj'' a r r')
   apply (drule com_validity_inter, assumption)
   subgoal by (rule com_validity_weaker, fastforce+)
  apply (drule atomics_merge, assumption, clarsimp)
  apply (erule allE, erule allE, erule impE, rule exI, rule conjI, assumption, rule refl)+
  apply (clarsimp simp: assertions_add_assn_com)
  apply (rename_tac aaj aaj' aai aai' acj' acj aci aci' acj'' aci'' a r r')
  apply (rule conjI)
   apply (drule com_validity_inter, assumption)
   subgoal by (rule com_validity_weaker, fastforce+)
  apply clarsimp  
  apply (drule assertions_merge, assumption, clarsimp)
  apply (erule allE, erule impE, rule exI, rule conjI, assumption, rule refl)+
  apply (drule_tac q="p \<inter> I \<union> - I'" and q'="p' \<inter> I'" in com_validity_inter, assumption) 
  by (rule com_validity_weaker, fastforce+) 
             
lemma interfree_composition_merge:
  "merge_prog_list_aux Ts Ts' = Some Ts'' \<Longrightarrow>
   length Ts = length Ts' \<Longrightarrow>
   length Ts'' = length Ts' \<Longrightarrow>
   interfree I' (map (add_inv_aux I) Ts) \<Longrightarrow>
   interfree UNIV (map (add_inv_aux I') Ts') \<Longrightarrow>
   interfree UNIV (map (add_inv_aux (I' \<inter> I)) Ts'')"
  apply (clarsimp simp: interfree_def post_add_inv_aux)
  by (meson interfree_aux_composition_merge merge_prog_list_aux_D) 
  
theorem oghoare_composition_merge:
  " I' \<parallel>-\<^sub>i I  p  c  q  \<Longrightarrow>
       \<parallel>-\<^sub>i I' p' c'  q'  \<Longrightarrow> 
    merge_prog_com c c' = Some c'' \<Longrightarrow>   
       \<parallel>-\<^sub>i (I'\<inter>I) (p\<inter>p') c'' (q\<inter>q')"
  \<comment>\<open>Proof\<close>
  (*<*)
  apply (induct c c' arbitrary: p p' q q' c'' rule: merge_prog_com.induct; 
         clarsimp split: if_splits option.splits simp: oghoare_inv_def)
  \<comment> \<open>Parallel\<close> 
      apply (frule merge_prog_list_aux_length) 
      apply (frule merge_prog_list_aux_some_length) 
      apply (drule Parallel', simp)+      
      apply (rule ParallelConseqRule)  
        \<comment> \<open>p is subset of pre\<close>
        apply (simp, elim conjE)  
        apply (drule Int_mono, assumption)             
        apply (rule subset_trans, assumption)
        apply (simp only: INT_extend_simps(6))
        apply (simp only: INT_Int_distrib[symmetric])
        apply (rule INT_anti_mono, simp)        
        apply (simp add: Int_commute)
        apply (drule merge_prog_list_aux_D)
        apply (erule allE, erule impE, assumption) 
 (*TODO: clean, rename*)
        apply (case_tac "Ts' ! x", simp)
        apply (case_tac "Ts ! x", simp)
        apply (case_tac a, simp)
         apply (case_tac aa, simp_all) [1]
          apply (clarsimp simp: add_inv_aux_def merge_prog_aux_def 
                          split:prod.splits option.splits)
         apply (clarsimp simp: merge_prog_aux_def) 
        apply clarsimp                 
        apply (case_tac aa, simp) 
         apply (clarsimp simp: merge_prog_aux_def) 
        apply (clarsimp simp: merge_prog_aux_def split: option.splits)
        apply (simp add: pre_add_inv_aux)
        apply (subst pre_add_inv_aux) 
         apply metis
        apply clarsimp
        apply (drule merge_ann_com_pre)
        apply (drule_tac t="_ ! _" in sym)
        apply fastforce
       
       \<comment> \<open>actual Parallel\<close>  
       apply (rule Parallel)
        apply (clarsimp simp:map_ann_hoare_def)
        apply (drule merge_prog_list_aux_D)
        apply (erule allE, erule impE, assumption)+
        apply clarsimp
        apply (drule merge_prog_aux_add_inv_aux, simp_all, clarsimp)
        apply (drule add_inv_aux_D)+
        apply clarsimp
        apply (drule ann_hoare_composition_merge, assumption+, simp) 
       apply (clarsimp simp:map_ann_hoare_def interfree_composition_merge)
      \<comment> \<open>post is subset of q\<close>
      apply (simp add:INTER_eq subset_eq)
      apply (auto simp: post_merge_prog_list_aux) [1]
     \<comment> \<open>Basic\<close>
     apply (drule Basic', simp)+
     apply (rule BasicRule, auto)[1]
    \<comment> \<open>Seq\<close>
    apply (drule Seq', simp)+
    apply clarsimp  
    apply (rule Seq[rotated], fastforce+)[1]
   \<comment> \<open>Cond\<close>

   apply (drule Cond', simp)+ 
   apply clarsimp
   apply (rule Cond)
    apply (rule Conseq[rotated], fastforce+)[1]
   apply (rule Conseq[rotated], fastforce+)[1]
  \<comment> \<open>While\<close>
  apply (drule While', simp)+
  apply clarsimp
  apply (rule While_helper)
     apply fastforce+
  done
  (*<*)

(************************************************************)

theorem ann_oghoare_strengthen_assm:
  "I' \<turnstile> c q \<Longrightarrow>   (I'\<inter>I'') \<turnstile> c q"
  apply (induct c arbitrary: I' q, simp_all)
  (*FIXME: this proof is an exact copy-paste of ann_hoare_composition
           so some refactoring/automation should be possible and done *)
       apply (clarsimp split: prod.splits)
       apply (drule AnnBasic', simp)+
       apply (rule AnnBasic) 
       apply blast
      apply (drule AnnSeq', simp)+
      apply clarsimp
      apply (rule AnnSeq, simp add: pre_add_inv_assn_com inf_assoc)
      apply auto[1]
     apply clarsimp
     apply (drule AnnCond1', simp)+
     apply clarsimp 
     apply (rule AnnCond1, auto simp add: pre_add_inv_assn_com)[1]
    apply clarsimp
    apply (drule AnnCond2', simp)+
    apply clarsimp 
    apply (rule AnnCond2, auto simp add: pre_add_inv_assn_com)[1]
   apply clarsimp
   apply (drule AnnWhile', simp)+
   apply (clarsimp simp: pre_add_inv_assn_com)
   apply (rule AnnWhile)
      apply blast
     apply (auto simp add: pre_add_inv_assn_com)[1]
    apply (simp add: inf_assoc)
   apply blast
  apply clarsimp
  apply (drule AnnAwait', simp)+
  apply clarsimp
  apply (rule AnnAwait, simp)
  apply clarsimp
  apply (rule oghoare_inter_conseq, assumption, assumption, blast, blast)
  done

theorem interfree_strengthen_assm:
  "interfree I' c \<Longrightarrow>  interfree (I' \<inter> I'') c"
  apply (clarsimp simp: interfree_def interfree_aux_def )
  apply (elim allE, erule impE, simp, clarsimp split: prod.splits)
  apply (rename_tac i j r a co')
  apply (erule_tac x="(r,a)" in ballE, simp_all, clarsimp)
  apply (rule conjI)
   apply (rule com_validity_weaker, simp, blast+)
  apply clarsimp
  apply (thin_tac "\<parallel>= _ _ _")
  apply (rename_tac p co)
  apply (erule_tac x=p in ballE, simp_all) 
  apply (rule com_validity_weaker, simp_all, blast+)
  done

theorem oghoare_strengthen_assm:
  "I' \<parallel>-  p  c  q  \<Longrightarrow>  
   (I'\<inter>I'') \<parallel>- p c q"
  apply (induct c arbitrary: p q, simp_all add:oghoare_inv_def)
      \<comment> \<open>Parallel\<close>
      apply (drule Parallel', simp)
      apply (rule ParallelConseqRule; blast?)
      apply (rule Parallel) 
       apply (meson ann_oghoare_strengthen_assm map_ann_hoare_def)
      apply (simp add: interfree_strengthen_assm)
     \<comment> \<open>Basic\<close>
     apply (drule Basic', simp_all)
     apply (rule BasicRule, auto)[1]
    \<comment> \<open>Seq\<close>
    apply (drule Seq', simp)+
    apply (blast intro:Seq)
   \<comment> \<open>Cond\<close>
   apply (drule Cond', simp)+
   apply (rule Cond, auto)[1]
  \<comment> \<open>While\<close>
  apply (drule While', simp, clarsimp)
  apply (rule_tac p="p'" and q="(p'\<inter>-x1)" in Conseq)
    apply simp
   apply (rule While)
   apply simp
  apply simp
  done

theorem oghoare_composition_merge_inter:
  " I' \<parallel>-\<^sub>i I  p  c  q  \<Longrightarrow>
       \<parallel>-\<^sub>i (I'\<inter>I'') p' c'  q'  \<Longrightarrow> 
    merge_prog_com c c' = Some c'' \<Longrightarrow>   
       \<parallel>-\<^sub>i (I'\<inter>I''\<inter>I) (p\<inter>p') c'' (q\<inter>q')"
  apply (rule oghoare_composition_merge)
  unfolding oghoare_inv_def
  apply (drule_tac I''=I'' in oghoare_strengthen_assm)
  apply auto
  done

(*<*)
end
(*>*)
