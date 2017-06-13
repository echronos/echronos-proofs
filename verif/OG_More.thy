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

theory OG_More

imports
  "../lib/Hoare_Parallel/OG_Tactics"
  "../lib/Hoare_Parallel/Quote_Antiquote"

begin

fun add_inv_assn_com :: "'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com" where
  "add_inv_assn_com I (AnnBasic(x, r) f) = (AnnBasic (x, r\<inter>I) f)"
| "add_inv_assn_com I (AnnSeq c1 c2) =  (AnnSeq (add_inv_assn_com I c1) (add_inv_assn_com I c2))"
| "add_inv_assn_com I (AnnCond1(x, r) bb c1 c2) = (AnnCond1 (x, r\<inter>I) bb (add_inv_assn_com I c1) (add_inv_assn_com I c2))" 
| "add_inv_assn_com I (AnnCond2(x, r) bb c) = (AnnCond2 (x, r\<inter>I) bb (add_inv_assn_com I c))"
| "add_inv_assn_com I (AnnWhile(x, r) bb (y, i) c) = (AnnWhile (x, r\<inter>I) bb (y, i\<inter>I) (add_inv_assn_com I c))"
| "add_inv_assn_com I (AnnAwait(x, r) bb c) = (AnnAwait (x, r\<inter>I) bb c)"

definition add_inv_aux:: "'a assn \<Rightarrow> ('a ann_com option \<times> 'a assn) \<Rightarrow> ('a ann_com option \<times> 'a assn)"
where
" add_inv_aux I p \<equiv>
    case p of
       (Some ac, aa) \<Rightarrow> (Some (add_inv_assn_com I ac), aa\<inter>I)
      |(None, aa) \<Rightarrow> (None, aa\<inter>I)"
      
primrec add_inv_com :: "'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com" where 
  "add_inv_com I (Parallel Ts) = (Parallel (map (add_inv_aux I) Ts))" 
| "add_inv_com I (Basic f)  =  (Basic f)" 
| "add_inv_com I (Seq c1 c2)  = (Seq (add_inv_com I c1) (add_inv_com I c2))" 
| "add_inv_com I (Cond bb c1 c2) = (Cond bb (add_inv_com I c1) (add_inv_com I c2))"
| "add_inv_com I (While bb i c)  = (While bb i (add_inv_com I c))"

(* FIXME: check if other similar lemmas are redundant*)
lemma pre_add_inv_assn_com:
  " pre (add_inv_assn_com I cc) = pre cc \<inter> I"
  apply (induct cc, simp_all)
  by (clarsimp split: prod.splits)+
  
lemma pre_add_inv_aux:
  "\<exists>cc q. c= (Some cc, q) \<Longrightarrow>
  pre (the (OG_Hoare.com (add_inv_aux I c))) =
  pre (the (OG_Hoare.com c)) \<inter> I"
  unfolding add_inv_aux_def
  apply (clarsimp split: prod.splits option.splits simp: pre_add_inv_assn_com)
  done

lemma post_add_inv_aux:
  "OG_Hoare.post (add_inv_aux I c) = OG_Hoare.post c \<inter> I"
  by (clarsimp simp: add_inv_aux_def 
                  split: prod.splits option.splits)
  
lemma atomics_add_assn_com:
  "(atomics (add_inv_assn_com I c)) 
     = {(r,a). \<exists> rr. (rr, a) \<in> atomics c \<and> r=rr\<inter>I }"
  by (induct c, auto)
  
lemma assertions_add_assn_com:
  "(assertions (add_inv_assn_com I c)) 
     = {r. \<exists> rr. rr \<in> assertions c \<and> r=rr\<inter>I }"
  apply (induct c arbitrary: I rule: add_inv_assn_com.induct, simp_all)
     apply auto [1] 
    apply blast
   apply blast
  apply blast
  done

lemma assertions_add_invs_assn_com:
  "assertions (add_inv_assn_com I a) = (\<lambda>A. A\<inter>I)`(assertions a)"
  by (induction a, simp_all, (clarsimp|blast)+)

lemma pre_add_inv_aux_inter:  
  "pre (the (OG_Hoare.com (add_inv_aux (I1\<inter>I2) c))) =
   pre (the (OG_Hoare.com (add_inv_aux I1 c))) \<inter> 
   pre (the (OG_Hoare.com (add_inv_aux I2 c)))"
  apply (simp add:add_inv_aux_def)
  apply (case_tac c)
  apply clarsimp
  apply (case_tac a)
   apply clarsimp
  apply clarsimp
  apply (auto simp:pre_add_inv_assn_com)
  done

lemma add_inv_aux_D:
  "add_inv_aux I t = (Some c, q) \<Longrightarrow> 
  \<exists> ac aa. t = (Some ac, aa) \<and> q = aa\<inter>I \<and> add_inv_assn_com I ac=c"
  by (simp add: add_inv_aux_def split: option.splits prod.splits) 

lemma com_add_inv_aux:
  "(OG_Hoare.com (add_inv_aux I p)) = 
      (case p of 
          (Some ac, aa) \<Rightarrow> (Some (add_inv_assn_com I ac)) 
         | (None, _) \<Rightarrow> None)"
  by (clarsimp simp: add_inv_aux_def split: prod.splits option.splits)

lemma add_inv_assn_com_idempotent:
  "add_inv_assn_com I (add_inv_assn_com I c) = add_inv_assn_com I c"
  by (induct c, simp_all, auto)

definition
  oghoare_inv :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(_ \<parallel>-\<^sub>i _//_//_//_)" [55,90,90,55,90] 50)
where
  "I' \<parallel>-\<^sub>i I p c q \<equiv> I' \<parallel>- p (add_inv_com I c) (q(*\<inter>I*))"

abbreviation
  oghoare_inv' :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(\<parallel>-\<^sub>i _//_//_//_)" [90,90,55,90] 50)
where
  "\<parallel>-\<^sub>i I p c q \<equiv> UNIV \<parallel>-\<^sub>i I p c q"


primrec add_await_ann_com :: "'a bexp \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com" where
  "add_await_ann_com P (AnnBasic r f) = (AnnAwait r P (Basic f))"
| "add_await_ann_com P (AnnSeq c1 c2) =  (AnnSeq (add_await_ann_com P c1) (add_await_ann_com P c2))"
| "add_await_ann_com P (AnnCond1 r bb c1 c2) = (AnnCond1 r bb (add_await_ann_com P c1) (add_await_ann_com P c2))"
| "add_await_ann_com P (AnnCond2 r bb c) = (AnnCond2 r bb (add_await_ann_com P c))"
| "add_await_ann_com P (AnnWhile r bb i c) = (AnnWhile r bb i (add_await_ann_com P c))"
| "add_await_ann_com P (AnnAwait r bb c) = (AnnAwait r (bb\<inter>P) c)"

definition add_await_aux:: "'a bexp \<Rightarrow> ('a ann_com option \<times> 'a assn) \<Rightarrow> ('a ann_com option \<times> 'a assn)"
where
  "add_await_aux P p \<equiv>
    case p of
       (Some ac, aa) \<Rightarrow> (Some (add_await_ann_com P ac), aa)
      |(None, aa) \<Rightarrow> (None, aa)"

fun add_await_com :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com" where
  "add_await_com P (Parallel Ts) = (Parallel (map (add_await_aux P) Ts))"
| "add_await_com P c = c"



(*Checks whether two programs are the same up to cruft*)
fun same_ann_program_assn_com :: "'a ann_com \<Rightarrow> 'a ann_com \<Rightarrow> bool" where
  "same_ann_program_assn_com (AnnBasic (_, r) f) (AnnBasic(_, r') f') = (r = r' \<and> f = f')"
| "same_ann_program_assn_com (AnnSeq c1 c2) (AnnSeq c1' c2') = (same_ann_program_assn_com c1 c1' \<and> same_ann_program_assn_com c2 c2')"
| "same_ann_program_assn_com (AnnCond1(_, r) bb c1 c2) (AnnCond1(_, r') bb' c1' c2') = (r = r' \<and> bb = bb' \<and> same_ann_program_assn_com c1 c1' \<and> same_ann_program_assn_com c2 c2')" 
| "same_ann_program_assn_com (AnnCond2(_, r) bb c) (AnnCond2(_, r') bb' c') = (r = r' \<and> bb = bb' \<and> same_ann_program_assn_com c c')"
| "same_ann_program_assn_com (AnnWhile(_, r) bb (y, i) c) (AnnWhile(_, r') bb' (_, i') c') = (r = r' \<and> bb = bb' \<and> i = i' \<and> same_ann_program_assn_com c c')"
| "same_ann_program_assn_com (AnnAwait(_, r) bb c) (AnnAwait(_, r') bb' c') = (r = r' \<and> bb = bb' \<and> c = c')"
| "same_ann_program_assn_com _ _ = False"

fun same_ann_prog_aux:: "('a ann_com option \<times> 'a assn) \<Rightarrow> ('a ann_com option \<times> 'a assn) \<Rightarrow> bool" where
  "same_ann_prog_aux (Some ac, aa) (Some ac', aa') = (same_ann_program_assn_com ac ac' \<and> aa = aa')"
| "same_ann_prog_aux (None, aa) (None, aa') = (aa = aa')"
| "same_ann_prog_aux _ _ = False"

fun same_ann_prog_com :: "'a com \<Rightarrow> 'a com \<Rightarrow> bool" where 
  "same_ann_prog_com (Parallel Ts) (Parallel Ts') = (length Ts = length Ts' \<and> list_all (\<lambda>(c, c'). same_ann_prog_aux c c') (zip Ts Ts'))" 
| "same_ann_prog_com (Basic f) (Basic f') = (f = f')" 
| "same_ann_prog_com (Seq c1 c2) (Seq c1' c2') = (same_ann_prog_com c1 c1' \<and> same_ann_prog_com c2 c2')" 
| "same_ann_prog_com (Cond bb c1 c2) (Cond bb' c1' c2') = (bb = bb' \<and> same_ann_prog_com c1 c1' \<and> same_ann_prog_com c2 c2')"
| "same_ann_prog_com (While bb i c) (While bb' i' c') = (bb = bb' \<and> i = i' \<and> same_ann_prog_com c c')"
| "same_ann_prog_com _ _ = False"

(*Combines two programs that are assumed to be the same up to cruft.
  If either program marks an annotation as cruft then the resulting
  annotation is marked as cruft.*)
fun combine_pres_assn_com :: "'a ann_com \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com" where
  "combine_pres_assn_com (AnnBasic (x, r) f) (AnnBasic(y, r') f') = (AnnBasic (x \<or> y, r) f)"
| "combine_pres_assn_com (AnnSeq c1 c2) (AnnSeq c1' c2') = (AnnSeq (combine_pres_assn_com c1 c1') (combine_pres_assn_com c2 c2'))"
| "combine_pres_assn_com (AnnCond1(x, r) bb c1 c2) (AnnCond1(y, r') bb' c1' c2') = (AnnCond1 (x \<or> y, r) bb (combine_pres_assn_com c1 c1') (combine_pres_assn_com c2 c2'))" 
| "combine_pres_assn_com (AnnCond2(x, r) bb c) (AnnCond2(y, r') bb' c') = (AnnCond2 (x \<or> y, r) bb (combine_pres_assn_com c c'))"
| "combine_pres_assn_com (AnnWhile(x, r) bb (y, i) c) (AnnWhile(x', r') bb' (y', i') c') = (AnnWhile (x \<or> x', r) bb (y \<or> y', i) (combine_pres_assn_com c c'))"
| "combine_pres_assn_com (AnnAwait(x, r) bb c) (AnnAwait(y, r') bb' c') = (AnnAwait (x \<or> y, r) bb c)"

fun combine_pres_aux:: "('a ann_com option \<times> 'a assn) \<Rightarrow> ('a ann_com option \<times> 'a assn) \<Rightarrow> ('a ann_com option \<times> 'a assn)" where
  "combine_pres_aux (Some ac, aa) (Some ac', aa') = (Some (combine_pres_assn_com ac ac'), aa)"
| "combine_pres_aux (None, aa) (None, aa') = (None, aa)"

fun combine_pres_com :: "'a com \<Rightarrow> 'a com \<Rightarrow> 'a com" where 
  "combine_pres_com (Parallel Ts) (Parallel Ts') = (Parallel (map (\<lambda>(c, c'). combine_pres_aux c c') (zip Ts Ts')))"
| "combine_pres_com (Basic f) (Basic f') = (Basic f)" 
| "combine_pres_com (Seq c1 c2) (Seq c1' c2') = (Seq (combine_pres_com c1 c1') (combine_pres_com c2 c2'))"
| "combine_pres_com (Cond bb c1 c2) (Cond bb' c1' c2') = (Cond bb (combine_pres_com c1 c1') (combine_pres_com c2 c2'))"
| "combine_pres_com (While bb i c) (While bb' i' c') = (While bb i (combine_pres_com c c'))"

lemma Parallel'[rule_format]:
  "I \<parallel>- p c q \<longrightarrow> c = Parallel Ts
       \<longrightarrow> p \<subseteq> ((\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts!i)))) \<union> -I)
        \<and> (\<Inter>i\<in>{i. i<length Ts}. post(Ts!i)) \<subseteq> q
        \<and> [\<turnstile>] I Ts \<and> interfree I Ts"
  apply (induct rule: oghoare_induct, (rule TrueI)+)
       by (auto simp: map_ann_hoare_def)

lemma Basic'[rule_format]:
  "I \<parallel>- p c q \<longrightarrow> c = Basic f \<longrightarrow> p \<subseteq> {s. f s \<subseteq> q}"
  apply (induct rule: oghoare_induct, (rule TrueI)+)
       apply (auto intro: Conseq dest: subsetD)
  done

lemma Seq'[rule_format]:
  "I \<parallel>- p c q \<longrightarrow> c = Seq c1 c2 \<longrightarrow> (\<exists>r. I \<parallel>- p c1 r \<and> I \<parallel>- r c2 q)"
  apply (induct rule: oghoare_induct, (rule TrueI)+)
       apply (auto intro: Conseq)
  done

lemma Cond'[rule_format]:
  "I \<parallel>- p c q \<longrightarrow> c = Cond b c1 c2 \<longrightarrow> I \<parallel>- (p \<inter> b) c1 q \<and> I \<parallel>- (p \<inter> -b) c2 q"
  apply (induct rule: oghoare_induct, (rule TrueI)+)
       apply simp_all
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply (erule Conseq[rotated])
     apply clarsimp
    apply blast
  apply (erule Conseq[rotated])
    apply clarsimp
   apply blast
  done

lemma While'[rule_format]:
  "I \<parallel>- p c q \<longrightarrow> c = While b i c1 \<longrightarrow> (\<exists>p'. p \<subseteq> p' \<and> p' \<inter> -b \<subseteq> q \<and> I \<parallel>- (p' \<inter> b) c1 p')"
  apply (induct rule: oghoare_induct, (rule TrueI)+)
       apply (simp_all)
   apply force
  apply clarsimp
  by (meson subset_trans)
  
lemma AnnBasic'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnBasic (b,r) f  \<longrightarrow>  r \<inter> I \<subseteq> {s. f s \<subseteq> q \<union> - I}"
  by (induct rule: ann_hoare_induct, auto) 
  
lemma AnnSeq'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnSeq c0 c1  \<longrightarrow>  I \<turnstile> c0 (pre c1) \<and> I \<turnstile> c1 q "
  apply (induct rule: ann_hoare_induct, simp_all)
  apply (auto intro: AnnConseq)
  done 

lemma AnnCond1'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnCond1 (x,r) b c1 c2  \<longrightarrow>   
   r \<inter> b \<inter> I \<subseteq> pre c1 \<and> I \<turnstile> c1 q \<and> r \<inter> -b \<inter> I \<subseteq> pre c2 \<and> I \<turnstile> c2 q"
  apply (induct rule: ann_hoare_induct, simp_all)
  apply (auto intro: AnnConseq)
  done 
  
lemma AnnCond2'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnCond2 (x,r) b c1  \<longrightarrow>   
   r \<inter> b \<inter> I \<subseteq> pre c1 \<and> I \<turnstile> c1 q \<and> r \<inter> -b \<inter> I \<subseteq> q  "
  apply (induct rule: ann_hoare_induct, simp_all)
  apply (auto intro: AnnConseq)
  done 
   
lemma AnnWhile'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnWhile (x,r) b (y,i) c1  \<longrightarrow>   
   r \<inter> I \<subseteq> i \<and> i \<inter> b \<inter> I \<subseteq> pre c1 \<and> I \<turnstile> c1 i \<and> i \<inter> -b \<inter> I \<subseteq> q"
  apply (induct rule: ann_hoare_induct, simp_all)
  apply (auto intro: AnnConseq)
  done 
     
lemma AnnAwait'[rule_format]:
  "I \<turnstile> c q \<longrightarrow> c = AnnAwait (x,r) b c1  \<longrightarrow>   
   atom_com c1 \<and> UNIV \<parallel>- (r \<inter> b \<inter> I) c1 (q \<union> -I)"
  apply (induct rule: ann_hoare_induct, simp_all)
  apply (auto intro: AnnConseq Conseq)
  done

lemma parallel_conseq_combine_aux':
  "\<lbrakk>same_ann_program_assn_com ac ac'; x \<in> pre ac; x \<in> pre ac'\<rbrakk>
    \<Longrightarrow> x \<in> pre (combine_pres_assn_com ac ac')"
   by (induct ac ac' rule: combine_pres_assn_com.induct) auto

lemma parallel_conseq_combine_aux:
  "\<lbrakk>\<forall>n<length Ts'. same_ann_prog_aux (Ts ! n) (Ts' ! n); p \<subseteq> p'; p \<subseteq> p'';
    p' \<subseteq> (\<Inter> i\<in>{i. i<length Ts'}. pre (the (OG_Hoare.com (Ts ! i)))) \<union> -I;
    p'' \<subseteq> (\<Inter> i\<in>{i. i<length Ts'}. pre (the (OG_Hoare.com (Ts' ! i)))) \<union> -I\<rbrakk>
   \<Longrightarrow> p \<subseteq> (\<Inter>i\<in>\<lbrace>\<acute>op < (length (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts')))\<rbrace>.
                 pre (the (OG_Hoare.com (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts') ! i)))) \<union> -I"
  by (fastforce elim: same_ann_prog_aux.elims  dest: parallel_conseq_combine_aux')
 
lemma inter_helper: 
  "\<forall>x\<in>q' \<inter> q''. x \<in> q \<Longrightarrow> x \<in> q' \<Longrightarrow> x \<in> q'' \<Longrightarrow> x \<in> q"
  by blast


lemma parallel_conseq_combine:
  "\<lbrakk>I \<parallel>- p'
         Parallel Ts
         q';
    I \<parallel>- p''
         Parallel Ts'
         q'';
    length Ts = length Ts'; list_all (\<lambda>(x, y). same_ann_prog_aux x y) (zip Ts Ts'); p \<subseteq> p';
    p \<subseteq> p''; q' \<inter> q'' \<subseteq> q;
    I \<parallel>- ((\<Inter> i\<in>{i. i<length (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts'))}.
            pre (the (OG_Hoare.com (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts') ! i)))) \<union> -I)
    Parallel (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts'))
    (\<Inter> i\<in>{i. i<length (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts'))}.
         OG_Hoare.post (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts') ! i))\<rbrakk>
   \<Longrightarrow> I \<parallel>- p
           Parallel (map (\<lambda>(x, y). combine_pres_aux x y) (zip Ts Ts'))
           q"
  apply (drule Parallel', fastforce)
  apply (drule Parallel', fastforce)
  apply (clarsimp simp: list_all_length)
  apply (rule ParallelConseqRule)
    apply (erule (4) parallel_conseq_combine_aux)
   apply (erule Conseq[rotated])
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: subset_eq)
  by (erule inter_helper; (erule bspec, fastforce elim: same_ann_prog_aux.elims))

lemma cruft_compose:
  assumes valid': "I \<parallel>- p' c' q'"
  and valid'': "I \<parallel>- p'' c'' q''"
  and same: "same_ann_prog_com c' c''"
  and combine: "c = combine_pres_com c' c''"
  and conseq: "p \<subseteq> p' \<inter> p''\<and> q' \<inter> q'' \<subseteq> q"j
  shows "I \<parallel>- p c q"
using assms
proof (induct c' c'' arbitrary: p p' p'' c q q' q'' rule: same_ann_prog_com.induct)
  case 1 then show ?case
    apply clarsimp
    apply (frule Parallel', fastforce)
    apply (erule (6) parallel_conseq_combine)
    apply (drule Parallel', fastforce)
    apply (rule ParallelRule)
apply clarsimp
     apply (clarsimp simp: map_ann_hoare_def)
  oops (*
next
  case 2 then show ?case
    apply clarsimp
    apply (drule Basic', fastforce)
    apply (drule Basic', fastforce)
    apply (rule BasicRule)
    apply force
  done
next
  case 3 then show ?case
    apply clarsimp
    apply (drule Seq', fastforce)
    apply (drule Seq', fastforce)
    apply clarsimp
    apply (rule_tac r="r \<inter> ra" in SeqRule)
     apply force
    apply (rule 3(2), force+)
  done
next
  case 4 then show ?case
    apply clarsimp
    apply (drule Cond', fastforce)
    apply (drule Cond', fastforce)
    apply clarsimp
    apply (rule Conseq[OF _ Cond subset_refl])
      apply force
     apply (rule 4(1), force+)[1]
    apply (rule 4(2), force+)[1]
  done
next
  case 5 then show ?case
    apply clarsimp
    apply (drule While', fastforce)
    apply (drule While', fastforce)
    apply clarsimp
    apply (rule_tac p="p' \<inter> p'aa" in Conseq[OF _ While _])
      apply force
     apply (rule 5(1), force+)[1]
    apply force
  done
next
qed simp_all*)

end
