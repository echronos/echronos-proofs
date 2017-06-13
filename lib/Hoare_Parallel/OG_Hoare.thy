section \<open>The Proof System\<close>

theory OG_Hoare imports OG_Tran begin

fun assertions :: "'a ann_com \<Rightarrow> ('a assn) set" where
  "assertions (AnnBasic (x, r) f) = (if x then {r} else {})"
| "assertions (AnnSeq c1 c2) = assertions c1 \<union> assertions c2"
| "assertions (AnnCond1 (x, r) b c1 c2) = (if x then {r} else {}) \<union> assertions c1 \<union> assertions c2"
| "assertions (AnnCond2 (x, r) b c) = (if x then {r} else {}) \<union> assertions c"
| "assertions (AnnWhile (x, r) b (y, i) c) = (if x then {r} else {}) \<union> (if y then {i} else {}) \<union> assertions c"
| "assertions (AnnAwait (x, r) b c) = (if x then {r} else {})"

primrec atomics :: "'a ann_com \<Rightarrow> ('a assn \<times> 'a com) set" where
  "atomics (AnnBasic r f) = {(snd r, Basic f)}"
| "atomics (AnnSeq c1 c2) = atomics c1 \<union> atomics c2"
| "atomics (AnnCond1 r b c1 c2) = atomics c1 \<union> atomics c2"
| "atomics (AnnCond2 r b c) = atomics c"
| "atomics (AnnWhile r b i c) = atomics c"
| "atomics (AnnAwait r b c) = {(snd r \<inter> b, c)}"

primrec uses_pre :: "'a ann_com \<Rightarrow> bool" where
  "uses_pre (AnnBasic r f) = fst r"
| "uses_pre (AnnSeq c1 c2) = uses_pre c1"
| "uses_pre (AnnCond1 r b c1 c2) = fst r"
| "uses_pre (AnnCond2 r b c) = fst r"
| "uses_pre (AnnWhile r b i c) = fst r"
| "uses_pre (AnnAwait r b c) = fst r"

primrec uses_all_pres :: "'a ann_com \<Rightarrow> bool" where
  "uses_all_pres (AnnBasic r f) = fst r"
| "uses_all_pres (AnnSeq c1 c2) = (uses_all_pres c1 \<and> uses_all_pres c2)"
| "uses_all_pres (AnnCond1 r b c1 c2) = (fst r \<and> uses_all_pres c1 \<and> uses_all_pres c2)"
| "uses_all_pres (AnnCond2 r b c) = (fst r \<and> uses_all_pres c)"
| "uses_all_pres (AnnWhile r b i c) = (fst r \<and> fst i \<and> uses_all_pres c)"
| "uses_all_pres (AnnAwait r b c) = fst r"

primrec uses_all_pres' :: "'a com \<Rightarrow> bool" where
  "uses_all_pres' (Parallel Ts) = (\<forall>i<length Ts. com(Ts ! i) \<noteq> None \<longrightarrow> uses_all_pres (the(com(Ts ! i))))"
| "uses_all_pres' (Basic f) = True"
| "uses_all_pres' (Seq c1 c2) = (uses_all_pres' c1 \<and> uses_all_pres' c2)"
| "uses_all_pres' (Cond b c1 c2) = (uses_all_pres' c1 \<and> uses_all_pres' c2)"
| "uses_all_pres' (While b i c) = uses_all_pres' c"

lemma uses_all_pres[simp]:
  "uses_all_pres c \<Longrightarrow> uses_pre c"
  apply(induct rule: ann_com_com.induct [THEN conjunct1])
  by auto

lemma atom_com_uses:
  "atom_com c \<Longrightarrow> uses_all_pres' c"
by induct auto

primrec com :: "'a ann_triple_op \<Rightarrow> 'a ann_com_op" where
  "com (c, q) = c"

primrec post :: "'a ann_triple_op \<Rightarrow> 'a assn" where
  "post (c, q) = q"

definition interfree_aux :: "'a assn \<Rightarrow> ('a ann_com_op \<times> 'a assn \<times> 'a ann_com_op) \<Rightarrow> bool" where
  "interfree_aux \<equiv> \<lambda>I (co, q, co'). co'= None \<or>
                    (\<forall>(r,a) \<in> atomics (the co'). \<parallel>= (q \<inter> r \<inter> I) a (q \<union> -I) \<and>
                    (co = None \<or> (\<forall>p \<in> assertions (the co). \<parallel>= (p \<inter> r \<inter> I) a (p \<union> -I))))"

definition interfree :: "'a assn \<Rightarrow> (('a ann_triple_op) list) \<Rightarrow> bool" where
  "interfree I Ts \<equiv> \<forall>i j. i < length Ts \<and> j < length Ts \<and> i \<noteq> j \<longrightarrow>
                           interfree_aux I (com (Ts!i), post (Ts!i), com (Ts!j))"

inductive
  oghoare :: "'a assn \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(4 _ \<parallel>- _//_//_)" [55,90,55,90] 50)
  and ann_hoare :: "'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(3 _ \<turnstile> _// _)" [55,60,90] 45)
where
  AnnBasic: "r \<inter> I \<subseteq> {s. f s \<subseteq> q \<union> - I} \<Longrightarrow> I \<turnstile> (AnnBasic (_, r) f) q"

| AnnSeq:   "\<lbrakk> I \<turnstile> c0 pre c1; I \<turnstile> c1 q \<rbrakk> \<Longrightarrow> I \<turnstile> (AnnSeq c0 c1) q"

| AnnCond1: "\<lbrakk> r \<inter> b \<inter> I \<subseteq> pre c1; I \<turnstile> c1 q; r \<inter> -b \<inter> I \<subseteq> pre c2; I \<turnstile> c2 q\<rbrakk>
              \<Longrightarrow> I \<turnstile> (AnnCond1 (_, r) b c1 c2) q"
| AnnCond2: "\<lbrakk> r \<inter> b \<inter> I \<subseteq> pre c; I \<turnstile> c q; r \<inter> -b \<inter> I \<subseteq> q \<rbrakk> \<Longrightarrow> I \<turnstile> (AnnCond2 (_, r) b c) q"

| AnnWhile: "\<lbrakk> r \<inter> I \<subseteq> i; i \<inter> b \<inter> I \<subseteq> pre c; I \<turnstile> c i; i \<inter> -b \<inter> I \<subseteq> q \<rbrakk>
              \<Longrightarrow> I \<turnstile> (AnnWhile (_, r) b (_, i) c) q"

| AnnAwait:  "\<lbrakk> atom_com c; UNIV \<parallel>- (r \<inter> b \<inter> I) c (q \<union> -I) \<rbrakk> \<Longrightarrow> I \<turnstile> (AnnAwait (_, r) b c) q"

| AnnConseq: "\<lbrakk>I \<turnstile> c q; q \<subseteq> q' \<rbrakk> \<Longrightarrow> I \<turnstile> c q'"


| Parallel: "\<lbrakk> \<forall>i<length Ts. \<exists>c q. Ts!i = (Some c, q) \<and> I \<turnstile> c q; interfree I Ts \<rbrakk>
           \<Longrightarrow> I \<parallel>- ((\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts!i)))) \<union> -I)
                       Parallel Ts
                    (\<Inter>i\<in>{i. i<length Ts}. post(Ts!i))"

| Basic:   "I \<parallel>- {s. f s \<subseteq> q} (Basic f) q"

| Seq:    "\<lbrakk> I \<parallel>- p c1 r; I \<parallel>- r c2 q \<rbrakk> \<Longrightarrow> I \<parallel>- p (Seq c1 c2) q "

| Cond:   "\<lbrakk> I \<parallel>- (p \<inter> b) c1 q; I \<parallel>- (p \<inter> -b) c2 q \<rbrakk> \<Longrightarrow> I \<parallel>- p (Cond b c1 c2) q"

| While:  "\<lbrakk> I \<parallel>- (p \<inter> b) c p \<rbrakk> \<Longrightarrow> I \<parallel>- p (While b i c) (p \<inter> -b)"

| Conseq: "\<lbrakk> p' \<subseteq> p; I \<parallel>- p c q ; q \<subseteq> q' \<rbrakk> \<Longrightarrow> I \<parallel>- p' c q'"

abbreviation
  oghoare' :: "'a assn \<Rightarrow> 'a com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(3 \<parallel>- _//_//_)" [90,55,90] 50)
where
  "\<parallel>- p c q \<equiv> UNIV \<parallel>- p c q"

abbreviation
  ann_hoare' :: "'a ann_com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(2\<turnstile> _// _)" [60,90] 45)
where
  "\<turnstile> c q \<equiv> UNIV \<turnstile> c q"

section \<open>Soundness\<close>
(* In the version Isabelle-10-Sep-1999: HOL: The THEN and ELSE
parts of conditional expressions (if P then x else y) are no longer
simplified.  (This allows the simplifier to unfold recursive
functional programs.)  To restore the old behaviour, we declare
@{text "lemmas [cong del] = if_weak_cong"}. *)

lemmas [cong del] = if_weak_cong

lemmas ann_hoare_induct = oghoare_ann_hoare.induct [THEN conjunct2]
lemmas oghoare_induct = oghoare_ann_hoare.induct [THEN conjunct1]

lemmas AnnBasic = oghoare_ann_hoare.AnnBasic
lemmas AnnSeq = oghoare_ann_hoare.AnnSeq
lemmas AnnCond1 = oghoare_ann_hoare.AnnCond1
lemmas AnnCond2 = oghoare_ann_hoare.AnnCond2
lemmas AnnWhile = oghoare_ann_hoare.AnnWhile
lemmas AnnAwait = oghoare_ann_hoare.AnnAwait
lemmas AnnConseq = oghoare_ann_hoare.AnnConseq

lemmas Parallel = oghoare_ann_hoare.Parallel
lemmas Basic = oghoare_ann_hoare.Basic
lemmas Seq = oghoare_ann_hoare.Seq
lemmas Cond = oghoare_ann_hoare.Cond
lemmas While = oghoare_ann_hoare.While
lemmas Conseq = oghoare_ann_hoare.Conseq

subsection \<open>Soundness of the System for Atomic Programs\<close>

lemma Basic_ntran [rule_format]:
 "(Basic f, s) -Pn\<rightarrow> (Parallel Ts, t) \<longrightarrow> All_None Ts \<longrightarrow> t \<in> f s"
apply(induct "n")
 apply(simp (no_asm))
apply(fast dest: relpow_Suc_D2 Parallel_empty_lemma elim: transition_cases)
done

lemma SEM_fwhile: "SEM S (p \<inter> b) \<subseteq> p \<Longrightarrow> SEM (fwhile b S k) p \<subseteq> (p \<inter> -b)"
apply (induct "k")
 apply(simp (no_asm) add: L3_5v_lemma3)
apply(simp (no_asm) add: L3_5iv L3_5ii Parallel_empty)
apply(rule conjI)
 apply (blast dest: L3_5i)
apply(simp add: SEM_def sem_def id_def)
apply (auto dest: Basic_ntran rtrancl_imp_UN_relpow)
apply blast
done

lemma atom_hoare_sound [rule_format]:
 "I \<parallel>- p c q \<longrightarrow> atom_com(c) \<longrightarrow> I = UNIV \<longrightarrow> \<parallel>= p c q"
apply (unfold com_validity_def)
apply(rule oghoare_induct)
apply simp_all
\<comment>\<open>Basic\<close>
    apply(simp add: SEM_def sem_def)
    apply(fast dest: rtrancl_imp_UN_relpow Basic_ntran)
\<comment>\<open>Seq\<close>
   apply(intro impI)
   apply(rule subset_trans)
    prefer 2 apply simp
   apply(simp add: L3_5ii L3_5i)
\<comment>\<open>Cond\<close>
  apply(simp add: L3_5iv)
\<comment>\<open>While\<close>
 apply (force simp add: L3_5v dest: SEM_fwhile)
\<comment>\<open>Conseq\<close>
apply(force simp add: SEM_def sem_def)
done

subsection \<open>Soundness of the System for Component Programs\<close>

inductive_cases ann_transition_cases:
    "(None,s) -1\<rightarrow> (c', s')"
    "(Some (AnnBasic r f),s) -1\<rightarrow> (c', s')"
    "(Some (AnnSeq c1 c2), s) -1\<rightarrow> (c', s')"
    "(Some (AnnCond1 r b c1 c2), s) -1\<rightarrow> (c', s')"
    "(Some (AnnCond2 r b c), s) -1\<rightarrow> (c', s')"
    "(Some (AnnWhile r b I c), s) -1\<rightarrow> (c', s')"
    "(Some (AnnAwait r b c),s) -1\<rightarrow> (c', s')"

text \<open>Strong Soundness for Component Programs:\<close>

lemma ann_hoare_case_analysis [rule_format]: "I \<turnstile> C q' \<longrightarrow>
  ((\<forall>x r f. C = AnnBasic (x, r) f \<longrightarrow> (\<exists>q. r \<inter> I \<subseteq> {s. f s \<subseteq> q \<union> -I } \<and> q \<inter> I \<subseteq> q')) \<and>
  (\<forall>c0 c1. C = AnnSeq c0 c1 \<longrightarrow> (\<exists>q. q \<inter> I \<subseteq> q' \<and> I \<turnstile> c0 pre c1 \<and> I \<turnstile> c1 q)) \<and>
  (\<forall>x r b c1 c2. C = AnnCond1 (x, r) b c1 c2 \<longrightarrow> (\<exists>q. q \<inter> I \<subseteq> q' \<and>
  r \<inter> b \<inter> I \<subseteq> pre c1 \<and> I \<turnstile> c1 q \<and> r \<inter> -b \<inter> I \<subseteq> pre c2 \<and> I \<turnstile> c2 q)) \<and>
  (\<forall>x r b c. C = AnnCond2 (x, r) b c \<longrightarrow>
  (\<exists>q. q \<inter> I \<subseteq> q' \<and> r \<inter> b \<inter> I \<subseteq> pre c  \<and> I \<turnstile> c q \<and> r \<inter> -b \<inter> I \<subseteq> q)) \<and>
  (\<forall>x r b y i c. C = AnnWhile (x, r) b (y, i) c \<longrightarrow>
  (\<exists>q. q \<inter> I \<subseteq> q' \<and> r \<inter> I \<subseteq> i \<and> i \<inter> b \<inter> I \<subseteq> pre c \<and> I \<turnstile> c i \<and> i \<inter> -b \<inter> I \<subseteq> q)) \<and>
  (\<forall>x r b c. C = AnnAwait (x, r) b c \<longrightarrow> (\<exists>q. q \<inter> I \<subseteq> q' \<and> \<parallel>- (r \<inter> b \<inter> I) c (q \<union> -I))))"
apply(rule ann_hoare_induct)
apply simp_all
 apply(rule_tac x=q in exI,simp)+
apply(rule conjI,clarify,simp,clarify,rule_tac x=qa in exI,fast)+
apply(clarify,simp,clarify,rule_tac x=qa in exI,fast)
done

lemma Help: "(transition \<inter> {(x,y). True}) = (transition)"
apply force
done

lemma Strong_Soundness_aux_aux [rule_format]:
 "(co, s) -1\<rightarrow> (co', t) \<longrightarrow> (\<forall>c. co = Some c \<longrightarrow> s\<in> pre c \<longrightarrow>
 (\<forall>q. \<turnstile> c q \<longrightarrow> (if co' = None then t\<in>q else t \<in> pre(the co') \<and> \<turnstile> (the co') q )))"
apply(rule ann_transition_transition.induct [THEN conjunct1])
apply simp_all
\<comment>\<open>Basic\<close>
         apply clarify
         apply(frule ann_hoare_case_analysis)
         apply force
\<comment>\<open>Seq\<close>
        apply clarify
        apply(frule ann_hoare_case_analysis,simp)
        apply(fast intro: AnnConseq)
       apply clarify
       apply(frule ann_hoare_case_analysis,simp)
       apply clarify
       apply(rule conjI)
        apply force
       apply(rule AnnSeq,simp)
       apply(fast intro: AnnConseq)
\<comment>\<open>Cond1\<close>
      apply clarify
      apply(frule ann_hoare_case_analysis,simp)
      apply(fast intro: AnnConseq)
     apply clarify
     apply(frule ann_hoare_case_analysis,simp)
     apply(fast intro: AnnConseq)
\<comment>\<open>Cond2\<close>
    apply clarify
    apply(frule ann_hoare_case_analysis,simp)
    apply(fast intro: AnnConseq)
   apply clarify
   apply(frule ann_hoare_case_analysis,simp)
   apply(fast intro: AnnConseq)
\<comment>\<open>While\<close>
  apply clarify
  apply(frule ann_hoare_case_analysis,simp)
  apply force
 apply clarify
 apply(frule ann_hoare_case_analysis,simp)
 apply auto
 apply(rule AnnSeq)
  apply simp
 apply(rule AnnWhile, simp_all)[1]
\<comment>\<open>Await\<close>
apply(frule ann_hoare_case_analysis,simp)
apply clarify
apply(drule atom_hoare_sound)
  apply simp
 apply simp
apply(simp add: com_validity_def SEM_def sem_def)
apply(simp add: Help All_None_def)
apply force
done

lemma Strong_Soundness_aux: "\<lbrakk> (Some c, s) -*\<rightarrow> (co, t); s \<in> pre c; \<turnstile> c q \<rbrakk>
  \<Longrightarrow> if co = None then t \<in> q else t \<in> pre (the co) \<and> \<turnstile> (the co) q"
apply(erule rtrancl_induct2)
 apply simp
apply(case_tac "a")
 apply(fast elim: ann_transition_cases)
apply(erule Strong_Soundness_aux_aux)
 apply simp
apply simp_all
done

lemma Strong_Soundness: "\<lbrakk> (Some c, s)-*\<rightarrow>(co, t); s \<in> pre c; \<turnstile> c q \<rbrakk>
  \<Longrightarrow> if co = None then t\<in>q else t \<in> pre (the co)"
apply(force dest:Strong_Soundness_aux)
done

lemma ann_hoare_sound: "\<turnstile> c q  \<Longrightarrow> \<Turnstile> c q"
apply (unfold ann_com_validity_def ann_SEM_def ann_sem_def)
apply clarify
apply(drule Strong_Soundness)
apply simp_all
done

subsection \<open>Soundness of the System for Parallel Programs\<close>

lemma Parallel_length_post_P1: "(Parallel Ts,s) -P1\<rightarrow> (R', t) \<Longrightarrow>
  (\<exists>Rs. R' = (Parallel Rs) \<and> (length Rs) = (length Ts) \<and>
  (\<forall>i. i<length Ts \<longrightarrow> post(Rs ! i) = post(Ts ! i)))"
apply(erule transition_cases)
apply simp
apply clarify
apply(case_tac "i=ia")
apply simp+
done

lemma Parallel_length_post_PStar: "(Parallel Ts,s) -P*\<rightarrow> (R',t) \<Longrightarrow>
  (\<exists>Rs. R' = (Parallel Rs) \<and> (length Rs) = (length Ts) \<and>
  (\<forall>i. i<length Ts \<longrightarrow> post(Ts ! i) = post(Rs ! i)))"
apply(erule rtrancl_induct2)
 apply(simp_all)
apply clarify
apply simp
apply(drule Parallel_length_post_P1)
apply auto
done

lemma assertions_lemma: "uses_pre c \<Longrightarrow> pre c \<in> assertions c"
apply(induct rule: ann_com_com.induct [THEN conjunct1])
apply auto
done

lemma interfree_aux1 [rule_format]:
  "(c,s) -1\<rightarrow> (r,t)  \<longrightarrow> (interfree_aux I (c1, q1, c) \<longrightarrow> interfree_aux I (c1, q1, r))"
apply (rule ann_transition_transition.induct [THEN conjunct1])
apply(safe)
prefer 13
apply (rule TrueI)
apply (simp_all add:interfree_aux_def)
apply force+
done

lemma interfree_aux2 [rule_format]:
  "(c,s) -1\<rightarrow> (r,t) \<longrightarrow> (interfree_aux I (c, q, a)  \<longrightarrow> interfree_aux I (r, q, a) )"
apply (rule ann_transition_transition.induct [THEN conjunct1])
apply(force simp add:interfree_aux_def)+
done

lemma interfree_lemma: "\<lbrakk> (Some c, s) -1\<rightarrow> (r, t);interfree I Ts ; i<length Ts;
           Ts!i = (Some c, q) \<rbrakk> \<Longrightarrow> interfree I (Ts[i:= (r, q)])"
apply(simp add: interfree_def)
apply clarify
apply(case_tac "i=j")
 apply(drule_tac t = "ia" in not_sym)
 apply simp_all
apply(force elim: interfree_aux1)
apply(force elim: interfree_aux2 simp add:nth_list_update)
done

text \<open>Strong Soundness Theorem for Parallel Programs:\<close>

lemma Parallel_Strong_Soundness_Seq_aux:
  "\<lbrakk>interfree I Ts; i<length Ts; com(Ts ! i) = Some(AnnSeq c0 c1); uses_pre c1 \<rbrakk>
  \<Longrightarrow>  interfree I (Ts[i:=(Some c0, pre c1)])"
apply(simp add: interfree_def)
apply clarify
apply(case_tac "i=j")
 apply(force simp add: nth_list_update interfree_aux_def)
apply(case_tac "i=ia")
 apply(erule_tac x=ia in allE)
 apply(force simp add:interfree_aux_def assertions_lemma)
apply simp
done

lemma Parallel_Strong_Soundness_Seq [rule_format (no_asm)]:
 "\<lbrakk> \<forall>i<length Ts. (if com(Ts!i) = None then b \<in> post(Ts!i)
  else b \<in> pre(the(com(Ts!i))) \<and> \<turnstile> the(com(Ts!i)) post(Ts!i));
  com(Ts ! i) = Some(AnnSeq c0 c1); i<length Ts; interfree I Ts; uses_pre c1 \<rbrakk> \<Longrightarrow>
 (\<forall>ia<length Ts. (if com(Ts[i:=(Some c0, pre c1)]! ia) = None
  then b \<in> post(Ts[i:=(Some c0, pre c1)]! ia)
 else b \<in> pre(the(com(Ts[i:=(Some c0, pre c1)]! ia))) \<and>
 \<turnstile> the(com(Ts[i:=(Some c0, pre c1)]! ia)) post(Ts[i:=(Some c0, pre c1)]! ia)))
  \<and> interfree I (Ts[i:= (Some c0, pre c1)])"
apply(rule conjI)
 apply safe
 apply(case_tac "i=ia")
  apply simp
  apply(force dest: ann_hoare_case_analysis)
 apply simp
apply(fast elim: Parallel_Strong_Soundness_Seq_aux)
done

lemma Parallel_Strong_Soundness_Seq_aux_aux:
 "\<lbrakk>\<forall>x<length Ts.
      (\<exists>y. OG_Hoare.com (Ts ! x) = Some y) \<longrightarrow> uses_all_pres (the (OG_Hoare.com (Ts ! x)));
   i < length Ts; OG_Hoare.com (Ts ! i) = Some (AnnSeq c0 c1)\<rbrakk>
    \<Longrightarrow> \<forall>ia<length Ts.
          (\<exists>y. OG_Hoare.com (Ts[i := (Some c0, pre c1)] ! ia) = Some y) \<longrightarrow>
          uses_all_pres (the (OG_Hoare.com (Ts[i := (Some c0, pre c1)] ! ia)))"
apply clarsimp
apply (erule_tac x=ia in allE)
apply clarsimp
apply (case_tac "i=ia")
 apply simp
apply simp
done

lemma Parallel_Strong_Soundness_aux_aux [rule_format]:
 "(Some c, b) -1\<rightarrow> (co, t) \<longrightarrow>
  (\<forall>Ts. i<length Ts \<longrightarrow> com(Ts ! i) = Some c \<longrightarrow>
  (\<forall>i<length Ts. com(Ts ! i) \<noteq> None \<longrightarrow> uses_all_pres (the (com (Ts ! i)))) \<longrightarrow>
  (\<forall>i<length Ts. (if com(Ts ! i) = None then b\<in>post(Ts!i)
  else b\<in>pre(the(com(Ts!i))) \<and> \<turnstile> the(com(Ts!i)) post(Ts!i))) \<longrightarrow>
 interfree UNIV Ts \<longrightarrow>
  (\<forall>j. j<length Ts \<and> i\<noteq>j \<longrightarrow>
  (if com(Ts!j) = None then t\<in>post(Ts!j)
   else t\<in>pre(the(com(Ts!j))) \<and> \<turnstile> the(com(Ts!j)) post(Ts!j))))"
apply(rule ann_transition_transition.induct [THEN conjunct1])
apply safe
prefer 11
apply(rule TrueI)
apply simp_all
\<comment>\<open>Basic\<close>
   apply(erule_tac x = "i" in all_dupE, erule (1) notE impE)
   apply(erule_tac x = "i" in all_dupE, erule (1) notE impE)
   apply(erule_tac x = "j" in allE , erule (1) notE impE)
   apply(erule_tac x = "j" in allE , erule (1) notE impE)
   apply(simp add: interfree_def)
   apply(erule_tac x = "j" in allE,simp)
   apply(erule_tac x = "i" in allE,simp)
   apply(drule_tac t = "i" in not_sym)
   apply(case_tac "com(Ts ! j)=None")
    apply(force intro: converse_rtrancl_into_rtrancl
          simp add: interfree_aux_def com_validity_def SEM_def sem_def All_None_def)[1]
   apply(simp add:interfree_aux_def)
   apply clarify
   apply simp
   apply(erule_tac x="pre y" in ballE)
    apply(force intro: converse_rtrancl_into_rtrancl
          simp add: com_validity_def SEM_def sem_def All_None_def)
   apply(clarsimp simp:assertions_lemma)
\<comment>\<open>Seqs\<close>
  apply(erule_tac x = "Ts[i:=(Some c0, pre c1)]" in allE)
  apply(erule_tac x = "i" in all_dupE)
  apply (drule  Parallel_Strong_Soundness_Seq,simp+)
  apply (erule impE)
   apply (erule  Parallel_Strong_Soundness_Seq_aux_aux,simp+)
 apply(erule_tac x = "Ts[i:=(Some c0, pre c1)]" in allE)
 apply(erule_tac x = "i" in all_dupE)
 apply(drule  Parallel_Strong_Soundness_Seq,simp+)
 apply (erule impE)
  apply (erule  Parallel_Strong_Soundness_Seq_aux_aux,simp+)

\<comment>\<open>Await\<close>
apply(erule_tac x=i in all_dupE)
apply(rule_tac x = "i" in allE , assumption , erule (1) notE impE)
apply(erule_tac x = "j" in allE , erule (1) notE impE)
apply(simp add: interfree_def)
apply(erule_tac x = "j" in allE,simp)
apply(erule_tac x = "j" in allE,simp)
apply(erule_tac x = "i" in allE,simp)
apply(drule_tac t = "i" in not_sym)
apply(case_tac "com(Ts ! j)=None")
 apply(force intro: converse_rtrancl_into_rtrancl simp add: interfree_aux_def
        com_validity_def SEM_def sem_def All_None_def Help)
apply(simp add:interfree_aux_def)
apply clarify
apply simp
apply(erule_tac x="pre y" in ballE)
 apply(force intro: converse_rtrancl_into_rtrancl
       simp add: com_validity_def SEM_def sem_def All_None_def Help)
apply(clarsimp simp:assertions_lemma)
done

lemma uses_all_pres_ann_transition[rule_format]:
  "(co, s) -1\<rightarrow> (co', t) \<longrightarrow> co \<noteq> None \<longrightarrow> uses_all_pres (the co) \<longrightarrow> co' \<noteq> None \<longrightarrow> uses_all_pres (the (co'))"
apply (induct rule: ann_transition_transition.induct[THEN conjunct1])
apply auto
done

lemma Parallel_uses_all_pres_P1:
  "\<lbrakk>(Parallel Ts,s) -P1\<rightarrow> (R', t);
    \<forall>i<length Ts. com(Ts ! i) \<noteq> None \<longrightarrow> uses_all_pres (the(com(Ts ! i)))\<rbrakk>
   \<Longrightarrow> \<exists>Rs. R' = (Parallel Rs) \<and>
         (\<forall>i<length Rs. com(Rs ! i) \<noteq> None \<longrightarrow> uses_all_pres (the(com(Rs ! i))))"
apply(erule transition_cases)
apply simp
apply clarify
apply(case_tac "i=ia")
apply (drule uses_all_pres_ann_transition)
apply auto
done

lemma Parallel_uses_all_pres_PStar:
  "\<lbrakk>(Parallel Ts,s) -P*\<rightarrow> (R',t);
    \<forall>i<length Ts. com(Ts ! i) \<noteq> None \<longrightarrow> uses_all_pres (the(com(Ts ! i)))\<rbrakk>
   \<Longrightarrow> \<exists>Rs. R' = (Parallel Rs) \<and>
         (\<forall>i<length Rs. com(Rs ! i) \<noteq> None \<longrightarrow> uses_all_pres (the(com(Rs ! i))))"
apply(erule rtrancl_induct2)
 apply(simp_all)
apply clarify
apply simp
apply(drule Parallel_uses_all_pres_P1, clarsimp)
apply clarsimp
done

lemma Parallel_Strong_Soundness_aux [rule_format]:
 "\<lbrakk>(Ts',s) -P*\<rightarrow> (Rs',t);  Ts' = (Parallel Ts); interfree UNIV Ts;
 \<forall>i. i<length Ts \<longrightarrow> (\<exists>c q. (Ts ! i) = (Some c, q) \<and> s\<in>(pre c) \<and> \<turnstile> c q \<and> uses_all_pres c) \<rbrakk> \<Longrightarrow>
  \<forall>Rs. Rs' = (Parallel Rs) \<longrightarrow>
  (\<forall>j. j<length Rs \<longrightarrow>
  (if com(Rs ! j) = None then t\<in>post(Ts ! j)
  else t\<in>pre(the(com(Rs ! j))) \<and> \<turnstile> the(com(Rs ! j)) post(Ts ! j))) \<and> interfree UNIV Rs"
apply(erule rtrancl_induct2)
 apply clarify
\<comment>\<open>Base\<close>
 apply force
\<comment>\<open>Induction step\<close>
apply clarify
apply(frule Parallel_length_post_PStar)
apply(drule Parallel_uses_all_pres_PStar)
 apply force
apply clarify
apply (ind_cases "(Parallel Ts, s) -P1\<rightarrow> (Parallel Rs, t)" for Ts s Rs t)
apply(rule conjI)
 apply clarify
 apply(case_tac "i=j")
  apply(simp split del:if_split)
  apply(erule Strong_Soundness_aux_aux,simp+)
   apply force
  apply force
 apply(clarsimp split del: if_split)
 apply(erule Parallel_Strong_Soundness_aux_aux)
 apply(simp_all add: split del: if_split)
  apply force
apply(rule interfree_lemma)
apply simp_all
done

lemma Parallel_Strong_Soundness:
 "\<lbrakk>(Parallel Ts, s) -P*\<rightarrow> (Parallel Rs, t); interfree UNIV Ts; j<length Rs;
  \<forall>i. i<length Ts \<longrightarrow> (\<exists>c q. Ts ! i = (Some c, q) \<and> s\<in>pre c \<and> \<turnstile> c q \<and> uses_all_pres c) \<rbrakk> \<Longrightarrow>
  if com(Rs ! j) = None then t\<in>post(Ts ! j) else t\<in>pre (the(com(Rs ! j)))"
apply(drule  Parallel_Strong_Soundness_aux)
apply auto
done

lemma oghoare_sound [rule_format]: "(I \<parallel>- p c q \<longrightarrow> uses_all_pres' c  \<longrightarrow> I = UNIV \<longrightarrow> \<parallel>= p c q)"
apply (unfold com_validity_def)
apply (induct rule: oghoare_induct)
apply(rule TrueI)+
\<comment>\<open>Parallel\<close>
      apply(simp add: SEM_def sem_def)
      apply(clarify, rename_tac x y i Ts')
      apply(frule Parallel_length_post_PStar)
      apply clarify
      apply(drule_tac j=i in Parallel_Strong_Soundness)
         apply simp
        apply simp
       apply clarsimp
       apply ((drule_tac x=ia in spec, clarsimp)+)[1]
      apply simp
      apply(erule_tac V = "\<forall>i. P i" for P in thin_rl)
      apply(drule_tac s = "length Rs" in sym)
      apply(erule allE, erule impE, assumption)
      apply(force dest: nth_mem simp add: All_None_def)
\<comment>\<open>Basic\<close>
    apply(simp add: SEM_def sem_def)
    apply(force dest: rtrancl_imp_UN_relpow Basic_ntran)
\<comment>\<open>Seq\<close>
   apply (intro impI)
   apply(rule subset_trans)
    prefer 2 apply simp
   apply(simp add: L3_5ii L3_5i)
\<comment>\<open>Cond\<close>
   apply (rule impI)
  apply(simp add: L3_5iv L3_5i Int_commute)[1]
\<comment>\<open>While\<close>
 apply(simp add: L3_5v)
 apply (blast dest: SEM_fwhile)
\<comment>\<open>Conseq\<close>
 apply (intro impI)
 apply simp
apply(auto simp add: SEM_def sem_def)
done

end
