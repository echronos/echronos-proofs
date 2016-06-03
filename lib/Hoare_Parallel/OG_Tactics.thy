section \<open>Generation of Verification Conditions\<close>

theory OG_Tactics
imports OG_Hoare "../../lib/Cache_Tactics"
begin

lemmas ann_hoare_intros=AnnBasic AnnSeq AnnCond1 AnnCond2 AnnWhile AnnAwait AnnConseq
lemmas oghoare_intros=Parallel Basic Seq Cond While Conseq

lemma ParallelConseqRule:
 "\<lbrakk> p \<subseteq> (\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts ! i)))) \<union> -I;
  I \<parallel>- ((\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts ! i)))) \<union> -I)
        (Parallel Ts)
       (\<Inter>i\<in>{i. i<length Ts}. post(Ts ! i));
  (\<Inter>i\<in>{i. i<length Ts}. post(Ts ! i)) \<subseteq> q \<rbrakk>
  \<Longrightarrow> I \<parallel>- p (Parallel Ts) q"
apply (rule Conseq)
prefer 2
 apply fast
apply assumption+
done

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> I \<parallel>- p (Basic ID) q"
apply(rule oghoare_intros)
  prefer 2 apply(rule Basic)
 prefer 2 apply(assumption)
apply force
done

lemma BasicRule: "p \<subseteq> {s. f s \<subseteq> q} \<Longrightarrow> I \<parallel>- p (Basic f) q"
apply(rule oghoare_intros)
  prefer 2 apply(rule oghoare_intros)
 prefer 2 apply(force)
apply assumption
done

lemma SeqRule: "\<lbrakk> I \<parallel>- p c1 r; I \<parallel>- r c2 q \<rbrakk> \<Longrightarrow> I \<parallel>- p (Seq c1 c2) q"
apply(rule Seq)
apply fast+
done

lemma CondRule:
 "\<lbrakk> p \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>w) \<and> (s\<notin>b \<longrightarrow> s\<in>w')}; I \<parallel>- w c1 q; I \<parallel>- w' c2 q \<rbrakk>
  \<Longrightarrow> I \<parallel>- p (Cond b c1 c2) q"
apply(rule Cond)
 apply(rule Conseq)
 prefer 4 apply(rule Conseq)
apply simp_all
apply force+
done

lemma WhileRule: "\<lbrakk> p \<subseteq> i; I \<parallel>- (i \<inter> b) c i ; i \<inter> (-b) \<subseteq> q \<rbrakk>
        \<Longrightarrow> I \<parallel>- p (While b i c) q"
apply(rule Conseq)
 prefer 2 apply(rule While)
apply assumption+
done

text \<open>Three new proof rules for special instances of the \<open>AnnBasic\<close> and the \<open>AnnAwait\<close> commands when the transformation
performed on the state is the identity, and for an \<open>AnnAwait\<close>
command where the boolean condition is \<open>{s. True}\<close>:\<close>

lemma AnnatomRule:
  "\<lbrakk> atom_com(c); \<parallel>- (r \<inter> I) c (q \<union> -I) \<rbrakk>  \<Longrightarrow> I \<turnstile> (AnnAwait (x, r) {s. True} c) q"
apply(rule AnnAwait)
apply simp_all
done

lemma AnnskipRule:
  "r \<inter> I \<subseteq> q \<union> -I \<Longrightarrow> I \<turnstile> (AnnBasic (x, r) ID) q"
apply(rule AnnBasic)
apply auto
done

lemma AnnwaitRule:
  "\<lbrakk> r \<inter> b \<inter> I \<subseteq> q \<union> -I \<rbrakk> \<Longrightarrow> I \<turnstile> (AnnAwait (x, r) b (Basic ID)) q"
apply(rule AnnAwait)
 apply simp
apply(rule BasicRule)
apply auto
done

text \<open>Lemmata to avoid using the definition of \<open>map_ann_hoare\<close>, \<open>interfree_aux\<close>, \<open>interfree_swap\<close> and
\<open>interfree\<close> by splitting it into different cases:\<close>

lemma interfree_aux_rule1: "interfree_aux I (co, q, None)"
by(simp add:interfree_aux_def)

lemma interfree_aux_rule2:
  "\<forall>(R,r)\<in>(atomics a). \<parallel>- (q \<inter> R \<inter> I) r (q \<union> -I) \<and> uses_all_pres' r \<Longrightarrow> interfree_aux I (None, q, Some a)"
apply(simp add:interfree_aux_def)
apply(force elim:oghoare_sound)
done

lemma interfree_aux_rule3:
  "(\<forall>(R, r)\<in>(atomics a). \<parallel>- (q \<inter> R \<inter> I) r (q \<union> -I) \<and> (\<forall>p\<in>(assertions c). \<parallel>- (p \<inter> R \<inter> I) r (p \<union> -I)) \<and> uses_all_pres' r)
  \<Longrightarrow> interfree_aux I (Some c, q, Some a)"
apply(simp add:interfree_aux_def)
apply(force elim:oghoare_sound)
done

lemma AnnBasic_assertions:
  "\<lbrakk>x \<longrightarrow> interfree_aux I (None, r, Some a); interfree_aux I (None, q, Some a)\<rbrakk> \<Longrightarrow>
    interfree_aux I (Some (AnnBasic (x, r) f), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnSeq_assertions:
  "\<lbrakk> interfree_aux I (Some c1, q, Some a); interfree_aux I (Some c2, q, Some a)\<rbrakk>\<Longrightarrow>
   interfree_aux I (Some (AnnSeq c1 c2), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond1_assertions:
  "\<lbrakk> x \<longrightarrow> interfree_aux I (None, r, Some a); interfree_aux I (Some c1, q, Some a);
  interfree_aux I (Some c2, q, Some a)\<rbrakk>\<Longrightarrow>
  interfree_aux I (Some(AnnCond1 (x, r) b c1 c2), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond2_assertions:
  "\<lbrakk> x \<longrightarrow> interfree_aux I (None, r, Some a); interfree_aux I (Some c, q, Some a)\<rbrakk>\<Longrightarrow>
  interfree_aux I (Some (AnnCond2 (x, r) b c), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnWhile_assertions:
  "\<lbrakk> x \<longrightarrow> interfree_aux I (None, r, Some a); y \<longrightarrow> interfree_aux I (None, i, Some a);
  interfree_aux I (Some c, q, Some a)\<rbrakk>\<Longrightarrow>
  interfree_aux I (Some (AnnWhile (x, r) b (y, i) c), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnAwait_assertions:
  "\<lbrakk> x \<longrightarrow> interfree_aux I (None, r, Some a); interfree_aux I (None, q, Some a)\<rbrakk>\<Longrightarrow>
  interfree_aux I (Some (AnnAwait (x, r) b c), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnBasic_atomics:
  "\<parallel>- (q \<inter> r \<inter> I) (Basic f) (q \<union> -I) \<Longrightarrow> interfree_aux I (None, q, Some (AnnBasic (x, r) f))"
by(simp add: interfree_aux_def oghoare_sound)

lemma AnnSeq_atomics:
  "\<lbrakk> interfree_aux I (Any, q, Some a1); interfree_aux I (Any, q, Some a2)\<rbrakk>\<Longrightarrow>
  interfree_aux I (Any, q, Some (AnnSeq a1 a2))"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond1_atomics:
  "\<lbrakk> interfree_aux I (Any, q, Some a1); interfree_aux I (Any, q, Some a2)\<rbrakk>\<Longrightarrow>
   interfree_aux I (Any, q, Some (AnnCond1 (x, r) b a1 a2))"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond2_atomics:
  "interfree_aux I (Any, q, Some a)\<Longrightarrow> interfree_aux I (Any, q, Some (AnnCond2 (x, r) b a))"
by(simp add: interfree_aux_def)

lemma AnnWhile_atomics: "interfree_aux I (Any, q, Some a)
     \<Longrightarrow> interfree_aux I (Any, q, Some (AnnWhile (x, r) b (y, i) a))"
by(simp add: interfree_aux_def)

lemma Annatom_atomics:
  "\<lbrakk>\<parallel>- (q \<inter> r \<inter> I) a (q \<union> -I); uses_all_pres' a\<rbrakk> \<Longrightarrow> interfree_aux I (None, q, Some (AnnAwait (x, r) {x. True} a))"
by(simp add: interfree_aux_def oghoare_sound)

lemma AnnAwait_atomics:
  "\<lbrakk>\<parallel>- (q \<inter> (r \<inter> b) \<inter> I) a (q \<union> -I); uses_all_pres' a\<rbrakk> \<Longrightarrow> interfree_aux I (None, q, Some (AnnAwait (x, r) b a))"
by(simp add: interfree_aux_def oghoare_sound)

definition interfree_swap :: "'a assn \<Rightarrow> ('a ann_triple_op * ('a ann_triple_op) list) \<Rightarrow> bool" where
  "interfree_swap I == \<lambda>(x, xs). \<forall>y\<in>set xs. interfree_aux I (com x, post x, com y)
  \<and> interfree_aux I (com y, post y, com x)"

lemma interfree_swap_Empty: "interfree_swap I (x, [])"
by(simp add:interfree_swap_def)

lemma interfree_swap_List:
  "\<lbrakk> interfree_aux I (com x, post x, com y);
  interfree_aux I (com y, post y ,com x); interfree_swap I (x, xs) \<rbrakk>
  \<Longrightarrow> interfree_swap I (x, y#xs)"
by(simp add:interfree_swap_def)

lemma interfree_swap_Map: "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> interfree_aux I (com x, post x, c k)
 \<and> interfree_aux I (c k, Q k, com x)
 \<Longrightarrow> interfree_swap I (x, map (\<lambda>k. (c k, Q k)) [i..<j])"
by(force simp add: interfree_swap_def less_diff_conv)

lemma interfree_Empty: "interfree I []"
by(simp add:interfree_def)

lemma interfree_List:
  "\<lbrakk> interfree_swap I (x, xs); interfree I xs \<rbrakk> \<Longrightarrow> interfree I (x#xs)"
apply(simp add:interfree_def interfree_swap_def)
apply clarify
apply(case_tac i)
 apply(case_tac j)
  apply simp_all
apply(case_tac j,simp+)
done

lemma interfree_Map:
  "(\<forall>i j. a\<le>i \<and> i<b \<and> a\<le>j \<and> j<b  \<and> i\<noteq>j \<longrightarrow> interfree_aux I (c i, Q i, c j))
  \<Longrightarrow> interfree I (map (\<lambda>k. (c k, Q k)) [a..<b])"
by(force simp add: interfree_def less_diff_conv)

definition map_ann_hoare :: "'a assn \<Rightarrow> (('a ann_com_op * 'a assn) list) \<Rightarrow> bool " ("[\<turnstile>] _ _" [0] 45) where
  "[\<turnstile>] I Ts == (\<forall>i<length Ts. \<exists>c q. Ts!i=(Some c, q) \<and> I \<turnstile> c q)"

lemma MapAnnEmpty: "[\<turnstile>] I []"
by(simp add:map_ann_hoare_def)

lemma MapAnnList: "\<lbrakk> I \<turnstile> c q ; [\<turnstile>] I xs \<rbrakk> \<Longrightarrow> [\<turnstile>] I (Some c,q)#xs"
apply(simp add:map_ann_hoare_def)
apply clarify
apply(case_tac i,simp+)
done

lemma MapAnnMap:
  "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> I \<turnstile> (c k) (Q k) \<Longrightarrow> [\<turnstile>] I (map (\<lambda>k. (Some (c k), Q k)) [i..<j])"
apply(simp add: map_ann_hoare_def less_diff_conv)
done

lemma ParallelRule:"\<lbrakk> [\<turnstile>] I Ts ; interfree I Ts \<rbrakk>
  \<Longrightarrow> I \<parallel>- ((\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts!i)))) \<union> -I)
          Parallel Ts
        (\<Inter>i\<in>{i. i<length Ts}. post(Ts!i))"
apply(rule Parallel)
 apply(simp add:map_ann_hoare_def)
apply simp
done
(*
lemma ParamParallelRule:
 "\<lbrakk> \<forall>k<n. \<turnstile> (c k) (Q k);
   \<forall>k l. k<n \<and> l<n  \<and> k\<noteq>l \<longrightarrow> interfree_aux (Some(c k), Q k, Some(c l)) \<rbrakk>
  \<Longrightarrow> \<parallel>- (\<Inter>i\<in>{i. i<n} . pre(c i)) COBEGIN SCHEME [0\<le>i<n] (c i) (Q i) COEND  (\<Inter>i\<in>{i. i<n} . Q i )"
apply(rule ParallelConseqRule)
  apply simp
  apply clarify
  apply force
 apply(rule ParallelRule)
  apply(rule MapAnnMap)
  apply simp
 apply(rule interfree_Map)
 apply simp
apply simp
apply clarify
apply force
done
*)

text \<open>The following are some useful lemmas and simplification
tactics to control which theorems are used to simplify at each moment,
so that the original input does not suffer any unexpected
transformation.\<close>

lemma Compl_Collect: "-(Collect b) = {x. \<not>(b x)}"
  by fast

lemma list_length: "length []=0" "length (x#xs) = Suc(length xs)"
  by simp_all
lemma list_lemmas: "length []=0" "length (x#xs) = Suc(length xs)"
    "(x#xs) ! 0 = x" "(x#xs) ! Suc n = xs ! n"
  by simp_all
lemma le_Suc_eq_insert: "{i. i <Suc n} = insert n {i. i< n}"
  by auto
lemmas primrecdef_list = "pre.simps" "assertions.simps" "atomics.simps" "atom_com.simps"
lemmas my_simp_list = list_lemmas fst_conv snd_conv
not_less0 refl le_Suc_eq_insert Suc_not_Zero Zero_not_Suc nat.inject
Collect_mem_eq ball_simps option.simps primrecdef_list
lemmas ParallelConseq_list = INTER_eq Collect_conj_eq length_map length_upt length_append

ML \<open>
fun before_interfree_simp_tac (ctxt as (ctxt',args)) =
  simp_tac (put_simpset HOL_basic_ss ctxt' addsimps [@{thm com.simps}, @{thm post.simps}])

fun interfree_simp_tac (ctxt as (ctxt',args)) =
  asm_simp_tac (put_simpset HOL_ss ctxt'
    addsimps [@{thm split}, @{thm ball_Un}, @{thm ball_empty}] @ @{thms my_simp_list})

fun ParallelConseq (ctxt as (ctxt',args)) =
  simp_tac (put_simpset HOL_basic_ss ctxt'
    addsimps @{thms ParallelConseq_list} @ @{thms my_simp_list})
\<close>

text \<open>The following tactic applies \<open>tac\<close> to each conjunct in a
subgoal of the form \<open>A \<Longrightarrow> a1 \<and> a2 \<and> .. \<and> an\<close>  returning
\<open>n\<close> subgoals, one for each conjunct:\<close>

ML \<open>
fun conjI_Tac ctxt tac i st = st |>
       ( (EVERY [resolve_tac ctxt [conjI] i,
          conjI_Tac ctxt tac (i+1),
          tac i]) ORELSE (tac i) )
\<close>


subsubsection \<open>Tactic for the generation of the verification conditions\<close>

text \<open>The tactic basically uses two subtactics:

\begin{description}

\item[HoareRuleTac] is called at the level of parallel programs, it
 uses the ParallelTac to solve parallel composition of programs.
 This verification has two parts, namely, (1) all component programs are
 correct and (2) they are interference free.  \<open>HoareRuleTac\<close> is
 also called at the level of atomic regions, i.e.  \<open>\<langle> \<rangle>\<close> and
 \<open>AWAIT b THEN _ END\<close>, and at each interference freedom test.

\item[AnnHoareRuleTac] is for component programs which
 are annotated programs and so, there are not unknown assertions
 (no need to use the parameter precond, see NOTE).

 NOTE: precond(::bool) informs if the subgoal has the form \<open>\<parallel>- ?p c q\<close>,
 in this case we have precond=False and the generated  verification
 condition would have the form \<open>?p \<subseteq> \<dots>\<close> which can be solved by
 \<open>rtac subset_refl\<close>, if True we proceed to simplify it using
 the simplification tactics above.

\end{description}
\<close>

lemma False_impI:
  "False \<longrightarrow> P"
  by simp

lemma True_impI:
  "P \<Longrightarrow> True \<longrightarrow> P"
  by simp

(* Push remaining subgoals into hyps to remove duplicates quickly *)
ML \<open>val hyp_tac = CSUBGOAL (fn (prem,i) => PRIMITIVE (fn thm =>
    let
      val thm' = Thm.permute_prems 0 (i-1) thm |> Goal.protect 1
      val asm = Thm.assume prem
    in
      case (try (fn thm' => (Thm.implies_elim thm' asm)) thm') of
      SOME thm => thm |> Goal.conclude |> Thm.permute_prems 0 (~(i-1))
     | NONE => error ("hyp_tac failed:" ^ (@{make_string} (thm',asm)))
    end
  ))
\<close>

ML \<open>
  
fun WlpTac (ctxt as (ctxt',args)) i = resolve_tac ctxt' @{thms SeqRule} i THEN HoareRuleTac ctxt false (i + 1)
and HoareRuleTac (ctxt as (ctxt',args)) precond i st =
((SUBGOAL (fn (prem,i) =>
    ((WlpTac ctxt i THEN HoareRuleTac ctxt precond i)
      ORELSE
      (FIRST[resolve_tac ctxt' @{thms SkipRule} i,
             resolve_tac ctxt' @{thms BasicRule} i,
             (EVERY[resolve_tac ctxt' @{thms ParallelConseqRule} i,
                   ParallelConseq ctxt (i+2),
                   ParallelTac ctxt (i+1),
                   ParallelConseq ctxt i]),
             EVERY[resolve_tac ctxt' @{thms CondRule} i,
                   HoareRuleTac ctxt false (i+2),
                   HoareRuleTac ctxt false (i+1)],
             EVERY[resolve_tac ctxt' @{thms WhileRule} i,
                   HoareRuleTac ctxt true (i+1)],
             all_tac ]
       THEN (if precond then (all_tac) else (resolve_tac ctxt' (@{thms subset_refl Int_lower1}) i)))
       ))) THEN_ALL_NEW hyp_tac) i st
   

and AnnWlpTac (ctxt as (ctxt',args)) i = resolve_tac ctxt' @{thms AnnSeq} i THEN AnnHoareRuleTac ctxt (i + 1)
and AnnHoareRuleTac (ctxt as (ctxt',args)) i st = (SUBGOAL (fn (prem,i) =>
    (
    ((AnnWlpTac ctxt i THEN AnnHoareRuleTac ctxt i )
     ORELSE
      (FIRST[(resolve_tac ctxt' @{thms AnnskipRule} i),
             EVERY[resolve_tac ctxt' @{thms AnnatomRule} i,
                   HoareRuleTac ctxt true (i+1)],
             (resolve_tac ctxt' @{thms AnnwaitRule} i),
             resolve_tac ctxt' @{thms AnnBasic} i,
             EVERY[resolve_tac ctxt' @{thms AnnCond1} i,
                   AnnHoareRuleTac ctxt (i+3),
                   AnnHoareRuleTac ctxt (i+1)],
             EVERY[resolve_tac ctxt' @{thms AnnCond2} i,
                   AnnHoareRuleTac ctxt (i+1)],
             EVERY[resolve_tac ctxt' @{thms AnnWhile} i,
                   AnnHoareRuleTac ctxt (i+2)],
             EVERY[resolve_tac ctxt' @{thms AnnAwait} i,
                   HoareRuleTac ctxt true (i+1)],
             all_tac]))))) i st

and ParallelTac (ctxt as (ctxt',args)) i = EVERY[resolve_tac ctxt' @{thms ParallelRule} i,
                          interfree_Tac ctxt (i+1),
                           MapAnn_Tac ctxt i]

and MapAnn_Tac (ctxt as (ctxt',args)) i st = st |>
    (FIRST[resolve_tac ctxt' @{thms MapAnnEmpty} i,
           EVERY[resolve_tac ctxt' @{thms MapAnnList} i,
                 MapAnn_Tac ctxt (i+1),
                 AnnHoareRuleTac ctxt i],
           EVERY[resolve_tac ctxt' @{thms MapAnnMap} i,
                 resolve_tac ctxt' @{thms allI} i,
                 resolve_tac ctxt' @{thms impI} i,
                 AnnHoareRuleTac ctxt i]])

and interfree_swap_Tac (ctxt as (ctxt',args)) i st = st |>
    (FIRST[resolve_tac ctxt' @{thms interfree_swap_Empty} i,
           EVERY[resolve_tac ctxt' @{thms interfree_swap_List} i,
                 interfree_swap_Tac ctxt (i+2),
                 interfree_aux_Tac ctxt (i+1),
                 interfree_aux_Tac ctxt i ],
           EVERY[resolve_tac ctxt' @{thms interfree_swap_Map} i,
                 resolve_tac ctxt' @{thms allI} i,
                 resolve_tac ctxt' @{thms impI} i,
                 conjI_Tac ctxt' (interfree_aux_Tac ctxt) i]])

and interfree_Tac (ctxt as (ctxt',args)) i st = st |>
   (FIRST[resolve_tac ctxt' @{thms interfree_Empty} i,
          EVERY[resolve_tac ctxt' @{thms interfree_List} i,
                interfree_Tac ctxt (i+1),
                interfree_swap_Tac ctxt i],
          EVERY[resolve_tac ctxt' @{thms interfree_Map} i,
                resolve_tac ctxt' @{thms allI} i,
                resolve_tac ctxt' @{thms allI} i,
                resolve_tac ctxt' @{thms impI} i,
                interfree_aux_Tac ctxt i ]])

and interfree_aux_Tac (ctxt as (ctxt',args)) i = (before_interfree_simp_tac ctxt i ) THEN
        (FIRST[resolve_tac ctxt' @{thms interfree_aux_rule1} i,
               dest_assertions_Tac ctxt i])

and dest_assertions_Tac (ctxt as (ctxt',args)) i st = (Cache_Tactics.SUBGOAL_CACHE
  (snd args)
  (fn (prem,i) =>
    (
    ((FIRST[EVERY[resolve_tac ctxt' (@{thms AnnBasic_assertions}) i,
                 dest_atomics_Tac ctxt (i+1),
                 dest_atomics_Tac_helper ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnSeq_assertions} i,
                 dest_assertions_Tac ctxt (i+1),
                 dest_assertions_Tac ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnCond1_assertions} i,
                 dest_assertions_Tac ctxt (i+2),
                 dest_assertions_Tac ctxt (i+1),
                 dest_atomics_Tac_helper ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnCond2_assertions} i,
                 dest_assertions_Tac ctxt (i+1),
                 dest_atomics_Tac_helper ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnWhile_assertions} i,
                 dest_assertions_Tac ctxt (i+2),
                 dest_atomics_Tac_helper ctxt (i+1),
                 dest_atomics_Tac_helper ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnAwait_assertions} i,
                 dest_atomics_Tac ctxt (i+1),
                 dest_atomics_Tac_helper ctxt i],
           dest_atomics_Tac ctxt i]))))) i st

and dest_atomics_Tac_helper (ctxt as (ctxt',args)) i =
    (resolve_tac ctxt' @{thms False_impI} THEN_ALL_NEW K no_tac) i
    ORELSE resolve_tac ctxt' @{thms True_impI} i THEN dest_atomics_Tac ctxt i

and uses_all_pres_Tac (ctxt as (ctxt',args)) i =
    TRY ((simp_tac (put_simpset HOL_ss ctxt' addsimps @{thms uses_all_pres.simps uses_all_pres'.simps}) THEN_ALL_NEW K no_tac) i)

and dest_atomics_Tac (ctxt as (ctxt',args)) i st = (Cache_Tactics.SUBGOAL_CACHE
  (fst args)
  (fn (prem,i) =>
    (
    (FIRST[EVERY[resolve_tac  ctxt' (@{thms AnnBasic_atomics}) i,
                 HoareRuleTac ctxt true i],
           EVERY[resolve_tac ctxt' @{thms AnnSeq_atomics} i,
                 dest_atomics_Tac ctxt (i+1),
                 dest_atomics_Tac ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnCond1_atomics} i,
                 dest_atomics_Tac ctxt (i+1),
                 dest_atomics_Tac ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnCond2_atomics} i,
                 dest_atomics_Tac ctxt i],
           EVERY[resolve_tac ctxt' @{thms AnnWhile_atomics} i,
                 dest_atomics_Tac ctxt i],
           EVERY[resolve_tac ctxt' @{thms Annatom_atomics} i,
                 uses_all_pres_Tac ctxt (i+1),
                 HoareRuleTac ctxt true i],
           EVERY[resolve_tac ctxt' @{thms AnnAwait_atomics} i,
                 uses_all_pres_Tac ctxt (i+1),
                 HoareRuleTac ctxt true i],
                 all_tac])))) i st 
\<close>


text \<open>The final tactic is given the name \<open>oghoare\<close>:\<close>

ML \<open>
fun cacheify_tactic tac ctxt i st =
  let
    val cache1 = Cache_Tactics.new_subgoal_cache ();
    val cache2 = Cache_Tactics.new_subgoal_cache ();
  in
      st |>
      (tac (ctxt,(cache1,cache2)) i
      THEN (PRIMITIVE Drule.implies_intr_hyps)
      THEN (PRIMITIVE (fn thm => 
        (Cache_Tactics.clear_subgoal_cache cache1;Cache_Tactics.clear_subgoal_cache cache2;thm))))
      
  end

  val oghoare_tac = cacheify_tactic (fn args => HoareRuleTac args true)
\<close>

text \<open>Notice that the tactic for parallel programs \<open>oghoare_tac\<close> is initially invoked with the value \<open>true\<close> for
the parameter \<open>precond\<close>.

Parts of the tactic can be also individually used to generate the
verification conditions for annotated sequential programs and to
generate verification conditions out of interference freedom tests:\<close>

ML \<open>
val annhoare_tac = cacheify_tactic AnnHoareRuleTac

val interfree_aux_tac = cacheify_tactic interfree_aux_Tac
\<close>

text \<open>The so defined ML tactics are then ``exported'' to be used in
Isabelle proofs.\<close>

method_setup oghoare = \<open>
  Scan.succeed (SIMPLE_METHOD' o oghoare_tac)\<close>
  "verification condition generator for the oghoare logic"

method_setup annhoare = \<open>
  Scan.succeed (SIMPLE_METHOD' o annhoare_tac)\<close>
  "verification condition generator for the ann_hoare logic"

method_setup interfree_aux = \<open>
  Scan.succeed (SIMPLE_METHOD' o interfree_aux_tac)\<close>
  "verification condition generator for interference freedom tests"

text \<open>Tactics useful for dealing with the generated verification conditions:\<close>

method_setup conjI_tac = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (conjI_Tac ctxt (K all_tac)))\<close>
  "verification condition generator for interference freedom tests"

ML \<open>
fun disjE_Tac ctxt tac i st = st |>
       ( (EVERY [eresolve_tac ctxt [disjE] i,
          disjE_Tac ctxt tac (i+1),
          tac i]) ORELSE (tac i) )
\<close>

method_setup disjE_tac = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (disjE_Tac ctxt (K all_tac)))\<close>
  "verification condition generator for interference freedom tests"

                                                                     
end
