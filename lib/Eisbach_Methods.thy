(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
   Methods and method combinators that are built using Eisbach.
*)

theory Eisbach_Methods
imports "subgoal_focus/Subgoal_Methods"
        "~~/src/HOL/Eisbach/Eisbach_Tools"
        Rule_By_Method
begin


section \<open>Debugging methods\<close>

method print_concl = (match conclusion in P for P \<Rightarrow> \<open>print_term P\<close>)

method_setup print_raw_goal = \<open>Scan.succeed (fn ctxt => fn facts => 
  (fn (ctxt, st) => (Output.writeln (Thm.string_of_thm ctxt st); 
    Seq.make_results (Seq.single (ctxt, st)))))\<close>

ML \<open>fun method_evaluate text ctxt facts = 
  Method.NO_CONTEXT_TACTIC ctxt
    (Method.evaluate_runtime text ctxt facts)\<close>


method_setup print_headgoal = 
  \<open>Scan.succeed (fn ctxt =>
   SIMPLE_METHOD
    (SUBGOAL (fn (t,_) => 
     (Output.writeln 
     (Pretty.string_of (Syntax.pretty_term ctxt t)); all_tac)) 1))\<close>

section \<open>Simple Combinators\<close>

method_setup defer_tac = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (defer_tac 1))\<close>
method_setup prefer_last = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (PRIMITIVE (Thm.permute_prems 0 ~1)))\<close>

method_setup all =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (ALLGOALS tac) facts end)
\<close>

method_setup determ =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (DETERM tac) facts end)
\<close>

method_setup changed =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (CHANGED tac) facts end)
\<close>

 
method_setup timeit =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let 
     fun timed_tac st seq = Seq.make (fn () => Option.map (apsnd (timed_tac st)) 
       (timeit (fn () => (Seq.pull seq))));

     fun tac st' =
       timed_tac st' (method_evaluate m ctxt facts st');

   in SIMPLE_METHOD tac [] end)
\<close>
 
 
method_setup timeout =
 \<open>Scan.lift Parse.int -- Method.text_closure >> (fn (i,m) => fn ctxt => fn facts =>
   let 
     fun str_of_goal th = Pretty.string_of (Goal_Display.pretty_goal ctxt th);
     
     fun limit st f x = Timeout.apply (Time.fromSeconds i) f x
       handle Timeout.TIMEOUT _ => error ("Method timed out:\n" ^ (str_of_goal st));
      
     fun timed_tac st seq = Seq.make (limit st (fn () => Option.map (apsnd (timed_tac st)) 
       (Seq.pull seq)));
       
     fun tac st' =
       timed_tac st' (method_evaluate m ctxt facts st');

   in SIMPLE_METHOD tac [] end)
\<close>

method repeat_new methods m = (m ; (repeat_new \<open>m\<close>)?)

text \<open>The following @{text fails} and @{text succeeds} methods protect the goal from the effect
      of a method, instead simply determining whether or not it can be applied to the current goal.
      The @{text fails} method inverts success, only succeeding if the given method would fail.\<close>

method_setup fails =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun fail_tac st' = 
       (case Seq.pull (method_evaluate m ctxt facts st') of
          SOME _ => Seq.empty
        | NONE => Seq.single st')

   in SIMPLE_METHOD fail_tac facts end)
\<close>

method_setup succeeds =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun can_tac st' = 
       (case Seq.pull (method_evaluate m ctxt facts st') of
          SOME (st'',_) => Seq.single st'
        | NONE => Seq.empty)

   in SIMPLE_METHOD can_tac facts end)
\<close>

text \<open>This method wraps up the "focus" mechanic of match without actually doing any matching.
      We need to consider whether or not there are any assumptions in the goal,
      as premise matching fails if there are none.

      If the @{text fails} method is removed here, then backtracking will produce
      a set of invalid results, where only the conclusion is focused despite
      the presence of subgoal premises.
      \<close>

method focus_concl methods m =
  ((fails \<open>erule thin_rl\<close>, match conclusion in _ \<Rightarrow> \<open>m\<close>)
  | match premises (local) in H:_ (multi) \<Rightarrow> \<open>m\<close>)

section \<open>Advanced combinators\<close>

subsection \<open>Protecting goal elements (assumptions or conclusion) from methods\<close>

context
begin

private definition "protect_concl x \<equiv> \<not> x"
private definition "protect_false \<equiv> False"

private lemma protect_start: "(protect_concl P \<Longrightarrow> protect_false) \<Longrightarrow> P" 
  by (simp add: protect_concl_def protect_false_def) (rule ccontr)

private lemma protect_end: "protect_concl P \<Longrightarrow> P \<Longrightarrow> protect_false" 
  by (simp add: protect_concl_def protect_false_def)

method only_asm methods m = 
  (match premises in H[thin]:_ (multi,cut) \<Rightarrow> 
    \<open>rule protect_start, 
     match premises in H'[thin]:"protect_concl _" \<Rightarrow> 
       \<open>insert H,m;rule protect_end[OF H']\<close>\<close>)

method only_concl methods m = (focus_concl \<open>m\<close>)

end

notepad begin
 fix D C
  assume DC:"D \<Longrightarrow> C"
  have "D \<and> D \<Longrightarrow> C \<and> C"
  apply (only_asm \<open>simp\<close>) -- "stash conclusion before applying method"
  apply (only_concl \<open>simp add: DC\<close>) -- "hide premises from method"
  by (rule DC)

end

subsection \<open>Safe subgoal folding (avoids expanding meta-conjuncts)\<close>

text \<open>Isabelle's goal mechanism wants to aggressively expand meta-conjunctions if they
      are the top-level connective. This means that @{text fold_subgoals} will immediately
      be unfolded if there are no common assumptions to lift over.

      To avoid this we simply wrap conjunction inside of conjunction' to hide it
      from the usual facilities.\<close>

context begin

definition
  conjunction' :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr "&^&" 2) where 
  "conjunction' A B \<equiv> (PROP A &&& PROP B)"


text \<open>In general the context antiquotation does not work in method definitions.
  Here it is fine because Conv.top_sweep_conv is just over-specified to need a Proof.context
  when anything would do.\<close>

method safe_meta_conjuncts =
  raw_tactic 
   \<open>REPEAT_DETERM
     (CHANGED_PROP 
      (PRIMITIVE 
        (Conv.gconv_rule ((Conv.top_sweep_conv (K (Conv.rewr_conv @{thm conjunction'_def[symmetric]})) @{context})) 1)))\<close>

method safe_fold_subgoals = (fold_subgoals (prefix), safe_meta_conjuncts)

lemma atomize_conj' [atomize]: "(A &^& B) == Trueprop (A & B)" 
  by (simp add: conjunction'_def, rule atomize_conj)

lemma context_conjunction'I:
  "PROP P \<Longrightarrow> (PROP P \<Longrightarrow> PROP Q) \<Longrightarrow> PROP P &^& PROP Q"
  apply (simp add: conjunction'_def)
  apply (rule conjunctionI)
   apply assumption
  apply (erule meta_mp)
  apply assumption
  done

lemma conjunction'I:
  "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP P &^& PROP Q"
  by (rule context_conjunction'I; simp)

lemma conjunction'E:
  assumes PQ: "PROP P &^& PROP Q"
  assumes PQR: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R"
  shows
  "PROP R"
  apply (rule PQR)
  apply (rule PQ[simplified conjunction'_def, THEN conjunctionD1])
  by (rule PQ[simplified conjunction'_def, THEN conjunctionD2])

end

notepad begin
  fix D C E
  
  assume DC: "D \<and> C"
  have "D" "C \<and> C"
  apply -
  apply (safe_fold_subgoals, simp, atomize (full))
  apply (rule DC)
  done

end


section \<open>Utility methods\<close>
  

subsection \<open>Finding a goal based on successful application of a method\<close>

context begin

method_setup find_goal =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun prefer_first i = SELECT_GOAL 
       (fn st' =>
         (case Seq.pull (method_evaluate m ctxt facts st') of
           SOME (st'',_) => Seq.single st''
         | NONE => Seq.empty)) i THEN prefer_tac i

   in SIMPLE_METHOD (FIRSTGOAL prefer_first) facts end)\<close>

end

notepad begin

  fix A B
  assume A: "A" and B: "B"

  have "A" "A" "B"
    apply (find_goal \<open>match conclusion in B \<Rightarrow> \<open>-\<close>\<close>)
    apply (rule B)
    by (rule A)+

  have "A \<and> A" "A \<and> A" "B"
    apply (find_goal \<open>fails \<open>simp\<close>\<close>) -- "find the first goal which cannot be simplified"
    apply (rule B)
    by (simp add: A)+

  have  "B" "A" "A \<and> A"
    apply (find_goal \<open>succeeds \<open>simp\<close>\<close>) -- "find the first goal which can be simplified (without doing so)"
    apply (rule conjI)
    by (rule A B)+
 
end


subsection \<open>Remove redundant subgoals\<close>

text \<open>Tries to solve subgoals by assuming the others and then using the given method.
      Backtracks over all possible re-orderings of the subgoals.\<close>

context begin

definition "protect (PROP P) \<equiv> P"

lemma protectE: "PROP protect P \<Longrightarrow> (PROP P \<Longrightarrow> PROP R) \<Longrightarrow> PROP R" by (simp add: protect_def)

private lemmas protect_thin = thin_rl[where V="PROP protect P" for P]

private lemma context_conjunction'I_protected:
  assumes P: "PROP P"
  assumes PQ: "PROP protect (PROP P) \<Longrightarrow> PROP Q"
  shows
  "PROP P &^& PROP Q"
   apply (simp add: conjunction'_def)
   apply (rule P)
  apply (rule PQ)
  apply (simp add: protect_def)
  by (rule P)

private lemma conjunction'_sym: "PROP P &^& PROP Q \<Longrightarrow> PROP Q &^& PROP P"
  apply (simp add: conjunction'_def)
  apply (frule conjunctionD1)
  apply (drule conjunctionD2)
  apply (rule conjunctionI)
  by assumption+


  
private lemmas context_conjuncts'I =
  context_conjunction'I_protected 
  context_conjunction'I_protected[THEN conjunction'_sym]

method distinct_subgoals_strong methods m = 
  (safe_fold_subgoals,
   (intro context_conjuncts'I; 
     (((elim protectE conjunction'E)?, solves \<open>m\<close>)
     | (elim protect_thin)?)))?

end

method forward_solve methods fwd m =
  (fwd, prefer_last, fold_subgoals, safe_meta_conjuncts, rule conjunction'I,
   defer_tac, ((intro conjunction'I)?; solves \<open>m\<close>))[1]

method frule_solve methods m uses rule = (forward_solve \<open>frule rule\<close> \<open>m\<close>)
method drule_solve methods m uses rule = (forward_solve \<open>drule rule\<close> \<open>m\<close>)

notepad begin
  {
  fix A B C D E
  assume ABCD: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D"
  assume ACD: "A \<Longrightarrow> C \<Longrightarrow> D"
  assume DE: "D \<Longrightarrow> E"
  assume B C

  have "A \<Longrightarrow> D"
  apply (frule_solve \<open>simp add: \<open>B\<close> \<open>C\<close>\<close> rule: ABCD)
  apply (drule_solve \<open>simp add: \<open>B\<close> \<open>C\<close>\<close> rule: ACD)
  apply (match premises in A \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)
  apply assumption
  done
  }
end


notepad begin
  {
  fix A B C
  assume A: "A"
  have "A" "B \<Longrightarrow> A"
  apply -
  apply (distinct_subgoals_strong \<open>assumption\<close>)
  by (rule A)

  have "B \<Longrightarrow> A" "A" 
  by (distinct_subgoals_strong \<open>assumption\<close>, rule A) -- "backtracking required here"
  }

  {
  fix A B C
  
  assume B: "B"
  assume BC: "B \<Longrightarrow> C" "B \<Longrightarrow> A"
  have "A" "B \<longrightarrow> (A \<and> C)" "B"
  apply (distinct_subgoals_strong \<open>simp\<close>, rule B) -- "backtracking required here"
  by (simp add: BC)
  
  }
end

section \<open>Attribute methods (for use with rule_by_method attributes)\<close>

method prove_prop_raw for P :: "prop" methods m =
  (erule thin_rl, rule revcut_rl[of "PROP P"],
    solves \<open>match conclusion in _ \<Rightarrow> \<open>m\<close>\<close>)

method prove_prop for P :: "prop" = (prove_prop_raw "PROP P" \<open>auto\<close>)

experiment begin

lemma assumes A[simp]:A shows A by (rule [[@\<open>prove_prop A\<close>]])

end

section \<open>Shortcuts for prove_prop. Note these are less efficient than using the raw syntax because
 the facts are re-proven every time.\<close>

method ruleP for P :: "prop" = (catch \<open>rule [[@\<open>prove_prop "PROP P"\<close>]]\<close> \<open>fail\<close>)
method insertP for P :: "prop" = (catch \<open>insert [[@\<open>prove_prop "PROP P"\<close>]]\<close> \<open>fail\<close>)[1]

experiment begin

lemma assumes A[simp]:A shows A by (ruleP False | ruleP A)
lemma assumes A:A shows A by (ruleP "\<And>P. P \<Longrightarrow> P \<Longrightarrow> P", rule A, rule A)

end

end
