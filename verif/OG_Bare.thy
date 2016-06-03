(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory OG_Bare

imports
  "../lib/Hoare_Parallel/OG_Tactics"
  "../lib/Hoare_Parallel/Quote_Antiquote"
  "OG_More"
  No_OG_Syntax
  

begin

datatype 'a bare_com = 
     BareParallel "('a bare_com option) list"
   | BareBasic "('a \<Rightarrow> 'a set)" 
   | BareSeq "('a bare_com)"  "('a bare_com)"
   | BareCond1 "('a bexp)"  "('a bare_com)"  "('a bare_com)"
   | BareCond2 "('a bexp)"  "('a bare_com)"
   | BareWhile "('a bexp)"  "('a bare_com)"
   | BareAwait "('a bexp)"  "('a bare_com)"

fun
  extract_ann_prg :: "'a ann_com \<Rightarrow> 'a bare_com" and
  extract_prg :: "'a com \<Rightarrow> 'a bare_com"
where
  "extract_ann_prg (AnnBasic r f) = BareBasic f"
| "extract_ann_prg (AnnSeq c1 c2) = BareSeq (extract_ann_prg c1) (extract_ann_prg c2)"
| "extract_ann_prg (AnnCond1 r b c1 c2) = BareCond1 b (extract_ann_prg c1) (extract_ann_prg c2)"
| "extract_ann_prg (AnnCond2 r b c) = BareCond2 b (extract_ann_prg c)"
| "extract_ann_prg (AnnWhile r b i c) = BareWhile b (extract_ann_prg c)"
| "extract_ann_prg (AnnAwait r b c) = BareAwait b (extract_prg c)"

| "extract_prg (Parallel Ts) = BareParallel (map ((map_option extract_ann_prg)\<circ>fst) Ts)"
| "extract_prg (Basic f) = BareBasic f"
| "extract_prg (Seq c1 c2) = BareSeq (extract_prg c1) (extract_prg c2)"
| "extract_prg (Cond b c1 c2) = BareCond1 b (extract_prg c1) (extract_prg c2)"
| "extract_prg (While b i c) = BareWhile b (extract_prg c)"


lemma [code]:
  fixes r f ac1 ac2 b ai ac c1 c2 c i cc
  shows
  "extract_ann_prg (AnnBasic r f) = BareBasic f"
  "extract_ann_prg (AnnSeq ac1 ac2) = BareSeq (extract_ann_prg ac1) (extract_ann_prg ac2)"
  "extract_ann_prg (AnnCond1 r b ac1 ac2) = BareCond1 b (extract_ann_prg ac1) (extract_ann_prg ac2)"
  "extract_ann_prg (AnnCond2 r b ac) = BareCond2 b (extract_ann_prg ac)"
  "extract_ann_prg (AnnWhile r b ai ac) = BareWhile b (extract_ann_prg ac)"
  "extract_ann_prg (AnnAwait r b c) = BareAwait b (extract_prg c)"

  "extract_prg (Parallel Ts) = BareParallel (map ((map_option extract_ann_prg)\<circ>fst) Ts)"
  "extract_prg (Basic f) = BareBasic f"
  "extract_prg (Seq c1 c2) = BareSeq (extract_prg c1) (extract_prg c2)"
  "extract_prg (Cond b c1 c2) = BareCond1 b (extract_prg c1) (extract_prg c2)"
  "extract_prg (While b i c) = BareWhile b (extract_prg c)"
  "extract_prg (Parallel (map (\<lambda>i. (Some (cc i), q)) [j..<k])) =
          BareParallel (map (\<lambda>i. (Some (extract_ann_prg (cc i)))) [j..<k])"
  by simp_all

primrec await_paint :: "'a bexp \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com" where
  "await_paint P (BareParallel Ts) = BareParallel (map (map_option (await_paint P)) Ts)"
| "await_paint P (BareBasic f) = (BareAwait P (BareBasic f))"
| "await_paint P (BareSeq c1 c2) =  (BareSeq (await_paint P c1) (await_paint P c2))"
| "await_paint P (BareCond1 bb c1 c2) = (BareCond1 bb (await_paint P c1) (await_paint P c2))"
| "await_paint P (BareCond2 bb c) = (BareCond2 bb (await_paint P c))"
| "await_paint P (BareWhile bb c) = (BareWhile bb (await_paint P c))"
| "await_paint P (BareAwait bb c) = (BareAwait (bb\<inter>P) c)"

definition
  oghoare_bare :: "'a assn \<Rightarrow> 'a assn\<Rightarrow> 'a bare_com \<Rightarrow> 'a assn \<Rightarrow> bool"  ("(\<parallel>-\<^sub>b _// _// _//_)" [60,90] 45)
where
  "\<parallel>-\<^sub>b I p c q \<equiv> \<exists> c'. extract_prg c' = c \<and> \<parallel>-\<^sub>i I p c' q"

lemma extract_ann_prg_add_inv:
  "extract_ann_prg (add_inv_assn_com I' c) = extract_ann_prg c"
  by (induct c) auto

lemma extract_prg_add_inv:
  "extract_prg (add_inv_com I' c) = extract_prg c"
  apply (induct c, simp_all add: add_inv_aux_def)
  apply (clarsimp split: option.splits)
  apply (rule extract_ann_prg_add_inv)
  done

lemma add_inv_assn_com_inter:
  "add_inv_assn_com (I \<inter> I') c =  add_inv_assn_com I (add_inv_assn_com I' c)"
  by (induct c, auto)

lemma add_inv_aux_inter:
  "add_inv_aux (I \<inter> I') c =  add_inv_aux I (add_inv_aux I' c)"
  apply (clarsimp simp: add_inv_aux_def split: option.splits prod.splits)
  apply (auto simp: add_inv_assn_com_inter)
  done

lemma add_inv_com_inter:
  "add_inv_com (I \<inter> I') c =  add_inv_com I (add_inv_com I' c)"
  by (induct c, simp_all add: add_inv_aux_inter)

lemma oghoare_bareI: 
   "\<exists> c'. extract_prg c' = c \<and> \<parallel>-\<^sub>i (I\<inter>I') p c' q \<Longrightarrow> \<parallel>-\<^sub>b I p c q"
   apply (clarsimp simp: oghoare_bare_def)
   apply (rule_tac x="add_inv_com I' c'" in exI)
   apply (simp add: extract_prg_add_inv oghoare_inv_def add_inv_com_inter)
   done

   

text\<open>Syntax for commands and for assertions and boolean expressions in
 commands @{text com} and annotated commands @{text ann_com}.\<close>

abbreviation Skip :: "'a bare_com"  ("SKIP" 63)
  where "SKIP \<equiv> BareBasic (\<lambda>s. {s})"

notation
  BareSeq  ("_,,/ _" [55, 56] 55) and
  BareSeq  ("_;;/ _" [60,61] 60)

syntax
  "_Assign"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a bare_com"    ("(\<acute>_ :=/ _)" [70, 65] 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST BareBasic \<guillemotleft>\<acute>(CONST DETERM (_update_name x (\<lambda>_. a)))\<guillemotright>"

abbreviation
  "update_var_b f S s \<equiv> (\<lambda>v. f (\<lambda>_. v) s) ` S"

syntax
  "_Pick"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a bare_com"    ("(\<acute>_ :\<in>/ _)" [70, 65] 61)

translations
  "\<acute>x :\<in> S" \<rightharpoonup> "CONST BareBasic \<guillemotleft>\<acute>(CONST update_var_b (_update_name x) S)\<guillemotright>"

syntax
  "_BareAwait"    :: "'a bexp  \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com"
                    ("AWAIT _ //THEN /_ /END"  [0,0] 61)
  "_BareAtom"     :: "'a bare_com \<Rightarrow> 'a bare_com"   ("\<langle>_\<rangle>" [0] 61)
  "_BareWait"     :: "'a bexp \<Rightarrow> 'a bare_com"   ("WAIT _ END" [0] 61)

  "_BareCond"     :: "'a bexp \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com"
                    ("IF _ //(2THEN _) //(2ELSE _) /FI" [0, 0, 0] 61)

  "_BareCond2"    :: "'a bexp  \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com"
                    ("IF _ //(2THEN _) /FI"  [0,0] 56)
  "_BareWhile"       :: "'a bexp \<Rightarrow> 'a bare_com \<Rightarrow> 'a bare_com"
                    ("(0WHILE _ /(0DO _ /OD))"  [0, 0] 61)

translations
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST BareCond1 \<lbrace>b\<rbrace> c1 c2"
translations
  "IF b THEN c FI" \<rightleftharpoons>  "CONST BareCond2 \<lbrace>b\<rbrace> c"
translations
  "WHILE b DO c OD" \<rightleftharpoons> "CONST BareWhile \<lbrace>b\<rbrace> c"

translations
  "AWAIT b THEN c END" \<rightharpoonup> "CONST BareAwait \<lbrace>b\<rbrace> c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN OG_Bare.SKIP END"

nonterminal prgs

syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" [57] 56)
  "_prg" :: "'a \<Rightarrow> prgs"        ("_" [60] 57)
  "_prgs" :: "['a, prgs] \<Rightarrow> prgs"  ("_//\<parallel>//_" [60,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"
                  ("SCHEME [_ \<le> _ < _] _" [0,0,0,60] 57)

translations
  "_prg c" \<rightleftharpoons> "[CONST Some c]"
  "_prgs c ps" \<rightleftharpoons> "(CONST Some c) # ps"
  "_PAR ps" \<rightleftharpoons> "CONST BareParallel ps"

  "_prg_scheme j i k c" \<rightleftharpoons> "CONST map (\<lambda>i. CONST Some c) [j..<k]"

  
print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, Const (@{const_syntax DETERM}, _) $ (f $ (Const (@{const_syntax "Map.empty"}, _))) $ Bound 0) :: ts) =
           quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
             (Abs (x, dummyT, Const (@{const_syntax None},dummyT)) :: ts)
      | assign_tr' (t as (Abs (x, _, Const (@{const_syntax DETERM},_) $ (f $ k) $ Bound 0)) :: ts) =
           quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
             (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' (t as (Abs (x, _, Const (@{const_syntax update_var_b},_) $ f $ k $ Bound 0)) :: ts) =
           quote_tr' (Syntax.const @{syntax_const "_Pick"} $ Syntax_Trans.update_name_tr' f)
             (Abs (x, dummyT, k) :: ts)
      | assign_tr' _ = raise Match;

    fun Parallel_PAR [(Const (@{const_syntax Cons}, _) $
            (Const (@{const_syntax Some},_) $ t1 ) $
            Const (@{const_syntax Nil}, _))] = Syntax.const @{syntax_const "_prg"} $ t1
      | Parallel_PAR [(Const (@{const_syntax Cons}, _) $
            (Const (@{const_syntax Some}, _) $ t1) $ ts)] =
          Syntax.const @{syntax_const "_prgs"} $ t1 $ Parallel_PAR [ts]
      | Parallel_PAR _ = raise Match;

    fun Parallel_tr' ts = Syntax.const @{syntax_const "_PAR"} $ Parallel_PAR ts;
  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax BareBasic}, K assign_tr'),
    (@{const_syntax BareCond1}, K (bexp_tr' @{syntax_const "_BareCond"})),
    (@{const_syntax BareCond2}, K (bexp_tr' @{syntax_const "_BareCond2"})),
    (@{const_syntax BareWhile}, K (bexp_tr' @{syntax_const "_BareWhile"})),
    (@{const_syntax BareAwait}, K (bexp_tr' @{syntax_const "_BareAwait"}))]
  end;
\<close>

end