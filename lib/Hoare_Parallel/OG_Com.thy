chapter \<open>The Owicki-Gries Method\<close>

section \<open>Abstract Syntax\<close>

theory OG_Com imports Main begin

text \<open>Type abbreviations for boolean expressions and assertions:\<close>

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

text \<open>The syntax of commands is defined by two mutually recursive
datatypes: \<open>'a ann_com\<close> for annotated commands and \<open>'a
com\<close> for non-annotated commands.\<close>

datatype 'a ann_com =
     AnnBasic "(bool \<times> 'a assn)"  "('a \<Rightarrow> 'a set)"
   | AnnSeq "('a ann_com)"  "('a ann_com)"
   | AnnCond1 "(bool \<times> 'a assn)"  "('a bexp)"  "('a ann_com)"  "('a ann_com)"
   | AnnCond2 "(bool \<times> 'a assn)"  "('a bexp)"  "('a ann_com)"
   | AnnWhile "(bool \<times> 'a assn)"  "('a bexp)" "(bool \<times> 'a assn)"  "('a ann_com)"
   | AnnAwait "(bool \<times> 'a assn)"  "('a bexp)"  "('a com)"
and 'a com =
     Parallel "('a ann_com option \<times> 'a assn) list"
   | Basic "('a \<Rightarrow> 'a set)"
   | Seq "('a com)"  "('a com)"
   | Cond "('a bexp)"  "('a com)"  "('a com)"
   | While "('a bexp)"  "('a assn)"  "('a com)"

text \<open>The function \<open>pre\<close> extracts the precondition of an
annotated command:\<close>

primrec pre ::"'a ann_com \<Rightarrow> 'a assn"  where
  "pre (AnnBasic r f) = snd r"
| "pre (AnnSeq c1 c2) = pre c1"
| "pre (AnnCond1 r b c1 c2) = snd r"
| "pre (AnnCond2 r b c) = snd r"
| "pre (AnnWhile r b i c) = snd r"
| "pre (AnnAwait r b c) = snd r"

text \<open>Well-formedness predicate for atomic programs:\<close>

primrec atom_com :: "'a com \<Rightarrow> bool" where
  "atom_com (Parallel Ts) = False"
| "atom_com (Basic f) = True"
| "atom_com (Seq c1 c2) = (atom_com c1 \<and> atom_com c2)"
| "atom_com (Cond b c1 c2) = (atom_com c1 \<and> atom_com c2)"
| "atom_com (While b i c) = atom_com c"

end