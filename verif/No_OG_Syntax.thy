(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory No_OG_Syntax
imports "../lib/Hoare_Parallel/OG_Syntax"
begin

text\<open>Syntax for commands and for assertions and boolean expressions in
 commands @{text com} and annotated commands @{text ann_com}.\<close>

no_notation Skip ("SKIP" 63) and
  AnnSkip ("_//SKIP" [90] 63) and
  AnnSkipIgnore ("_*//SKIP" [90] 63)

no_notation
  Seq  ("_,,/ _" [55, 56] 55) and
  AnnSeq  ("_;;/ _" [60,61] 60)

no_syntax
  "_Assign"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_AnnAssign"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_ \<acute>_ :=/ _)" [90,70,65] 61)
  "_AnnAssignIgnore"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_* \<acute>_ :=/ _)" [90,70,65] 61)

hide_const (open) update_var

no_syntax
  "_Pick"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(\<acute>_ :\<in>/ _)" [70, 65] 61)
  "_AnnPick"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_ \<acute>_ :\<in>/ _)" [90,70,65] 61)
  "_AnnPickIgnore"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_* \<acute>_ :\<in>/ _)" [90,70,65] 61)

no_syntax
  "_AnnCond1"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //IF _ /THEN _ /ELSE _ /FI"  [90,0,0,0] 61)
  "_AnnCond2"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //IF _ /THEN _ /FI"  [90,0,0] 61)
  "_AnnWhile"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //WHILE _ /INV _ //DO _//OD"  [90,0,0,0] 61)
  "_AnnAwait"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"
                    ("_ //AWAIT _ /THEN /_ /END"  [90,0,0] 61)
  "_AnnAtom"     :: "'a assn  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"   ("_//\<langle>_\<rangle>" [90,0] 61)
  "_AnnWait"     :: "'a assn \<Rightarrow> 'a bexp \<Rightarrow> 'a ann_com"   ("_//WAIT _ END" [90,0] 61)

  "_AnnCond1Ig"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_* //IF _ /THEN _ /ELSE _ /FI"  [90,0,0,0] 61)
  "_AnnCond2Ig"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_* //IF _ /THEN _ /FI"  [90,0,0] 61)
  "_AnnWhileIg"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_* //WHILE _ /INV _ //DO _//OD"  [90,0,0,0] 61)
  "_AnnWhileIg'"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //WHILE _ /INV _* //DO _//OD"  [90,0,0,0] 61)
  "_AnnWhileIg''"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_* //WHILE _ /INV _* //DO _//OD"  [90,0,0,0] 61)
  "_AnnAwaitIg"  :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"
                    ("_* //AWAIT _ /THEN /_ /END"  [90,0,0] 61)
  "_AnnAtomIg"   :: "'a assn  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"   ("_*//\<langle>_\<rangle>" [90,0] 61)
  "_AnnWaitIg"   :: "'a assn \<Rightarrow> 'a bexp \<Rightarrow> 'a ann_com"   ("_*//WAIT _ END" [90,0] 61)

  "_Cond"        :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"
                                  ("(0IF _/ THEN _/ ELSE _/ FI)" [0, 0, 0] 61)
  "_Cond2"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"   ("IF _ THEN _ FI" [0,0] 56)
  "_While_inv"   :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _/ INV _ //DO _ /OD)"  [0, 0, 0] 61)
  "_While"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _ //DO _ /OD)"  [0, 0] 61)

no_syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" [57] 56)
  "_prg" :: "['a, 'a] \<Rightarrow> prgs"        ("_//_" [60, 90] 57)
  "_prgs" :: "['a, 'a, prgs] \<Rightarrow> prgs"  ("_//_//\<parallel>//_" [60,90,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"
                  ("SCHEME [_ \<le> _ < _] _// _" [0,0,0,60, 90] 57)

end