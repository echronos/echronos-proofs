The files in this directory are based on the existing files from the
Isabelle/HOL code-base. They have been modified in the following ways:
* Added non-determinism to OG commands.
* Changed the oghoare tactic in a variety of ways.
    * Improved performance through the use of memoization.
    * Improved performance by removing redundant subgoals.
    * Added the ability to use cached results. This is unsafe and is
      intended for use during development of proofs.
* Added a feature for assuming invariants and modified the soundness
  proof accordingly.
* Added the experimental unsafe cruft feature. This makes it possible
  to temporarily mark annotations so that their corresponding
  interference-freedom conditions are not generated. The intention of
  this feature is to allow multiple people to work on the same proof
  at the same time.