/-
Part D: Polyregular functions, from *Transducers* (M. Bojańczyk).

This file collects the contents of the directory `RequestProject/PartD`: the numbered results of
Section *Polyregular functions* and of Section *Pebble transducers* (`Statements.lean`), together
with the results of Section *Pebble transducers* that are stated in terms of the string
representation of configurations and of child configuration graphs, and are therefore proved after
`Statements.lean`: Lemma `lem:reachability-pebble-automaton` and Claim
`claim:reachability-basic-run` (`PebReach.lean`), Claim
`claim:from-child-configuration-graph-to-children` (`ChildGraphFor.lean`) and Claim
`claim:from-configuration-to-child-configuration-graph` together with Lemma
`lem:children-of-configuration-in-pebble-run` (`CGFor.lean`), and a machine for which the
hypotheses of the last two are satisfied (`ChildExample.lean`), and the undecidability results of
Section *A functional programming language*: Lemma `lem:tiling` and Theorem
`thm:undecidability-higher-order` (`TilingUndec.lean`), and the results of subsection *Simon trees* of
Section *Evaluation*: Theorem `thm:monoids-equal-automata` and Lemma `lem:semigroup-is-group`
(`MonoidAut.lean`), the Factorisation Forest Theorem `thm:factorisation-forest` with the lemmas of
its proof (`FactForest.lean`), Lemma `lem:factorisation-forest-evaluation` (`SimonEval.lean`),
Lemma `lem:factorisation-forest-rational` (`SimonRat.lean`), and, from subsection *The evaluation
algorithm*, Claim `claim:mso-formula-recognised-by-homomorphism` (`MSOProfile.lean`). -/
import RequestProject.PartD.Statements
import RequestProject.PartD.PebReach
import RequestProject.PartD.ChildGraphFor
import RequestProject.PartD.CGFor
import RequestProject.PartD.ChildExample
import RequestProject.PartD.TilingUndec
import RequestProject.PartD.FactForest
import RequestProject.PartD.SimonEval
import RequestProject.PartD.SimonRat
import RequestProject.PartD.MSOProfile
