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
hypotheses of the last two are satisfied (`ChildExample.lean`). -/
import RequestProject.PartD.Statements
import RequestProject.PartD.PebReach
import RequestProject.PartD.ChildGraphFor
import RequestProject.PartD.CGFor
import RequestProject.PartD.ChildExample
