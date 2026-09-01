/-
The decision procedure of Exercise `exer:rational-injectivity-decidable` of the
chapter on rational functions (`rational-functions.tex`) of *Transducers*
(M. Bojańczyk).
-/
import RequestProject.PartB.RatEqDec

/-!
# Injectivity of a rational function is decidable

Exercise `exer:rational-injectivity-decidable` asks for a decision procedure
for injectivity of a rational function.  The solution of the book has three
steps.

1. The inverse relation of `f` is rational; it is made total by sending the
   strings outside the range of `f` to a default value, and the Uniformisation
   Lemma `lem:uniformisation` produces a rational function `g` inside it, so
   that `f (g v) = v` for every `v` in the range of `f`.
2. `f` is injective if and only if `g` inverts it on the other side as well,
   that is if and only if `g ∘ f` is the identity.
3. Theorem `thm:equivalence-rational-functions` decides whether `g ∘ f` is the
   identity.

Step 1 is proved semantically in `RequestProject/Exercises/RatInjective.lean`
(`Transducers.Exercises.exists_rationalFun_inverse_of_injective`), and step 2 is
`Transducers.Exercises.rationalFun_injective_iff_exists_inverse` there.  This
file carries out the decision procedure itself, in the code-based setting that
the project uses for all its decidability statements (`Transducers.RelCode`,
`Transducers.DecidableUnderPromise`).

Two things are needed for that.

* The *identity code* `Transducers.Exercises.idCode`, which describes the
  identity function on the alphabet of a given code.  It is built and its
  semantics proved here in full.
* An effective form of step 1: from a code of `f` one can *compute* a code of
  `g ∘ f`.  The project has the Uniformisation Lemma as a statement about
  functions only, not as a construction on codes, so this is taken as the
  explicit hypothesis `Transducers.Exercises.EffectiveRationalSection`.

Given these, the equivalence test of Theorem `thm:equivalence-rational-functions`
(`Transducers.rationalFun_equivalence_decidable_aux`, itself proved outright) decides
injectivity: this is
`Transducers.Exercises.rationalFun_injectivity_decidable`.  The mathematical
content of step 2 is *not* assumed; it is proved here again, at the level of
codes, as `Transducers.Exercises.codeInjective_iff_section_comp_id`.
-/

namespace Transducers.Exercises

open Transducers

/-! ## The identity code -/

/-- The transitions of the identity code of `c`: one loop for every letter of the alphabet of
`c`, which copies that letter to the output. -/
def idTrans (c : RelCode) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  (codeAlphabet c).map (fun a => (0, [a], [a], 0))

/-- The code of the identity function on the alphabet of `c`. -/
def idCode (c : RelCode) : RelCode := (idTrans c, ([0], [0]))

lemma mem_idTrans {c : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ idTrans c ↔ ∃ a ∈ codeAlphabet c, t = (0, [a], [a], 0) := by
  simp [idTrans, eq_comm]

lemma codeAlphabet_idCode (c : RelCode) : codeAlphabet (idCode c) = codeAlphabet c := by
  have h : ∀ l : List ℕ, l.flatMap (fun a => [a]) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  simp [codeAlphabet, idCode, idTrans, List.flatMap_map, h]

lemma relFrom_idCode (c : RelCode) {q p : ℕ} {w v : List ℕ}
    (h : (codeAut (idCode c)).relFrom q w v p) : q = p ∧ v = w ∧ CodeWord c w := by
  refine NFAO.relFrom_induction (M := codeAut (idCode c))
    (motive := fun q w v => q = p ∧ v = w ∧ CodeWord c w) ⟨rfl, rfl, by simp [CodeWord]⟩ ?_ h
  rintro q q' u x w v ht - ⟨hq', hv, hcw⟩
  have ht' : (q, u, x, q') ∈ idTrans c := ht
  obtain ⟨a, ha, hteq⟩ := mem_idTrans.1 ht'
  have h1 : q = 0 := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) hteq
  have h2 : u = [a] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) hteq
  have h3 : x = [a] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) hteq
  have h4 : q' = 0 := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) hteq
  subst h2; subst h3; subst hv
  refine ⟨by omega, rfl, ?_⟩
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · rw [List.mem_singleton.1 hy]; exact ha
  · exact hcw y hy

lemma relFrom_idCode_self (c : RelCode) {w : List ℕ} (hw : CodeWord c w) :
    (codeAut (idCode c)).relFrom 0 w w 0 := by
  induction w with
  | nil => exact (codeAut (idCode c)).relFrom_nil 0
  | cons a w ih =>
      have ha : a ∈ codeAlphabet c := hw a (by simp)
      have ht : ((0 : ℕ), [a], [a], (0 : ℕ)) ∈ (codeAut (idCode c)).δ :=
        mem_idTrans.2 ⟨a, ha, rfl⟩
      have := NFAO.relFrom_step ht (ih (fun x hx => hw x (List.mem_cons_of_mem a hx)))
      simpa using this

/-- **The identity code computes the identity**: it relates a string over the alphabet of `c` to
itself, and relates nothing else. -/
lemma codeRel_idCode (c : RelCode) (w v : List ℕ) :
    codeRel (idCode c) w v ↔ v = w ∧ CodeWord c w := by
  constructor
  · intro h
    obtain ⟨q, -, p, -, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    obtain ⟨-, hv, hcw⟩ := relFrom_idCode c hrel
    exact ⟨hv, hcw⟩
  · rintro ⟨rfl, hcw⟩
    exact (NFAO.rel_iff_relFrom _ _ _).2 ⟨0, by simp [codeAut, idCode], 0,
      by simp [codeAut, idCode], relFrom_idCode_self c hcw⟩

lemma codeWord_of_codeWord_idCode {c : RelCode} {w : List ℕ} (hw : CodeWord (idCode c) w) :
    CodeWord c w := by
  intro x hx
  have := hw x hx
  rwa [codeAlphabet_idCode] at this

lemma codeFunctional_idCode (c : RelCode) : CodeFunctional (idCode c) := by
  intro w hw
  have hcw : CodeWord c w := codeWord_of_codeWord_idCode hw
  exact ⟨w, (codeRel_idCode c w w).2 ⟨rfl, hcw⟩, fun v hv => ((codeRel_idCode c w v).1 hv).1⟩

lemma primrec_codeAlphabet : Primrec codeAlphabet := by
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun z : RelCode × (ℕ × List ℕ × List ℕ × ℕ) => z.2.2.1
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma primrec_idCode : Primrec idCode := by
  refine Primrec.pair ?_ (Primrec.const ([0], [0]))
  refine Primrec.list_map primrec_codeAlphabet ?_
  show Primrec fun z : RelCode × ℕ => ((0 : ℕ), [z.2], [z.2], (0 : ℕ))
  exact Primrec.pair (Primrec.const 0)
    (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
        (Primrec.const 0)))

/-! ## Injectivity -/

/-- A code describes an injective function: two strings over its alphabet with a common output
are equal. -/
def CodeInjective (c : RelCode) : Prop :=
  ∀ w w', CodeWord c w → CodeWord c w' → ∀ v, codeRel c w v → codeRel c w' v → w = w'

/-- **Assumed: an effective form of the Uniformisation Lemma.**

There is a computable map `inv` which, given a code `c` of a rational function `f`, returns a
code of the function `g ∘ f`, where `g` is a rational *section* of `f`: a rational function which
picks, for every `v` in the range of `f`, some input string that `f` maps to `v`.

*Why this is true.*  This is step 1 of the solution of
`exer:rational-injectivity-decidable`, carried out on codes.  The inverse relation of `f` is
rational and its automaton is obtained from the automaton of `f` by swapping the input and the
output of every transition; the range of `f` is a regular language whose automaton is obtained
by projection, so the inverse relation can be made total by adding a default output outside the
range; the Uniformisation Lemma `lem:uniformisation` turns that total relation into a rational
function `g`, and its proof is a construction on automata; and the composition of two rational
functions is rational, again by a construction on automata.  Each of these steps transforms
automata in a primitive recursive way.

*Why it is not available here.*  The project proves each of these steps as a statement about
functions and relations — the Uniformisation Lemma is
`Transducers.exists_rationalFun_of_total_rel`, and step 1 in this form is
`Transducers.Exercises.exists_rationalFun_inverse_of_injective` — but not as a construction on
`RelCode`s with a `Computable` proof; the uniformisation in particular is proved by a choice
argument over the runs of the automaton.  Only the effectivity is assumed here: the semantic
content of the exercise is proved below. -/
def EffectiveRationalSection : Prop :=
  ∃ inv : RelCode → RelCode, Computable inv ∧
    ∀ c, CodeFunctional c →
      CodeFunctional (inv c) ∧
      ∃ g : List ℕ → List ℕ,
        (∀ w v, CodeWord c w → codeRel c w v → CodeWord c (g v) ∧ codeRel c (g v) v) ∧
        (∀ w u, codeRel (inv c) w u ↔ ∃ v, CodeWord c w ∧ codeRel c w v ∧ u = g v)

/-- **Step 2 of the solution**, at the level of codes: a code describes an injective function
exactly when composing it with a section of it gives the identity.  Nothing is assumed here about
how the section is obtained. -/
theorem codeInjective_iff_section_comp_id {c d : RelCode} {g : List ℕ → List ℕ}
    (hc : CodeFunctional c)
    (hsec : ∀ w v, CodeWord c w → codeRel c w v → CodeWord c (g v) ∧ codeRel c (g v) v)
    (hd : ∀ w u, codeRel d w u ↔ ∃ v, CodeWord c w ∧ codeRel c w v ∧ u = g v) :
    CodeInjective c ↔ codeRel d = codeRel (idCode c) := by
  constructor
  · intro hinj
    funext w u
    refine propext ⟨?_, ?_⟩
    · intro h
      obtain ⟨v, hw, hwv, rfl⟩ := (hd w u).1 h
      obtain ⟨hgw, hgv⟩ := hsec w v hw hwv
      exact (codeRel_idCode c w (g v)).2 ⟨hinj (g v) w hgw hw v hgv hwv, hw⟩
    · intro h
      obtain ⟨rfl, hw⟩ := (codeRel_idCode c w u).1 h
      obtain ⟨v, hwv, -⟩ := hc u hw
      obtain ⟨hgw, hgv⟩ := hsec u v hw hwv
      have : u = g v := hinj u (g v) hw hgw v hwv hgv
      exact (hd u u).2 ⟨v, hw, hwv, this⟩
  · intro heq w w' hw hw' v hwv hw'v
    have h1 : codeRel d w (g v) := (hd w (g v)).2 ⟨v, hw, hwv, rfl⟩
    have h2 : codeRel d w' (g v) := (hd w' (g v)).2 ⟨v, hw', hw'v, rfl⟩
    rw [heq] at h1 h2
    have e1 := ((codeRel_idCode c w (g v)).1 h1).1
    have e2 := ((codeRel_idCode c w' (g v)).1 h2).1
    rw [← e1, ← e2]

/-- **Exercise `exer:rational-injectivity-decidable`.**  Injectivity of a rational function is
decidable: under the promise that a code describes a function, one can decide whether that
function is injective.

The two hypotheses are the effectivity hypotheses of the project:
`Transducers.EffectiveWeightedEvalEq`, which is what makes the equivalence problem for rational
functions (Theorem `thm:equivalence-rational-functions`) decidable, and
`EffectiveRationalSection`, the effective form of the Uniformisation Lemma described above.  The
mathematics of the exercise — that injectivity is equivalent to the composition with a section
being the identity — is proved, not assumed. -/
theorem rationalFun_injectivity_decidable (hSec : EffectiveRationalSection) :
    DecidableUnderPromise CodeFunctional CodeInjective := by
  obtain ⟨Deq, hDcomp, hDeq⟩ := rationalFun_equivalence_decidable_aux
  obtain ⟨inv, hinvComp, hinv⟩ := hSec
  refine ⟨fun c => Deq (inv c, idCode c), ?_, ?_⟩
  · exact hDcomp.comp (Computable.pair hinvComp primrec_idCode.to_comp)
  · intro c hc
    obtain ⟨hfun, g, hsec, hd⟩ := hinv c hc
    rw [hDeq (inv c, idCode c) ⟨hfun, codeFunctional_idCode c⟩]
    exact (codeInjective_iff_section_comp_id hc hsec hd).symm

end Transducers.Exercises
