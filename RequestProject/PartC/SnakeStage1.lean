/-
**Stage 1 of the induction step of the book's snake lemma**: the rational
function that marks the record-breaking columns of a run and the pieces of the
record-breaker decomposition inside the blocks that they delimit.

This is the one remaining gap in Theorem C.2.9.  Everything else in the
induction step is proved:

* the decomposition of a halting run of width at most `K` into the pieces of the
  record-breaker decomposition is `TwoWay.runOut_eq_partsOut`
  (`RequestProject/PartC/SnakeParts.lean`);
* the identification of each piece with the whole run of a *window transducer*
  on a factor of the input, to which the induction hypothesis applies, is
  `TwoWay.exists_widthOut_excHalves`, `TwoWay.exists_widthOut_prog`
  (`RequestProject/PartC/SnakePieceIdent.lean`) and
  `TwoWay.exists_widthOut_finalProg_confined`
  (`RequestProject/PartC/SnakeFinalConf.lean`);
* the *block function*, which recomputes the pieces of one pair of neighbouring
  blocks from the annotated input, is regular (`TwoWay.isRegularFun_blockFun`),
  and the neighbouring-block map combinator applied to it computes the output of
  the run (`TwoWay.pairMap_blockFun_eq_runOut`), both in
  `RequestProject/PartC/SnakeBlock.lean`;
* **a correct marking of the input exists** for every nonempty input whose run
  halts and has width at most `K` (`TwoWay.exists_isSnakeMarking`,
  `RequestProject/PartC/SnakeData.lean`): the blocks are cut at the
  record-breaking columns and every piece is confined to the pair of blocks that
  carries it.  This is the mathematical content of the book's first stage.

What is stated here, and left open, is the *machine-theoretic* content of that
stage: *"we mark the record-breakers, i.e. we compute the string
`w₀ # w₁ # ⋯ # wₙ`, where `wᵢ` is the part of the input string between the
record-breakers `xᵢ₋₁` and `xᵢ`.  This stage can be implemented by a rational
function, since a nondeterministic automaton with output can guess the
record-breakers, and then check that they satisfy the conditions in the
definition."*

It is stated in exactly that shape (`TwoWay.exists_regular_snakeLang`): what has
to be produced is the language of the *checking* automaton, that is, a **regular
language of correctly annotated inputs** which contains an annotation of every
input.  Guessing and checking is then Nivat's construction
(`Transducers.isRationalRel_of_regular_nivat`,
`RequestProject/PartB/GuessCheck.lean`): a regular language of annotations, read
through the homomorphism that erases the annotation and written through the
homomorphism that produces the marked string, is a rational relation
(`TwoWay.exists_rational_snakeRel`).  Since a total rational relation contains
the graph of a rational function (`Transducers.exists_rationalFun_of_total_rel`,
Lemma B.2.5), this gives the regular function that the induction step needs
(`TwoWay.exists_snakeMarking`), and no functionality of the guessing has to be
proved.

The annotation is kept *letter to letter*: an annotated letter is a letter of
the input together with a `TwoWay.SnakeDatum`, and the separators are inserted
afterwards by the homomorphism `TwoWay.snakeOutLet`.  Keeping the annotation
length-preserving means that a position of the annotated string is a position of
the input, so that a condition on the annotation can be checked against the
regular languages of *marked inputs* of `RequestProject/PartC/RunMark.lean` and
`RequestProject/PartC/TwoWayOrder.lean`, which is how the checking automaton is
meant to be built.

The annotation has to carry a little more than the separators, because the
pieces of a pair of neighbouring blocks have to be recovered from that pair
alone: every letter carries, for each of the `2K+1` piece slots of a pair and
for each of the two sides of the separator, the bit saying whether it belongs to
the window of that piece and the parameters of the window transducer computing
it (`TwoWay.SnakeLet`, `TwoWay.slot`).  That is exactly what
`TwoWay.IsSnakeMarking` demands, and what `TwoWay.exists_isSnakeMarking`
provides.

Two side conditions of the statements below deserve a comment.

* Only a *regular* annotation is asked for, not a rational one: the annotation
  is composed with the regular function `pairMap (blockFun …)`, so regularity is
  all that the assembly of the induction step uses.
* The empty input is excluded.  On the empty input the annotation has no letters
  at all, so it cannot carry the parameters of the pieces, while the run may
  perfectly well produce a nonempty output; the induction step therefore treats
  the empty input separately, by a case distinction over the regular language
  `{[]}` (`Transducers.boundedWidth_isRegular_step`).
-/
import RequestProject.PartC.SnakeData
import RequestProject.PartB.UniformFun
import RequestProject.PartB.GuessCheck

namespace Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-- The inputs on which the marking of stage 1 has to be correct: the nonempty
inputs whose run halts and has width at most `K`. -/
def GoodInput (M : TwoWay A B Q) (K : ℕ) (w : List A) : Prop :=
  w ≠ [] ∧ (∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K

/-- **What the marking of stage 1 has to satisfy**: on the inputs on which the
induction step uses it, the annotation is a correct marking of the
record-breaker decomposition; on all other inputs it must produce no pair of
neighbouring blocks at all, so that the block function contributes nothing. -/
def SnakeRel (M : TwoWay A B Q) (K : ℕ) (w : List A)
    (v : List (Option (SnakeLet A Q (2 * (2 * K + 1))))) : Prop :=
  (GoodInput M K w → IsSnakeMarking M K w v) ∧ (¬ GoodInput M K w → pairBlocks v = [])

/-- A word without separators has no pair of neighbouring blocks. -/
lemma pairBlocks_map_some {C : Type} (v : List C) : pairBlocks (v.map some) = [] := by
  rw [pairBlocks, show (v.map some : List (Option C)) = blockStr [v] from
    (blockStr_singleton v).symm, splitSep_blockStr [v] (by simp), pairsList_singleton]

/-- **A value of the marking always exists**: on a good input by
`TwoWay.exists_isSnakeMarking`, and on every other input because the annotation
without separators is allowed there. -/
theorem exists_snakeRel (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) (w : List A) :
    ∃ v, SnakeRel M K w v := by
  classical
  by_cases hgood : GoodInput M K w
  · obtain ⟨hw, ⟨T, hT⟩, hwidth⟩ := hgood
    obtain ⟨a, b, p, hmark⟩ := exists_isSnakeMarking hw hK hT hwidth
    exact ⟨_, fun _ => hmark, fun hcon => absurd ⟨hw, ⟨T, hT⟩, hwidth⟩ hcon⟩
  · refine ⟨(w.map (fun c => (c, fun _ => (false, default)))).map some,
      fun hcon => absurd hcon hgood, fun _ => pairBlocks_map_some _⟩

/-! ## The letter-to-letter annotation of stage 1 -/

/-- The datum that the annotation of stage 1 attaches to a letter of the input:
the bit saying that a block boundary precedes that letter, the bit saying that a
block boundary follows it -- which is used only at the last letter, the block
boundaries strictly inside the input being recorded by the first bit -- and the
data of the `2 * (2K+1)` piece slots. -/
abbrev SnakeDatum (A Q : Type) (K : ℕ) :=
  Bool × Bool × (Fin (2 * (2 * K + 1)) → Bool × PieceParam A Q)

/-- Erasing the annotation of stage 1: an annotated letter stands for the letter
that it carries. -/
def snakeIn (K : ℕ) : A × SnakeDatum A Q K → List A := fun c => [c.1]

/-- Inserting the separators: an annotated letter produces the letter that it
carries, preceded and followed by a separator as its two bits prescribe. -/
def snakeOutLet (K : ℕ) :
    A × SnakeDatum A Q K → List (Option (SnakeLet A Q (2 * (2 * K + 1)))) :=
  fun c => (if c.2.1 then [none] else []) ++ some (c.1, c.2.2.2) ::
    (if c.2.2.1 then [none] else [])

lemma homOf_snakeIn (K : ℕ) (u : List (A × SnakeDatum A Q K)) :
    homOf (snakeIn K) u = u.map Prod.fst := by
  induction u with
  | nil => rfl
  | cons c u ih =>
      rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, snakeIn,
        List.singleton_append, List.map_cons]

/-- **Stage 1 of the induction step of the snake lemma** (still open), in the
shape in which the book states it: the marking is *guessed* by a
nondeterministic automaton with output and *checked*, so that what has to be
produced is the language of the checking automaton -- a regular language of
correctly annotated inputs which contains an annotation of every input -- and
not a function.

The intended proof is the book's.  The conditions to be checked are conditions
on the run of `M` at, and between, the marked positions, and each of them is a
regular property of the input marked at one or at two positions:

* that the run visits a given cut in a given state is
  `TwoWay.visitLang_isRegular` (`RequestProject/PartC/TwoWayVisit.lean`);
* that the run reaches one marked configuration before another one -- the two
  configurations being at two *different* marked positions -- is
  `RunMark.isRegular_beforeLang` (`RequestProject/PartC/RunMark.lean`), which is
  exactly what the definition of the record-breaking columns compares: `xᵢ₊₁` is
  the first column whose first visit comes after the last visit to `xᵢ`.

Since these are properties of marked inputs, and the annotation here is letter
to letter, they become mso formulas with one and with two free variables by
Theorem C.4.1 in the form of `MarkLogic.exists_form_of_regular` and of
`MarkLogic2`; the conditions on the annotation are first-order combinations of
them -- each condition relates a marked position to the *next* marked one, and
the marks are letters of the annotated alphabet -- so the language of correct
annotations is mso-definable, hence regular by Theorem C.4.1
(`Transducers.isRegular_of_msoDefinable`).

That a correct marking of every input *exists*, which is the mathematical half
of the stage, is `TwoWay.exists_snakeRel`, and rests on
`TwoWay.exists_isSnakeMarking`; what is open here is only that the correct
markings can be *recognised*. -/
theorem exists_regular_snakeLang [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ L : Language (A × SnakeDatum A Q K), L.IsRegular ∧
      (∀ u ∈ L, SnakeRel M K (homOf (snakeIn K) u) (homOf (snakeOutLet K) u)) ∧
      (∀ w : List A, ∃ u ∈ L, homOf (snakeIn K) u = w) := by
  sorry

/-- **Stage 1, as a rational relation.**  Guessing an annotation, checking it
against the regular language of `TwoWay.exists_regular_snakeLang` and inserting
the separators is a total rational relation all of whose values are correct
markings (Nivat's construction, `Transducers.isRationalRel_of_regular_nivat`). -/
theorem exists_rational_snakeRel [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ R : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1)))) → Prop,
      IsRationalRel R ∧ (∀ w, ∃ v, R w v) ∧ (∀ w v, R w v → SnakeRel M K w v) := by
  classical
  obtain ⟨L, hreg, hsound, hcover⟩ := exists_regular_snakeLang M hK
  refine ⟨fun w v => ∃ u ∈ L, homOf (snakeIn K) u = w ∧ homOf (snakeOutLet K) u = v,
    isRationalRel_of_regular_nivat _ _ hreg, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu, hup⟩ := hcover w
    exact ⟨homOf (snakeOutLet K) u, u, hu, hup, rfl⟩
  · rintro w v ⟨u, hu, rfl, rfl⟩
    exact hsound u hu

/-- **The marking of stage 1 is computed by a regular function**: the guessing
relation of `TwoWay.exists_rational_snakeRel` is total and rational, hence it
contains the graph of a rational -- so regular -- function (Lemma B.2.5). -/
theorem exists_snakeMarking [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ ann : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1)))),
      IsRegularFun ann ∧ ∀ w : List A, SnakeRel M K w (ann w) := by
  classical
  obtain ⟨R, hRat, hTot, hSound⟩ := exists_rational_snakeRel M hK
  obtain ⟨f, hf, hfR⟩ := exists_rationalFun_of_total_rel hRat hTot
  exact ⟨f, IsRegularFun.of_rational hf, fun w => hSound w (f w) (hfR w)⟩

/-- **The width-`K` output function is the neighbouring-block map combinator
applied to the block function**, on the annotation of stage 1, for every
nonempty input. -/
theorem widthOut_eq_pairMap [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) (K : ℕ)
    {ann : List A → List (Option (SnakeLet A Q (2 * (2 * K + 1))))}
    (hann : ∀ w : List A, SnakeRel M K w (ann w))
    {w : List A} (hw : w ≠ []) :
    widthOut M K w = pairMap (blockFun M (K - 1) (2 * K + 1)) (ann w) := by
  classical
  by_cases hgood : GoodInput M K w
  · obtain ⟨-, ⟨T, hT⟩, hwidth⟩ := hgood
    rw [widthOut, if_pos hwidth,
      pairMap_blockFun_eq_runOut ((hann w).1 ⟨hw, ⟨T, hT⟩, hwidth⟩) hT hwidth]
  · have hnil : pairBlocks (ann w) = [] := (hann w).2 hgood
    rw [pairMap, hnil]
    simp only [List.map_nil, List.flatten_nil]
    by_cases hwidth : WidthLe M w K
    · have hhalt : ¬ ∃ T, cfgAt M w T = some Cfg.halt := fun h => hgood ⟨hw, h, hwidth⟩
      rw [widthOut, if_pos hwidth, runOut, dif_neg hhalt]
    · rw [widthOut, if_neg hwidth]

end TwoWay

end Transducers
