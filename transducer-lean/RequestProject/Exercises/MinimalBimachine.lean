/-
Exercise `nolabel:exer-minimal-bimachine-lexicographic` of the chapter on machine
independent characterisations (`myhill-nerode.tex`) of *Transducers*
(M. Bojańczyk).
-/
import RequestProject.PartB.RatIndex

/-!
# The suffix automaton of a minimal bimachine is unique

Exercise `nolabel:exer-minimal-bimachine-lexicographic` orders bimachines by the number
of states of the *suffix* automaton alone, and asks to show that the suffix
automaton of a minimal bimachine is unique up to isomorphism.

The solution follows the proof of Theorem
`thm:machine-independent-rational-functions`, whose equivalence relation `∼` is
`Transducers.BoundedVarRel` in this project: two suffixes are equivalent when
the outputs of their common left extensions stay at a bounded left distance.
The solution has two halves.

* *Every suffix automaton refines `∼`*, so it has at least as many states as
  `∼` has classes.  This is proved here, from
  `Transducers.BimachIndex.boundedVarRel_of_sfx_eq`: the map that sends a state
  of the suffix automaton to the class of the suffixes that reach it is
  well defined and, on a machine all of whose suffix states are reachable,
  surjective (`Transducers.Exercises.card_classSet_le`).
* *The bound is attained*: some bimachine has one suffix state per class.  This
  is what the second paragraph of the solution claims, reading the first of the
  two steps of the proof of Theorem
  `thm:machine-independent-rational-functions` as a suffix automaton, and it is
  the explicit hypothesis `Transducers.Exercises.CanonicalSuffixBimachineExists`.
  **That half is false**, and this file now proves it false
  (`Transducers.Exercises.not_canonicalSuffixBimachineExists`).  The counterexample is the
  function `w ↦ [w.length is even]` over a one letter alphabet: all suffixes are
  `∼`-equivalent, so `∼` has a single class, but a bimachine with a single
  suffix state computes a function whose output on a string is a prefix of its
  output on any one letter extension, which this function is not.  Two suffix
  states are needed, to tell the empty suffix from the others; that is exactly
  the end-of-input flush of the subsequential transducer of the second step of
  the proof of Theorem `thm:machine-independent-rational-functions`, which a
  suffix automaton with one state per `∼`-class cannot trigger.

Everything else — that a suffix automaton with exactly that many states *is* the
automaton of `∼`-classes, initial state and transitions included, and hence that
any two bimachines attaining the bound have isomorphic suffix automata — is
proved: `Transducers.Exercises.suffix_automaton_unique` is the unconditional
statement.  Since the bound is not always attained, this does not settle the
exercise, and the exercise itself — `nolabel:exer-minimal-bimachine-lexicographic` —
has since been **withdrawn from the book by the author**, so nothing here is
stated conditionally any more.  What would have been missing for an
unconditional proof is a Myhill–Nerode theory of bimachines proper: a
canonical right-to-left congruence, finer than `∼`, that records how much of the
output is still pending, and which every suffix automaton refines and some
bimachine realises.  The counterexample below shows that `∼` itself is not that
congruence.

As in the book, all states of the suffix automaton are assumed reachable
(`Transducers.Exercises.SuffixReachable`); unreachable states can be removed
without changing the function, and without that assumption the statement is
false, since a minimal machine could carry a useless extra state.
-/

namespace Transducers.Exercises

open Transducers

variable {A B : Type}

/-! ## The classes of the equivalence relation -/

/-- The `∼`-class of a suffix: the strings whose outputs stay at bounded left distance from
those of `w` under all common left extensions. -/
def clsOf (f : List A → List B) (w : List A) : Set (List A) := {w' | BoundedVarRel f w w'}

/-- The set of `∼`-classes.  This is the set whose finiteness is the easy half of Theorem
`thm:machine-independent-rational-functions` (`Transducers.finiteIndex_of_isRationalFun`). -/
def ClassSet (f : List A → List B) : Set (Set (List A)) := {C | ∃ w, C = clsOf f w}

lemma clsOf_eq_iff {f : List A → List B} {w w' : List A} :
    clsOf f w = clsOf f w' ↔ BoundedVarRel f w w' := by
  constructor
  · intro h
    have : w' ∈ clsOf f w := by
      rw [h]
      exact BoundedVarRel.refl w'
    exact this
  · intro h
    ext u
    exact ⟨fun hu => (h.symm).trans hu, fun hu => h.trans hu⟩

lemma clsOf_mem (f : List A → List B) (w : List A) : clsOf f w ∈ ClassSet f := ⟨w, rfl⟩

/-! ## The map from suffix states to classes -/

variable {P S : Type}

/-- All states of the suffix automaton are reachable. -/
def SuffixReachable (M : Bimachine A B P S) : Prop :=
  ∀ s : S, ∃ w : List A, BimachIndex.sfx M w = s

/-- A suffix that reaches a given state of the suffix automaton. -/
noncomputable def sfxRep {M : Bimachine A B P S} (h : SuffixReachable M) (s : S) : List A :=
  (h s).choose

lemma sfx_sfxRep {M : Bimachine A B P S} (h : SuffixReachable M) (s : S) :
    BimachIndex.sfx M (sfxRep h s) = s := (h s).choose_spec

/-- The class of the suffixes that reach a state of the suffix automaton. -/
noncomputable def sfxCls (f : List A → List B) {M : Bimachine A B P S} (h : SuffixReachable M)
    (s : S) : Set (List A) := clsOf f (sfxRep h s)

lemma sfxCls_sfx [Finite P] {f : List A → List B} {M : Bimachine A B P S} (hf : M.eval = f)
    (h : SuffixReachable M) (w : List A) :
    sfxCls f h (BimachIndex.sfx M w) = clsOf f w := by
  have hs : BimachIndex.sfx M (sfxRep h (BimachIndex.sfx M w)) = BimachIndex.sfx M w :=
    sfx_sfxRep h _
  have hb : BoundedVarRel M.eval (sfxRep h (BimachIndex.sfx M w)) w :=
    BimachIndex.boundedVarRel_of_sfx_eq M hs
  rw [hf] at hb
  exact clsOf_eq_iff.2 hb

/-- Reading one more letter of the suffix, from right to left, prepends that letter. -/
lemma sfx_cons (M : Bimachine A B P S) (a : A) (w : List A) :
    BimachIndex.sfx M (a :: w) = M.suffixStep (BimachIndex.sfx M w) a := by
  simp only [BimachIndex.sfx, List.reverse_cons]
  rw [BimachIndex.strTrans_append]
  rfl

/-- The map from the states of the suffix automaton to the `∼`-classes. -/
noncomputable def sfxToClass (f : List A → List B) {M : Bimachine A B P S}
    (h : SuffixReachable M) (s : S) : ClassSet f := ⟨sfxCls f h s, clsOf_mem f _⟩

lemma sfxToClass_surjective [Finite P] {f : List A → List B} {M : Bimachine A B P S}
    (hf : M.eval = f) (h : SuffixReachable M) : Function.Surjective (sfxToClass f h) := by
  rintro ⟨C, w, rfl⟩
  exact ⟨BimachIndex.sfx M w, Subtype.ext (sfxCls_sfx hf h w)⟩

/-- **The first half of the solution**: the suffix automaton of a bimachine refines `∼`, so it
has at least as many states as `∼` has classes. -/
theorem card_classSet_le [Finite P] [Finite S] {f : List A → List B} {M : Bimachine A B P S}
    (hf : M.eval = f) (h : SuffixReachable M) : Nat.card (ClassSet f) ≤ Nat.card S :=
  Nat.card_le_card_of_surjective _ (sfxToClass_surjective hf h)

/-! ## The canonical suffix automaton -/

/-- A suffix that represents a `∼`-class. -/
noncomputable def clsRep (f : List A → List B) (C : ClassSet f) : List A := C.2.choose

lemma clsRep_spec (f : List A → List B) (C : ClassSet f) : C.1 = clsOf f (clsRep f C) :=
  C.2.choose_spec

/-- The transition of the canonical suffix automaton: reading a letter from right to left
prepends it to the suffixes of the class.  This is well defined because `∼` is a left
congruence. -/
noncomputable def clsStep (f : List A → List B) (C : ClassSet f) (a : A) : ClassSet f :=
  ⟨clsOf f (a :: clsRep f C), clsOf_mem f _⟩

lemma clsStep_apply {f : List A → List B} {C : ClassSet f} {w : List A} (hw : C.1 = clsOf f w)
    (a : A) : clsStep f C a = ⟨clsOf f (a :: w), clsOf_mem f _⟩ := by
  have h : BoundedVarRel f (clsRep f C) w := clsOf_eq_iff.1 ((clsRep_spec f C).symm.trans hw)
  exact Subtype.ext (clsOf_eq_iff.2 (h.cons a))

/-- The initial state of the canonical suffix automaton: the class of the empty suffix. -/
noncomputable def clsInit (f : List A → List B) : ClassSet f := ⟨clsOf f [], clsOf_mem f _⟩

lemma sfxToClass_init [Finite P] {f : List A → List B} {M : Bimachine A B P S} (hf : M.eval = f)
    (h : SuffixReachable M) : sfxToClass f h M.suffixInit = clsInit f := by
  have h0 : BimachIndex.sfx M [] = M.suffixInit := rfl
  exact Subtype.ext (by rw [sfxToClass, ← h0]; exact sfxCls_sfx hf h [])

lemma sfxToClass_step [Finite P] {f : List A → List B} {M : Bimachine A B P S} (hf : M.eval = f)
    (h : SuffixReachable M) (s : S) (a : A) :
    sfxToClass f h (M.suffixStep s a) = clsStep f (sfxToClass f h s) a := by
  have hs : BimachIndex.sfx M (sfxRep h s) = s := sfx_sfxRep h s
  have h1 : sfxToClass f h (M.suffixStep s a)
      = ⟨clsOf f (a :: sfxRep h s), clsOf_mem f _⟩ := by
    refine Subtype.ext ?_
    have : M.suffixStep s a = BimachIndex.sfx M (a :: sfxRep h s) := by
      rw [sfx_cons, hs]
    rw [sfxToClass, this]
    exact sfxCls_sfx hf h _
  rw [h1, clsStep_apply (C := sfxToClass f h s) (w := sfxRep h s) rfl a]

/-! ## Uniqueness -/

/-- Isomorphism of the suffix automata of two bimachines: a bijection of their state sets that
matches the initial states and the transitions. -/
def SuffixIso {P₁ S₁ P₂ S₂ : Type} (M₁ : Bimachine A B P₁ S₁) (M₂ : Bimachine A B P₂ S₂) :
    Prop :=
  ∃ e : S₁ ≃ S₂, e M₁.suffixInit = M₂.suffixInit ∧
    ∀ s a, e (M₁.suffixStep s a) = M₂.suffixStep (e s) a

/-- A bimachine whose suffix automaton has one state per `∼`-class *is* the automaton of
`∼`-classes: the map to classes is a bijection matching the initial states and the
transitions. -/
lemma sfxToClass_bijective [Finite P] [Finite S] {f : List A → List B} {M : Bimachine A B P S}
    (hf : M.eval = f) (h : SuffixReachable M) (hcard : Nat.card S = Nat.card (ClassSet f)) :
    Function.Bijective (sfxToClass f h) :=
  (Nat.bijective_iff_surjective_and_card _).2 ⟨sfxToClass_surjective hf h, hcard⟩

/-- **The suffix automaton with the least possible number of states is unique up to
isomorphism.**  Two bimachines for the same function, both with all suffix states reachable and
both with one suffix state per `∼`-class, have isomorphic suffix automata. -/
theorem suffix_automaton_unique {P₁ S₁ P₂ S₂ : Type} [Finite P₁] [Finite S₁] [Finite P₂]
    [Finite S₂] {f : List A → List B} {M₁ : Bimachine A B P₁ S₁} {M₂ : Bimachine A B P₂ S₂}
    (hf₁ : M₁.eval = f) (hf₂ : M₂.eval = f)
    (h₁ : SuffixReachable M₁) (h₂ : SuffixReachable M₂)
    (hc₁ : Nat.card S₁ = Nat.card (ClassSet f)) (hc₂ : Nat.card S₂ = Nat.card (ClassSet f)) :
    SuffixIso M₁ M₂ := by
  set e₁ := Equiv.ofBijective _ (sfxToClass_bijective hf₁ h₁ hc₁) with he₁
  set e₂ := Equiv.ofBijective _ (sfxToClass_bijective hf₂ h₂ hc₂) with he₂
  refine ⟨e₁.trans e₂.symm, ?_, ?_⟩
  · have h : e₁ M₁.suffixInit = e₂ M₂.suffixInit := by
      rw [he₁, he₂]
      show sfxToClass f h₁ M₁.suffixInit = sfxToClass f h₂ M₂.suffixInit
      rw [sfxToClass_init hf₁ h₁, sfxToClass_init hf₂ h₂]
    simp [h]
  · intro s a
    have h : e₁ (M₁.suffixStep s a) = e₂ (M₂.suffixStep (e₂.symm (e₁ s)) a) := by
      rw [he₁, he₂]
      show sfxToClass f h₁ (M₁.suffixStep s a) = sfxToClass f h₂ (M₂.suffixStep _ a)
      rw [sfxToClass_step hf₁ h₁, sfxToClass_step hf₂ h₂]
      congr 1
      show (e₁ : S₁ → ClassSet f) s = e₂ (e₂.symm (e₁ s))
      rw [Equiv.apply_symm_apply]
    calc (e₁.trans e₂.symm) (M₁.suffixStep s a) = e₂.symm (e₁ (M₁.suffixStep s a)) := rfl
      _ = e₂.symm (e₂ (M₂.suffixStep (e₂.symm (e₁ s)) a)) := by rw [h]
      _ = M₂.suffixStep ((e₁.trans e₂.symm) s) a := by rw [Equiv.symm_apply_apply]; rfl

/-! ## The exercise -/

/-- A bimachine is minimal for the order of `nolabel:exer-minimal-bimachine-lexicographic`: no bimachine
computing the same function, with all suffix states reachable, has a smaller suffix automaton. -/
def MinimalSuffixBimachine {P S : Type} (f : List A → List B) (M : Bimachine A B P S) : Prop :=
  M.eval = f ∧ SuffixReachable M ∧
    ∀ (P' S' : Type), Finite P' → Finite S' → ∀ M' : Bimachine A B P' S', M'.eval = f →
      SuffixReachable M' → Nat.card S ≤ Nat.card S'

/-- **The bound of the first half of the solution is attained** — the second paragraph of the
solution of `nolabel:exer-minimal-bimachine-lexicographic`: for every function computed by a bimachine
there is a bimachine, with all suffix states reachable, whose suffix automaton has exactly one
state per `∼`-class.

**This statement is false**, and `Transducers.Exercises.not_canonicalSuffixBimachineExists`
proves it false.  Nothing in the project assumes it: it is kept only so that its refutation has
something to refute, since that refutation is the reason the exercise was withdrawn.

*Where the solution of the book breaks down.*  The proof of Theorem
`thm:machine-independent-rational-functions` decomposes the function into a right-to-left
automaton that annotates every position with the `∼`-class of the suffix after it, followed by a
*subsequential* function on the annotated strings.  Reading the first step as the suffix
automaton of a bimachine and the second step as its prefix automaton does give the state of the
prefix automaton correctly — the annotations can be recovered from the class of the remaining
suffix, `∼` being a left congruence.  What it does not give is the *end of input*: a
subsequential transducer flushes a final output when the input ends, and a bimachine can only
produce that flush at the gap whose suffix state says that the remaining suffix is empty.  The
automaton of `∼`-classes need not say that: for the function of the counterexample below, all
suffixes are `∼`-equivalent, and the flush would be produced at every gap.

So the suffix automaton of a minimal bimachine is in general strictly finer than the automaton
of `∼`-classes, and the exercise needs a canonical congruence that `∼` is not. -/
def CanonicalSuffixBimachineExists (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ SuffixReachable M ∧ Nat.card S = Nat.card (ClassSet f)

/-- A minimal bimachine has exactly one suffix state per `∼`-class, *if* the bound is attained.
The hypothesis `hattain` is false in general — see `not_canonicalSuffixBimachineExists`. -/
lemma card_eq_of_minimal [Finite P] [Finite S] {f : List A → List B} {M : Bimachine A B P S}
    (hattain : CanonicalSuffixBimachineExists f) (hmin : MinimalSuffixBimachine f M) :
    Nat.card S = Nat.card (ClassSet f) := by
  obtain ⟨hf, hreach, hle⟩ := hmin
  obtain ⟨P₀, S₀, hP₀, hS₀, M₀, hf₀, hreach₀, hcard₀⟩ := hattain
  refine le_antisymm ?_ (card_classSet_le hf hreach)
  exact hcard₀ ▸ hle P₀ S₀ hP₀ hS₀ M₀ hf₀ hreach₀

/-! ### The exercise this file was written for, and why it is gone

Exercise `nolabel:exer-minimal-bimachine-lexicographic` asked to show that if bimachines are ordered by
the number of states of the suffix automaton alone, then the suffix automaton of a minimal
bimachine is unique up to isomorphism.  It was formalised here as

    theorem minimal_bimachine_lexicographic
        (hattain : CanonicalSuffixBimachineExists f)
        (hmin₁ : MinimalSuffixBimachine f M₁) (hmin₂ : MinimalSuffixBimachine f M₂) :
      SuffixIso M₁ M₂

and that is where the matter rested: true as stated, but saying nothing about any function for
which the bound is not attained -- and `not_canonicalSuffixBimachineExists` below shows there are
such functions, so the hypothesis is false in general and the theorem proved no exercise.  The
author has since **withdrawn the exercise from the book**, and the conditional statement is
removed with it; it is recorded here only in this comment.

What the file still proves, unconditionally, is the mathematics the exercise was reaching for:
the lower bound `card_classSet_le`, the uniqueness `suffix_automaton_unique` of a suffix
automaton that attains it, and `not_canonicalSuffixBimachineExists`, the reason the exercise
could not stand as written.  An exercise of this shape needs a Myhill-Nerode theory of
bimachines proper -- a canonical right-to-left congruence, finer than `∼`, that records how much
output is still pending -- which this project does not have. -/

/-! ## The bound of the first half is *not* attained in general

The following is a counterexample to `CanonicalSuffixBimachineExists`: a function computed by a
bimachine for which `∼` has exactly one class, but which no bimachine with a single suffix state
computes.  See the docstring of `CanonicalSuffixBimachineExists`. -/

section Counterexample

open Transducers

/-- A bimachine whose suffix automaton has only one state computes a function whose values grow
monotonically along prefixes: the output on `u` is a prefix of the output on `u ++ [a]`.  Indeed,
with a single suffix state the output produced at the positions of `u` does not depend on what
follows `u`, and the output produced at the last gap of `u` is produced at the corresponding gap
of `u ++ [a]` as well. -/
lemma eval_prefix_eval_append_of_subsingleton {P S : Type} [Subsingleton S]
    (M : Bimachine A B P S) (u : List A) (a : A) : M.eval u <+: M.eval (u ++ [a]) := by
  have hu : M.eval u = BimachIndex.bmPref M M.prefixInit u (BimachIndex.sfx M [])
      ++ M.evalFrom (strTrans M.prefixStep u M.prefixInit) [] := by
    rw [Bimachine.eval_eq_evalFrom, ← BimachIndex.evalFrom_append M M.prefixInit u []]
    simp
  have hua : M.eval (u ++ [a]) = BimachIndex.bmPref M M.prefixInit u (BimachIndex.sfx M [])
      ++ M.evalFrom (strTrans M.prefixStep u M.prefixInit) [a] := by
    rw [Bimachine.eval_eq_evalFrom, BimachIndex.evalFrom_append M M.prefixInit u [a]]
    congr 2
    exact Subsingleton.elim _ _
  set q := strTrans M.prefixStep u M.prefixInit with hq
  have hstep : M.evalFrom q [a] = M.evalFrom q [] ++ M.out (M.prefixStep q a) M.suffixInit := by
    rw [Bimachine.evalFrom_cons]
    simp only [Bimachine.evalFrom_nil]
    congr 2
    exact Subsingleton.elim _ _
  rw [hu, hua, hstep, ← List.append_assoc]
  exact ⟨_, rfl⟩

/-- The function of the counterexample: a string over a one letter alphabet is mapped to the
single letter that says whether its length is even. -/
def evenLenFun (w : List Unit) : List Bool := [decide (w.length % 2 = 0)]

/-- A bimachine for `evenLenFun`: the prefix automaton computes the parity of the length of the
prefix, the suffix automaton tests whether the suffix is empty, and the whole output is produced
at the last gap. -/
def evenLenBimach : Bimachine Unit Bool Bool Bool where
  prefixInit := true
  prefixStep p _ := !p
  suffixInit := true
  suffixStep _ _ := false
  out p s := if s then [p] else []

lemma evenLenBimach_evalFrom (p : Bool) (w : List Unit) :
    evenLenBimach.evalFrom p w = [if w.length % 2 = 0 then p else !p] := by
  induction w generalizing p with
  | nil => simp [evenLenBimach]
  | cons a w ih =>
    rw [Bimachine.evalFrom_cons]
    have hs : strTrans evenLenBimach.suffixStep (a :: w).reverse evenLenBimach.suffixInit
        = false := by
      simp [strTrans, List.reverse_cons, evenLenBimach]
    have hout : evenLenBimach.out p false = [] := by simp [evenLenBimach]
    rw [hs, hout, List.nil_append, ih]
    have hstep : evenLenBimach.prefixStep p a = !p := rfl
    rw [hstep]
    simp only [List.length_cons]
    rcases Nat.even_or_odd w.length with h | h
    · rw [Nat.even_iff] at h
      simp [h, Nat.add_mod]
    · rw [Nat.odd_iff] at h
      simp [h, Nat.add_mod]

lemma evenLenBimach_eval : evenLenBimach.eval = evenLenFun := by
  funext w
  rw [Bimachine.eval_eq_evalFrom, evenLenBimach_evalFrom]
  show _ = [decide (w.length % 2 = 0)]
  have : evenLenBimach.prefixInit = true := rfl
  rw [this]
  by_cases h : w.length % 2 = 0 <;> simp [h]

lemma evenLenBimach_suffixReachable : SuffixReachable evenLenBimach := by
  intro s
  cases s with
  | false => exact ⟨[()], rfl⟩
  | true => exact ⟨[], rfl⟩

/-- All strings are `∼`-equivalent for `evenLenFun`: the outputs are single letters, so they are
always at left distance at most `1`. -/
lemma boundedVarRel_evenLenFun (v₁ v₂ : List Unit) : BoundedVarRel evenLenFun v₁ v₂ :=
  ⟨1, fun w => leftDist_le (v := []) (v₁ := evenLenFun (w ++ v₁)) (v₂ := evenLenFun (w ++ v₂))
    (by simp) (by simp) (by simp [evenLenFun]) (by simp [evenLenFun])⟩

lemma clsOf_evenLenFun (w : List Unit) : clsOf evenLenFun w = Set.univ :=
  Set.eq_univ_of_forall fun w' => boundedVarRel_evenLenFun w w'

lemma classSet_evenLenFun : ClassSet evenLenFun = {Set.univ} := by
  ext C
  constructor
  · rintro ⟨w, rfl⟩
    exact clsOf_evenLenFun w
  · rintro rfl
    exact ⟨[], (clsOf_evenLenFun []).symm⟩

lemma card_classSet_evenLenFun : Nat.card (ClassSet evenLenFun) = 1 := by
  rw [classSet_evenLenFun]
  simp

/-- No bimachine with a single suffix state computes `evenLenFun`. -/
lemma two_le_card_of_eval_evenLenFun {P S : Type} [Finite S]
    (M : Bimachine Unit Bool P S) (hf : M.eval = evenLenFun) : 2 ≤ Nat.card S := by
  haveI : Nonempty S := ⟨M.suffixInit⟩
  have h1 : 1 ≤ Nat.card S := Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨‹Nonempty S›, ‹Finite S›⟩)
  have h2 : Nat.card S ≠ 1 := by
    intro h
    haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.1 h).1
    have hpref := eval_prefix_eval_append_of_subsingleton M [] ()
    rw [hf] at hpref
    simp [evenLenFun] at hpref
  omega

/-- **The hypothesis `CanonicalSuffixBimachineExists` is false.**  For `evenLenFun` the relation
`∼` has a single class, but every bimachine computing it has at least two suffix states. -/
theorem not_canonicalSuffixBimachineExists :
    ¬ CanonicalSuffixBimachineExists evenLenFun := by
  rintro ⟨P, S, hP, hS, M, hf, hreach, hcard⟩
  haveI : Finite S := hS
  have h2 := two_le_card_of_eval_evenLenFun M hf
  rw [hcard, card_classSet_evenLenFun] at h2
  omega

/-- The bimachine `evenLenBimach` is minimal in the sense of the exercise, and it has two suffix
states, whereas `∼` has a single class: the lower bound `card_classSet_le` is strict here. -/
theorem evenLenBimach_minimal : MinimalSuffixBimachine evenLenFun evenLenBimach := by
  refine ⟨evenLenBimach_eval, evenLenBimach_suffixReachable, ?_⟩
  intro P' S' _ hS' M' hf' _
  haveI : Finite S' := hS'
  have := two_le_card_of_eval_evenLenFun M' hf'
  simpa using this

end Counterexample

end Transducers.Exercises

