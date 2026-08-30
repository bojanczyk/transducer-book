/-
Exercise `exer:minimal-bimachine-lexicographic` of the chapter on machine
independent characterisations (`myhill-nerode.tex`) of *Transducers*
(M. Bojańczyk).
-/
import RequestProject.PartB.RatIndex

/-!
# The suffix automaton of a minimal bimachine is unique

Exercise `exer:minimal-bimachine-lexicographic` orders bimachines by the number
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
  is the construction in the proof of Theorem
  `thm:machine-independent-rational-functions`, refined so that the first of its
  two steps is read as a suffix automaton; the project has that theorem, but not
  in a form that exposes the construction, so this half is the explicit
  hypothesis `Transducers.Exercises.CanonicalSuffixBimachineExists`.

Everything else — that a suffix automaton with exactly that many states *is* the
automaton of `∼`-classes, initial state and transitions included, and hence that
any two minimal ones are isomorphic — is proved:
`Transducers.Exercises.suffix_automaton_unique` is the unconditional statement,
and `Transducers.Exercises.minimal_bimachine_lexicographic` is the exercise.

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

/-- A bimachine is minimal for the order of `exer:minimal-bimachine-lexicographic`: no bimachine
computing the same function, with all suffix states reachable, has a smaller suffix automaton. -/
def MinimalSuffixBimachine {P S : Type} (f : List A → List B) (M : Bimachine A B P S) : Prop :=
  M.eval = f ∧ SuffixReachable M ∧
    ∀ (P' S' : Type), Finite P' → Finite S' → ∀ M' : Bimachine A B P' S', M'.eval = f →
      SuffixReachable M' → Nat.card S ≤ Nat.card S'

/-- **Assumed: the bound of the first half of the solution is attained.**

For every function computed by a bimachine there is a bimachine, with all suffix states
reachable, whose suffix automaton has exactly one state per `∼`-class.

*Why this is true.*  This is the second paragraph of the solution of
`exer:minimal-bimachine-lexicographic`.  The proof of Theorem
`thm:machine-independent-rational-functions` decomposes the function into a right-to-left
automaton that annotates every position with the `∼`-class of the suffix after it, followed by a
subsequential function on the annotated strings; the first step, read as a suffix automaton, is
precisely the automaton of `∼`-classes, and the state of the subsequential transducer after an
annotated prefix depends only on the prefix and on the class of the remaining suffix — because
the annotations can be recovered from that class, `∼` being a left congruence — so it can serve
as the state of the prefix automaton.

*Why it is not available here.*  The project proves Theorem
`thm:machine-independent-rational-functions` in the direction that is used elsewhere, and it
does not expose the two-step decomposition of its proof in a form from which the suffix
automaton of `∼`-classes can be read off.  Only this existence statement is assumed; the
uniqueness argument, which is what the exercise asks for, is proved. -/
def CanonicalSuffixBimachineExists (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ SuffixReachable M ∧ Nat.card S = Nat.card (ClassSet f)

/-- A minimal bimachine has exactly one suffix state per `∼`-class. -/
lemma card_eq_of_minimal [Finite P] [Finite S] {f : List A → List B} {M : Bimachine A B P S}
    (hattain : CanonicalSuffixBimachineExists f) (hmin : MinimalSuffixBimachine f M) :
    Nat.card S = Nat.card (ClassSet f) := by
  obtain ⟨hf, hreach, hle⟩ := hmin
  obtain ⟨P₀, S₀, hP₀, hS₀, M₀, hf₀, hreach₀, hcard₀⟩ := hattain
  refine le_antisymm ?_ (card_classSet_le hf hreach)
  exact hcard₀ ▸ hle P₀ S₀ hP₀ hS₀ M₀ hf₀ hreach₀

/-- **Exercise `exer:minimal-bimachine-lexicographic`.**  If bimachines are ordered by the number
of states of the suffix automaton alone, then the suffix automaton of a minimal bimachine is
unique up to isomorphism.

The only assumption is `CanonicalSuffixBimachineExists`, that the lower bound of the first half
of the solution is attained; see its docstring. -/
theorem minimal_bimachine_lexicographic {P₁ S₁ P₂ S₂ : Type} [Finite P₁] [Finite S₁] [Finite P₂]
    [Finite S₂] {f : List A → List B} {M₁ : Bimachine A B P₁ S₁} {M₂ : Bimachine A B P₂ S₂}
    (hattain : CanonicalSuffixBimachineExists f)
    (hmin₁ : MinimalSuffixBimachine f M₁) (hmin₂ : MinimalSuffixBimachine f M₂) :
    SuffixIso M₁ M₂ :=
  suffix_automaton_unique hmin₁.1 hmin₂.1 hmin₁.2.1 hmin₂.2.1
    (card_eq_of_minimal hattain hmin₁) (card_eq_of_minimal hattain hmin₂)

end Transducers.Exercises
