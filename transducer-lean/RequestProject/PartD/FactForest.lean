/-
Part D, Section *Evaluation*, subsection *Simon trees*: the Factorisation Forest Theorem
(`thm:factorisation-forest`) and the lemmas of its proof (`lem:factorisation-forest-single-letter`,
`lem:factorisation-forest-shrinking-letter`, `lem:factorisation-forest-group`).

The Simon trees are those of `Transducers.FactTree.IsSimon` (`PartD/SimonTree.lean`), the
definition headed *Simon tree* in the book, which carries no `\label`.

## Semigroups

The book proves the theorem for semigroup homomorphisms `A⁺ → S`, and states the three lemmas in
that setting.  A semigroup homomorphism `A⁺ → S` is determined by the images `φ : A → S` of the
letters, and its Simon trees are the Simon trees, with nonempty underlying string, of the monoid
homomorphism `A* → S¹` into the monoid `S¹ = WithOne S` obtained by adjoining an identity
(`Transducers.semigroupHom φ`): the value of a nonempty string lies in `S`, and an element of `S` is
idempotent in `S¹` exactly when it is idempotent in `S`.  This is how Lemmas
`lem:factorisation-forest-single-letter` and `lem:factorisation-forest-group` are stated.

## The induction step

Lemma `lem:factorisation-forest-shrinking-letter` is, in the book, the induction step of the proof:
"the theorem holds if some letter value `s` shrinks the semigroup on the right" means that it holds
for `S` *given the induction hypothesis* -- that it holds for every smaller semigroup, and for `S`
with fewer letter values.  `Transducers.factorisation_forest_shrinking_letter` states it in exactly
that form.  The semigroups of the induction are represented as finite subsets `T` of a finite monoid
that are closed under multiplication (every finite semigroup `S` is one, inside `S¹`), and the
letter values as a subset `L ⊆ T`; the conclusion and the two induction hypotheses are the statement
of the theorem for those data.  The step is proved outright, and it is the step that the proof of
Theorem `thm:factorisation-forest` uses (`Transducers.Simon.good_shrink`).
-/
import RequestProject.PartD.SimonInduction
import RequestProject.PartD.MonoidAut

namespace Transducers

open Simon

/-- The semigroup homomorphism `A⁺ → S` determined by the images of the letters, as a monoid
homomorphism `A* → S¹` into the semigroup with an identity adjoined. -/
def semigroupHom {A S : Type} [Semigroup S] (φ : A → S) : FreeMonoid A →* WithOne S :=
  FreeMonoid.lift fun a => (φ a : WithOne S)

namespace Simon

variable {M : Type} [Monoid M]

lemma lift_of_eq {A : Type} (φ : A → M) :
    (fun a => FreeMonoid.lift φ (FreeMonoid.of a)) = φ :=
  funext fun a => FreeMonoid.lift_eval_of φ a

/-- From a bound for `Bnd` to Simon trees. -/
lemma trees_of_good {L : Finset M} (hG : Good L) : ∃ k : ℕ, ∀ (X : Type) (φ : X → M)
    (w : List X), w ≠ [] → (∀ x ∈ w, φ x ∈ L) →
      ∃ t : FactTree X, t.yield = w ∧ t.IsSimon (FreeMonoid.lift φ) ∧ t.height ≤ k := by
  obtain ⟨K, hK⟩ := hG
  refine ⟨K, fun X φ w hw hx => ?_⟩
  have hb := hK X φ w hw hx
  rw [← lift_of_eq φ] at hb
  exact Bnd.exists_tree _ hb

/-- From Simon trees to a bound for `Bnd`. -/
lemma good_of_trees {L : Finset M} (h : ∃ k : ℕ, ∀ (X : Type) (φ : X → M)
    (w : List X), w ≠ [] → (∀ x ∈ w, φ x ∈ L) →
      ∃ t : FactTree X, t.yield = w ∧ t.IsSimon (FreeMonoid.lift φ) ∧ t.height ≤ k) :
    Good L := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun X φ w hw hx => ?_⟩
  obtain ⟨t, rfl, hs, hh⟩ := hk X φ w hw hx
  have hb := Bnd.of_isSimon _ hs hw
  rw [lift_of_eq φ] at hb
  exact hb.mono hh

end Simon

/-- **Theorem `thm:factorisation-forest` (Factorisation Forest Theorem).**  For every monoid
homomorphism `h : A* → M` into a finite monoid there is a constant `k ∈ {1, 2, …}` such that every
input string admits a Simon tree of height at most `k`.  (The alphabet `A` is arbitrary; the empty
string has the Simon tree with a single node and no leaves, of height `1`.) -/
theorem factorisation_forest {A M : Type} [Monoid M] [Finite M] (h : FreeMonoid A →* M) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ w : List A,
      ∃ t : FactTree A, t.yield = w ∧ t.IsSimon h ∧ t.height ≤ k := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  obtain ⟨K, hK⟩ := good_univ (M := M)
  refine ⟨K + 1, by omega, fun w => ?_⟩
  rcases eq_or_ne w [] with rfl | hw
  · refine ⟨.node [], by simp, .node [] (by simp) (by simp), ?_⟩
    rw [FactTree.height_node]; simp
  · obtain ⟨t, ht, hs, hh⟩ :=
      Bnd.exists_tree h (hK A (fun a => h (FreeMonoid.of a)) w hw (fun _ _ => Finset.mem_univ _))
    exact ⟨t, ht, hs, by omega⟩

/-- The Factorisation Forest Theorem for semigroup homomorphisms `A⁺ → S` into a finite semigroup,
the form in which the book proves it: every nonempty string has a Simon tree of bounded height. -/
theorem factorisation_forest_semigroup {A S : Type} [Semigroup S] [Finite S] (φ : A → S) :
    ∃ k : ℕ, ∀ w : List A, w ≠ [] →
      ∃ t : FactTree A, t.yield = w ∧ t.IsSimon (semigroupHom φ) ∧ t.height ≤ k := by
  haveI : Finite (WithOne S) := inferInstanceAs (Finite (Option S))
  obtain ⟨k, -, hk⟩ := factorisation_forest (semigroupHom φ)
  exact ⟨k, fun w _ => hk w⟩

/-- **Lemma `lem:factorisation-forest-single-letter`.**  The Factorisation Forest Theorem holds
when all input letters are mapped to the same semigroup element `s`: there is a bound `k` such that
every nonempty string has a Simon tree of height at most `k`.  (The proof groups the string into
factors of length `p`, where `s^p` is an idempotent; the bound is `2p`.) -/
theorem factorisation_forest_single_letter {A S : Type} [Semigroup S] [Finite S] (φ : A → S)
    (s : S) (hs : ∀ a, φ a = s) :
    ∃ k : ℕ, ∀ w : List A, w ≠ [] →
      ∃ t : FactTree A, t.yield = w ∧ t.IsSimon (semigroupHom φ) ∧ t.height ≤ k := by
  classical
  haveI : Finite (WithOne S) := inferInstanceAs (Finite (Option S))
  obtain ⟨k, hk⟩ := trees_of_good (good_single ((s : WithOne S)))
  refine ⟨k, fun w hw => hk A (fun a => (φ a : WithOne S)) w hw fun a _ => ?_⟩
  simp [hs a]

/-- **Lemma `lem:factorisation-forest-shrinking-letter`** (the induction step).  Let `T` be a finite
semigroup, represented as a subset of a finite monoid `M` closed under multiplication, and let
`L ⊆ T` be the set of letter values.  Suppose that some letter value `s ∈ L` shrinks the semigroup
on the right, `T·s ⊊ T`, and that the theorem holds for every smaller semigroup and for `T` with
fewer letter values.  Then the theorem holds for `T` and `L`: there is a bound `k` such that every
nonempty string, over any alphabet, whose letters have values in `L`, has a Simon tree of height at
most `k`. -/
theorem factorisation_forest_shrinking_letter {M : Type} [Monoid M] [Finite M] [DecidableEq M]
    (T L : Finset M) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T) (hLT : L ⊆ T) (s : M) (hs : s ∈ L)
    (hshrink : T.image (· * s) ⊂ T)
    (ih_size : ∀ T' : Finset M, (∀ a ∈ T', ∀ b ∈ T', a * b ∈ T') → T'.card < T.card →
      ∀ L' ⊆ T', ∃ k : ℕ, ∀ (X : Type) (φ : X → M) (w : List X), w ≠ [] →
        (∀ x ∈ w, φ x ∈ L') →
          ∃ t : FactTree X, t.yield = w ∧ t.IsSimon (FreeMonoid.lift φ) ∧ t.height ≤ k)
    (ih_letters : ∀ L' ⊆ T, L'.card < L.card → ∃ k : ℕ, ∀ (X : Type) (φ : X → M) (w : List X),
      w ≠ [] → (∀ x ∈ w, φ x ∈ L') →
        ∃ t : FactTree X, t.yield = w ∧ t.IsSimon (FreeMonoid.lift φ) ∧ t.height ≤ k) :
    ∃ k : ℕ, ∀ (X : Type) (φ : X → M) (w : List X), w ≠ [] → (∀ x ∈ w, φ x ∈ L) →
      ∃ t : FactTree X, t.yield = w ∧ t.IsSimon (FreeMonoid.lift φ) ∧ t.height ≤ k := by
  have hsT : s ∈ T := hLT hs
  have hclosed : Closed (T.image (· * s)) := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨a' * s * b', hT _ (hT _ ha' _ hsT) _ hb', ?_⟩
    simp [mul_assoc]
  refine trees_of_good (good_shrink hT hLT (s := s) (good_of_trees ?_) (good_of_trees ?_))
  · exact ih_letters (L.erase s) (subset_trans (Finset.erase_subset _ _) hLT)
      (Finset.card_erase_lt_of_mem hs)
  · exact ih_size _ hclosed (Finset.card_lt_card hshrink) _ subset_rfl

/-- **Lemma `lem:factorisation-forest-group`.**  The Factorisation Forest Theorem holds when the
semigroup is a (finite) group: every nonempty string has a Simon tree of height at most three times
the size of the group.  (The book's proof shows the finer bound `3·|σ(w)|`, where `σ(w)` is the set
of values of the prefixes of `w` that are neither empty nor full; see
`Transducers.Simon.good_group`.) -/
theorem factorisation_forest_group {A G : Type} [Group G] [Finite G] (h : FreeMonoid A →* G) :
    ∀ w : List A, w ≠ [] →
      ∃ t : FactTree A, t.yield = w ∧ t.IsSimon h ∧ t.height ≤ 3 * Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨K, hK, hb⟩ := good_group (T := (Finset.univ : Finset G))
    (fun _ _ _ _ => Finset.mem_univ _) (fun g _ x _ y _ hxy => mul_left_cancel hxy)
  intro w hw
  obtain ⟨t, ht, hs, hh⟩ := Bnd.exists_tree h
    (hb A (fun a => h (FreeMonoid.of a)) w hw (fun _ _ => Finset.mem_univ _))
  refine ⟨t, ht, hs, ?_⟩
  rw [hK, Finset.card_univ, ← Nat.card_eq_fintype_card] at hh
  exact hh

end Transducers
