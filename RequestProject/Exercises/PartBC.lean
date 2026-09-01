/-
The exercises of Parts B and C of *Transducers* (M. Bojańczyk): the exercises of the sections
*Rational relations* (`rational-relations.tex`), *Rational functions* (`rational-functions.tex`),
*Regular functions* (`regular-primes.tex`) and *Logic* (`logic.tex`).

Exercises are not numbered results of the book, so they are not listed in `THEOREMS.md`; they are
recorded in `EXERCISES.md` instead.  The exercises that carry a LaTeX `\label` are referred to by
that label, exactly as the numbered results are; those that do not are referred to by their position
in the chapter.

Each statement follows the exercise, and each proof follows the author's own solution, unless the
docstring says otherwise.  The auxiliary facts that the solutions take for granted are in
`RequestProject/Exercises/PartBCAux.lean`.
-/
import RequestProject.Exercises.PartBCAux
import RequestProject.PCP.Index
import RequestProject.Exercises.PartBCPCP
import RequestProject.Exercises.PartBCUnary

namespace Transducers
namespace Exercises

open LabAut NFAO

/-! ## Rational relations (`rational-relations.tex`) -/

/-! ### Exercise `exer:regular-languages-for-rational-relations` -/

/-- **Exercise `exer:regular-languages-for-rational-relations`, first item.**  The domain of a
rational relation — the inputs that produce at least one output — is a regular language.

This is the author's first argument: the domain is the inverse image of the regular language `B*`
under the relation, which is regular by the continuity of rational relations (Theorem
`thm:continuity-rational-relations`). -/
theorem rationalRel_domain_isRegular {A B : Type} {R : List A → List B → Prop}
    (hR : IsRationalRel R) : Language.IsRegular ({w | ∃ v, R w v} : Language A) := by
  have h := rationalRel_continuous hR Set.univ isRegular_univ
  have : {w : List A | ∃ v, R w v ∧ v ∈ (Set.univ : Language B)} = {w | ∃ v, R w v} := by
    ext w; simp
  rwa [this] at h

/-- **Exercise `exer:regular-languages-for-rational-relations`, second item.**  The range of a
rational relation — the outputs that arise from at least one input — is a regular language.

As in the author's solution, this is the first item applied to the inverse relation, which is
rational by the symmetry of rational relations with respect to input and output
(`Transducers.Exercises.isRationalRel_inv`). -/
theorem rationalRel_range_isRegular {A B : Type} {R : List A → List B → Prop}
    (hR : IsRationalRel R) : Language.IsRegular ({v | ∃ w, R w v} : Language B) :=
  rationalRel_domain_isRegular (isRationalRel_inv hR)

/-! ### Exercise `exer:non-regular-languages-for-rational-relations` -/

/-- The homomorphism `keep c` deletes the letters different from `c` and turns the remaining ones
into the single letter of the one-letter output alphabet.  The two functions of the author's
solution are `keep false` ("keep only the `a`s") and `keep true` ("keep only the `b`s and replace
them by `a`s"). -/
def keep (c : Bool) : List Bool → List Unit := homOf (fun a => if a = c then [()] else [])

@[simp] lemma keep_nil (c : Bool) : keep c [] = [] := rfl

lemma keep_cons (c : Bool) (a : Bool) (w : List Bool) :
    keep c (a :: w) = (if a = c then [()] else []) ++ keep c w := by
  simp [keep, homOf]

lemma keep_length (c : Bool) (w : List Bool) : (keep c w).length = w.count c := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [keep_cons, List.length_append, ih, List.count_cons]
      by_cases h : a = c
      · simp [h, Nat.add_comm]
      · simp [h]

/-- The two functions agree exactly on the strings that have as many `false`s as `true`s. -/
lemma keep_false_eq_keep_true_iff (w : List Bool) :
    keep false w = keep true w ↔ w.count false = w.count true := by
  rw [list_unit_eq_iff, keep_length, keep_length]

/-- The letters of an annotated string. -/
lemma homOf_fst (u : List (Bool × Bool)) :
    homOf (fun z : Bool × Bool => [z.1]) u = u.map Prod.fst := by
  induction u with
  | nil => rfl
  | cons z u ih => simp [homOf] at ih ⊢; exact ih

lemma homOf_keep (c : Bool) (u : List (Bool × Bool)) (hu : ∀ z ∈ u, z.2 = c) :
    homOf (fun z : Bool × Bool => if z.1 = z.2 then [()] else []) u = keep c (u.map Prod.fst) := by
  induction u with
  | nil => rfl
  | cons z u ih =>
      have hz : z.2 = c := hu z (by simp)
      rw [List.map_cons, keep_cons, ← ih (fun y hy => hu y (by simp [hy]))]
      simp [homOf, hz]

/-- **Exercise `exer:non-regular-languages-for-rational-relations`.**  For some rational relation
the set of inputs that produce at most one output is not regular.

The relation is the one of the author's solution: the union of the two rational functions `keep
false` and `keep true`, over the input alphabet `Bool` and the one-letter output alphabet `Unit`.
An input produces two outputs exactly when the two functions disagree on it, so the inputs with at
most one output are the strings with as many `false`s as `true`s, which is not a regular language.
The relation is rational by guess and check (`Transducers.isRationalRel_of_regular_nivat`): the
annotation records, in every position, which of the two functions is being applied, and the
regular language of correct annotations is the one where this choice is the same in all
positions. -/
theorem exists_rationalRel_atMostOneOutput_not_isRegular :
    ∃ R : List Bool → List Unit → Prop, IsRationalRel R ∧
      ¬ Language.IsRegular ({w | ∀ v v', R w v → R w v' → v = v'} : Language Bool) := by
  classical
  refine ⟨fun w v => v = keep false w ∨ v = keep true w, ?_, ?_⟩
  · have hL : Language.IsRegular ({u : List (Bool × Bool) |
        (∀ z ∈ u, z.2 = true) ∨ (∀ z ∈ u, z.2 = false)} : Language (Bool × Bool)) := by
      have h12 := (isRegular_forall_mem (fun z : Bool × Bool => z.2 = true)).add
        (isRegular_forall_mem (fun z : Bool × Bool => z.2 = false))
      convert h12 using 1
    refine isRationalRel_congr
      (isRationalRel_of_regular_nivat (fun z : Bool × Bool => [z.1])
        (fun z : Bool × Bool => if z.1 = z.2 then [()] else []) hL) ?_
    intro w v
    constructor
    · intro h
      obtain rfl | rfl := h
      · refine ⟨w.map (fun a => (a, false)), Or.inr ?_, ?_, ?_⟩
        · intro z hz
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz
          rfl
        · rw [homOf_fst]; simp [Function.comp_def]
        · have hall : ∀ z ∈ w.map (fun a => (a, false)), z.2 = false := by
            intro z hz
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz
            rfl
          rw [homOf_keep false _ hall]
          simp [Function.comp_def]
      · refine ⟨w.map (fun a => (a, true)), Or.inl ?_, ?_, ?_⟩
        · intro z hz
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz
          rfl
        · rw [homOf_fst]; simp [Function.comp_def]
        · have hall : ∀ z ∈ w.map (fun a => (a, true)), z.2 = true := by
            intro z hz
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz
            rfl
          rw [homOf_keep true _ hall]
          simp [Function.comp_def]
    · rintro ⟨u, hu, hin, hout⟩
      obtain hu | hu := hu
      · subst hin; subst hout
        exact Or.inr (by rw [homOf_keep true u hu, homOf_fst])
      · subst hin; subst hout
        exact Or.inl (by rw [homOf_keep false u hu, homOf_fst])
  · have hset : {w : List Bool | ∀ v v', (v = keep false w ∨ v = keep true w) →
        (v' = keep false w ∨ v' = keep true w) → v = v'}
        = {w : List Bool | w.count false = w.count true} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        exact (keep_false_eq_keep_true_iff w).1 (h _ _ (Or.inl rfl) (Or.inr rfl))
      · intro h v v' hv hv'
        have hkeq : keep false w = keep true w := (keep_false_eq_keep_true_iff w).2 h
        obtain rfl | rfl := hv <;> obtain rfl | rfl := hv' <;> simp [hkeq]
    have hnr := not_isRegular_balanced
    rw [← hset] at hnr
    exact hnr

/-! ### Exercise `exer:rational-relations-not-closed-under-intersection` -/

lemma keep_eq_replicate (c : Bool) (w : List Bool) :
    keep c w = List.replicate (w.count c) () := by
  conv_lhs => rw [list_unit_eq_replicate (keep c w)]
  rw [keep_length]

lemma homOf_single {B : Type} (u : List B) : homOf (fun b => [b]) u = u := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [homOf, List.map_cons, List.flatten_cons] at ih ⊢; rw [ih]; rfl

/-- **Exercise `exer:rational-relations-not-closed-under-intersection`.**  Rational relations are
not closed under intersection.

The two relations are the ones of the author's solution, over the one-letter input alphabet `Unit`
and the two-letter output alphabet `Bool` (`false` is `b` and `true` is `c`):

  `R = {(aⁿ, bⁿcᵐ)}`   and   `S = {(aⁿ, bᵐcⁿ)}`.

Both are rational by guess and check (`Transducers.isRationalRel_of_regular_nivat`) over the regular
language `b* c*` of annotations, the input letter being produced by the `b`s for `R` and by the
`c`s for `S`.  Their intersection is `{(aⁿ, bⁿcⁿ)}`, whose range `{bⁿcⁿ}` is not regular, so it is
not rational by the second item of Exercise `exer:regular-languages-for-rational-relations`
(the observation, after Theorem `thm:continuity-rational-relations`, that a rational relation maps
regular languages to regular languages). -/
theorem exists_rationalRel_inter_not_rationalRel :
    ∃ R S : List Unit → List Bool → Prop, IsRationalRel R ∧ IsRationalRel S ∧
      ¬ IsRationalRel (fun w v => R w v ∧ S w v) := by
  classical
  refine ⟨fun w v => ∃ n m, w = List.replicate n () ∧
            v = List.replicate n false ++ List.replicate m true,
          fun w v => ∃ n m, w = List.replicate n () ∧
            v = List.replicate m false ++ List.replicate n true, ?_, ?_, ?_⟩
  · refine isRationalRel_congr
      (isRationalRel_of_regular_nivat (fun a : Bool => if a = false then [()] else [])
        (fun a : Bool => [a]) isRegular_sortedBool) ?_
    intro w v
    constructor
    · rintro ⟨n, m, rfl, rfl⟩
      refine ⟨List.replicate n false ++ List.replicate m true, ⟨n, m, rfl⟩, ?_, homOf_single _⟩
      rw [show (fun a : Bool => if a = false then [()] else []) = _ from rfl]
      exact (keep_eq_replicate false _).trans (by rw [count_false_replicate])
    · rintro ⟨u, ⟨n, m, rfl⟩, hin, hout⟩
      refine ⟨n, m, ?_, ?_⟩
      · rw [← hin]
        exact (keep_eq_replicate false _).trans (by rw [count_false_replicate])
      · rw [← hout, homOf_single]
  · refine isRationalRel_congr
      (isRationalRel_of_regular_nivat (fun a : Bool => if a = true then [()] else [])
        (fun a : Bool => [a]) isRegular_sortedBool) ?_
    intro w v
    constructor
    · rintro ⟨n, m, rfl, rfl⟩
      refine ⟨List.replicate m false ++ List.replicate n true, ⟨m, n, rfl⟩, ?_, homOf_single _⟩
      exact (keep_eq_replicate true _).trans (by rw [count_true_replicate])
    · rintro ⟨u, ⟨m, n, rfl⟩, hin, hout⟩
      refine ⟨n, m, ?_, ?_⟩
      · rw [← hin]
        exact (keep_eq_replicate true _).trans (by rw [count_true_replicate])
      · rw [← hout, homOf_single]
  · intro hinter
    have hrange := rationalRel_range_isRegular hinter
    have hset : {v : List Bool | ∃ w : List Unit,
        (∃ n m, w = List.replicate n () ∧ v = List.replicate n false ++ List.replicate m true) ∧
        (∃ n m, w = List.replicate n () ∧ v = List.replicate m false ++ List.replicate n true)}
        = {v : List Bool | ∃ n, v = List.replicate n false ++ List.replicate n true} := by
      ext v
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨w, ⟨n, m, hw, hv⟩, ⟨n', m', hw', hv'⟩⟩
        have hnn : n = n' := by
          have := congrArg List.length (hw.symm.trans hw')
          simpa using this
        subst hnn
        have h1 := congrArg (fun l : List Bool => l.count false) (hv.symm.trans hv')
        have h2 := congrArg (fun l : List Bool => l.count true) (hv.symm.trans hv')
        simp only [count_false_replicate, count_true_replicate] at h1 h2
        exact ⟨n, by rw [hv, h2]⟩
      · rintro ⟨n, rfl⟩
        exact ⟨List.replicate n (), ⟨n, n, rfl, rfl⟩, ⟨n, n, rfl, rfl⟩⟩
    rw [hset] at hrange
    exact not_isRegular_eqReplicate hrange

/-! ### Exercise `exer:rational-relations-intersection-undecidable` -/

/-- **Exercise `exer:rational-relations-intersection-undecidable`.**  It is undecidable whether two
rational relations have a nonempty intersection.

As for the numbered results of Part B, a decision problem about rational relations is a problem
about their finite descriptions, the codes `Transducers.RelCode`, and the undecidability of the
Post correspondence problem is now itself proved, as
`Transducers.PCP.solvable_not_computablePred` (`RequestProject/PCP/Index.lean`), so this
exercise is unconditional; `intersection_undecidable_aux` still takes it as an argument,
since that is what the reduction is.

The reduction is the author's, and is carried out in `RequestProject/Exercises/PartBCPCP.lean`: a
homomorphism `g`, viewed as the relation `{(w, g w) | w ≠ ε}`, is computed by a two-state
automaton, and the two relations obtained this way from the two homomorphisms of an instance meet
exactly when the instance has a solution.  Since these two relations are functions, the problem
remains undecidable for rational functions. -/
theorem rationalRel_intersection_undecidable :
    ¬ ComputablePred (fun p : RelCode × RelCode => ∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v) :=
  intersection_undecidable_aux PCP.solvable_not_computablePred

/-! ### Exercise `exer:rational-output-size` -/

/-- **Exercise `exer:rational-output-size`.**  For a rational relation the following are
equivalent: every input string produces at most finitely many outputs, and the output lengths are
bounded by an affine function of the input length.

The implication from the bound to the finiteness is the author's: there are finitely many strings
of bounded length.  For the converse the author analyses the runs by hand; here the analysis is the
one already carried out for Lemma `lemma:eliminate-epsilon-transitions`, whose second half says
that a rational relation with finitely many outputs is computed by an nfa with output in which
every transition of an accepting run reads exactly one letter (and a run on the empty input
consists of a single transition).  Such a run on an input of length `n` has `n` transitions, each
producing at most `K` letters of output, where `K` is the largest output of a transition, and hence
the output has length at most `K·n + K`. -/
theorem rationalRel_finiteOutputs_iff_affine {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    (∀ w, {v | R w v}.Finite) ↔ ∃ c d : ℕ, ∀ w v, R w v → v.length ≤ c * w.length + d := by
  constructor
  · intro hfin
    obtain ⟨-, hε⟩ := epsilon_elimination hR
    obtain ⟨Q, hQ, M, hfree, hrel⟩ := hε hfin
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ t ∈ M.δ, (t.2.2.1 : List B).length ≤ K := by
      obtain ⟨K, hKmem⟩ := (M.δ_finite.image (fun t => (t.2.2.1 : List B).length)).bddAbove
      exact ⟨K, fun t ht => hKmem ⟨t, ht, rfl⟩⟩
    refine ⟨K, K, fun w v hRwv => ?_⟩
    obtain ⟨ts, hacc, hin, hout⟩ := (hrel w v).1 hRwv
    obtain ⟨q, -, p, -, hpath⟩ := id hacc
    have hmem := path_mem_delta hpath
    have hbound := outputOf_length_le (M := M) hK ts hmem
    obtain ⟨hone, hnil⟩ := hfree ts hacc
    by_cases hw : w = []
    · have h1 : ts.length = 1 := hnil (by rw [hin, hw])
      rw [← hout, hw]
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
      rw [h1] at hbound
      simpa using hbound
    · have h1 : ts.length = w.length := by
        rw [← hin]
        exact (inputOf_length_of_one ts (hone (by rw [hin]; exact hw))).symm
      rw [h1] at hbound
      rw [← hout]
      omega
  · rintro ⟨c, d, hbd⟩ w
    exact (finite_lists_length_le (c * w.length + d)).subset (fun v hv => hbd w v hv)

/-! ### Exercise `ex:recognisable-relations` -/

/-- **Definition of a recognisable subset of `A* × B*`.**  This is the book's Definition
`def:rational-recognisable-subsets` specialised to the monoid `A* × B*`, whose product is
concatenation in each coordinate; the general notion, for an arbitrary monoid, is not part of this
formalisation, and the exercise is the only place that needs it.

As in the author's solution, recognisability is used in the form "inverse image of a subset of a
finite monoid under a monoid homomorphism" (the solution recalls that this is equivalent to the
definition by a congruence of finite index).  A homomorphism out of `A* × B*` is given here by a
plain function together with the two equations it satisfies, so that no monoid instance has to be
put on `List A × List B`. -/
def IsRecognisableRel {A B : Type} (R : Set (List A × List B)) : Prop :=
  ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (h : List A × List B → M) (F : Set M),
    h ([], []) = 1 ∧
    (∀ w w' : List A, ∀ v v' : List B, h (w ++ w', v ++ v') = h (w, v) * h (w', v')) ∧
    R = {p | h p ∈ F}

/-- **Exercise `ex:recognisable-relations`.**  The recognisable subsets of `A* × B*` are exactly
the unions of finitely many products `K × L` of a regular language over the input alphabet with a
regular language over the output alphabet.  The finite union is indexed by `Fin n`.

Both directions are the author's.  For a finite union, each `K i` is recognised by a homomorphism
`gA i` into a finite monoid and each `L i` by a homomorphism `gB i`
(`Transducers.Exercises.exists_wordHom_of_isRegular`), and the product of all the monoids
`(MA i) × (MB i)` recognises the union in one go.  Conversely, if `h` recognises `R`, then every
pair factors as `(w, v) = (w, ε) · (ε, v)`, so `h (w, v) = g w * k v` for the two homomorphisms
`g w = h (w, ε)` and `k v = h (ε, v)`; hence `R` is the union, over the pairs `(m, n)` of the
finite monoid whose product lies in the accepting set, of the products `g⁻¹(m) × k⁻¹(n)`, and
these are regular because inverse images under a homomorphism into a finite monoid are
(`Transducers.Exercises.isRegular_of_wordHom`).  The union is indexed here by all pairs `(m, n)`,
the sets belonging to a pair whose product is not accepting being empty. -/
theorem isRecognisableRel_iff_finite_union {A B : Type} (R : Set (List A × List B)) :
    IsRecognisableRel R ↔
      ∃ (n : ℕ) (K : Fin n → Language A) (L : Fin n → Language B),
        (∀ i, (K i).IsRegular) ∧ (∀ i, (L i).IsRegular) ∧
        R = {p | ∃ i, p.1 ∈ K i ∧ p.2 ∈ L i} := by
  constructor
  · rintro ⟨M, _, _, h, F, hnil, happ, rfl⟩
    classical
    set g : List A → M := fun w => h (w, []) with hgdef
    set k : List B → M := fun v => h ([], v) with hkdef
    have hg : IsWordHom g := by
      refine ⟨hnil, fun u u' => ?_⟩
      have := happ u u' [] []
      simpa [hgdef] using this
    have hk : IsWordHom k := by
      refine ⟨hnil, fun u u' => ?_⟩
      have := happ [] [] u u'
      simpa [hkdef] using this
    have hsplit : ∀ p : List A × List B, h p = g p.1 * k p.2 := by
      rintro ⟨w, v⟩
      have := happ w [] [] v
      simpa [hgdef, hkdef] using this
    set e : Fin (Fintype.card (M × M)) ≃ M × M := (Fintype.equivFin (M × M)).symm with hedef
    refine ⟨Fintype.card (M × M),
      fun i => {w | g w = (e i).1 ∧ (e i).1 * (e i).2 ∈ F},
      fun i => {v | k v = (e i).2}, ?_, ?_, ?_⟩
    · intro i
      show Language.IsRegular {w | g w = (e i).1 ∧ (e i).1 * (e i).2 ∈ F}
      by_cases hF : (e i).1 * (e i).2 ∈ F
      · have : {w | g w = (e i).1 ∧ (e i).1 * (e i).2 ∈ F} = {w | g w ∈ ({(e i).1} : Set M)} := by
          ext w; simp [hF]
        rw [this]; exact isRegular_of_wordHom hg _
      · have : {w | g w = (e i).1 ∧ (e i).1 * (e i).2 ∈ F} = {w | g w ∈ (∅ : Set M)} := by
          ext w; simp [hF]
        rw [this]; exact isRegular_of_wordHom hg _
    · intro i
      show Language.IsRegular {v | k v = (e i).2}
      exact isRegular_of_wordHom hk {(e i).2}
    · ext p
      simp only [Set.mem_setOf_eq, hsplit p]
      constructor
      · intro hp
        refine ⟨e.symm (g p.1, k p.2), ⟨?_, ?_⟩, ?_⟩
        · show g p.1 = (e (e.symm (g p.1, k p.2))).1
          simp
        · show (e (e.symm (g p.1, k p.2))).1 * (e (e.symm (g p.1, k p.2))).2 ∈ F
          simpa using hp
        · show k p.2 = (e (e.symm (g p.1, k p.2))).2
          simp
      · rintro ⟨i, ⟨h1, h2⟩, h3⟩
        rw [h1, h3]; exact h2
  · rintro ⟨n, K, L, hK, hL, rfl⟩
    classical
    have hK' : ∀ i, ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (h : List A → M) (F : Set M),
        IsWordHom h ∧ K i = {w | h w ∈ F} := fun i => exists_wordHom_of_isRegular (hK i)
    have hL' : ∀ i, ∃ (M : Type) (_ : Monoid M) (_ : Fintype M) (h : List B → M) (F : Set M),
        IsWordHom h ∧ L i = {w | h w ∈ F} := fun i => exists_wordHom_of_isRegular (hL i)
    choose MA instA finA gA FA homA eqA using hK'
    choose MB instB finB gB FB homB eqB using hL'
    refine ⟨∀ i, MA i × MB i, inferInstance, inferInstance,
      fun p i => (gA i p.1, gB i p.2), {m | ∃ i, (m i).1 ∈ FA i ∧ (m i).2 ∈ FB i}, ?_, ?_, ?_⟩
    · funext i
      exact Prod.ext ((homA i).1) ((homB i).1)
    · intro w w' v v'
      funext i
      exact Prod.ext ((homA i).2 w w') ((homB i).2 v v')
    · ext p
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, h1, h2⟩
        rw [eqA i] at h1
        rw [eqB i] at h2
        exact ⟨i, h1, h2⟩
      · rintro ⟨i, h1, h2⟩
        exact ⟨i, by rw [eqA i]; exact h1, by rw [eqB i]; exact h2⟩

/-! ## Rational functions (`rational-functions.tex`) -/

/-! ### Exercise `exer:examples-of-rational-fun`

The three functions of the exercise, each represented both as a bimachine (`IsBimachine`) and as a
rational function (`IsRationalFun`).  The bimachines are the ones described in the author's
solution; rationality is then Theorem `thm:bimachines`, in the form
`Transducers.rationalFun_of_isBimachine`, so nothing is reproved here. -/

section EvenLength

variable {A : Type}

private lemma decide_odd (n : ℕ) : decide (Odd n) = !decide (Even n) := by
  by_cases h : Even n
  · simp [h, Nat.not_odd_iff_even.2 h]
  · simp [h, Nat.not_even_iff_odd.1 h]

/-- The bimachine for the first item of Exercise `exer:examples-of-rational-fun`: the prefix
automaton and the suffix automaton both track a parity, and the suffix automaton also remembers the
first letter of the suffix.  The output in a gap is that letter when the two parities agree, that
is when the whole input has even length, and the empty string otherwise. -/
def evenBM : Bimachine A A Bool (Bool × Option A) where
  prefixInit := false
  prefixStep := fun p _ => !p
  suffixInit := (false, none)
  suffixStep := fun s a => (!s.1, some a)
  out := fun p s => if p = s.1 then s.2.toList else []

lemma evenBM_sfx (w : List A) :
    BimachIndex.sfx (evenBM (A := A)) w = (decide (Odd w.length), w.head?) := by
  induction w with
  | nil => simp [evenBM]
  | cons a w ih =>
    rw [sfx_cons, ih]
    simp [evenBM, decide_odd, Nat.even_add_one]

lemma evenBM_evalFrom (p : Bool) (w : List A) :
    (evenBM (A := A)).evalFrom p w = if p = decide (Odd w.length) then w else [] := by
  induction w generalizing p with
  | nil => simp [evenBM]
  | cons a w ih =>
    rw [evalFrom_cons', evenBM_sfx, ih]
    have hodd : decide (Odd (a :: w).length) = !decide (Odd w.length) := by
      simp [decide_odd, Nat.even_add_one]
    rw [hodd]
    cases p <;> cases decide (Odd w.length) <;> simp [evenBM]

/-- **Exercise `exer:examples-of-rational-fun`, first item.**  The function that returns its input
when the input has even length, and the empty string otherwise, is computed by a bimachine and is
a rational function. -/
theorem isBimachine_isRationalFun_evenLength [Finite A] :
    IsBimachine (fun w : List A => if Even w.length then w else []) ∧
      IsRationalFun (fun w : List A => if Even w.length then w else []) := by
  have hbm : IsBimachine (fun w : List A => if Even w.length then w else []) := by
    refine ⟨Bool, Bool × Option A, inferInstance, inferInstance, evenBM, ?_⟩
    funext w
    rw [Bimachine.eval_eq_evalFrom, evenBM_evalFrom]
    by_cases h : Even w.length
    · simp [evenBM, h, Nat.not_odd_iff_even.2 h]
    · simp [evenBM, h, Nat.not_even_iff_odd.1 h]
  exact ⟨hbm, rationalFun_of_isBimachine hbm⟩

end EvenLength

section SwapFirstLast

variable {A : Type}

/-- Swapping the first and the last letter of a string; strings of length at most one are left
unchanged. -/
def swapFirstLast : List A → List A
  | [] => []
  | [a] => [a]
  | a :: b :: w => ((b :: w).getLast (List.cons_ne_nil b w)) :: ((b :: w).dropLast ++ [a])

/-- `Transducers.Exercises.swapFirstLast` really does swap the first and the last letter. -/
lemma swapFirstLast_swaps (a c : A) (v : List A) :
    swapFirstLast (a :: (v ++ [c])) = c :: (v ++ [a]) := by
  cases v with
  | nil => simp [swapFirstLast]
  | cons b v =>
    show swapFirstLast (a :: b :: (v ++ [c])) = _
    rw [swapFirstLast]
    have hd : (b :: (v ++ [c])).dropLast = b :: v := by
      rw [show b :: (v ++ [c]) = (b :: v) ++ [c] from rfl, List.dropLast_concat]
    have hg : (b :: (v ++ [c])).getLast (List.cons_ne_nil b (v ++ [c])) = c := by simp
    rw [hd, hg]

/-- The bimachine for the second item of Exercise `exer:examples-of-rational-fun`: the prefix
automaton remembers the first letter of the prefix, and the suffix automaton remembers the first
and the last letter of the suffix, as well as whether the suffix has at least two letters. -/
def swapBM : Bimachine A A (Option A) (Option (A × A × Bool)) where
  prefixInit := none
  prefixStep := fun p a => some (p.getD a)
  suffixInit := none
  suffixStep := fun s a =>
    match s with
    | none => some (a, a, false)
    | some (_, l, _) => some (a, l, true)
  out := fun p s =>
    match s with
    | none => []
    | some (f, l, two) =>
      match p with
      | none => [l]
      | some pf => if two then [f] else [pf]

lemma swapBM_sfx_cons (a : A) (w : List A) :
    BimachIndex.sfx (swapBM (A := A)) (a :: w)
      = some (a, (a :: w).getLast (List.cons_ne_nil a w), decide (w ≠ [])) := by
  induction w generalizing a with
  | nil => simp [BimachIndex.sfx, swapBM, strTrans]
  | cons b w ih =>
    rw [sfx_cons, ih b]
    simp [swapBM, List.getLast_cons]

lemma swapBM_evalFrom_some (pf : A) (w : List A) :
    (swapBM (A := A)).evalFrom (some pf) w = if w = [] then [] else w.dropLast ++ [pf] := by
  induction w with
  | nil => simp [swapBM]
  | cons a w ih =>
    rw [evalFrom_cons', swapBM_sfx_cons,
      show (swapBM (A := A)).prefixStep (some pf) a = some pf from rfl, ih]
    cases w with
    | nil => simp [swapBM]
    | cons b w => simp [swapBM]

/-- **Exercise `exer:examples-of-rational-fun`, second item.**  Swapping the first and the last
letter is computed by a bimachine and is a rational function. -/
theorem isBimachine_isRationalFun_swapFirstLast [Finite A] :
    IsBimachine (swapFirstLast : List A → List A) ∧
      IsRationalFun (swapFirstLast : List A → List A) := by
  have hbm : IsBimachine (swapFirstLast : List A → List A) := by
    refine ⟨Option A, Option (A × A × Bool), inferInstance, inferInstance, swapBM, ?_⟩
    funext w
    rw [Bimachine.eval_eq_evalFrom]
    cases w with
    | nil => simp [swapBM, swapFirstLast]
    | cons a w =>
      rw [show (swapBM (A := A)).prefixInit = none from rfl, evalFrom_cons', swapBM_sfx_cons]
      rw [show (swapBM (A := A)).prefixStep none a = some a from rfl, swapBM_evalFrom_some]
      cases w with
      | nil => simp [swapBM, swapFirstLast]
      | cons b w => simp [swapBM, swapFirstLast, List.getLast_cons]
  exact ⟨hbm, rationalFun_of_isBimachine hbm⟩

end SwapFirstLast

section LastHash

variable {A : Type} [DecidableEq A]

/-- The function of the third item of Exercise `exer:examples-of-rational-fun`: the input is copied
up to and including the last `hash`, and every letter after that is replaced by `hash`.  Equivalently
— and this is the form used here, which is the observation of the author's solution — a letter is
copied exactly when the suffix that begins at its position contains a `hash`.  The convention for an
input without any `hash` is the author's: all of its letters are replaced by `hash`. -/
def upToLastHash (hash : A) : List A → List A
  | [] => []
  | a :: w => (if hash ∈ a :: w then a else hash) :: upToLastHash hash w

/-- On a string without any `hash`, every letter is replaced by `hash`. -/
lemma upToLastHash_of_not_mem (hash : A) {w : List A} (h : hash ∉ w) :
    upToLastHash hash w = w.map (fun _ => hash) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [upToLastHash, if_neg h, ih (fun hw => h (List.mem_cons_of_mem a hw))]
    simp

/-- The function copies the input up to and including the last `hash`, and replaces every later
letter by `hash`. -/
lemma upToLastHash_split (hash : A) (u v : List A) (hv : hash ∉ v) :
    upToLastHash hash (u ++ hash :: v) = u ++ hash :: v.map (fun _ => hash) := by
  induction u with
  | nil =>
    rw [List.nil_append, upToLastHash, if_pos (by simp), upToLastHash_of_not_mem hash hv]
    simp
  | cons a u ih =>
    rw [List.cons_append, upToLastHash, if_pos (by simp), ih]
    simp

/-- The bimachine for the third item of Exercise `exer:examples-of-rational-fun`.  The prefix
automaton is not needed; the suffix automaton remembers the first letter of the suffix and whether
the suffix contains a `hash`. -/
def lastHashBM (hash : A) : Bimachine A A Unit (Option (A × Bool)) where
  prefixInit := ()
  prefixStep := fun _ _ => ()
  suffixInit := none
  suffixStep := fun s a => some (a, decide (a = hash) || s.elim false (·.2))
  out := fun _ s =>
    match s with
    | none => []
    | some (f, c) => if c then [f] else [hash]

lemma lastHashBM_sfx_cons (hash : A) (a : A) (w : List A) :
    BimachIndex.sfx (lastHashBM hash) (a :: w) = some (a, decide (hash ∈ a :: w)) := by
  induction w generalizing a with
  | nil => simp [BimachIndex.sfx, lastHashBM, strTrans, eq_comm]
  | cons b w ih =>
    rw [sfx_cons, ih b]
    simp [lastHashBM, eq_comm]

lemma lastHashBM_evalFrom (hash : A) (p : Unit) (w : List A) :
    (lastHashBM hash).evalFrom p w = upToLastHash hash w := by
  induction w with
  | nil => simp [lastHashBM, upToLastHash]
  | cons a w ih =>
    rw [evalFrom_cons', lastHashBM_sfx_cons, ih]
    by_cases h : hash ∈ a :: w <;> simp [lastHashBM, upToLastHash, h]

/-- **Exercise `exer:examples-of-rational-fun`, third item.**  Copying the input up to the last
`hash` and replacing every later letter by `hash` is computed by a bimachine and is a rational
function. -/
theorem isBimachine_isRationalFun_upToLastHash [Finite A] (hash : A) :
    IsBimachine (upToLastHash hash) ∧ IsRationalFun (upToLastHash hash) := by
  have hbm : IsBimachine (upToLastHash hash) :=
    ⟨Unit, Option (A × Bool), inferInstance, inferInstance, lastHashBM hash,
      funext fun w => lastHashBM_evalFrom hash _ w⟩
  exact ⟨hbm, rationalFun_of_isBimachine hbm⟩

end LastHash

/-! ### Exercise `exer:non-rational` -/

/-- The first half of a string, rounded up. -/
def firstHalf {A : Type} (w : List A) : List A := w.take ((w.length + 1) / 2)

/-- The first half of `falseⁱ trueʲ` uses the letter `false` only exactly when `j ≤ i`. -/
lemma firstHalf_replicate (i j : ℕ) :
    (∀ x ∈ firstHalf (List.replicate i false ++ List.replicate j true), x = false) ↔ j ≤ i := by
  have hsplit : firstHalf (List.replicate i false ++ List.replicate j true)
      = List.replicate (min ((i + j + 1) / 2) i) false
        ++ List.replicate (min ((i + j + 1) / 2 - i) j) true := by
    rw [firstHalf, List.take_append, List.take_replicate, List.take_replicate]
    simp
  rw [hsplit]
  constructor
  · intro hall
    by_contra hij
    have hpos : min ((i + j + 1) / 2 - i) j ≠ 0 := by omega
    have htf : (true : Bool) = false :=
      hall true (List.mem_append_right _ (List.mem_replicate.2 ⟨hpos, rfl⟩))
    exact absurd htf (by simp)
  · intro hij x hx
    have h0 : min ((i + j + 1) / 2 - i) j = 0 := by omega
    rw [h0, List.replicate_zero, List.append_nil] at hx
    exact List.eq_of_mem_replicate hx

/-- **Exercise `exer:non-rational`, first item.**  The function that returns the first half of its
input, rounded up, is not rational.

This is the author's solution.  The function is not continuous, so it is not rational by Theorem
`thm:continuity-rational-relations`: the inverse image of the regular language `false*` meets the
regular language `false* true*` in `{ falseⁱ trueʲ | j ≤ i }`, which is not regular. -/
theorem not_isRationalFun_firstHalf : ¬ IsRationalFun (firstHalf : List Bool → List Bool) := by
  intro hf
  have hK := (continuous_of_isRationalFun hf _
    (isRegular_forall_mem (fun a : Bool => a = false))).inf isRegular_sortedBool
  have heq : ({w : List Bool | firstHalf w ∈ ({u : List Bool | ∀ a ∈ u, a = false} : Language Bool)}
        : Language Bool)
      ⊓ ({u : List Bool | ∃ n m, u = List.replicate n false ++ List.replicate m true}
        : Language Bool)
      = atMostAsMany := by
    ext w
    constructor
    · rintro ⟨h1, p, q, rfl⟩
      exact ⟨p, q, (firstHalf_replicate p q).1 h1, rfl⟩
    · rintro ⟨p, q, hpq, rfl⟩
      exact ⟨(firstHalf_replicate p q).2 hpq, p, q, rfl⟩
  rw [heq] at hK
  exact not_isRegular_atMostAsMany hK

/-- **Exercise `exer:non-rational`, second item.**  The duplicating function `w ↦ w w` is not
rational over a two-letter alphabet.

This is the author's solution: a rational relation maps a regular language to a regular language —
here the second item of Exercise `exer:regular-languages-for-rational-relations`, applied to the
whole of `A*` — and the image of the duplicating function is the language of the squares `{ u u }`,
which is not regular.  As the author remarks, the restriction to at least two letters is necessary:
over a one-letter alphabet duplication is the homomorphism `a ↦ a a`, which is rational. -/
theorem not_isRationalFun_duplicate : ¬ IsRationalFun (fun w : List Bool => w ++ w) := by
  intro hf
  have hrange := rationalRel_range_isRegular hf
  exact not_isRegular_square hrange

/-! ### Exercise `exer:decide-rational-colision` -/

/-- **Exercise `exer:decide-rational-colision`, item (a).**  It is undecidable whether two rational
functions have the same output on some input.

As for the numbered results of Part B, a decision problem about rational functions is a problem
about their finite descriptions, the codes `Transducers.RelCode`, under the promise that they
describe functions (`Transducers.CodeFunctional`), and the undecidability of the Post
correspondence problem is now itself proved, as
`Transducers.PCP.solvable_not_computablePred` (`RequestProject/PCP/Index.lean`), so this
exercise is unconditional, exactly as Theorem
`thm:undecidable-equivalence-rational-relations` now is.

The reduction is the author's, and is carried out in `RequestProject/Exercises/PartBCPCP.lean`:
the two homomorphisms of an instance of the Post correspondence problem are turned into rational
functions, which — as the author points out — must be given different outputs on the empty input,
since two homomorphisms always agree there; a rational function can do this because it treats the
empty input separately.  The two functions then collide exactly when the instance is solvable.

Item (b) of the exercise, the decidability of the existence of an input on which the two outputs
have the same length, is not formalised: its solution goes through the semilinearity of Parikh
images of regular languages, which this project does not have. -/
theorem rationalFun_collision_undecidable :
    ¬ DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => ∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v) :=
  collision_undecidable_aux PCP.solvable_not_computablePred

/-! ### Exercise `exer:rational-one-letter-input` -/

open Unary in
/-- **Exercise `exer:rational-one-letter-input`.**  The graph of a rational function whose input
alphabet has one letter is a finite union of sets of the form

  `{ (aᵅ⁺ᵝᵏ, x yᵏ z) | k ∈ ℕ }`,

with natural coefficients `α`, `β` and strings `x`, `y`, `z` over the output alphabet.

The one-letter input alphabet is `Unit`; any one-letter alphabet is isomorphic to it.  The finite
union is indexed by `Fin n`, the input `aⁿ` is `List.replicate n ()`, and the repetition `yᵏ` is
`(List.replicate k y).flatten`, since strings are lists here.  The output alphabet is assumed
finite, as everywhere in the book, because Theorem `thm:bimachines` is used.

The proof is the author's.  A bimachine computing the function exists by Theorem `thm:bimachines`
(`Transducers.isBimachine_of_rationalFun`).  Over a one-letter alphabet its prefix and suffix
automata are deterministic automata with one letter, so their runs are eventually periodic with a
common threshold `lam` and period `per`; the pieces of the first `lam` gaps and of the last `lam`
gaps then depend only on the length modulo `per`, and each further period of length `per` inserts
one more group of `per` gaps in the middle, producing the same string as the other such groups.
This is `Transducers.Exercises.Unary.eval_replicate_period`, in
`RequestProject/Exercises/PartBCUnary.lean`; the inputs shorter than `2 * lam + per` are the
finitely many members of the union that have `β = 0`. -/
theorem rationalFun_unary_graph {B : Type} [Finite B] {f : List Unit → List B}
    (hf : IsRationalFun f) :
    ∃ (n : ℕ) (al be : Fin n → ℕ) (x y z : Fin n → List B),
      {p : List Unit × List B | f p.1 = p.2} =
        {p | ∃ (i : Fin n) (k : ℕ),
          p.1 = List.replicate (al i + be i * k) () ∧
          p.2 = x i ++ (List.replicate k (y i)).flatten ++ z i} := by
  obtain ⟨P, S, hP, hS, M, hM⟩ := isBimachine_of_rationalFun hf
  obtain ⟨lam, per, hper, hp, hs⟩ := exists_periodicity M
  have key : ∀ i k : ℕ, f (List.replicate (i + coefB lam per i * k) ()) =
      wordX M lam per i ++ (List.replicate k (wordY M lam per i)).flatten ++ wordZ M lam per i := by
    intro i k
    rw [← hM]
    exact eval_eq_wordX hp hs i k
  refine ⟨2 * lam + per + per, fun i => i.val, fun i => coefB lam per i.val,
    fun i => wordX M lam per i.val, fun i => wordY M lam per i.val,
    fun i => wordZ M lam per i.val, ?_⟩
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hfp
    obtain ⟨i, hi, k, hik⟩ := exists_index lam per hper p.1.length
    have hp1 : p.1 = List.replicate (i + coefB lam per i * k) () := by
      rw [hik]; exact eq_replicate_unit p.1
    exact ⟨⟨i, hi⟩, k, hp1, by rw [← hfp, hp1]; exact key i k⟩
  · rintro ⟨i, k, h1, h2⟩
    rw [h1, h2]
    exact key i.val k

/-! ### Exercise `exer:function-that-is-not-rational` -/

section Reversal

variable {A B P S : Type}

/-- The bimachine with the prefix and the suffix automata swapped, and with the two arguments of
the output function swapped.  This is the construction of the author's solution. -/
def swapBimachine (M : Bimachine A B P S) : Bimachine A B S P where
  prefixInit := M.suffixInit
  prefixStep := M.suffixStep
  suffixInit := M.prefixInit
  suffixStep := M.prefixStep
  out := fun s p => M.out p s

private lemma sum_range_reflect' (n : ℕ) (f : ℕ → ℕ) :
    ((List.range (n + 1)).map f).sum = ((List.range (n + 1)).map (fun j => f (n - j))).sum := by
  show (∑ i ∈ Finset.range (n + 1), f i) = ∑ i ∈ Finset.range (n + 1), f (n - i)
  rw [← Finset.sum_range_reflect (fun i => f i) (n + 1)]
  simp

/-- Reversing the input is a bijection on the gaps of the input string which swaps the prefix with
the suffix.  So the swapped bimachine produces on `w` exactly the pieces that the original
bimachine produces on `w.reverse`, in the opposite order; in particular the two outputs have the
same length. -/
lemma length_eval_swapBimachine (M : Bimachine A B P S) (w : List A) :
    ((swapBimachine M).eval w).length = (M.eval w.reverse).length := by
  set n := w.length with hn
  set piece : ℕ → List B := fun i =>
    M.out (strTrans M.prefixStep (w.drop i).reverse M.prefixInit)
      (strTrans M.suffixStep (w.take i) M.suffixInit) with hpiece
  have h1 : (swapBimachine M).eval w = ((List.range (n + 1)).map piece).flatten := rfl
  have h2 : M.eval w.reverse = ((List.range (n + 1)).map (fun j => piece (n - j))).flatten := by
    have hlen : w.reverse.length = n := by simp [hn]
    rw [Bimachine.eval, hlen]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [hpiece, List.take_reverse, List.drop_reverse, ← hn]
  rw [h1, h2, List.length_flatten, List.length_flatten, List.map_map, List.map_map]
  exact sum_range_reflect' n (fun i => (piece i).length)

/-- **Exercise `exer:function-that-is-not-rational`.**  There is a function which is not rational,
yet whose composition with every rational function into a one-letter output alphabet is rational.

The author's witness is string reversal.  That reversal is not rational is Example
`ex:string-reversal-not-rational` of the main text, which is not part of this formalisation; it is
therefore taken here as the explicit hypothesis `hrev`, and everything else in the exercise is
proved.  The rest is the author's solution: a rational `g` into `1*` is computed by a bimachine
(Theorem `thm:bimachines`), and the bimachine with its prefix and suffix automata swapped computes
`g` on the reversed input, because it produces the same pieces of output in the opposite order,
which is invisible over a one-letter alphabet. -/
theorem exists_not_isRationalFun_unary_compositions_rational
    (hrev : ¬ IsRationalFun (List.reverse : List Bool → List Bool)) :
    ∃ f : List Bool → List Bool, ¬ IsRationalFun f ∧
      ∀ g : List Bool → List Unit, IsRationalFun g → IsRationalFun (g ∘ f) := by
  refine ⟨List.reverse, hrev, fun g hg => ?_⟩
  obtain ⟨P, S, hP, hS, M, hM⟩ := isBimachine_of_rationalFun hg
  refine rationalFun_of_isBimachine ⟨S, P, hS, hP, swapBimachine M, ?_⟩
  funext w
  show (swapBimachine M).eval w = g w.reverse
  rw [← hM]
  exact (list_unit_eq_iff _ _).2 (length_eval_swapBimachine M w)

end Reversal

/-! ### Exercise `exer:some-ideals` -/

section Ideals

/-- **Ideals of rational functions**, as the series of exercises that begins with
`exer:some-ideals` defines them: a family `I` of rational functions, one class for every pair of
alphabets, with `I = Rational · I · Rational`.  The inclusion from right to left is the content of
the definition — a function that factors through the ideal stays in it — and the inclusion from
left to right is automatic, since the identity is rational; so it is the closure property that is
stated here, together with the requirement that the members of an ideal are rational functions.
All alphabets are finite, as they are everywhere in the book. -/
def IsIdeal (I : ∀ (A B : Type), (List A → List B) → Prop) : Prop :=
  (∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), I A B f → IsRationalFun f) ∧
  (∀ (A B C D : Type) [Finite A] [Finite B] [Finite C] [Finite D]
      (g : List A → List B) (f : List B → List C) (h : List C → List D),
      IsRationalFun g → I B C f → IsRationalFun h → I A D (h ∘ f ∘ g))

/-- The rational functions whose range has at most `k` elements. -/
def RangeAtMost (k : ℕ) : ∀ (A B : Type), (List A → List B) → Prop := fun _ _ f =>
  IsRationalFun f ∧ (Set.range f).Finite ∧ (Set.range f).ncard ≤ k

/-- The rational functions with `O(n^k)` outputs: the number of outputs on the inputs of length at
most `n` is bounded by `C·(n+1)^k` for some constant `C`. -/
def OutputsPoly (k : ℕ) : ∀ (A B : Type), (List A → List B) → Prop := fun A _ f =>
  IsRationalFun f ∧
    ∃ C : ℕ, ∀ n : ℕ, (f '' {w : List A | w.length ≤ n}).ncard ≤ C * (n + 1) ^ k

/-- A rational function does not increase the length of its input by more than an affine function:
this is the second condition of Exercise `exer:rational-output-size`, for the graph of a
function. -/
lemma exists_affine_bound {A B : Type} [Finite A] [Finite B] {g : List A → List B}
    (hg : IsRationalFun g) : ∃ c d : ℕ, ∀ w, (g w).length ≤ c * w.length + d := by
  obtain ⟨c, d, hcd⟩ := (rationalRel_finiteOutputs_iff_affine hg).1
    (fun w => Set.Finite.subset (Set.finite_singleton (g w)) (fun v hv => hv))
  exact ⟨c, d, fun w => hcd w (g w) rfl⟩

/-- **Exercise `exer:some-ideals`, first item.**  For every `k`, the rational functions whose range
has at most `k` elements form an ideal.

This is the author's argument: pre-composing or post-composing with any function cannot increase
the size of the range. -/
theorem isIdeal_rangeAtMost (k : ℕ) : IsIdeal (RangeAtMost k) := by
  refine ⟨fun A B _ _ f hf => hf.1, ?_⟩
  intro A B C D _ _ _ _ g f h hg ⟨hf, hfin, hcard⟩ hh
  have hsub : Set.range (h ∘ f ∘ g) ⊆ h '' Set.range f := by
    rintro y ⟨w, rfl⟩
    exact ⟨f (g w), ⟨g w, rfl⟩, rfl⟩
  have himg : (h '' Set.range f).Finite := hfin.image h
  have hfg : IsRationalFun (fun w => f (g w)) := isRationalFun_comp hg hf
  have hcomp := isRationalFun_comp hfg hh
  exact ⟨hcomp, himg.subset hsub,
    le_trans (Set.ncard_le_ncard hsub himg) (le_trans (Set.ncard_image_le hfin) hcard)⟩

/-- **Exercise `exer:some-ideals`, second item.**  For every `k`, the rational functions with
`O(n^k)` outputs form an ideal.

This is the author's argument.  Post-composition cannot increase the number of outputs.  For
pre-composition, the output length of a rational function is bounded by an affine function of the
input length (Exercise `exer:rational-output-size`), so the inputs of length at most `n` are sent
into the inputs of length at most `c·n + d`, and `(c·n + d + 1)^k ≤ (c + d + 1)^k · (n+1)^k`, which
leaves the degree of the polynomial unchanged. -/
theorem isIdeal_outputsPoly (k : ℕ) : IsIdeal (OutputsPoly k) := by
  refine ⟨fun A B _ _ f hf => hf.1, ?_⟩
  intro A B C D _ _ _ _ g f h hg ⟨hf, Cc, hC⟩ hh
  obtain ⟨c, d, hcd⟩ := exists_affine_bound hg
  have hfg : IsRationalFun (fun w => f (g w)) := isRationalFun_comp hg hf
  have hcomp := isRationalFun_comp hfg hh
  refine ⟨hcomp, Cc * (c + d + 1) ^ k, fun n => ?_⟩
  have hfinite : ({u : List B | u.length ≤ c * n + d}).Finite := finite_lists_length_le _
  have hsub : (h ∘ f ∘ g) '' {w : List A | w.length ≤ n}
      ⊆ h '' (f '' {u : List B | u.length ≤ c * n + d}) := by
    rintro y ⟨w, hw, rfl⟩
    have : (g w).length ≤ c * n + d :=
      le_trans (hcd w) (by exact Nat.add_le_add_right (Nat.mul_le_mul_left c hw) d)
    exact ⟨f (g w), ⟨g w, this, rfl⟩, rfl⟩
  have himg : (h '' (f '' {u : List B | u.length ≤ c * n + d})).Finite :=
    (hfinite.image f).image h
  have h1 : ((h ∘ f ∘ g) '' {w : List A | w.length ≤ n}).ncard
      ≤ (f '' {u : List B | u.length ≤ c * n + d}).ncard :=
    le_trans (Set.ncard_le_ncard hsub himg) (Set.ncard_image_le (hfinite.image f))
  have h2 : (c * n + d + 1) ^ k ≤ ((c + d + 1) * (n + 1)) ^ k :=
    Nat.pow_le_pow_left (by nlinarith) k
  calc ((h ∘ f ∘ g) '' {w : List A | w.length ≤ n}).ncard
      ≤ (f '' {u : List B | u.length ≤ c * n + d}).ncard := h1
    _ ≤ Cc * (c * n + d + 1) ^ k := hC (c * n + d)
    _ ≤ Cc * ((c + d + 1) * (n + 1)) ^ k := Nat.mul_le_mul_left _ h2
    _ = Cc * (c + d + 1) ^ k * (n + 1) ^ k := by rw [Nat.mul_pow, Nat.mul_assoc]

/-- The ideal `OutputsPoly 0` is the class of the rational functions with finitely many outputs, as
the author observes at the beginning of his solution to Exercise `exer:some-ideals`. -/
theorem outputsPoly_zero_iff_finite_range {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : OutputsPoly 0 A B f ↔ IsRationalFun f ∧ (Set.range f).Finite := by
  constructor
  · rintro ⟨hrat, C, hC⟩
    refine ⟨hrat, ?_⟩
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq (C + 1)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ y ∈ t, ∃ w, w.length ≤ n ∧ f w = y := by
      classical
      refine ⟨(t.attach.image fun y => (Classical.choose (hts y.2) : List A).length).sup id,
        fun y hy => ?_⟩
      refine ⟨Classical.choose (hts hy), ?_, Classical.choose_spec (hts hy)⟩
      exact Finset.le_sup (f := id) (Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩)
    have hsub : (t : Set (List B)) ⊆ f '' {w : List A | w.length ≤ n} := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := hn y hy
      exact ⟨w, hw, rfl⟩
    have hfin : (f '' {w : List A | w.length ≤ n}).Finite :=
      (finite_lists_length_le n).image f
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, htc] at this
    exact absurd (le_trans this (hC n)) (by simp)
  · rintro ⟨hrat, hfin⟩
    refine ⟨hrat, (Set.range f).ncard, fun n => ?_⟩
    have hsub : f '' {w : List A | w.length ≤ n} ⊆ Set.range f := by
      rintro y ⟨w, -, rfl⟩
      exact ⟨w, rfl⟩
    simpa using Set.ncard_le_ncard hsub hfin

/-! ### Exercise `exer:finite-range-ideals` -/

/-- The key step of the author's solution to Exercise `exer:finite-range-ideals`: if an ideal
contains a function `f` with finitely many outputs, then it contains every rational function `g`
whose number of outputs is at most that of `f`.

This is the author's construction.  Choose an injection of the outputs `v_1, …, v_ℓ` of `g` into
the outputs `f(w_1), …, f(w_k)` of `f`; then `g` is obtained by first applying `g` with each output
`v_i` replaced by a preimage `w_i` under `f`, then applying `f`, and finally replacing `f(w_i)` by
`v_i`.  The first and the third step are finite case distinctions on strings, hence rational, so
`g` factors through `f` and therefore belongs to the ideal. -/
theorem ideal_mem_of_ncard_le {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I)
    {A B C D : Type} [Finite A] [Finite B] [Finite C] [Finite D]
    {f : List A → List B} {g : List C → List D}
    (hf : I A B f) (hfr : (Set.range f).Finite)
    (hg : IsRationalFun g) (hgr : (Set.range g).Finite)
    (hcard : (Set.range g).ncard ≤ (Set.range f).ncard) :
    I C D g := by
  classical
  have hcard' : hgr.toFinset.card ≤ hfr.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hgr, ← Set.ncard_eq_toFinset_card _ hfr]
    exact hcard
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard'
  let e := Finset.equivOfCardEq htc.symm
  let psi : List D → List B :=
    fun v => if h : v ∈ hgr.toFinset then ((e ⟨v, h⟩ : {x // x ∈ t}) : List B) else []
  let pre : List B → List A := fun b => if h : ∃ a, f a = b then h.choose else []
  have hpre : ∀ b, (∃ a, f a = b) → f (pre b) = b := by
    intro b hb
    simp only [pre, dif_pos hb]
    exact hb.choose_spec
  let g1 : List D → List A := fun v => if v ∈ hgr.toFinset then pre (psi v) else []
  let phi2 : List B → List D :=
    fun b => if hb : b ∈ t then ((e.symm ⟨b, hb⟩ : {x // x ∈ hgr.toFinset}) : List D) else []
  let h2 : List B → List D := fun b => if b ∈ t then phi2 b else []
  have hg1 : IsRationalFun g1 := isRationalFun_finsetCases _ _
  have hh2 : IsRationalFun h2 := isRationalFun_finsetCases _ _
  have hg' : IsRationalFun (fun c => g1 (g c)) := isRationalFun_comp hg hg1
  have hkey : ∀ c : List C, h2 (f (g1 (g c))) = g c := by
    intro c
    have hv : g c ∈ hgr.toFinset := hgr.mem_toFinset.2 ⟨c, rfl⟩
    have hb : ((e ⟨g c, hv⟩ : {x // x ∈ t}) : List B) ∈ t := (e ⟨g c, hv⟩).2
    have hbf : ∃ a, f a = ((e ⟨g c, hv⟩ : {x // x ∈ t}) : List B) :=
      hfr.mem_toFinset.1 (hts hb)
    have h1 : g1 (g c) = pre ((e ⟨g c, hv⟩ : {x // x ∈ t}) : List B) := by
      simp only [g1, if_pos hv, psi, dif_pos hv]
    rw [h1, hpre _ hbf]
    have h3 : (⟨((e ⟨g c, hv⟩ : {x // x ∈ t}) : List B), hb⟩ : {x // x ∈ t}) = e ⟨g c, hv⟩ := rfl
    simp only [h2, if_pos hb, phi2, dif_pos hb, h3, Equiv.symm_apply_apply]
  have := hI.2 C A B D (fun c => g1 (g c)) f h2 hg' hf hh2
  have heq : (h2 ∘ f ∘ fun c => g1 (g c)) = g := funext hkey
  exact heq ▸ this

/-- The set of the sizes of the ranges of the functions of a family `I`, over all pairs of
alphabets.  It is used to state the classification of Exercise `exer:finite-range-ideals`. -/
def IdealRangeSizes (I : ∀ (A B : Type), (List A → List B) → Prop) : Set ℕ :=
  {n | ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B),
        I A B f ∧ (Set.range f).ncard = n}

/-- **Exercise `exer:finite-range-ideals`.**  An ideal in which every function has a finite range
is one of the ideals `RangeAtMost k` of the first item of Exercise `exer:some-ideals`, or the ideal
`OutputsPoly 0` of the second item.

This is the author's argument.  By `ideal_mem_of_ncard_le` the ideal is determined by the set of
sizes of the ranges of its members.  If that set is bounded then it has a largest element `k`,
which is attained, and the ideal is `RangeAtMost k`; the empty ideal is covered by `k = 0`, since a
function has at least one output and `RangeAtMost 0` is therefore empty as well.  If the set is
unbounded, then every rational function with a finite range is dominated by a member of the ideal
and hence belongs to it, so the ideal consists of all rational functions with finitely many
outputs, which is `OutputsPoly 0` by `outputsPoly_zero_iff_finite_range`. -/
theorem finite_range_ideal_classification
    {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I)
    (hfin : ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
      I A B f → (Set.range f).Finite) :
    (∃ k : ℕ, ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ RangeAtMost k A B f) ∨
      (∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ OutputsPoly 0 A B f) := by
  classical
  by_cases hbdd : BddAbove (IdealRangeSizes I)
  · left
    by_cases hne : (IdealRangeSizes I).Nonempty
    · obtain ⟨A₀, B₀, i₁, i₂, f₀, hf₀, hc₀⟩ := Nat.sSup_mem hne hbdd
      haveI := i₁; haveI := i₂
      refine ⟨sSup (IdealRangeSizes I), fun A B _ _ f => ⟨fun hfI => ?_, fun hf => ?_⟩⟩
      · exact ⟨hI.1 A B f hfI, hfin A B f hfI,
          le_csSup hbdd ⟨A, B, ‹Finite A›, ‹Finite B›, f, hfI, rfl⟩⟩
      · exact ideal_mem_of_ncard_le hI hf₀ (hfin _ _ _ hf₀) hf.1 hf.2.1 (by rw [hc₀]; exact hf.2.2)
    · refine ⟨0, fun A B _ _ f => ⟨fun hfI => ?_, fun hf => ?_⟩⟩
      · exact absurd ⟨_, ⟨A, B, ‹Finite A›, ‹Finite B›, f, hfI, rfl⟩⟩ hne
      · have : 0 < (Set.range f).ncard := Set.ncard_pos hf.2.1 |>.2 ⟨f [], ⟨[], rfl⟩⟩
        exact absurd hf.2.2 (by omega)
  · right
    intro A B _ _ f
    refine ⟨fun hfI => (outputsPoly_zero_iff_finite_range f).2 ⟨hI.1 _ _ _ hfI, hfin _ _ _ hfI⟩,
      fun hpoly => ?_⟩
    obtain ⟨hrat, hfinr⟩ := (outputsPoly_zero_iff_finite_range f).1 hpoly
    obtain ⟨n, ⟨A₀, B₀, i₁, i₂, f₀, hf₀, rfl⟩, hlt⟩ :=
      not_bddAbove_iff.1 hbdd ((Set.range f).ncard)
    haveI := i₁; haveI := i₂
    exact ideal_mem_of_ncard_le hI hf₀ (hfin _ _ _ hf₀) hrat hfinr hlt.le

end Ideals

/-! ### Exercise `exer:surjective-rational-function` -/

/-- **Exercise `exer:surjective-rational-function`.**  A surjective rational function `f : A* → B*`
has a rational one-sided inverse: a rational function `g : B* → A*` with `f (g v) = v` for every
`v`, which is the book's `g · f = id` (the book composes from left to right).

This is the author's solution: the inverse relation is rational by the symmetry of rational
relations with respect to input and output, and it is total because `f` is surjective, so the
Uniformisation Lemma `lem:uniformisation` — in the form
`Transducers.exists_rationalFun_of_total_rel` — provides a rational function contained in it. -/
theorem exists_rationalFun_leftInverse {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hsurj : Function.Surjective f) :
    ∃ g : List B → List A, IsRationalFun g ∧ ∀ v, f (g v) = v := by
  obtain ⟨g, hg, hgspec⟩ :=
    exists_rationalFun_of_total_rel (isRationalRel_inv hf)
      (fun v => (hsurj v).imp (fun w hw => hw.symm))
  exact ⟨g, hg, fun v => (hgspec v).symm⟩

/-! ## Regular functions (`regular-primes.tex`) -/

/-! ### Exercise `exer:two-letter-alphabet-suffices` -/

section TwoLetterAlphabet

/-- The prime regular functions of Definition `def:regular-functions`, with map reverse and map
duplicate restricted to the two-letter alphabet `Bool`: the alphabet of the two prime functions
is `Bool + 1`, which is expressed by the bijections `e` and `e'` with `Option Bool`. -/
def RegularFam2 : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRationalFun f ∨
  (∃ (e : A ≃ Option Bool) (e' : B ≃ Option Bool),
      ∀ w, f w = (mapReverse Bool (w.map e)).map e'.symm) ∨
  (∃ (e : A ≃ Option Bool) (e' : B ≃ Option Bool),
      ∀ w, f w = (mapDuplicate Bool (w.map e)).map e'.symm)

/-- A prime regular function over a two-letter alphabet is a prime regular function. -/
lemma regularFam_of_regularFam2 {A B : Type} {f : List A → List B} (h : RegularFam2 A B f) :
    RegularFam A B f := by
  rcases h with h | ⟨e, e', hf⟩ | ⟨e, e', hf⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨Bool, e, e', hf⟩)
  · exact Or.inr (Or.inr ⟨Bool, e, e', hf⟩)

/-- Map duplicate over the two-letter alphabet is a prime function of the restricted family. -/
lemma regularFam2_mapDuplicate :
    RegularFam2 (Option Bool) (Option Bool) (mapDuplicate Bool) :=
  Or.inr (Or.inr ⟨Equiv.refl _, Equiv.refl _, fun w => by simp⟩)

/-- Map reverse over the two-letter alphabet is a prime function of the restricted family. -/
lemma regularFam2_mapReverse :
    RegularFam2 (Option Bool) (Option Bool) (mapReverse Bool) :=
  Or.inr (Or.inl ⟨Equiv.refl _, Equiv.refl _, fun w => by simp⟩)

/-- A rational function belongs to the composition closure of the restricted family. -/
lemma compClosure2_of_rational {A B : Type} {f : List A → List B} (hf : IsRationalFun f) :
    CompClosure RegularFam2 A B f :=
  CompClosure.base (Or.inl hf)

/-- **Map duplicate over an arbitrary finite alphabet is a composition of rational functions and
of map duplicate over a two-letter alphabet.** -/
theorem compClosure2_mapDuplicate (A₀ : Type) [Finite A₀] :
    CompClosure RegularFam2 (Option A₀) (Option A₀) (mapDuplicate A₀) := by
  have henc : CompClosure RegularFam2 (Option A₀) (Option Bool)
      (mapLift (homOf (TwoLetter.code : A₀ → List Bool))) :=
    compClosure2_of_rational (isRationalFun_mapLift (isRationalFun_homOf _))
  have hdec : CompClosure RegularFam2 (Option Bool) (Option A₀)
      (mapLift (TwoLetter.decBlock A₀)) :=
    compClosure2_of_rational (isRationalFun_mapLift TwoLetter.isRationalFun_decBlock)
  have h := (henc.comp (CompClosure.base regularFam2_mapDuplicate)).comp hdec
  have he : mapLift (TwoLetter.decBlock A₀) ∘ (mapDuplicate Bool ∘
      mapLift (homOf (TwoLetter.code : A₀ → List Bool))) = mapDuplicate A₀ :=
    funext fun w => TwoLetter.mapDuplicate_decomp w
  exact he ▸ h

/-- **Map reverse over an arbitrary finite alphabet is a composition of rational functions and
of map reverse over a two-letter alphabet.** -/
theorem compClosure2_mapReverse (A₀ : Type) [Finite A₀] :
    CompClosure RegularFam2 (Option A₀) (Option A₀) (mapReverse A₀) := by
  have henc : CompClosure RegularFam2 (Option A₀) (Option Bool)
      (mapLift (homOf (TwoLetter.codeRev : A₀ → List Bool))) :=
    compClosure2_of_rational (isRationalFun_mapLift (isRationalFun_homOf _))
  have hdec : CompClosure RegularFam2 (Option Bool) (Option A₀)
      (mapLift (TwoLetter.decBlock A₀)) :=
    compClosure2_of_rational (isRationalFun_mapLift TwoLetter.isRationalFun_decBlock)
  have h := (henc.comp (CompClosure.base regularFam2_mapReverse)).comp hdec
  have he : mapLift (TwoLetter.decBlock A₀) ∘ (mapReverse Bool ∘
      mapLift (homOf (TwoLetter.codeRev : A₀ → List Bool))) = mapReverse A₀ :=
    funext fun w => TwoLetter.mapReverse_decomp w
  exact he ▸ h

/-- Every regular function between finite alphabets is a composition of rational functions and of
the two prime functions over a two-letter alphabet.  The finiteness of the two alphabets is
carried as an explicit hypothesis, so that the induction on the composition tree has access to
the finiteness of the intermediate alphabets. -/
theorem compClosure2_of_isRegularFun {A B : Type} {f : List A → List B} (hf : IsRegularFun f) :
    Finite A → Finite B → CompClosure RegularFam2 A B f := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact compClosure2_of_rational hrat
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 := compClosure2_of_rational (isRationalFun_map (e : A → Option A₀))
        have h3 := compClosure2_of_rational (isRationalFun_map (e'.symm : Option A₀ → B))
        have h := (h1.comp (compClosure2_mapReverse A₀)).comp h3
        have he : (fun w : List A => (mapReverse A₀ (w.map e)).map e'.symm) = f :=
          funext fun w => (hfe w).symm
        exact he ▸ h
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 := compClosure2_of_rational (isRationalFun_map (e : A → Option A₀))
        have h3 := compClosure2_of_rational (isRationalFun_map (e'.symm : Option A₀ → B))
        have h := (h1.comp (compClosure2_mapDuplicate A₀)).comp h3
        have he : (fun w : List A => (mapDuplicate A₀ (w.map e)).map e'.symm) = f :=
          funext fun w => (hfe w).symm
        exact he ▸ h
  | id A => intro _ _; exact CompClosure.id A
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      exact CompClosure.comp (ihf hA hB) (ihg hB hC)

/-- **Exercise `exer:two-letter-alphabet-suffices`.**  In Definition `def:regular-functions`, map
reverse and map duplicate are taken over arbitrary alphabets of the form `A + 1`.  The class of
regular functions does not change if only two-letter alphabets `A` are used.

The exercise is stated for functions between finite alphabets: the composition closure of
Definition `def:regular-functions` requires the intermediate alphabets to be finite, but not the
input and the output alphabets, and over an infinite alphabet the prime functions cannot be
simulated over a two-letter one. -/
theorem isRegularFun_iff_compClosure2 {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRegularFun f ↔ CompClosure RegularFam2 A B f := by
  constructor
  · intro hf
    exact compClosure2_of_isRegularFun hf ‹_› ‹_›
  · intro hf
    induction hf with
    | base h => exact CompClosure.base (regularFam_of_regularFam2 h)
    | id A => exact CompClosure.id A
    | comp _ _ ihf ihg => exact CompClosure.comp ihf ihg

end TwoLetterAlphabet

/-! ## Logic (`logic.tex`) -/

/-! ### Exercise `exer:mealy-as-restricted-mso-relabelling` -/

section MealyRelabelling

variable {A B : Type}

/-- The three additional restrictions that Exercise `exer:mealy-as-restricted-mso-relabelling`
imposes on Definition `def:mso-relabeling`. -/
structure RestrictedRelabelling (R : MSORelabelling A B) : Prop where
  /-- The string for the empty input is empty. -/
  emptyOut : R.emptyOut = []
  /-- The output map sends every formula to a one-letter string. -/
  out_length : ∀ i, (R.out i).length = 1
  /-- The formulas depend only on the past: whether a formula holds in a position of the input
  string depends only on the prefix up to and including that position. -/
  past : ∀ (w w' : List A) (p : ℕ), p < w.length → p < w'.length →
    w.take (p + 1) = w'.take (p + 1) → ∀ i,
      (MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i) ↔
        MSO.Sat w' (fun _ => p) (fun _ => ∅) (R.form i))

private lemma flatten_map_singleton {C : Type} (n : ℕ) (g : ℕ → C) :
    ((List.range n).map (fun p => [g p])).flatten = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.flatten_append, ih]
      simp

private lemma eq_map_range_getD {C : Type} (l : List C) (d : C) :
    l = (List.range l.length).map (fun p => l.getD p d) := by
  refine List.ext_getElem (by simp) fun n h1 _ => ?_
  simp [List.getElem?_eq_getElem h1]

/-- A Mealy machine is an mso relabelling with the three restrictions: the formulas say which
output letter is produced in a position, which is a regular property of the input string marked at
that position (Claim `claim:transition-formula`, here in the form
`Transducers.MarkLogic.exists_form_of_regular`). -/
lemma restrictedRelabelling_of_isMealy [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy f) :
    ∃ R : MSORelabelling A B, RestrictedRelabelling R ∧ ∀ w, R.Relabels w (f w) := by
  classical
  obtain ⟨Q, hQ, M, rfl⟩ := hf
  haveI := hQ
  choose form hform using fun b : B =>
    MarkLogic.exists_form_of_regular (mealyMarkDFA M b).accepts
      (isRegular_of_dfa (mealyMarkDFA M b) rfl)
  have hsat : ∀ (b : B) (w : List A) (x : ℕ),
      MSO.Sat w (fun _ => x) (fun _ => ∅) (form b) ↔ (M.eval w)[x]? = some b := by
    intro b w x
    rw [hform b w x]
    exact mealyMark_accepts M b w x
  have huniq : ∀ (w : List A) (p : ℕ), p < w.length →
      ∃! b : B, MSO.Sat w (fun _ => p) (fun _ => ∅) (form b) := by
    intro w p hp
    have hp' : p < (M.eval w).length := by rw [Mealy.eval_length]; exact hp
    refine ⟨(M.eval w)[p], (hsat _ w p).2 (List.getElem?_eq_getElem hp'), fun b hb => ?_⟩
    have h := (hsat b w p).1 hb
    rw [List.getElem?_eq_getElem hp'] at h
    exact (Option.some_inj.1 h).symm
  refine ⟨⟨B, inferInstance, form, fun b => [b], [], huniq⟩, ⟨rfl, fun _ => rfl, ?_⟩, ?_⟩
  · intro w w' p hp hp' htake b
    rw [hsat, hsat]
    have h1 : w.take p = w'.take p := by
      have h := congrArg (fun l : List A => l.take p) htake
      simpa [List.take_take] using h
    have h2 : w[p] = w'[p] := by
      have h := congrArg (fun l : List A => l[p]?) htake
      simp only [List.getElem?_take, if_pos (Nat.lt_succ_self p)] at h
      rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hp'] at h
      exact Option.some_inj.1 h
    rw [mealy_eval_getElem? M w p hp, mealy_eval_getElem? M w' p hp', h1, h2]
  · intro w
    rcases eq_or_ne w [] with rfl | hw
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      have hlen : (M.eval w).length = w.length := M.eval_length w
      have hpos : 0 < (M.eval w).length := by
        rw [hlen]; exact List.length_pos_iff.2 hw
      obtain ⟨b0⟩ : Nonempty B := ⟨(M.eval w)[0]⟩
      refine ⟨hw, fun p => (M.eval w).getD p b0, fun p hp => ?_, ?_⟩
      · refine (hsat _ w p).2 ?_
        have hp' : p < (M.eval w).length := by rw [hlen]; exact hp
        show (M.eval w)[p]? = some ((M.eval w).getD p b0)
        rw [List.getElem?_eq_getElem hp', List.getD_eq_getElem _ _ hp']
      · show M.eval w = ((List.range w.length).map (fun p => [(M.eval w).getD p b0])).flatten
        rw [flatten_map_singleton, ← hlen]
        exact eq_map_range_getD (M.eval w) b0

/-- An mso relabelling with the three restrictions is a Mealy machine.  It is rational by Theorem
`thm:logic-rational-functions`, it is length preserving because every formula outputs one letter,
and past-dependence of the formulas makes the output at a position depend only on the prefix up to
that position, so Theorem `thm:rational-is-mealy-characterisation` applies. -/
lemma isMealy_of_restrictedRelabelling [Finite A] [Finite B] {f : List A → List B}
    {R : MSORelabelling A B} (hres : RestrictedRelabelling R) (hR : ∀ w, R.Relabels w (f w)) :
    IsMealy f := by
  classical
  choose sing hsing using fun i : R.Idx => List.length_eq_one_iff.1 (hres.out_length i)
  have hmain : ∀ w : List A, w ≠ [] → ∃ g : ℕ → R.Idx,
      (∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) ∧
      f w = (List.range w.length).map (fun p => sing (g p)) := by
    intro w hw
    rcases hR w with ⟨h0, -⟩ | ⟨-, g, hg, hv⟩
    · exact absurd h0 hw
    · refine ⟨g, hg, ?_⟩
      rw [hv, show (fun p => R.out (g p)) = (fun p => [sing (g p)]) from funext fun p => hsing (g p),
        flatten_map_singleton]
  have hlen : LengthPreserving f := by
    intro w
    rcases eq_or_ne w [] with rfl | hw
    · rcases hR [] with ⟨-, hv⟩ | ⟨h0, -⟩
      · rw [hv, hres.emptyOut]; rfl
      · exact absurd rfl h0
    · obtain ⟨g, -, hfw⟩ := hmain w hw
      rw [hfw]; simp
  have hget : ∀ (w : List A) (p : ℕ), p < w.length →
      ∃ i, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i) ∧ (f w)[p]? = some (sing i) := by
    intro w p hp
    have hw : w ≠ [] := by rintro rfl; simp at hp
    obtain ⟨g, hg, hfw⟩ := hmain w hw
    refine ⟨g p, hg p hp, ?_⟩
    rw [hfw]
    simp [hp]
  have hrat : IsRationalFun f := (rational_iff_msoRelabelling f).2 ⟨R, hR⟩
  refine (rational_isMealy_iff hrat).2 ⟨hlen, fun w v n hwv => ?_⟩
  have hminlen : min n w.length = min n v.length := by
    have h := congrArg List.length hwv
    simpa using h
  refine List.ext_getElem? fun p => ?_
  rw [List.getElem?_take, List.getElem?_take]
  by_cases hpn : p < n
  · simp only [if_pos hpn]
    by_cases hpw : p < w.length
    · have hpv : p < v.length := by omega
      obtain ⟨i, hi, hfi⟩ := hget w p hpw
      obtain ⟨j, hj, hfj⟩ := hget v p hpv
      have htake : w.take (p + 1) = v.take (p + 1) := by
        have h := congrArg (fun l : List A => l.take (p + 1)) hwv
        simpa [List.take_take, Nat.min_eq_left (by omega : p + 1 ≤ n)] using h
      have hij : j = i := by
        have hsi : MSO.Sat v (fun _ => p) (fun _ => ∅) (R.form i) :=
          (hres.past w v p hpw hpv htake i).1 hi
        obtain ⟨k, -, hk⟩ := R.unique v p hpv
        rw [hk j hj, hk i hsi]
      rw [hfi, hfj, hij]
    · have hpv : ¬ p < v.length := by omega
      rw [List.getElem?_eq_none (by rw [hlen w]; omega),
        List.getElem?_eq_none (by rw [hlen v]; omega)]
  · simp [hpn]

/-- **Exercise `exer:mealy-as-restricted-mso-relabelling`.**  A function is computed by a Mealy
machine if and only if it is defined by an mso relabelling satisfying the three additional
restrictions of the exercise. -/
theorem isMealy_iff_restrictedRelabelling [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ ∃ R : MSORelabelling A B, RestrictedRelabelling R ∧ ∀ w, R.Relabels w (f w) :=
  ⟨restrictedRelabelling_of_isMealy,
    fun ⟨_, hres, hR⟩ => isMealy_of_restrictedRelabelling hres hR⟩

end MealyRelabelling

end Exercises
end Transducers
