/-
Splitting the output blocks of a code into single letters.

This is the first step of the effective form of the Uniformisation Lemma `lem:uniformisation`
of *Transducers* (M. Bojańczyk), which discharges the effectivity hypothesis of Exercise
`exer:rational-injectivity-decidable`.

The inverse of the relation described by a code `c` is obtained by exchanging the input and the
output of every transition.  For that inverse to be described by a *letter automaton*
(`Transducers.Exercises.LCode`), which reads exactly one letter per transition, the output
blocks of `c` have to be single letters.  `Transducers.Exercises.Split.splitCode` puts a code
into that shape, replacing a transition that writes `b₀ ⋯ b_{k-1}` by a chain of `k` transitions
writing one letter each; the relation and the input alphabet are unchanged.
-/
import RequestProject.PartB.Codes

namespace Transducers.Exercises

open Transducers

namespace Split

/-! ## States -/

/-- The states of the split code: either a state of the original code, or an intermediate state
`(z, q')`, meaning that the output block `z` still has to be written, after which the original
code is in the state `q'`. -/
def st : ℕ ⊕ (List ℕ × ℕ) → ℕ := Encodable.encode

lemma st_inj {x y : ℕ ⊕ (List ℕ × ℕ)} (h : st x = st y) : x = y :=
  Encodable.encode_injective h

/-- A state of the original code, as a state of the split code. -/
def old (q : ℕ) : ℕ := st (Sum.inl q)

/-- The intermediate state at which the block `z` still has to be written, after which the
original code is in the state `q'`. -/
def mid (z : List ℕ) (q' : ℕ) : ℕ := st (Sum.inr (z, q'))

lemma old_ne_mid (q : ℕ) (z : List ℕ) (q' : ℕ) : old q ≠ mid z q' := by
  intro h
  have := st_inj h
  simp at this

lemma old_inj {q q' : ℕ} (h : old q = old q') : q = q' := by
  have := st_inj h; simpa [Sum.inl.injEq] using this

lemma mid_inj {z z' : List ℕ} {q q' : ℕ} (h : mid z q = mid z' q') : z = z' ∧ q = q' := by
  have := st_inj h
  simp only [Sum.inr.injEq, Prod.mk.injEq] at this
  exact this

/-- The state reached once the block `z` has still to be written before returning to `q'`: the
intermediate state `mid z q'`, or the original state `q'` when `z` is empty. -/
def nxt (z : List ℕ) (q' : ℕ) : ℕ := if z = [] then old q' else mid z q'

/-! ## The construction -/

/-- The chain of transitions replacing a transition from `s` reading `u` and writing `y`, ending
in the original state `q'`.  Each transition of the chain writes a single letter. -/
def chain (q' : ℕ) : List ℕ → ℕ → List ℕ → List (ℕ × List ℕ × List ℕ × ℕ)
  | [], s, u => [(s, u, [], old q')]
  | b :: y, s, u => (s, u, [b], nxt y q') :: chain q' y (nxt y q') []

/-- The transitions of the split code. -/
def trans (c : RelCode) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  c.1.flatMap (fun t => chain t.2.2.2 t.2.2.1 (old t.1) t.2.1)

/-- **The split code**: the same relation, with every output block split into single letters. -/
def splitCode (c : RelCode) : RelCode := (trans c, c.2.1.map old, c.2.2.map old)

/-! ## The shape of the transitions -/

lemma mem_chain (q' : ℕ) : ∀ (y : List ℕ) (s : ℕ) (u : List ℕ) (tr : ℕ × List ℕ × List ℕ × ℕ),
    tr ∈ chain q' y s u →
      (y = [] ∧ tr = (s, u, [], old q')) ∨
      (∃ b z, y = b :: z ∧ tr = (s, u, [b], nxt z q')) ∨
      (tr = (old q', [], [], old q')) ∨
      (∃ b z, tr = (mid (b :: z) q', [], [b], nxt z q')) := by
  intro y
  induction y with
  | nil =>
      intro s u tr h
      rw [chain, List.mem_singleton] at h
      exact Or.inl ⟨rfl, h⟩
  | cons b y ih =>
      intro s u tr h
      rw [chain, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inr (Or.inl ⟨b, y, rfl, rfl⟩)
      · rcases ih (nxt y q') [] tr h with ⟨hy, htr⟩ | ⟨b₂, z, hy, htr⟩ | htr | htr
        · subst hy
          simp only [nxt] at htr
          exact Or.inr (Or.inr (Or.inl htr))
        · subst hy
          refine Or.inr (Or.inr (Or.inr ⟨b₂, z, ?_⟩))
          simpa [nxt] using htr
        · exact Or.inr (Or.inr (Or.inl htr))
        · exact Or.inr (Or.inr (Or.inr htr))

lemma mem_trans {c : RelCode} {tr : ℕ × List ℕ × List ℕ × ℕ} (h : tr ∈ trans c) :
    (∃ q u q', (q, u, [], q') ∈ c.1 ∧ tr = (old q, u, [], old q')) ∨
    (∃ q u b z q', (q, u, b :: z, q') ∈ c.1 ∧ tr = (old q, u, [b], nxt z q')) ∨
    (∃ q', tr = (old q', [], [], old q')) ∨
    (∃ b z q', tr = (mid (b :: z) q', [], [b], nxt z q')) := by
  rw [trans, List.mem_flatMap] at h
  obtain ⟨t, ht, htr⟩ := h
  obtain ⟨q, u, y, q'⟩ := t
  rcases mem_chain q' y (old q) u tr htr with ⟨hy, h⟩ | ⟨b, z, hy, h⟩ | h | ⟨b, z, h⟩
  · exact Or.inl ⟨q, u, q', by rw [← hy]; exact ht, h⟩
  · exact Or.inr (Or.inl ⟨q, u, b, z, q', by rw [← hy]; exact ht, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨q', h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b, z, q', h⟩))

/-! ## The alphabet is unchanged -/

lemma flatMap_input_chain (q' : ℕ) : ∀ (y : List ℕ) (s : ℕ) (u : List ℕ),
    (chain q' y s u).flatMap (fun t => t.2.1) = u := by
  intro y
  induction y with
  | nil => intro s u; simp [chain]
  | cons b y ih => intro s u; simp [chain, ih]

lemma flatMap_input_trans (l : List (ℕ × List ℕ × List ℕ × ℕ)) :
    (l.flatMap (fun t => chain t.2.2.2 t.2.2.1 (old t.1) t.2.1)).flatMap (fun t => t.2.1)
      = l.flatMap (fun t => t.2.1) := by
  induction l with
  | nil => simp
  | cons t l ih => simp [List.flatMap_append, flatMap_input_chain, ih]

lemma codeAlphabet_splitCode (c : RelCode) : codeAlphabet (splitCode c) = codeAlphabet c := by
  simpa [codeAlphabet, splitCode, trans] using flatMap_input_trans c.1

/-! ## The relation is unchanged -/

/-- Every chain of the split code realises the transition that it replaces. -/
lemma chain_relFrom {c : RelCode} (q' : ℕ) : ∀ (y : List ℕ) (s : ℕ) (u : List ℕ),
    (∀ tr ∈ chain q' y s u, tr ∈ trans c) →
      (codeAut (splitCode c)).relFrom s u y (old q') := by
  intro y
  induction y with
  | nil =>
      intro s u hsub
      have ht : (s, u, ([] : List ℕ), old q') ∈ (codeAut (splitCode c)).δ :=
        hsub _ (by rw [chain]; exact List.mem_singleton_self _)
      exact NFAO.relFrom_single ht
  | cons b y ih =>
      intro s u hsub
      have hhead : (s, u, [b], nxt y q') ∈ (codeAut (splitCode c)).δ :=
        hsub _ (by rw [chain]; exact List.mem_cons_self ..)
      have hrest : ∀ tr ∈ chain q' y (nxt y q') [], tr ∈ trans c := by
        intro tr htr
        exact hsub tr (by rw [chain]; exact List.mem_cons_of_mem _ htr)
      have hy : (codeAut (splitCode c)).relFrom (nxt y q') [] y (old q') := ih (nxt y q') [] hrest
      simpa using NFAO.relFrom_step hhead hy

lemma relFrom_splitCode_of_relFrom {c : RelCode} {q p : ℕ} {w v : List ℕ}
    (h : (codeAut c).relFrom q w v p) :
    (codeAut (splitCode c)).relFrom (old q) w v (old p) := by
  refine NFAO.relFrom_induction (M := codeAut c)
    (motive := fun q w v => (codeAut (splitCode c)).relFrom (old q) w v (old p))
    ((codeAut (splitCode c)).relFrom_nil (old p)) ?_ h
  intro q q' u x w v ht _ ih
  have hsub : ∀ tr ∈ chain q' x (old q) u, tr ∈ trans c := by
    intro tr htr
    exact List.mem_flatMap.2 ⟨(q, u, x, q'), ht, htr⟩
  exact NFAO.relFrom_trans (chain_relFrom (c := c) q' x (old q) u hsub) ih

/-- The meaning of a state of the split code, as seen from a fixed final state `p₀`. -/
private def Meaning (c : RelCode) (p₀ : ℕ) (s : ℕ) (w v : List ℕ) : Prop :=
  (∀ q, s = old q → (codeAut c).relFrom q w v p₀) ∧
  (∀ z q', s = mid z q' → ∃ v', v = z ++ v' ∧ (codeAut c).relFrom q' w v' p₀)

private lemma meaning_of_relFrom {c : RelCode} {p₀ : ℕ} {s : ℕ} {w v : List ℕ}
    (h : (codeAut (splitCode c)).relFrom s w v (old p₀)) : Meaning c p₀ s w v := by
  refine NFAO.relFrom_induction (M := codeAut (splitCode c))
    (motive := fun s w v => Meaning c p₀ s w v) ⟨?_, ?_⟩ ?_ h
  · intro q hq
    rw [← old_inj hq]
    exact (codeAut c).relFrom_nil p₀
  · intro z q' hz
    exact absurd hz (old_ne_mid p₀ z q')
  · intro s s' u x w v ht _ ih
    have htr : (s, u, x, s') ∈ trans c := ht
    rcases mem_trans htr with ⟨q, u₀, q', hc, he⟩ | ⟨q, u₀, b, z, q', hc, he⟩ |
      ⟨q', he⟩ | ⟨b, z, q', he⟩
    · have hs : s = old q := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) he
      have hu : u = u₀ := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) he
      have hx : x = [] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) he
      have hs' : s' = old q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) he
      subst hu; subst hx
      refine ⟨?_, ?_⟩
      · intro q₂ hq₂
        rw [hs] at hq₂
        rw [← old_inj hq₂]
        have := ih.1 q' hs'
        simpa using NFAO.relFrom_step (M := codeAut c) hc this
      · intro z q₂ hz
        rw [hs] at hz
        exact absurd hz (old_ne_mid q z q₂)
    · have hs : s = old q := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) he
      have hu : u = u₀ := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) he
      have hx : x = [b] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) he
      have hs' : s' = nxt z q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) he
      subst hu; subst hx
      refine ⟨?_, ?_⟩
      · intro q₂ hq₂
        rw [hs] at hq₂
        rw [← old_inj hq₂]
        have hfin : ∃ v', v = z ++ v' ∧ (codeAut c).relFrom q' w v' p₀ := by
          by_cases hz : z = []
          · subst hz
            exact ⟨v, by simp, ih.1 q' (by rw [hs']; simp [nxt])⟩
          · exact ih.2 z q' (by rw [hs']; simp [nxt, hz])
        obtain ⟨v', hv, hrel⟩ := hfin
        have := NFAO.relFrom_step (M := codeAut c) hc hrel
        rw [hv]
        simpa using this
      · intro z₂ q₂ hz₂
        rw [hs] at hz₂
        exact absurd hz₂ (old_ne_mid q z₂ q₂)
    · have hs : s = old q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) he
      have hu : u = [] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) he
      have hx : x = [] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) he
      have hs' : s' = old q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) he
      subst hu; subst hx
      refine ⟨?_, ?_⟩
      · intro q₂ hq₂
        rw [hs] at hq₂
        rw [← old_inj hq₂]
        simpa using ih.1 q' hs'
      · intro z q₂ hz
        rw [hs] at hz
        exact absurd hz (old_ne_mid q' z q₂)
    · have hs : s = mid (b :: z) q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) he
      have hu : u = [] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) he
      have hx : x = [b] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) he
      have hs' : s' = nxt z q' := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) he
      subst hu; subst hx
      refine ⟨?_, ?_⟩
      · intro q₂ hq₂
        rw [hs] at hq₂
        exact absurd hq₂.symm (old_ne_mid q₂ (b :: z) q')
      · intro z₂ q₂ hz₂
        rw [hs] at hz₂
        obtain ⟨hzz, hqq⟩ := mid_inj hz₂
        subst hzz; subst hqq
        have hfin : ∃ v', v = z ++ v' ∧ (codeAut c).relFrom q' w v' p₀ := by
          by_cases hz : z = []
          · subst hz
            exact ⟨v, by simp, ih.1 q' (by rw [hs']; simp [nxt])⟩
          · exact ih.2 z q' (by rw [hs']; simp [nxt, hz])
        obtain ⟨v', hv, hrel⟩ := hfin
        exact ⟨v', by rw [hv]; simp, by simpa using hrel⟩

lemma relFrom_of_relFrom_splitCode {c : RelCode} {q p₀ : ℕ} {w v : List ℕ}
    (h : (codeAut (splitCode c)).relFrom (old q) w v (old p₀)) :
    (codeAut c).relFrom q w v p₀ :=
  (meaning_of_relFrom h).1 q rfl

/-- **The split code describes the same relation.** -/
theorem codeRel_splitCode (c : RelCode) (w v : List ℕ) :
    codeRel (splitCode c) w v ↔ codeRel c w v := by
  constructor
  · intro h
    obtain ⟨s, hs, s', hs', hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    have hs2 : s ∈ c.2.1.map old := hs
    have hs'2 : s' ∈ c.2.2.map old := hs'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs2
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs'2
    exact (NFAO.rel_iff_relFrom _ _ _).2 ⟨q, hq, p, hp, relFrom_of_relFrom_splitCode hrel⟩
  · intro h
    obtain ⟨q, hq, p, hp, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨old q, ?_, old p, ?_, relFrom_splitCode_of_relFrom hrel⟩
    · exact List.mem_map.2 ⟨q, hq, rfl⟩
    · exact List.mem_map.2 ⟨p, hp, rfl⟩

/-- Every transition of the split code writes at most one letter. -/
lemma length_output_le_one {c : RelCode} {tr : ℕ × List ℕ × List ℕ × ℕ} (h : tr ∈ trans c) :
    tr.2.2.1.length ≤ 1 := by
  rcases mem_trans h with ⟨q, u, q', -, he⟩ | ⟨q, u, b, z, q', -, he⟩ | ⟨q', he⟩ | ⟨b, z, q', he⟩ <;>
    · rw [he]; simp

end Split

end Transducers.Exercises
