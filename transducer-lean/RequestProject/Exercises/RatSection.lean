/-
The rational section of a code, and its composition with the code.

This is the last step of the effective form of the Uniformisation Lemma `lem:uniformisation`
of *Transducers* (M. Bojańczyk), which discharges the effectivity hypothesis of Exercise
`exer:rational-injectivity-decidable`.

`Transducers.Exercises.LAut.secLCode c` is the letter automaton obtained by uniformising the
inverse of `c`: it computes a *function* whose graph is contained in the inverse of the relation
of `c` and whose domain is the whole range of that relation — a *section* of `c`.
`Transducers.Exercises.LAut.invCode c` is the composition of `c` with that section, obtained by
the usual product construction: since the section reads one letter at a time, the output block
of a transition of `c` can be fed to it inside a single transition of the product.
-/
import RequestProject.Exercises.LAutInv
import RequestProject.Exercises.LAutUnif

namespace Transducers.Exercises

open Transducers

namespace LAut

/-! ## Paths of a letter automaton over a concatenation -/

lemma pathFrom_nil_eq {L : LCode} {q r : ℕ} {is u : List ℕ} (h : pathFrom L q [] is = some (r, u)) :
    is = [] ∧ r = q ∧ u = [] := by
  match is with
  | [] =>
      refine ⟨rfl, ?_, ?_⟩
      · exact (congrArg Prod.fst (Option.some.inj h)).symm
      · exact (congrArg Prod.snd (Option.some.inj h)).symm
  | _ :: _ => simp at h

lemma pathFrom_append_of (L : LCode) : ∀ (v₁ : List ℕ) (is₁ : List ℕ) (q m : ℕ) (u₁ : List ℕ)
    (v₂ is₂ : List ℕ) (r : ℕ) (u₂ : List ℕ),
    pathFrom L q v₁ is₁ = some (m, u₁) → pathFrom L m v₂ is₂ = some (r, u₂) →
      pathFrom L q (v₁ ++ v₂) (is₁ ++ is₂) = some (r, u₁ ++ u₂) := by
  intro v₁
  induction v₁ with
  | nil =>
      intro is₁ q m u₁ v₂ is₂ r u₂ h₁ h₂
      obtain ⟨rfl, rfl, rfl⟩ := pathFrom_nil_eq h₁
      simpa using h₂
  | cons a v₁ ih =>
      intro is₁ q m u₁ v₂ is₂ r u₂ h₁ h₂
      match is₁ with
      | [] => simp at h₁
      | i :: is₁ =>
          rw [pathFrom_cons_cons] at h₁
          cases hstep : step L q a i with
          | none => rw [hstep] at h₁; simp at h₁
          | some w =>
              rw [hstep, Option.bind_some, Option.map_eq_some_iff] at h₁
              obtain ⟨y, hy, hyeq⟩ := h₁
              have e1 : y.1 = m := congrArg Prod.fst hyeq
              have e2 : w.2 ++ y.2 = u₁ := congrArg Prod.snd hyeq
              have hrec := ih is₁ w.1 m y.2 v₂ is₂ r u₂
                (by rw [hy]; simp [Prod.ext_iff, e1]) h₂
              rw [List.cons_append, List.cons_append, pathFrom_cons_cons, hstep,
                Option.bind_some, hrec]
              simp [← e2]

lemma pathFrom_append (L : LCode) : ∀ (v₁ v₂ is : List ℕ) (q r : ℕ) (u : List ℕ),
    pathFrom L q (v₁ ++ v₂) is = some (r, u) →
      ∃ (is₁ is₂ : List ℕ) (m : ℕ) (u₁ u₂ : List ℕ), is = is₁ ++ is₂ ∧
        pathFrom L q v₁ is₁ = some (m, u₁) ∧ pathFrom L m v₂ is₂ = some (r, u₂) ∧ u = u₁ ++ u₂ := by
  intro v₁
  induction v₁ with
  | nil =>
      intro v₂ is q r u h
      exact ⟨[], is, q, [], u, rfl, rfl, by simpa using h, by simp⟩
  | cons a v₁ ih =>
      intro v₂ is q r u h
      match is with
      | [] => simp at h
      | i :: is =>
          rw [List.cons_append, pathFrom_cons_cons] at h
          cases hstep : step L q a i with
          | none => rw [hstep] at h; simp at h
          | some w =>
              rw [hstep, Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨y, hy, hyeq⟩ := h
              have e1 : y.1 = r := congrArg Prod.fst hyeq
              have e2 : w.2 ++ y.2 = u := congrArg Prod.snd hyeq
              obtain ⟨is₁, is₂, m, u₁, u₂, hiseq, hp₁, hp₂, hu⟩ :=
                ih v₂ is w.1 r y.2 (by rw [hy]; simp [Prod.ext_iff, e1])
              refine ⟨i :: is₁, is₂, m, w.2 ++ u₁, u₂, by rw [hiseq]; simp, ?_, hp₂, ?_⟩
              · rw [pathFrom_cons_cons, hstep, Option.bind_some, hp₁]
                simp
              · rw [← e2, hu]; simp

lemma accFrom_append (L : LCode) {v₁ is₁ : List ℕ} {q m : ℕ} {u₁ : List ℕ}
    {v₂ is₂ : List ℕ} {k : ℕ} {u₂ : List ℕ}
    (h₁ : pathFrom L q v₁ is₁ = some (m, u₁)) (h₂ : accFrom L m v₂ is₂ k = some u₂) :
    accFrom L q (v₁ ++ v₂) (is₁ ++ is₂) k = some (u₁ ++ u₂) := by
  rw [accFrom, Option.bind_eq_some_iff] at h₂
  obtain ⟨z, hz, he⟩ := h₂
  rw [Option.map_eq_some_iff] at he
  obtain ⟨e, he1, he2⟩ := he
  rw [accFrom, pathFrom_append_of L v₁ is₁ q m u₁ v₂ is₂ z.1 z.2 h₁ hz, Option.bind_some, he1]
  simp [← he2]

/-! ## All the paths of a letter automaton over a given word -/

/-- One round of the computation of all the paths over a word: extend every path found so far
by one transition reading the letter `a`. -/
def apStep (L : LCode) (acc : List (ℕ × List ℕ)) (a : ℕ) : List (ℕ × List ℕ) :=
  acc.flatMap (fun z => L.1.filterMap (fun t =>
    if t.1 = z.1 ∧ t.2.1 = a then some (t.2.2.2, z.2 ++ t.2.2.1) else none))

/-- All the paths of `L` starting in `s` and reading `y`: the list of pairs consisting of the
state reached and of the output written. -/
def allPathsOver (L : LCode) (s : ℕ) (y : List ℕ) : List (ℕ × List ℕ) :=
  y.foldl (apStep L) [(s, [])]

lemma mem_apStep {L : LCode} {acc : List (ℕ × List ℕ)} {a r : ℕ} {x : List ℕ} :
    (r, x) ∈ apStep L acc a ↔
      ∃ q u, (q, u) ∈ acc ∧ ∃ i w, step L q a i = some (r, w) ∧ x = u ++ w := by
  constructor
  · intro h
    rw [apStep, List.mem_flatMap] at h
    obtain ⟨z, hz, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨t, ht, hteq⟩ := h
    by_cases hc : t.1 = z.1 ∧ t.2.1 = a
    · rw [if_pos hc, Option.some.injEq, Prod.mk.injEq] at hteq
      obtain ⟨i, hi⟩ := exists_index ht
      refine ⟨z.1, z.2, by simpa using hz, i, t.2.2.1, ?_, ?_⟩
      · rw [step, hi, Option.bind_some, if_pos hc, hteq.1]
      · rw [hteq.2]
    · rw [if_neg hc] at hteq; exact absurd hteq (by simp)
  · rintro ⟨q, u, hqu, i, w, hstep, rfl⟩
    rw [step, Option.bind_eq_some_iff] at hstep
    obtain ⟨t, ht, hcond⟩ := hstep
    by_cases hc : t.1 = q ∧ t.2.1 = a
    · rw [if_pos hc, Option.some.injEq, Prod.mk.injEq] at hcond
      refine List.mem_flatMap.2 ⟨(q, u), hqu, List.mem_filterMap.2 ⟨t, List.mem_of_getElem? ht, ?_⟩⟩
      rw [if_pos hc, hcond.1, hcond.2]
    · rw [if_neg hc] at hcond; exact absurd hcond (by simp)

lemma mem_foldl_apStep {L : LCode} : ∀ (y : List ℕ) (acc : List (ℕ × List ℕ)) (r : ℕ) (x : List ℕ),
    (r, x) ∈ y.foldl (apStep L) acc ↔
      ∃ q u, (q, u) ∈ acc ∧ ∃ is z, pathFrom L q y is = some (r, z) ∧ x = u ++ z := by
  intro y
  induction y with
  | nil =>
      intro acc r x
      simp only [List.foldl_nil]
      constructor
      · intro h; exact ⟨r, x, h, [], [], rfl, by simp⟩
      · rintro ⟨q, u, hqu, is, z, hp, rfl⟩
        obtain ⟨-, rfl, rfl⟩ := pathFrom_nil_eq hp
        simpa using hqu
  | cons a y ih =>
      intro acc r x
      rw [List.foldl_cons, ih]
      constructor
      · rintro ⟨q, u, hqu, is, z, hp, rfl⟩
        obtain ⟨q₀, u₀, hq₀, i, w, hstep, rfl⟩ := mem_apStep.1 hqu
        refine ⟨q₀, u₀, hq₀, i :: is, w ++ z, ?_, by simp⟩
        rw [pathFrom_cons_cons, hstep, Option.bind_some, hp]
        simp
      · rintro ⟨q, u, hqu, is, z, hp, rfl⟩
        match is with
        | [] => simp at hp
        | i :: is =>
            rw [pathFrom_cons_cons] at hp
            cases hstep : step L q a i with
            | none => rw [hstep] at hp; simp at hp
            | some w =>
                rw [hstep, Option.bind_some, Option.map_eq_some_iff] at hp
                obtain ⟨z', hz', hzeq⟩ := hp
                have e1 : z'.1 = r := congrArg Prod.fst hzeq
                have e2 : w.2 ++ z'.2 = z := congrArg Prod.snd hzeq
                refine ⟨w.1, u ++ w.2, mem_apStep.2 ⟨q, u, hqu, i, w.2, ?_, rfl⟩, is, z'.2, ?_, ?_⟩
                · rw [hstep]
                · rw [hz']; simp [Prod.ext_iff, e1]
                · rw [← e2]; simp

lemma mem_allPathsOver {L : LCode} : ∀ (y : List ℕ) (s r : ℕ) (z : List ℕ),
    (r, z) ∈ allPathsOver L s y ↔ ∃ is : List ℕ, pathFrom L s y is = some (r, z) := by
  intro y s r z
  rw [allPathsOver, mem_foldl_apStep]
  constructor
  · rintro ⟨q, u, hqu, is, z', hp, rfl⟩
    rw [List.mem_singleton, Prod.mk.injEq] at hqu
    obtain ⟨rfl, rfl⟩ := hqu
    exact ⟨is, by simpa using hp⟩
  · rintro ⟨is, hp⟩
    exact ⟨s, [], by simp, is, z, hp, by simp⟩

/-! ## The section -/

/-- **The rational section of a code**, as a letter automaton: the uniformisation of the inverse
of the code. -/
def secLCode (c : RelCode) : LCode := unifLCode (invLCode (Split.splitCode c))

theorem secLCode_sound {c : RelCode} {v u : List ℕ} (h : rel (secLCode c) v u) :
    codeRel c u v :=
  (Split.codeRel_splitCode c u v).1 (invLCode_sound (unifLCode_sound h))

theorem secLCode_dom {c : RelCode} {u v : List ℕ} (h : codeRel c u v) : dom (secLCode c) v :=
  unifLCode_dom (invLCode_dom (fun _ ht => Split.length_output_le_one ht)
    ((Split.codeRel_splitCode c u v).2 h))

theorem secLCode_functional {c : RelCode} {v u u' : List ℕ} (h : rel (secLCode c) v u)
    (h' : rel (secLCode c) v u') : u = u' := unifLCode_functional h h'

/-! ## The product of a code with a letter automaton -/

/-- The states of the product: a pair of a state of the code and a state of the letter
automaton, a final sink, or an unreachable state carrying the alphabet. -/
def pst : (ℕ × ℕ) ⊕ Bool → ℕ := Encodable.encode

/-- A state of the product. -/
def pair (q s : ℕ) : ℕ := pst (Sum.inl (q, s))

/-- The final state of the product. -/
def sink : ℕ := pst (Sum.inr true)

/-- The unreachable state of the product that carries the alphabet of the code. -/
def dummy : ℕ := pst (Sum.inr false)

lemma pair_inj {q s q' s' : ℕ} (h : pair q s = pair q' s') : q = q' ∧ s = s' := by
  have hh := Encodable.encode_injective h
  simp only [Sum.inl.injEq, Prod.mk.injEq] at hh
  exact hh

lemma pair_ne_sink (q s : ℕ) : pair q s ≠ sink := by
  intro h; have := Encodable.encode_injective h; simp at this

lemma pair_ne_dummy (q s : ℕ) : pair q s ≠ dummy := by
  intro h; have := Encodable.encode_injective h; simp at this

lemma sink_ne_dummy : sink ≠ dummy := by
  intro h; have := Encodable.encode_injective h; simp at this

/-- The transitions of the product of a code with a letter automaton. -/
def prodTrans (c : RelCode) (L : LCode) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  c.1.flatMap (fun t => (states L).flatMap (fun s =>
      (allPathsOver L s t.2.2.1).map (fun z => (pair t.1 s, t.2.1, z.2, pair t.2.2.2 z.1))))
    ++ c.2.2.flatMap (fun q => L.2.2.map (fun e => (pair q e.1, ([] : List ℕ), e.2, sink)))
    ++ (codeAlphabet c).map (fun a => (dummy, [a], ([] : List ℕ), dummy))

/-- **The product of a code with a letter automaton**: it relates `w` to `u` exactly when the
code relates `w` to some `v` which the letter automaton relates to `u`. -/
def prodCode (c : RelCode) (L : LCode) : RelCode :=
  (prodTrans c L, c.2.1.flatMap (fun q => L.2.1.map (fun s => pair q s)), [sink])

lemma mem_prodTrans {c : RelCode} {L : LCode} {tr : ℕ × List ℕ × List ℕ × ℕ}
    (h : tr ∈ prodTrans c L) :
    (∃ t ∈ c.1, ∃ s ∈ states L, ∃ z ∈ allPathsOver L s t.2.2.1,
        tr = (pair t.1 s, t.2.1, z.2, pair t.2.2.2 z.1)) ∨
      (∃ q ∈ c.2.2, ∃ e ∈ L.2.2, tr = (pair q e.1, ([] : List ℕ), e.2, sink)) ∨
      (∃ a ∈ codeAlphabet c, tr = (dummy, [a], ([] : List ℕ), dummy)) := by
  rw [prodTrans, List.mem_append, List.mem_append] at h
  rcases h with (h | h) | h
  · rw [List.mem_flatMap] at h
    obtain ⟨t, ht, h⟩ := h
    rw [List.mem_flatMap] at h
    obtain ⟨s, hs, h⟩ := h
    rw [List.mem_map] at h
    obtain ⟨z, hz, hzeq⟩ := h
    exact Or.inl ⟨t, ht, s, hs, z, hz, hzeq.symm⟩
  · rw [List.mem_flatMap] at h
    obtain ⟨q, hq, h⟩ := h
    rw [List.mem_map] at h
    obtain ⟨e, he, heq⟩ := h
    exact Or.inr (Or.inl ⟨q, hq, e, he, heq.symm⟩)
  · rw [List.mem_map] at h
    obtain ⟨a, ha, heq⟩ := h
    exact Or.inr (Or.inr ⟨a, ha, heq.symm⟩)

lemma mem_prodTrans_of {c : RelCode} {L : LCode} {t : ℕ × List ℕ × List ℕ × ℕ} {s : ℕ}
    {z : ℕ × List ℕ} (ht : t ∈ c.1) (hs : s ∈ states L) (hz : z ∈ allPathsOver L s t.2.2.1) :
    (pair t.1 s, t.2.1, z.2, pair t.2.2.2 z.1) ∈ prodTrans c L := by
  rw [prodTrans]
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_flatMap.2 ⟨t, ht, List.mem_flatMap.2 ⟨s, hs, List.mem_map.2 ⟨z, hz, rfl⟩⟩⟩

lemma mem_prodTrans_term {c : RelCode} {L : LCode} {q : ℕ} {e : ℕ × List ℕ} (hq : q ∈ c.2.2)
    (he : e ∈ L.2.2) : (pair q e.1, ([] : List ℕ), e.2, sink) ∈ prodTrans c L := by
  rw [prodTrans]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_flatMap.2 ⟨q, hq, List.mem_map.2 ⟨e, he, rfl⟩⟩

/-! ### The alphabet of the product -/

lemma mem_codeAlphabet_prodCode {c : RelCode} {L : LCode} {x : ℕ} :
    x ∈ codeAlphabet (prodCode c L) ↔ x ∈ codeAlphabet c := by
  constructor
  · intro h
    rw [codeAlphabet, List.mem_flatMap] at h
    obtain ⟨tr, htr, hx⟩ := h
    rcases mem_prodTrans htr with ⟨t, ht, s, -, z, -, heq⟩ | ⟨q, -, e, -, heq⟩ | ⟨a, ha, heq⟩
    · rw [heq] at hx
      exact List.mem_flatMap.2 ⟨t, ht, hx⟩
    · rw [heq] at hx; simp at hx
    · rw [heq] at hx
      simp only [List.mem_singleton] at hx
      rwa [hx]
  · intro h
    refine List.mem_flatMap.2 ⟨(dummy, [x], [], dummy), ?_, by simp⟩
    rw [prodCode, prodTrans]
    exact List.mem_append_right _ (List.mem_map.2 ⟨x, h, rfl⟩)

lemma codeWord_prodCode {c : RelCode} {L : LCode} {w : List ℕ} :
    CodeWord (prodCode c L) w ↔ CodeWord c w := by
  constructor
  · intro h x hx; exact mem_codeAlphabet_prodCode.1 (h x hx)
  · intro h x hx; exact mem_codeAlphabet_prodCode.2 (h x hx)

/-! ### Completeness of the product -/

lemma prod_relFrom_of {c : RelCode} {L : LCode} {f : ℕ} {q : ℕ} {w v : List ℕ}
    (h : (codeAut c).relFrom q w v f) :
    ∀ (s : ℕ), s ∈ states L → ∀ (is : List ℕ) (r : ℕ) (z : List ℕ),
      pathFrom L s v is = some (r, z) →
        (codeAut (prodCode c L)).relFrom (pair q s) w z (pair f r) := by
  refine NFAO.relFrom_induction (M := codeAut c)
    (motive := fun q w v => ∀ s, s ∈ states L → ∀ is r z, pathFrom L s v is = some (r, z) →
      (codeAut (prodCode c L)).relFrom (pair q s) w z (pair f r)) ?_ ?_ h
  · intro s _ is r z hp
    obtain ⟨-, rfl, rfl⟩ := pathFrom_nil_eq hp
    exact (codeAut (prodCode c L)).relFrom_nil _
  · intro q q' u x w v ht _ ih s hs is r z hp
    obtain ⟨is₁, is₂, m, u₁, u₂, -, hp₁, hp₂, hu⟩ := pathFrom_append L x v is s r z hp
    have hz₁ : ((m, u₁) : ℕ × List ℕ) ∈ allPathsOver L s x := (mem_allPathsOver x s m u₁).2 ⟨is₁, hp₁⟩
    have htr : (pair q s, u, u₁, pair q' m) ∈ (codeAut (prodCode c L)).δ :=
      mem_prodTrans_of (t := (q, u, x, q')) ht hs hz₁
    have hrec := ih m (mem_states_of_pathFrom x is₁ s m u₁ hp₁ hs) is₂ r u₂ hp₂
    rw [hu]
    exact NFAO.relFrom_step htr hrec

/-- **Completeness of the product.** -/
theorem codeRel_prodCode_of {c : RelCode} {L : LCode} {w v u : List ℕ} (hc : codeRel c w v)
    (hL : rel L v u) : codeRel (prodCode c L) w u := by
  obtain ⟨q₀, hq₀, f, hf, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 hc
  obtain ⟨j, s₀, k, is, hj, hacc⟩ := hL
  rw [accFrom, Option.bind_eq_some_iff] at hacc
  obtain ⟨z, hz, he⟩ := hacc
  rw [Option.map_eq_some_iff] at he
  obtain ⟨e, he1, he2⟩ := he
  have hs₀ : s₀ ∈ L.2.1 := List.mem_of_getElem? hj
  have hpath := prod_relFrom_of (L := L) hrel s₀ (mem_states_of_init hs₀) is z.1 z.2 hz
  -- the last transition, into the sink
  rw [term, Option.bind_eq_some_iff] at he1
  obtain ⟨tm, htm, hcond⟩ := he1
  by_cases hcm : tm.1 = z.1
  · rw [if_pos hcm] at hcond
    have hte : tm.2 = e := Option.some.inj hcond
    have hmem : tm ∈ L.2.2 := List.mem_of_getElem? htm
    have htr : (pair f tm.1, ([] : List ℕ), tm.2, sink) ∈ (codeAut (prodCode c L)).δ :=
      mem_prodTrans_term hf hmem
    rw [hcm, hte] at htr
    have hlast : (codeAut (prodCode c L)).relFrom (pair f z.1) [] e sink :=
      NFAO.relFrom_single htr
    refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨pair q₀ s₀, ?_, sink, ?_, ?_⟩
    · exact List.mem_flatMap.2 ⟨q₀, hq₀, List.mem_map.2 ⟨s₀, hs₀, rfl⟩⟩
    · show sink ∈ ({q | q ∈ [sink]} : Set ℕ)
      simp
    · have hcomb := NFAO.relFrom_trans hpath hlast
      rw [← he2]
      simpa using hcomb
  · rw [if_neg hcm] at hcond; simp at hcond

/-! ### Soundness of the product -/

private def PMeaning (c : RelCode) (L : LCode) (S : ℕ) (w u : List ℕ) : Prop :=
  (∀ q s, S = pair q s → ∃ (v : List ℕ) (f : ℕ) (is : List ℕ) (k : ℕ),
      f ∈ c.2.2 ∧ (codeAut c).relFrom q w v f ∧ accFrom L s v is k = some u) ∧
    (S = sink → w = [] ∧ u = []) ∧ (S = dummy → False)

private lemma pmeaning_of_relFrom {c : RelCode} {L : LCode} {S : ℕ} {w u : List ℕ}
    (h : (codeAut (prodCode c L)).relFrom S w u sink) : PMeaning c L S w u := by
  refine NFAO.relFrom_induction (M := codeAut (prodCode c L))
    (motive := fun S w u => PMeaning c L S w u) ⟨?_, ?_, ?_⟩ ?_ h
  · intro q s hs; exact absurd hs.symm (pair_ne_sink q s)
  · intro _; exact ⟨rfl, rfl⟩
  · intro hs; exact absurd hs sink_ne_dummy
  · intro S S' u₀ x w u htr _ ih
    have htr' : (S, u₀, x, S') ∈ prodTrans c L := htr
    rcases mem_prodTrans htr' with ⟨t, ht, s, -, z, hz, heq⟩ | ⟨q, hq, e, he, heq⟩ |
      ⟨a, -, heq⟩
    · have e1 : S = pair t.1 s := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.1) heq
      have e2 : u₀ = t.2.1 := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.1) heq
      have e3 : x = z.2 := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.2.1) heq
      have e4 : S' = pair t.2.2.2 z.1 := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.2.2) heq
      refine ⟨?_, ?_, ?_⟩
      · intro q₂ s₂ hq₂
        rw [e1] at hq₂
        obtain ⟨hqq, hss⟩ := pair_inj hq₂.symm
        subst hqq; subst hss
        obtain ⟨v, f, is, k, hf, hrel, hacc⟩ := ih.1 t.2.2.2 z.1 e4
        obtain ⟨is₁, hp₁⟩ := (mem_allPathsOver t.2.2.1 s₂ z.1 z.2).1 (by simpa using hz)
        refine ⟨t.2.2.1 ++ v, f, is₁ ++ is, k, hf, ?_, ?_⟩
        · have hm : (t.1, t.2.1, t.2.2.1, t.2.2.2) ∈ (codeAut c).δ := ht
          rw [e2]
          exact NFAO.relFrom_step hm hrel
        · rw [e3]
          exact accFrom_append L hp₁ hacc
      · intro hs; rw [e1] at hs; exact absurd hs (pair_ne_sink t.1 s)
      · intro hs; rw [e1] at hs; exact absurd hs (pair_ne_dummy t.1 s)
    · have e1 : S = pair q e.1 := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.1) heq
      have e2 : u₀ = ([] : List ℕ) := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.1) heq
      have e3 : x = e.2 := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.2.1) heq
      have e4 : S' = sink := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.2.2) heq
      obtain ⟨hw, hu⟩ := ih.2.1 e4
      refine ⟨?_, ?_, ?_⟩
      · intro q₂ s₂ hq₂
        rw [e1] at hq₂
        obtain ⟨hqq, hss⟩ := pair_inj hq₂.symm
        subst hqq; subst hss
        obtain ⟨k, hk⟩ := exists_index he
        refine ⟨[], q₂, [], k, hq, ?_, ?_⟩
        · rw [e2, hw]
          simpa using (codeAut c).relFrom_nil q₂
        · rw [e3, hu]
          simp only [accFrom_nil_nil, term, hk, Option.bind_some]
          simp
      · intro hs; rw [e1] at hs; exact absurd hs (pair_ne_sink q e.1)
      · intro hs; rw [e1] at hs; exact absurd hs (pair_ne_dummy q e.1)
    · have e1 : S = dummy := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.1) heq
      have e4 : S' = dummy := congrArg (fun x : ℕ × List ℕ × List ℕ × ℕ => x.2.2.2) heq
      exact absurd (ih.2.2 e4) not_false

/-- **Soundness of the product.** -/
theorem codeRel_prodCode_iff (c : RelCode) (L : LCode) (w u : List ℕ) :
    codeRel (prodCode c L) w u ↔ ∃ v, codeRel c w v ∧ rel L v u := by
  constructor
  · intro h
    obtain ⟨S, hS, T, hT, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    have hTs : T = sink := by
      have : T ∈ [sink] := hT
      simpa using this
    subst hTs
    have hSi : S ∈ c.2.1.flatMap (fun q => L.2.1.map (fun s => pair q s)) := hS
    rw [List.mem_flatMap] at hSi
    obtain ⟨q₀, hq₀, hSm⟩ := hSi
    rw [List.mem_map] at hSm
    obtain ⟨s₀, hs₀, hSeq⟩ := hSm
    obtain ⟨v, f, is, k, hf, hrelc, hacc⟩ :=
      (pmeaning_of_relFrom hrel).1 q₀ s₀ hSeq.symm
    obtain ⟨j, hj⟩ := exists_index hs₀
    exact ⟨v, (NFAO.rel_iff_relFrom _ _ _).2 ⟨q₀, hq₀, f, hf, hrelc⟩, ⟨j, s₀, k, is, hj, hacc⟩⟩
  · rintro ⟨v, hc, hL⟩
    exact codeRel_prodCode_of hc hL

/-! ## The composition of a code with its section -/

/-- **The composition of a code with a section of it.** -/
def invCode (c : RelCode) : RelCode := prodCode c (secLCode c)

open Classical in
/-- The section, as a function.  It is only meaningful on the range of the code. -/
noncomputable def secFun (c : RelCode) (v : List ℕ) : List ℕ :=
  if h : ∃ u, rel (secLCode c) v u then h.choose else []

lemma rel_secFun {c : RelCode} {v : List ℕ} (h : dom (secLCode c) v) :
    rel (secLCode c) v (secFun c v) := by
  have hd : ∃ u, rel (secLCode c) v u := h
  rw [secFun, dif_pos hd]
  exact hd.choose_spec

lemma secFun_eq {c : RelCode} {v u : List ℕ} (h : rel (secLCode c) v u) : secFun c v = u :=
  secLCode_functional (rel_secFun ⟨u, h⟩) h

/-- A string that a code relates to something is a string over the alphabet of the code. -/
theorem codeWord_of_codeRel {c : RelCode} {w v : List ℕ} (h : codeRel c w v) : CodeWord c w := by
  obtain ⟨ts, ⟨q₀, _, p₀, _, hpath⟩, hin, -⟩ := h
  intro x hx
  refine mem_codeAlphabet_of_mem_input (fun t ht => LabAut.Path.mem_delta hpath t ht) ?_
  rw [hin]; exact hx

/-- The section maps every value of the code back to a string over the alphabet of the code that
the code maps to it. -/
theorem secFun_spec {c : RelCode} {w v : List ℕ} (h : codeRel c w v) :
    CodeWord c (secFun c v) ∧ codeRel c (secFun c v) v := by
  have hcr : codeRel c (secFun c v) v := secLCode_sound (rel_secFun (secLCode_dom h))
  exact ⟨codeWord_of_codeRel hcr, hcr⟩

/-- **The composition of a code with a section of it computes what it should.** -/
theorem codeRel_invCode (c : RelCode) (w u : List ℕ) :
    codeRel (invCode c) w u ↔ ∃ v, codeRel c w v ∧ u = secFun c v := by
  rw [invCode, codeRel_prodCode_iff]
  constructor
  · rintro ⟨v, hc, hL⟩
    exact ⟨v, hc, (secFun_eq hL).symm⟩
  · rintro ⟨v, hc, rfl⟩
    exact ⟨v, hc, rel_secFun (secLCode_dom hc)⟩

lemma codeWord_invCode {c : RelCode} {w : List ℕ} : CodeWord (invCode c) w ↔ CodeWord c w :=
  codeWord_prodCode

/-- The composition of a code with a section of it is again a function, on the alphabet of the
code, as soon as the code is. -/
theorem codeFunctional_invCode {c : RelCode} (hc : CodeFunctional c) :
    CodeFunctional (invCode c) := by
  intro w hw
  have hw' : CodeWord c w := codeWord_invCode.1 hw
  obtain ⟨v, hv, huniq⟩ := hc w hw'
  refine ⟨secFun c v, (codeRel_invCode c w _).2 ⟨v, hv, rfl⟩, ?_⟩
  intro u hu
  obtain ⟨v', hv', rfl⟩ := (codeRel_invCode c w u).1 hu
  rw [huniq v' hv']

end LAut

end Transducers.Exercises
