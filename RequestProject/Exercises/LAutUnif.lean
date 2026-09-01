/-
**Uniformisation of a letter automaton, as an explicit construction on codes.**

This is the effective form of the Uniformisation Lemma `lem:uniformisation` of *Transducers*
(M. Bojańczyk) for the machine model of `RequestProject/Exercises/LAut.lean`: from a code `L` one
computes a code `unifLCode L` whose relation is contained in that of `L`, has the same domain,
and is a *function*.

The construction is the classical selection of the lexicographically least accepting run.  A
state of `unifLCode L` is a pair `(q, S)`: the state `q` of the run that is being guessed,
together with the set `S` of the states of the runs that have already *diverged below* it —
runs that agreed with the guessed run up to some position, where they took a smaller transition
(or started from an earlier initial state).  The automaton may stop in `(q, S)` only if `q`
admits a terminal entry and no state of `S` does; that is exactly the statement that the guessed
run is the least accepting one, and it makes the automaton unambiguous.
-/
import RequestProject.Exercises.LAut
import Mathlib.Data.List.Sublists

namespace Transducers.Exercises

namespace LAut

/-! ## Generic facts about codes -/

lemma mem_of_step {M : LCode} {q a I : ℕ} {r : ℕ × List ℕ} (h : step M q a I = some r) :
    (q, a, r.2, r.1) ∈ M.1 := by
  rw [step, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, ht'⟩ := h
  have htmem : t ∈ M.1 := List.mem_of_getElem? ht
  split_ifs at ht' with hc
  · have hr : (t.2.2.2, t.2.2.1) = r := Option.some.inj ht'
    obtain ⟨hc1, hc2⟩ := hc
    have : (q, a, r.2, r.1) = t := by
      rw [← hr, ← hc1, ← hc2]
    rw [this]
    exact htmem

lemma step_of_mem {M : LCode} {q a : ℕ} {y : List ℕ} {q' : ℕ} (h : (q, a, y, q') ∈ M.1) :
    ∃ I, step M q a I = some (q', y) := by
  obtain ⟨I, hI, hIe⟩ := List.mem_iff_getElem.1 h
  refine ⟨I, ?_⟩
  rw [step, List.getElem?_eq_getElem hI, hIe]
  simp

lemma mem_of_term {M : LCode} {q k : ℕ} {e : List ℕ} (h : term M q k = some e) : (q, e) ∈ M.2.2 := by
  rw [term, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, ht'⟩ := h
  have htmem : t ∈ M.2.2 := List.mem_of_getElem? ht
  split_ifs at ht' with hc
  · have he : t.2 = e := Option.some.inj ht'
    have : (q, e) = t := by rw [← he, ← hc]
    rw [this]; exact htmem

lemma term_of_mem {M : LCode} {q : ℕ} {e : List ℕ} (h : (q, e) ∈ M.2.2) :
    ∃ k, term M q k = some e := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 h
  refine ⟨k, ?_⟩
  rw [term, List.getElem?_eq_getElem hk, hke]
  simp

lemma init_of_mem {M : LCode} {q : ℕ} (h : q ∈ M.2.1) : ∃ j : ℕ, M.2.1[j]? = some q := by
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 h
  exact ⟨j, by rw [List.getElem?_eq_getElem hj, hje]⟩

/-! ## The states of a code -/

/-- The states that a code mentions. -/
def states (L : LCode) : List ℕ :=
  L.2.1 ++ L.1.flatMap (fun t => [t.1, t.2.2.2]) ++ L.2.2.map Prod.fst

lemma mem_states_of_init {L : LCode} {q : ℕ} (h : q ∈ L.2.1) : q ∈ states L := by
  simp [states, h]

lemma mem_states_of_step {L : LCode} {q a I : ℕ} {r : ℕ × List ℕ} (h : step L q a I = some r) :
    r.1 ∈ states L := by
  have hmem := mem_of_step h
  simp only [states, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨_, hmem, by simp⟩)

/-- The canonical form of a set of states: the states of `L` that belong to it, listed in the
order of `states L`. -/
def canon (L : LCode) (S : List ℕ) : List ℕ := (states L).filter (fun q => decide (q ∈ S))

@[simp] lemma mem_canon {L : LCode} {S : List ℕ} {q : ℕ} :
    q ∈ canon L S ↔ q ∈ states L ∧ q ∈ S := by
  simp [canon, List.mem_filter]

lemma canon_sublist (L : LCode) (S : List ℕ) : canon L S ∈ (states L).sublists :=
  List.mem_sublists.2 List.filter_sublist

lemma canon_idem (L : LCode) (S : List ℕ) : canon L (canon L S) = canon L S := by
  simp only [canon]
  apply List.filter_congr
  intro q hq
  simp [hq]

/-- Encoding of a pair (state, set of states) as a state of the uniformised automaton. -/
def enc (q : ℕ) (S : List ℕ) : ℕ := Encodable.encode (q, S)

lemma enc_inj {q q' : ℕ} {S S' : List ℕ} (h : enc q S = enc q' S') : q = q' ∧ S = S' := by
  have := Encodable.encode_injective h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-! ## The construction -/

/-- The states reachable in one step from a state of `S`, reading `a`. -/
def succSet (L : LCode) (S : List ℕ) (a : ℕ) : List ℕ :=
  S.flatMap fun s => (List.range L.1.length).filterMap fun i => (step L s a i).map Prod.fst

/-- The states reachable from `q` reading `a` by a transition whose index is below `i`. -/
def smallerSet (L : LCode) (q a i : ℕ) : List ℕ :=
  (List.range i).filterMap fun j => (step L q a j).map Prod.fst

/-- The initial states of `L` that come before the index `j`. -/
def initsBefore (L : LCode) (j : ℕ) : List ℕ :=
  (List.range j).filterMap fun j' => L.2.1[j']?

lemma mem_succSet {L : LCode} {S : List ℕ} {a r : ℕ} :
    r ∈ succSet L S a ↔ ∃ s ∈ S, ∃ i y, step L s a i = some (r, y) := by
  simp only [succSet, List.mem_flatMap, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
  constructor
  · rintro ⟨s, hs, i, -, z, hz, hzr⟩
    exact ⟨s, hs, i, z.2, by rw [hz, ← hzr]⟩
  · rintro ⟨s, hs, i, y, hi⟩
    exact ⟨s, hs, i, step_isSome_lt (by rw [hi]; simp), (r, y), hi, rfl⟩

lemma mem_smallerSet {L : LCode} {q a i r : ℕ} :
    r ∈ smallerSet L q a i ↔ ∃ j < i, ∃ y, step L q a j = some (r, y) := by
  simp only [smallerSet, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
  constructor
  · rintro ⟨j, hj, z, hz, hzr⟩
    exact ⟨j, hj, z.2, by rw [hz, ← hzr]⟩
  · rintro ⟨j, hj, y, hy⟩
    exact ⟨j, hj, (r, y), hy, rfl⟩

lemma mem_initsBefore {L : LCode} {j q : ℕ} :
    q ∈ initsBefore L j ↔ ∃ j' < j, L.2.1[j']? = some q := by
  simp only [initsBefore, List.mem_filterMap, List.mem_range]

/-- The state of `unifLCode L` reached after a transition of index `i` from the state `(q, S)`
reading `a`. -/
def nextSet (L : LCode) (q : ℕ) (S : List ℕ) (a i : ℕ) : List ℕ :=
  canon L (succSet L S a ++ smallerSet L q a i)

/-- **The uniformisation of a letter automaton.** -/
def unifLCode (L : LCode) : LCode :=
  ( (List.range L.1.length).flatMap (fun i =>
      ((states L).sublists).filterMap (fun S =>
        (L.1[i]?).map (fun t =>
          (enc t.1 (canon L S), t.2.1, t.2.2.1,
            enc t.2.2.2 (nextSet L t.1 (canon L S) t.2.1 i))))),
    (List.range L.2.1.length).filterMap (fun j =>
      (L.2.1[j]?).map (fun q => enc q (canon L (initsBefore L j)))),
    (states L).flatMap (fun q =>
      ((states L).sublists).filterMap (fun S =>
        if (canon L S).all (fun p => (leastTerm L p).isNone) then
          ((leastTerm L q).bind (fun k => term L q k)).map (fun e => (enc q (canon L S), e))
        else none)) )

/-! ### The transitions of the uniformisation -/

lemma step_unif_sound {L : LCode} {s a I : ℕ} {r : ℕ × List ℕ}
    (h : step (unifLCode L) s a I = some r) :
    ∃ (q q' i : ℕ) (S : List ℕ), s = enc q (canon L S) ∧ step L q a i = some (q', r.2) ∧
      r.1 = enc q' (nextSet L q (canon L S) a i) := by
  have hmem := mem_of_step h
  simp only [unifLCode, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff] at hmem
  obtain ⟨i, hi, S, -, t, ht, hteq⟩ := hmem
  refine ⟨t.1, t.2.2.2, i, S, ?_, ?_, ?_⟩
  · have := congrArg (fun x : ℕ × ℕ × List ℕ × ℕ => x.1) hteq
    simpa using this.symm
  · have h2 := congrArg (fun x : ℕ × ℕ × List ℕ × ℕ => x.2.1) hteq
    have h3 := congrArg (fun x : ℕ × ℕ × List ℕ × ℕ => x.2.2.1) hteq
    simp only at h2 h3
    rw [step, ht]
    simp only [Option.bind_some]
    simp only [true_and, if_pos h2, h3]
  · have h4 := congrArg (fun x : ℕ × ℕ × List ℕ × ℕ => x.2.2.2) hteq
    have h2 := congrArg (fun x : ℕ × ℕ × List ℕ × ℕ => x.2.1) hteq
    simp only at h4 h2
    rw [← h4, ← h2]

lemma step_unif_complete {L : LCode} {q q' a i : ℕ} {y : List ℕ} {S : List ℕ}
    (h : step L q a i = some (q', y)) :
    ∃ I, step (unifLCode L) (enc q (canon L S)) a I =
      some (enc q' (nextSet L q (canon L S) a i), y) := by
  have hmem : (enc q (canon L S), a, y, enc q' (nextSet L q (canon L S) a i)) ∈ (unifLCode L).1 := by
    simp only [unifLCode, List.mem_flatMap, List.mem_filterMap, List.mem_range,
      Option.map_eq_some_iff]
    refine ⟨i, step_isSome_lt (by rw [h]; simp), canon L S, canon_sublist L S,
      (q, a, y, q'), ?_, by rw [canon_idem]⟩
    rw [step, Option.bind_eq_some_iff] at h
    obtain ⟨t, ht, ht'⟩ := h
    split_ifs at ht' with hc
    · have hr : (t.2.2.2, t.2.2.1) = (q', y) := Option.some.inj ht'
      obtain ⟨hc1, hc2⟩ := hc
      have h1 : t.2.2.2 = q' := congrArg Prod.fst hr
      have h2 : t.2.2.1 = y := congrArg Prod.snd hr
      have : (q, a, y, q') = t := by rw [← hc1, ← hc2, ← h1, ← h2]
      rw [this]; exact ht
  exact step_of_mem hmem

/-! ### The terminal entries of the uniformisation -/

lemma term_unif_sound {L : LCode} {s k' : ℕ} {e : List ℕ}
    (h : term (unifLCode L) s k' = some e) :
    ∃ (q k : ℕ) (S : List ℕ), s = enc q (canon L S) ∧ leastTerm L q = some k ∧
      term L q k = some e ∧ ∀ p ∈ canon L S, leastTerm L p = none := by
  have hmem := mem_of_term h
  simp only [unifLCode, List.mem_flatMap, List.mem_filterMap] at hmem
  obtain ⟨q, -, S, -, hS⟩ := hmem
  split_ifs at hS with hall
  · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at hS
    obtain ⟨e', ⟨k, hk, hke⟩, heq⟩ := hS
    refine ⟨q, k, S, ?_, hk, ?_, ?_⟩
    · have := congrArg (fun x : ℕ × List ℕ => x.1) heq
      simpa using this.symm
    · have := congrArg (fun x : ℕ × List ℕ => x.2) heq
      simp only at this
      rw [hke, this]
    · intro p hp
      have := List.all_eq_true.1 hall p hp
      simpa using this

lemma term_unif_complete {L : LCode} {q k : ℕ} {e : List ℕ} {S : List ℕ}
    (hq : q ∈ states L) (hk : leastTerm L q = some k) (hke : term L q k = some e)
    (hS : ∀ p ∈ canon L S, leastTerm L p = none) :
    ∃ k', term (unifLCode L) (enc q (canon L S)) k' = some e := by
  refine term_of_mem ?_
  simp only [unifLCode, List.mem_flatMap, List.mem_filterMap]
  refine ⟨q, hq, canon L S, canon_sublist L S, ?_⟩
  rw [canon_idem]
  rw [if_pos (List.all_eq_true.2 (fun p hp => by rw [hS p hp]; simp))]
  simp [hk, hke]

/-! ### The initial states of the uniformisation -/

lemma init_unif_sound {L : LCode} {j' s : ℕ} (h : (unifLCode L).2.1[j']? = some s) :
    ∃ (j q : ℕ), L.2.1[j]? = some q ∧ s = enc q (canon L (initsBefore L j)) := by
  have hmem : s ∈ (unifLCode L).2.1 := List.mem_of_getElem? h
  simp only [unifLCode, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hmem
  obtain ⟨j, -, q, hq, hqs⟩ := hmem
  exact ⟨j, q, hq, hqs.symm⟩

lemma init_unif_complete {L : LCode} {j q : ℕ} (h : L.2.1[j]? = some q) :
    ∃ j' : ℕ, (unifLCode L).2.1[j']? = some (enc q (canon L (initsBefore L j))) := by
  refine init_of_mem ?_
  simp only [unifLCode, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
  refine ⟨j, ?_, q, h, rfl⟩
  by_contra hj
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

/-! ## The divergence set along a path -/

/-- The set of states of the runs that have diverged below the path with indices `is`, after
that path has been followed from `q` over `v`, starting from the set `S`. -/
def divSet (L : LCode) : ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | _, S, [], _ => S
  | q, S, a :: v, i :: is =>
      match step L q a i with
      | some r => divSet L r.1 (nextSet L q S a i) v is
      | none => S
  | _, S, _ :: _, [] => S
  termination_by _ _ v _ => v.length

@[simp] lemma divSet_nil (L : LCode) (q : ℕ) (S is : List ℕ) : divSet L q S [] is = S := by
  match is with
  | [] => simp [divSet]
  | _ :: _ => simp [divSet]

lemma divSet_cons (L : LCode) (q a i : ℕ) (S v is : List ℕ) {r : ℕ × List ℕ}
    (h : step L q a i = some r) :
    divSet L q S (a :: v) (i :: is) = divSet L r.1 (nextSet L q S a i) v is := by
  rw [divSet, h]

/-- **Any run of the uniformisation projects to a run of the original automaton**, and its state
records the divergence set. -/
lemma pathFrom_unif_sound {L : LCode} : ∀ (v : List ℕ) (q : ℕ) (S : List ℕ) (Is : List ℕ)
    (s' : ℕ) (u : List ℕ), pathFrom (unifLCode L) (enc q (canon L S)) v Is = some (s', u) →
    ∃ is q', pathFrom L q v is = some (q', u) ∧ s' = enc q' (divSet L q (canon L S) v is) := by
  intro v
  induction v with
  | nil =>
      intro q S Is s' u h
      match Is with
      | [] =>
          simp only [pathFrom_nil_nil, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          exact ⟨[], q, by simp [← h2], by simp [← h1]⟩
      | _ :: _ => simp at h
  | cons a v ih =>
      intro q S Is s' u h
      match Is with
      | [] => simp at h
      | I :: Is =>
          rw [pathFrom_cons_cons] at h
          cases hstep : step (unifLCode L) (enc q (canon L S)) a I with
          | none => rw [hstep] at h; simp at h
          | some r =>
              rw [hstep, Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨z, hz, hzeq⟩ := h
              obtain ⟨q₀, q', i, S₀, hs, hstepL, hr⟩ := step_unif_sound hstep
              obtain ⟨hq₀, hS₀⟩ := enc_inj hs
              subst hq₀
              rw [← hS₀] at hr
              have hz' : pathFrom (unifLCode L) (enc q' (nextSet L q (canon L S) a i)) v Is =
                  some z := by
                rw [← hr]; exact hz
              obtain ⟨is, q'', hpath, hst⟩ :=
                ih q' (succSet L (canon L S) a ++ smallerSet L q a i) Is z.1 z.2 hz'
              refine ⟨i :: is, q'', ?_, ?_⟩
              · rw [pathFrom_cons_cons, hstepL, Option.bind_some, hpath]
                have h2 : r.2 ++ z.2 = u := congrArg Prod.snd hzeq
                simp [h2]
              · have h1 : z.1 = s' := congrArg Prod.fst hzeq
                rw [← h1, hst, divSet_cons L q a i (canon L S) v is hstepL]
                rfl

/-- **Every run of the original automaton is realised by the uniformisation** (whose state then
records the divergence set); the acceptance condition is a separate matter. -/
lemma pathFrom_unif_complete {L : LCode} : ∀ (v is : List ℕ) (q q' : ℕ) (S : List ℕ) (u : List ℕ),
    pathFrom L q v is = some (q', u) →
    ∃ Is, pathFrom (unifLCode L) (enc q (canon L S)) v Is =
      some (enc q' (divSet L q (canon L S) v is), u) := by
  intro v
  induction v with
  | nil =>
      intro is q q' S u h
      match is with
      | [] =>
          simp only [pathFrom_nil_nil, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          exact ⟨[], by simp [← h1, ← h2]⟩
      | _ :: _ => simp at h
  | cons a v ih =>
      intro is q q' S u h
      match is with
      | [] => simp at h
      | i :: is =>
          rw [pathFrom_cons_cons] at h
          cases hstepL : step L q a i with
          | none => rw [hstepL] at h; simp at h
          | some r =>
              rw [hstepL, Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨z, hz, hzeq⟩ := h
              obtain ⟨I, hI⟩ := step_unif_complete (S := S) hstepL
              obtain ⟨Is, hIs⟩ := ih is r.1 z.1 (succSet L (canon L S) a ++ smallerSet L q a i)
                z.2 hz
              refine ⟨I :: Is, ?_⟩
              rw [pathFrom_cons_cons, hI, Option.bind_some]
              have hnext : nextSet L q (canon L S) a i =
                  canon L (succSet L (canon L S) a ++ smallerSet L q a i) := rfl
              rw [hnext, hIs]
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
              have h1 : z.1 = q' := congrArg Prod.fst hzeq
              have h2 : r.2 ++ z.2 = u := congrArg Prod.snd hzeq
              refine ⟨?_, h2⟩
              rw [h1, divSet_cons L q a i (canon L S) v is hstepL, hnext]

/-- **What the divergence set is**: the states reached either from the starting set, or by a run
that diverged below the given one. -/
lemma mem_divSet {L : LCode} : ∀ (v is : List ℕ) (q : ℕ) (S : List ℕ) (r : ℕ),
    (∀ x ∈ S, x ∈ states L) → ∀ (q' : ℕ) (u : List ℕ), pathFrom L q v is = some (q', u) →
    (r ∈ divSet L q S v is ↔
      (∃ s ∈ S, ∃ ks z, pathFrom L s v ks = some (r, z)) ∨
      (∃ ks z, LexLt ks is ∧ pathFrom L q v ks = some (r, z))) := by
  intro v
  induction v with
  | nil =>
      intro is q S r hS q' u hpath
      match is with
      | _ :: _ => simp at hpath
      | [] =>
        simp only [divSet_nil]
        constructor
        · intro hr
          exact Or.inl ⟨r, hr, [], [], by simp⟩
        · rintro (⟨s, hs, ks, z, hks⟩ | ⟨ks, z, hlex, -⟩)
          · match ks with
            | [] =>
                simp only [pathFrom_nil_nil, Option.some.injEq, Prod.mk.injEq] at hks
                rw [← hks.1]; exact hs
            | _ :: _ => simp at hks
          · cases hlex
  | cons a v ih =>
      intro is q S r hS q' u hpath
      match is with
      | [] => simp at hpath
      | i :: is =>
          rw [pathFrom_cons_cons] at hpath
          cases hstepL : step L q a i with
          | none => rw [hstepL] at hpath; simp at hpath
          | some r₁ =>
              rw [hstepL, Option.bind_some, Option.map_eq_some_iff] at hpath
              obtain ⟨z₀, hz₀, -⟩ := hpath
              have hS₁ : ∀ x ∈ nextSet L q S a i, x ∈ states L := by
                intro x hx
                exact (mem_canon.1 hx).1
              rw [divSet_cons L q a i S v is hstepL]
              rw [ih is r₁.1 (nextSet L q S a i) r hS₁ z₀.1 z₀.2 hz₀]
              constructor
              · rintro (⟨s, hs, ks, z, hks⟩ | ⟨ks, z, hlex, hks⟩)
                · have hs' := mem_canon.1 hs
                  rcases List.mem_append.1 hs'.2 with hsucc | hsmall
                  · obtain ⟨s₀, hs₀, i₀, y₀, hstep₀⟩ := mem_succSet.1 hsucc
                    exact Or.inl ⟨s₀, hs₀, i₀ :: ks, y₀ ++ z, by
                      rw [pathFrom_cons_cons, hstep₀, Option.bind_some, hks]; simp⟩
                  · obtain ⟨j, hj, y, hstepj⟩ := mem_smallerSet.1 hsmall
                    exact Or.inr ⟨j :: ks, y ++ z, LexLt.head hj, by
                      rw [pathFrom_cons_cons, hstepj, Option.bind_some, hks]; simp⟩
                · exact Or.inr ⟨i :: ks, r₁.2 ++ z, LexLt.tail hlex, by
                    rw [pathFrom_cons_cons, hstepL, Option.bind_some, hks]; simp⟩
              · rintro (⟨s, hs, ks, z, hks⟩ | ⟨ks, z, hlex, hks⟩)
                · match ks with
                  | [] => simp at hks
                  | k :: ks =>
                      rw [pathFrom_cons_cons] at hks
                      cases hstepk : step L s a k with
                      | none => rw [hstepk] at hks; simp at hks
                      | some s₁ =>
                          rw [hstepk, Option.bind_some, Option.map_eq_some_iff] at hks
                          obtain ⟨z₁, hz₁, hz₁eq⟩ := hks
                          refine Or.inl ⟨s₁.1, ?_, ks, z₁.2, ?_⟩
                          · refine mem_canon.2 ⟨mem_states_of_step hstepk, ?_⟩
                            exact List.mem_append.2 (Or.inl (mem_succSet.2
                              ⟨s, hs, k, s₁.2, hstepk⟩))
                          · have h1 : z₁.1 = r := congrArg Prod.fst hz₁eq
                            rw [hz₁, ← h1]
                · match ks with
                  | [] => cases hlex
                  | k :: ks =>
                      rw [pathFrom_cons_cons] at hks
                      cases hstepk : step L q a k with
                      | none => rw [hstepk] at hks; simp at hks
                      | some s₁ =>
                          rw [hstepk, Option.bind_some, Option.map_eq_some_iff] at hks
                          obtain ⟨z₁, hz₁, hz₁eq⟩ := hks
                          have h1 : z₁.1 = r := congrArg Prod.fst hz₁eq
                          cases hlex with
                          | head hlt =>
                              refine Or.inl ⟨s₁.1, ?_, ks, z₁.2, by rw [hz₁, ← h1]⟩
                              refine mem_canon.2 ⟨mem_states_of_step hstepk, ?_⟩
                              exact List.mem_append.2 (Or.inr (mem_smallerSet.2
                                ⟨k, hlt, s₁.2, hstepk⟩))
                          | tail hlex' =>
                              have hs₁ : s₁ = r₁ := by
                                rw [hstepL] at hstepk; exact (Option.some.inj hstepk).symm
                              refine Or.inr ⟨ks, z₁.2, hlex', ?_⟩
                              rw [← hs₁, hz₁, ← h1]

/-! ## The three properties of the uniformisation -/

lemma mem_states_of_pathFrom {L : LCode} : ∀ (v is : List ℕ) (q r : ℕ) (u : List ℕ),
    pathFrom L q v is = some (r, u) → q ∈ states L → r ∈ states L := by
  intro v
  induction v with
  | nil =>
      intro is q r u h hq
      match is with
      | [] =>
          simp only [pathFrom_nil_nil, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]; exact hq
      | _ :: _ => simp at h
  | cons a v ih =>
      intro is q r u h hq
      match is with
      | [] => simp at h
      | i :: is =>
          rw [pathFrom_cons_cons] at h
          cases hstep : step L q a i with
          | none => rw [hstep] at h; simp at h
          | some r₁ =>
              rw [hstep, Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨z, hz, hzeq⟩ := h
              have h1 : z.1 = r := congrArg Prod.fst hzeq
              exact ih is r₁.1 r z.2 (by rw [hz, ← h1]) (mem_states_of_step hstep)

lemma canon_divSet (L : LCode) : ∀ (v is : List ℕ) (q : ℕ) (S : List ℕ),
    canon L (divSet L q (canon L S) v is) = divSet L q (canon L S) v is := by
  intro v
  induction v with
  | nil => intro is q S; simp [canon_idem]
  | cons a v ih =>
      intro is q S
      match is with
      | [] => simp [divSet, canon_idem]
      | i :: is =>
          cases hstep : step L q a i with
          | none => rw [divSet, hstep]; exact canon_idem L S
          | some r =>
              rw [divSet_cons L q a i (canon L S) v is hstep]
              have hnext : nextSet L q (canon L S) a i =
                  canon L (succSet L (canon L S) a ++ smallerSet L q a i) := rfl
              rw [hnext]
              exact ih is r.1 _

/-- The relation computed by the uniformisation is contained in the original one. -/
theorem unifLCode_sound {L : LCode} {v u : List ℕ} (h : rel (unifLCode L) v u) : rel L v u := by
  obtain ⟨j', s, k', Is, hinit, hacc⟩ := h
  rw [accFrom, Option.bind_eq_some_iff] at hacc
  obtain ⟨z, hz, he⟩ := hacc
  rw [Option.map_eq_some_iff] at he
  obtain ⟨e, he, hue⟩ := he
  obtain ⟨j, q, hj, hs⟩ := init_unif_sound hinit
  rw [hs] at hz
  obtain ⟨is, q', hpath, hst⟩ := pathFrom_unif_sound v q _ Is z.1 z.2 (by rw [← hz])
  rw [hst] at he
  obtain ⟨q₂, k, S₂, hq₂, hlt, hterm, -⟩ := term_unif_sound he
  obtain ⟨hqq, -⟩ := enc_inj hq₂
  have hterm' : term L q' k = some e := by rw [hqq]; exact hterm
  exact ⟨j, q, k, is, hj, by simp [accFrom, hpath, hterm', ← hue]⟩

/-- The index of the first initial state from which an accepting run over `v` exists. -/
def leastInit (L : LCode) (v : List ℕ) : Option ℕ :=
  (List.range L.2.1.length).find? fun j =>
    match L.2.1[j]? with
    | some q => compFrom L q v
    | none => false

lemma leastInit_spec {L : LCode} {v : List ℕ} {j : ℕ} (h : leastInit L v = some j) :
    (∃ q, L.2.1[j]? = some q ∧ compFrom L q v = true) ∧
      ∀ j' < j, ∀ q', L.2.1[j']? = some q' → compFrom L q' v = false := by
  obtain ⟨-, h2, h3⟩ := find?_range_spec h
  constructor
  · cases hq : L.2.1[j]? with
    | none => rw [hq] at h2; simp at h2
    | some q => exact ⟨q, rfl, by rw [hq] at h2; exact h2⟩
  · intro j' hj' q' hq'
    have := h3 j' hj'
    rw [hq'] at this
    exact this

lemma leastInit_isSome {L : LCode} {v : List ℕ} {j q : ℕ} (hj : L.2.1[j]? = some q)
    (hq : compFrom L q v = true) : (leastInit L v).isSome = true := by
  cases hfind : leastInit L v with
  | some _ => simp
  | none =>
      have hjlt : j < L.2.1.length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega)] at hj
        simp at hj
      have := find?_range_none hfind j hjlt
      simp [hj, hq] at this

/-- The uniformisation has the same domain as the original automaton. -/
theorem unifLCode_dom {L : LCode} {v : List ℕ} (h : dom L v) : dom (unifLCode L) v := by
  obtain ⟨u, j, q, k, is, hj, hacc⟩ := h
  have hcomp : compFrom L q v = true := (compFrom_iff L v q).2 ⟨is, k, u, hacc⟩
  have hleast := leastInit_isSome hj hcomp
  cases hfind : leastInit L v with
  | none => rw [hfind] at hleast; simp at hleast
  | some j₀ =>
      obtain ⟨⟨q₀, hq₀, hcomp₀⟩, hmin⟩ := leastInit_spec hfind
      obtain ⟨r, z, hpath, hr⟩ := pathFrom_leastPathFrom L v q₀ hcomp₀
      have hkr := leastTerm_isSome hr
      cases hkfind : leastTerm L r with
      | none => rw [hkfind] at hkr; simp at hkr
      | some k₀ =>
          obtain ⟨hk₀, -⟩ := leastTerm_spec hkfind
          obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hk₀
          -- the run of the uniformisation that follows the canonical run of `L`
          obtain ⟨j', hj'⟩ := init_unif_complete hq₀
          obtain ⟨Is, hIs⟩ := pathFrom_unif_complete v (leastPathFrom L q₀ v) q₀ r
            (initsBefore L j₀) z hpath
          -- no state of the divergence set admits a terminal entry
          have hdiv : ∀ p ∈ divSet L q₀ (canon L (initsBefore L j₀)) v (leastPathFrom L q₀ v),
              leastTerm L p = none := by
            intro p hp
            have hS : ∀ x ∈ canon L (initsBefore L j₀), x ∈ states L := fun x hx => (mem_canon.1 hx).1
            rw [mem_divSet v (leastPathFrom L q₀ v) q₀ (canon L (initsBefore L j₀)) p hS r z hpath]
              at hp
            by_contra hcon
            obtain ⟨kp, hkp⟩ := Option.isSome_iff_exists.1 (by
              cases hcp : leastTerm L p with
              | none => exact absurd hcp hcon
              | some _ => simp : (leastTerm L p).isSome = true)
            have hcp : compFrom L p [] = true := compFrom_nil_of_leastTerm hkp
            rcases hp with ⟨s, hs, ks, zs, hks⟩ | ⟨ks, zs, hlex, hks⟩
            · obtain ⟨j₁, hj₁, hj₁e⟩ := mem_initsBefore.1 (mem_canon.1 hs).2
              have : compFrom L s v = true := compFrom_of_pathFrom hks hcp
              rw [hmin j₁ hj₁ s hj₁e] at this
              simp at this
            · have := not_compFrom_of_lexLt L v q₀ hcomp₀ ks hlex p zs hks
              rw [hcp] at this
              simp at this
          have hcanon : canon L (divSet L q₀ (canon L (initsBefore L j₀)) v
              (leastPathFrom L q₀ v)) = divSet L q₀ (canon L (initsBefore L j₀)) v
              (leastPathFrom L q₀ v) := canon_divSet L v (leastPathFrom L q₀ v) q₀ _
          have hrstates : r ∈ states L :=
            mem_states_of_pathFrom v _ q₀ r z hpath (mem_states_of_init (List.mem_of_getElem? hq₀))
          obtain ⟨k', hk'⟩ := term_unif_complete (S := divSet L q₀
            (canon L (initsBefore L j₀)) v (leastPathFrom L q₀ v)) hrstates hkfind he
            (by rw [hcanon]; exact hdiv)
          rw [hcanon] at hk'
          exact ⟨z ++ e, j', _, k', Is, hj', by rw [accFrom, hIs, Option.bind_some, hk']; simp⟩

lemma lexLt_total : ∀ (l l' : List ℕ), l.length = l'.length →
    l = l' ∨ LexLt l l' ∨ LexLt l' l := by
  intro l
  induction l with
  | nil =>
      intro l' hlen
      match l' with
      | [] => exact Or.inl rfl
      | _ :: _ => simp at hlen
  | cons a l ih =>
      intro l' hlen
      match l' with
      | [] => simp at hlen
      | b :: l' =>
          rcases lt_trichotomy a b with hab | rfl | hab
          · exact Or.inr (Or.inl (LexLt.head hab))
          · rcases ih l' (by simpa using hlen) with rfl | hlt | hlt
            · exact Or.inl rfl
            · exact Or.inr (Or.inl (LexLt.tail hlt))
            · exact Or.inr (Or.inr (LexLt.tail hlt))
          · exact Or.inr (Or.inr (LexLt.head hab))

/-- The data of an accepting run of the uniformisation, read off from the original automaton. -/
private lemma unif_run_data {L : LCode} {v u : List ℕ} (h : rel (unifLCode L) v u) :
    ∃ (j q r k : ℕ) (is z e : List ℕ),
      L.2.1[j]? = some q ∧ pathFrom L q v is = some (r, z) ∧ leastTerm L r = some k ∧
        term L r k = some e ∧ u = z ++ e ∧
        ∀ p ∈ divSet L q (canon L (initsBefore L j)) v is, leastTerm L p = none := by
  obtain ⟨j', s, k', Is, hinit, hacc⟩ := h
  rw [accFrom, Option.bind_eq_some_iff] at hacc
  obtain ⟨z, hz, he⟩ := hacc
  rw [Option.map_eq_some_iff] at he
  obtain ⟨e, he, hue⟩ := he
  obtain ⟨j, q, hj, hs⟩ := init_unif_sound hinit
  rw [hs] at hz
  obtain ⟨is, q', hpath, hst⟩ := pathFrom_unif_sound v q _ Is z.1 z.2 (by rw [← hz])
  rw [hst] at he
  obtain ⟨q₂, k, S₂, hq₂, hlt, hterm, hcond⟩ := term_unif_sound he
  obtain ⟨hqq, hSS⟩ := enc_inj hq₂
  refine ⟨j, q, q', k, is, z.2, e, hj, hpath, by rw [hqq]; exact hlt, by rw [hqq]; exact hterm,
    hue.symm, ?_⟩
  intro p hp
  exact hcond p (by rw [hSS] at hp; exact hp)

/-- **The uniformisation computes a function.** -/
theorem unifLCode_functional {L : LCode} {v u u' : List ℕ}
    (h : rel (unifLCode L) v u) (h' : rel (unifLCode L) v u') : u = u' := by
  obtain ⟨j₁, q₁, r₁, k₁, is₁, z₁, e₁, hj₁, hp₁, hk₁, ht₁, hu₁, hd₁⟩ := unif_run_data h
  obtain ⟨j₂, q₂, r₂, k₂, is₂, z₂, e₂, hj₂, hp₂, hk₂, ht₂, hu₂, hd₂⟩ := unif_run_data h'
  -- a run that diverges below another one cannot be accepting
  have key : ∀ (ja qa ra ka : ℕ) (isa za : List ℕ) (jb qb rb : ℕ) (isb zb : List ℕ),
      L.2.1[ja]? = some qa → pathFrom L qa v isa = some (ra, za) → leastTerm L ra = some ka →
      L.2.1[jb]? = some qb → pathFrom L qb v isb = some (rb, zb) →
      (∀ p ∈ divSet L qb (canon L (initsBefore L jb)) v isb, leastTerm L p = none) →
      (ja < jb ∨ (ja = jb ∧ LexLt isa isb)) → False := by
    intro ja qa ra ka isa za jb qb rb isb zb hja hpa hka hjb hpb hdb hcase
    have hS : ∀ x ∈ canon L (initsBefore L jb), x ∈ states L := fun x hx => (mem_canon.1 hx).1
    have hmem : ra ∈ divSet L qb (canon L (initsBefore L jb)) v isb := by
      rw [mem_divSet v isb qb (canon L (initsBefore L jb)) ra hS rb zb hpb]
      rcases hcase with hlt | ⟨rfl, hlex⟩
      · refine Or.inl ⟨qa, ?_, isa, za, hpa⟩
        exact mem_canon.2 ⟨mem_states_of_init (List.mem_of_getElem? hja),
          mem_initsBefore.2 ⟨ja, hlt, hja⟩⟩
      · have : qa = qb := by rw [hja] at hjb; exact Option.some.inj hjb
        subst this
        exact Or.inr ⟨isa, za, hlex, hpa⟩
    rw [hdb ra hmem] at hka
    simp at hka
  have hlen₁ : is₁.length = v.length := length_of_pathFrom L hp₁
  have hlen₂ : is₂.length = v.length := length_of_pathFrom L hp₂
  rcases lt_trichotomy j₁ j₂ with hj | rfl | hj
  · exact absurd (key j₁ q₁ r₁ k₁ is₁ z₁ j₂ q₂ r₂ is₂ z₂ hj₁ hp₁ hk₁ hj₂ hp₂ hd₂ (Or.inl hj))
      (by simp)
  · have hq : q₁ = q₂ := by rw [hj₁] at hj₂; exact Option.some.inj hj₂
    subst hq
    rcases lexLt_total is₁ is₂ (by rw [hlen₁, hlen₂]) with rfl | hlex | hlex
    · have hr : (r₁, z₁) = (r₂, z₂) := by rw [hp₁] at hp₂; exact Option.some.inj hp₂
      have hr1 : r₁ = r₂ := congrArg Prod.fst hr
      have hz : z₁ = z₂ := congrArg Prod.snd hr
      have hkk : k₁ = k₂ := by rw [hr1] at hk₁; rw [hk₁] at hk₂; exact Option.some.inj hk₂
      have hee : e₁ = e₂ := by
        rw [hr1, hkk] at ht₁; rw [ht₁] at ht₂; exact Option.some.inj ht₂
      rw [hu₁, hu₂, hz, hee]
    · exact absurd (key j₁ q₁ r₁ k₁ is₁ z₁ j₁ q₁ r₂ is₂ z₂ hj₁ hp₁ hk₁ hj₁ hp₂ hd₂
        (Or.inr ⟨rfl, hlex⟩)) (by simp)
    · exact absurd (key j₁ q₁ r₂ k₂ is₂ z₂ j₁ q₁ r₁ is₁ z₁ hj₁ hp₂ hk₂ hj₁ hp₁ hd₁
        (Or.inr ⟨rfl, hlex⟩)) (by simp)
  · exact absurd (key j₂ q₂ r₂ k₂ is₂ z₂ j₁ q₁ r₁ is₁ z₁ hj₂ hp₂ hk₂ hj₁ hp₁ hd₁ (Or.inl hj))
      (by simp)

end LAut

end Transducers.Exercises
