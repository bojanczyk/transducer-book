/-
Parikh's theorem for weighted graphs: the set of weights of the accepting paths of a finite
graph whose edges carry weights in `ℕ × ℕ` is a semilinear subset of `ℕ × ℕ`, and a semilinear
description of it can be computed from the graph.

The proof is the classical state-elimination (Kleene) argument, carried out directly on weights
instead of on words: for a set `S` of states allowed in the *interior* of a path, the weights of
the paths from `p` to `q` through `S` form a semilinear set `kleene G S p q`, computed by
induction on `S` from union, Minkowski sum and the generated submonoid -- the three operations
of `RequestProject/Exercises/Semilinear.lean`.

Nothing here is about transducers.  The file is used by
`RequestProject/Exercises/LengthCollision.lean`, item (b) of Exercise
`exer:decide-rational-colision`.
-/
import RequestProject.Exercises.Semilinear

namespace Transducers
namespace Exercises

/-! ## Weighted graphs -/

/-- An edge of a weighted graph: a source state, a weight, and a target state. -/
abbrev WEdge : Type := ℕ × (ℕ × ℕ) × ℕ

/-- A finite graph with weights in `ℕ × ℕ`: a list of edges, a list of initial states and a list
of final states. -/
abbrev WGraph : Type := List WEdge × List ℕ × List ℕ

/-- `IsPath G p es q` says that `es` is a path of `G` from `p` to `q`. -/
def IsPath (G : WGraph) : ℕ → List WEdge → ℕ → Prop
  | p, [], q => p = q
  | p, e :: es, q => e ∈ G.1 ∧ e.1 = p ∧ IsPath G e.2.2 es q

@[simp] lemma isPath_nil {G : WGraph} {p q : ℕ} : IsPath G p [] q ↔ p = q := Iff.rfl

@[simp] lemma isPath_cons {G : WGraph} {p q : ℕ} {e : WEdge} {es : List WEdge} :
    IsPath G p (e :: es) q ↔ e ∈ G.1 ∧ e.1 = p ∧ IsPath G e.2.2 es q := Iff.rfl

/-- The weight of a path: the sum of the weights of its edges. -/
def pathWt (es : List WEdge) : ℕ × ℕ := (es.map (fun e => e.2.1)).sum

@[simp] lemma pathWt_nil : pathWt [] = 0 := rfl

@[simp] lemma pathWt_cons (e : WEdge) (es : List WEdge) :
    pathWt (e :: es) = e.2.1 + pathWt es := rfl

lemma pathWt_append (A B : List WEdge) : pathWt (A ++ B) = pathWt A + pathWt B := by
  simp [pathWt, List.map_append]

/-- The interior states of a path: the targets of all its edges but the last. -/
def interior : List WEdge → List ℕ
  | [] => []
  | [_] => []
  | e :: f :: es => e.2.2 :: interior (f :: es)

@[simp] lemma interior_nil : interior [] = [] := rfl

@[simp] lemma interior_singleton (e : WEdge) : interior [e] = [] := rfl

lemma interior_cons_of_ne_nil (e : WEdge) {l : List WEdge} (h : l ≠ []) :
    interior (e :: l) = e.2.2 :: interior l := by
  cases l with
  | nil => exact absurd rfl h
  | cons f l => rfl

lemma interior_append (A : List WEdge) {B : List WEdge} (hB : B ≠ []) :
    interior (A ++ B) = A.map (fun e => e.2.2) ++ interior B := by
  induction A with
  | nil => simp
  | cons e A ih =>
      have hne : A ++ B ≠ [] := by
        intro h
        exact hB (List.append_eq_nil_iff.1 h).2
      rw [List.cons_append, interior_cons_of_ne_nil e hne, ih, List.map_cons, List.cons_append]

lemma eq_nil_or_singleton_of_interior_nil :
    ∀ {es : List WEdge}, interior es = [] → es = [] ∨ ∃ e, es = [e]
  | [], _ => Or.inl rfl
  | [e], _ => Or.inr ⟨e, rfl⟩
  | _ :: _ :: _, h => by simp [interior] at h

/-- The targets of the edges of a path from `p` to `q` are its interior states followed by `q`. -/
lemma map_target_eq {G : WGraph} : ∀ {A : List WEdge} {p q : ℕ}, IsPath G p A q → A ≠ [] →
    A.map (fun e => e.2.2) = interior A ++ [q]
  | [], _, _, _, h => absurd rfl h
  | [e], p, q, h, _ => by
      have : e.2.2 = q := h.2.2
      simp [this]
  | e :: f :: A, p, q, h, _ => by
      have ih := map_target_eq (A := f :: A) h.2.2 (by simp)
      rw [List.map_cons, ih, interior_cons_of_ne_nil e (by simp), List.cons_append]

/-! ## Paths with a restricted interior -/

/-- A path from `p` to `q` all of whose interior states lie in `S`. -/
def PathIn (G : WGraph) (S : List ℕ) (p : ℕ) (es : List WEdge) (q : ℕ) : Prop :=
  IsPath G p es q ∧ ∀ r ∈ interior es, r ∈ S

/-- The set of weights of the paths from `p` to `q` with interior in `S`. -/
def wSet (G : WGraph) (S : List ℕ) (p q : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ es, PathIn G S p es q ∧ x = pathWt es}

lemma PathIn.mono {G : WGraph} {S T : List ℕ} {p q : ℕ} {es : List WEdge}
    (h : PathIn G S p es q) (hST : ∀ r ∈ S, r ∈ T) : PathIn G T p es q :=
  ⟨h.1, fun r hr => hST r (h.2 r hr)⟩

lemma wSet_mono {G : WGraph} {S T : List ℕ} {p q : ℕ} (hST : ∀ r ∈ S, r ∈ T) :
    wSet G S p q ⊆ wSet G T p q := by
  rintro x ⟨es, h, rfl⟩
  exact ⟨es, h.mono hST, rfl⟩

lemma isPath_append {G : WGraph} : ∀ {A : List WEdge} {p r q : ℕ} {B : List WEdge},
    IsPath G p A r → IsPath G r B q → IsPath G p (A ++ B) q
  | [], p, r, q, B, h1, h2 => by
      cases h1; exact h2
  | e :: A, p, r, q, B, h1, h2 =>
      ⟨h1.1, h1.2.1, isPath_append h1.2.2 h2⟩

lemma concatPath {G : WGraph} {T : List ℕ} {p r q : ℕ} {A B : List WEdge}
    (h1 : PathIn G T p A r) (h2 : PathIn G T r B q) (hr : r ∈ T) :
    PathIn G T p (A ++ B) q := by
  refine ⟨isPath_append h1.1 h2.1, ?_⟩
  rcases eq_or_ne B [] with rfl | hB
  · simpa using h1.2
  rcases eq_or_ne A [] with rfl | hA
  · simpa using h2.2
  rw [interior_append A hB, map_target_eq h1.1 hA]
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · rcases List.mem_append.1 hs with hs | hs
    · exact h1.2 s hs
    · rw [List.mem_singleton.1 hs]; exact hr
  · exact h2.2 s hs

/-! ## Splitting a path at a state -/

/-- A path whose interior lies in `v :: S` either avoids `v` altogether, or splits at the first
visit of `v` into a nonempty initial segment with interior in `S` and a remainder. -/
lemma pathIn_split {G : WGraph} {v : ℕ} {S : List ℕ} :
    ∀ {es : List WEdge} {p q : ℕ}, PathIn G (v :: S) p es q →
      PathIn G S p es q ∨
        ∃ A B, es = A ++ B ∧ A ≠ [] ∧ PathIn G S p A v ∧ PathIn G (v :: S) v B q
  | [], p, q, h => Or.inl ⟨h.1, by simp⟩
  | e :: es, p, q, h => by
      rcases eq_or_ne es [] with rfl | hes
      · exact Or.inl ⟨h.1, by simp⟩
      have hint : interior (e :: es) = e.2.2 :: interior es := interior_cons_of_ne_nil e hes
      have hmem : e.2.2 ∈ v :: S := h.2 _ (by rw [hint]; exact List.mem_cons_self ..)
      have hrest : ∀ r ∈ interior es, r ∈ v :: S := by
        intro r hr; exact h.2 r (by rw [hint]; exact List.mem_cons_of_mem _ hr)
      rcases List.mem_cons.1 hmem with hv | hv
      · refine Or.inr ⟨[e], es, rfl, by simp, ⟨⟨h.1.1, h.1.2.1, ?_⟩, by simp⟩, ⟨?_, hrest⟩⟩
        · exact hv
        · rw [← hv]; exact h.1.2.2
      · have hsub : PathIn G (v :: S) e.2.2 es q := ⟨h.1.2.2, hrest⟩
        rcases pathIn_split hsub with hl | ⟨A, B, rfl, hA, hpA, hpB⟩
        · exact Or.inl ⟨h.1, by
            rw [hint]
            intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · exact hv
            · exact hl.2 r hr⟩
        · refine Or.inr ⟨e :: A, B, rfl, by simp, ⟨⟨h.1.1, h.1.2.1, hpA.1⟩, ?_⟩, hpB⟩
          rw [interior_cons_of_ne_nil e hA]
          intro r hr
          rcases List.mem_cons.1 hr with rfl | hr
          · exact hv
          · exact hpA.2 r hr

/-! ## Loops -/

lemma mem_starSet_of_mem {A : Set (ℕ × ℕ)} {a x : ℕ × ℕ} (ha : a ∈ A) (hx : x ∈ starSet A) :
    a + x ∈ starSet A := by
  obtain ⟨L, hL, rfl⟩ := hx
  refine ⟨a :: L, ?_, by simp⟩
  intro y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact ha
  · exact hL y hy

lemma mem_sumSet_star_right {A B : Set (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ B) :
    x ∈ sumSet (starSet A) B :=
  ⟨0, zero_mem_starSet A, x, hx, by simp⟩

/-- Any finite family of loop weights at `v` is realised by a single loop at `v`. -/
lemma loopPath {G : WGraph} {S : List ℕ} {v : ℕ} :
    ∀ {L : List (ℕ × ℕ)}, (∀ y ∈ L, y ∈ wSet G S v v) →
      ∃ es, PathIn G (v :: S) v es v ∧ pathWt es = L.sum
  | [], _ => ⟨[], ⟨rfl, by simp⟩, by simp⟩
  | y :: L, hL => by
      obtain ⟨es₁, h₁, rfl⟩ := hL y (by simp)
      obtain ⟨es₂, h₂, h₂w⟩ := loopPath (L := L) (fun z hz => hL z (List.mem_cons_of_mem _ hz))
      refine ⟨es₁ ++ es₂, concatPath (h₁.mono (fun r hr => List.mem_cons_of_mem _ hr)) h₂
        (List.mem_cons_self ..), ?_⟩
      rw [pathWt_append, h₂w, List.sum_cons]

/-- Peeling the loops at `v` off a path that starts at `v`. -/
lemma pathWt_peel {G : WGraph} {S : List ℕ} {v q : ℕ} :
    ∀ (n : ℕ) (es : List WEdge), es.length ≤ n → PathIn G (v :: S) v es q →
      pathWt es ∈ sumSet (starSet (wSet G S v v)) (wSet G S v q) := by
  intro n
  induction n with
  | zero =>
      intro es hlen h
      have : es = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst this
      exact mem_sumSet_star_right ⟨[], ⟨h.1, by simp⟩, rfl⟩
  | succ n ih =>
      intro es hlen h
      rcases pathIn_split h with hl | ⟨A, B, rfl, hA, hpA, hpB⟩
      · exact mem_sumSet_star_right ⟨es, hl, rfl⟩
      · have hBlen : B.length ≤ n := by
          have : A.length ≠ 0 := by
            intro hz
            exact hA (List.eq_nil_of_length_eq_zero hz)
          have := List.length_append (as := A) (bs := B)
          omega
        obtain ⟨s, hs, c, hc, hsc⟩ := ih B hBlen hpB
        refine ⟨pathWt A + s, mem_starSet_of_mem ⟨A, hpA, rfl⟩ hs, c, hc, ?_⟩
        rw [pathWt_append, hsc]
        abel

/-! ## The Kleene construction -/

/-- The base case: paths with empty interior, i.e. paths of length at most one. -/
def klBase (G : WGraph) (p q : ℕ) : List LinPair :=
  (if p = q then [(((0 : ℕ), (0 : ℕ)), ([] : List (ℕ × ℕ)))] else []) ++
    G.1.filterMap (fun e => if e.1 = p ∧ e.2.2 = q then some (e.2.1, []) else none)

/-- The weights of the paths from `p` to `q` with interior in `S`, as a semilinear description. -/
def kleene (G : WGraph) : List ℕ → ℕ → ℕ → List LinPair
  | [], p, q => klBase G p q
  | v :: S, p, q =>
      kleene G S p q ++
        slSum (kleene G S p v) (slSum (slStar (kleene G S v v)) (kleene G S v q))

lemma mem_semiPairSet_singleton {b : ℕ × ℕ} {x : ℕ × ℕ} :
    x ∈ semiPairSet [(b, ([] : List (ℕ × ℕ)))] ↔ x = b := by
  constructor
  · rintro ⟨l, hl, ns, hns⟩
    rw [List.mem_singleton] at hl
    subst hl
    simpa [Prod.ext_iff] using hns
  · rintro rfl
    exact ⟨(x, []), by simp, ⟨[], by simp⟩⟩

lemma semiPairSet_klBase (G : WGraph) (p q : ℕ) :
    semiPairSet (klBase G p q) = wSet G [] p q := by
  ext x
  rw [klBase, semiPairSet_append]
  constructor
  · rintro (hx | hx)
    · by_cases hpq : p = q
      · rw [if_pos hpq] at hx
        rw [mem_semiPairSet_singleton.1 hx]
        exact ⟨[], ⟨hpq, by simp⟩, rfl⟩
      · rw [if_neg hpq] at hx
        simp at hx
    · obtain ⟨l, hl, hxl⟩ := hx
      rw [List.mem_filterMap] at hl
      obtain ⟨e, he, hel⟩ := hl
      by_cases hc : e.1 = p ∧ e.2.2 = q
      · rw [if_pos hc] at hel
        have hl2 : l = (e.2.1, []) := (Option.some_injective _ hel).symm
        subst hl2
        obtain ⟨ns, hns⟩ := hxl
        have hx : x = e.2.1 := by simpa [Prod.ext_iff] using hns
        subst hx
        exact ⟨[e], ⟨⟨he, hc.1, hc.2⟩, by simp⟩, by simp [pathWt]⟩
      · rw [if_neg hc] at hel
        exact absurd hel (by simp)
  · rintro ⟨es, ⟨hpath, hint⟩, rfl⟩
    have hnil : interior es = [] := by
      cases h : interior es with
      | nil => rfl
      | cons r l => exact absurd (hint r (by rw [h]; simp)) (by simp)
    rcases eq_nil_or_singleton_of_interior_nil hnil with rfl | ⟨e, rfl⟩
    · have hpq : p = q := hpath
      left
      rw [if_pos hpq]
      exact mem_semiPairSet_singleton.2 rfl
    · right
      refine ⟨(e.2.1, []), ?_, ?_⟩
      · rw [List.mem_filterMap]
        exact ⟨e, hpath.1, by rw [if_pos ⟨hpath.2.1, hpath.2.2⟩]⟩
      · exact ⟨[], by simp [pathWt]⟩

/-- **The Kleene construction is correct.** -/
theorem semiPairSet_kleene (G : WGraph) : ∀ (S : List ℕ) (p q : ℕ),
    semiPairSet (kleene G S p q) = wSet G S p q
  | [], p, q => semiPairSet_klBase G p q
  | v :: S, p, q => by
      rw [kleene, semiPairSet_append, semiPairSet_slSum, semiPairSet_slSum, semiPairSet_slStar,
        semiPairSet_kleene G S p q, semiPairSet_kleene G S p v, semiPairSet_kleene G S v v,
        semiPairSet_kleene G S v q]
      ext x
      constructor
      · rintro (hx | ⟨a, ⟨A, hA, rfl⟩, y, ⟨s, ⟨L, hL, rfl⟩, c, ⟨C, hC, rfl⟩, rfl⟩, rfl⟩)
        · exact wSet_mono (fun r hr => List.mem_cons_of_mem _ hr) hx
        · obtain ⟨es, hes, hesw⟩ := loopPath hL
          refine ⟨A ++ (es ++ C), concatPath (hA.mono (fun r hr => List.mem_cons_of_mem _ hr))
            (concatPath hes (hC.mono (fun r hr => List.mem_cons_of_mem _ hr))
              (List.mem_cons_self ..)) (List.mem_cons_self ..), ?_⟩
          rw [pathWt_append, pathWt_append, hesw]
      · rintro ⟨es, hes, rfl⟩
        rcases pathIn_split hes with hl | ⟨A, B, rfl, _, hpA, hpB⟩
        · exact Or.inl ⟨es, hl, rfl⟩
        · obtain ⟨s, hs, c, hc, hsc⟩ := pathWt_peel B.length B le_rfl hpB
          refine Or.inr ⟨pathWt A, ⟨A, hpA, rfl⟩, s + c, ⟨s, hs, c, hc, rfl⟩, ?_⟩
          rw [pathWt_append, hsc]

/-! ## The accepting paths of a weighted graph -/

lemma mem_edges_of_isPath {G : WGraph} : ∀ {es : List WEdge} {p q : ℕ}, IsPath G p es q →
    ∀ e ∈ es, e ∈ G.1
  | [], _, _, _, e, he => by simp at he
  | e' :: es, p, q, h, e, he => by
      rcases List.mem_cons.1 he with rfl | he
      · exact h.1
      · exact mem_edges_of_isPath h.2.2 e he

lemma mem_interior : ∀ {es : List WEdge} {r : ℕ}, r ∈ interior es → ∃ e ∈ es, e.2.2 = r
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | e :: f :: es, r, h => by
      rw [interior_cons_of_ne_nil e (by simp)] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨e, by simp, rfl⟩
      · obtain ⟨e', he', rfl⟩ := mem_interior h
        exact ⟨e', List.mem_cons_of_mem _ he', rfl⟩

/-- All the states that occur in the graph. -/
def wStates (G : WGraph) : List ℕ := G.1.flatMap (fun e => [e.1, e.2.2])

/-- A semilinear description of the weights of the accepting paths of `G`. -/
def wAcc (G : WGraph) : List LinPair :=
  G.2.1.flatMap (fun p => G.2.2.flatMap (fun q => kleene G (wStates G) p q))

/-- The set of weights of the accepting paths of `G`. -/
def wAccSet (G : WGraph) : Set (ℕ × ℕ) :=
  {x | ∃ p ∈ G.2.1, ∃ q ∈ G.2.2, ∃ es, IsPath G p es q ∧ x = pathWt es}

lemma mem_semiPairSet_flatMap {α : Type} (L : List α) (f : α → List LinPair) (x : ℕ × ℕ) :
    x ∈ semiPairSet (L.flatMap f) ↔ ∃ a ∈ L, x ∈ semiPairSet (f a) := by
  simp only [semiPairSet, Set.mem_setOf_eq, List.mem_flatMap]
  constructor
  · rintro ⟨l, ⟨a, ha, hl⟩, hx⟩
    exact ⟨a, ha, l, hl, hx⟩
  · rintro ⟨a, ha, l, hl, hx⟩
    exact ⟨l, ⟨a, ha, hl⟩, hx⟩

/-- **Parikh's theorem for weighted graphs.**  The set of weights of the accepting paths of a
finite graph with weights in `ℕ × ℕ` is semilinear, and `wAcc` computes a description of it. -/
theorem semiPairSet_wAcc (G : WGraph) : semiPairSet (wAcc G) = wAccSet G := by
  ext x
  rw [wAcc, mem_semiPairSet_flatMap]
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [mem_semiPairSet_flatMap] at hx
    obtain ⟨q, hq, hx⟩ := hx
    rw [semiPairSet_kleene] at hx
    obtain ⟨es, hpath, rfl⟩ := hx
    exact ⟨p, hp, q, hq, es, hpath.1, rfl⟩
  · rintro ⟨p, hp, q, hq, es, hpath, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [mem_semiPairSet_flatMap]
    refine ⟨q, hq, ?_⟩
    rw [semiPairSet_kleene]
    refine ⟨es, ⟨hpath, fun r hr => ?_⟩, rfl⟩
    obtain ⟨e, he, rfl⟩ := mem_interior hr
    exact List.mem_flatMap.2 ⟨e, mem_edges_of_isPath hpath e he, by simp⟩

end Exercises
end Transducers
