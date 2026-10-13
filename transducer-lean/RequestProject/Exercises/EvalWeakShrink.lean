/-
Exercise `exer:weak-simon-tree-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): the induction step of a letter value `s` that shrinks the
semigroup on the right.

This is the step of Lemma `lem:factorisation-forest-shrinking-letter` (as formalised in
`Transducers.Simon.good_shrink`), redone so that the ranks of the tree are computed from the values
of the prefix and of the suffix in a finite aperiodic monoid.  A string is decomposed as
`c₀ · (b₁ c₁) ⋯ (bₖ cₖ) · bl`, where the `cᵢ` are nonempty runs of letters of value `s`, the `bᵢ`
nonempty runs of other letters, `c₀` a (possibly empty) run of value `s` and `bl` a (possibly
empty) run of other letters.  The tree is

  `node [node [c₀ (flat), substitution of the block trees in an outer tree], tree of bl]`

where the tree of a block `bᵢ cᵢ` is `node [tree of bᵢ, cᵢ (flat)]`, the trees of the runs `bᵢ`
come from the induction hypothesis for the other letter values, and the outer tree, over the string
of blocks, from the induction hypothesis for the smaller semigroup `T·s` (all blocks have values in
`T·s`).  All the nodes have at most two children except the flat nodes, whose children are letters
of the same value `s`, and the nodes of the trees given by the induction hypotheses.
-/
import RequestProject.Exercises.EvalWeakWords

namespace Transducers.Exercises

open FactTree TreeSym Simon

/-- `WGood L`: there are a bound `K`, a finite aperiodic monoid `N`, a map `θ : M → N` and a rank
function `G : N → N → ℕ` such that every nonempty string, over any alphabet, whose letters have
values in `L`, has a weak Simon tree with all leaves at depth `K + 1` whose encoding has, between
two letters, the rank `G (θ-value of the prefix) (θ-value of the suffix)`. -/
def WGood {M : Type} [Monoid M] (L : Set M) : Prop :=
  ∃ (K : ℕ) (N : Type) (_ : Monoid N) (_ : Finite N), Aper N ∧ ∃ (θ : M → N) (G : N → N → ℕ),
    ∀ (X : Type) (φ : X → M) (w : List X), w ≠ [] → (∀ x ∈ w, φ x ∈ L) →
      ∃ t, Rep φ (θ ∘ φ) G K 1 1 t w

lemma Rep.castK {X M N : Type} [Monoid M] [Monoid N] {φ : X → M} {ψ : X → N} {G : N → N → ℕ}
    {K K' : ℕ} {α β : N} {t : FactTree X} {w : List X} (h : Rep φ ψ G K α β t w) (hK : K = K') :
    Rep φ ψ G K' α β t w := hK ▸ h

lemma Rep.ctx {X M N : Type} [Monoid M] [Monoid N] {φ : X → M} {ψ : X → N} {G : N → N → ℕ}
    {K : ℕ} {α β α' β' : N} {t : FactTree X} {w : List X} (h : Rep φ ψ G K α β t w)
    (hα : α = α') (hβ : β = β') : Rep φ ψ G K α' β' t w := hα ▸ hβ ▸ h

lemma takeWhile_dropWhile_block {X : Type} (p : X → Bool) {b c : List X}
    (hb : ∀ x ∈ b, p x = true) (hc : ∀ x ∈ c.head?, p x = false) :
    b.takeWhile p = b ∧ (b ++ c).takeWhile p = b ∧ (b ++ c).dropWhile p = c := by
  induction b with
  | nil =>
    rcases c with _ | ⟨y, c⟩
    · simp
    · simp [hc y rfl]
  | cons x b ih =>
    have := ih fun y hy => hb y (by simp [hy])
    simp [hb x (by simp), this.1, this.2.1, this.2.2]

section Shrink

variable {M : Type} [Monoid M] [DecidableEq M] (s : M) {NB NO : Type} [Monoid NB] [Monoid NO]
  (θB : M → NB) (θO : M → NO) (GB : NB → NB → ℕ) (GO : NO → NO → ℕ) (KB KO : ℕ)

/-- The rank function of the induction step: inside a run of `s`, `0`; inside a run of other
letters, the rank of the induction hypothesis for the other letter values; between a run of other
letters and a run of `s` (inside a block), `KB + 1`; between two blocks, the rank of the outer tree
shifted by `KB + 2`; after `c₀`, `KO + KB + 3`; before `bl`, `KO + KB + 4`. -/
def GS (P S : Run NB × Cut θO) : ℕ :=
  if Cut.lastS P.2 then
    if Cut.firstS S.2 then 0
    else if Run.hasS S.1 then
      (if Cut.hasNS P.2 then GO (Cut.blocksL P.2) (Cut.blocksR S.2) + KB + 2 else KO + KB + 3)
    else KO + KB + 4
  else if Cut.firstS S.2 then KB + 1 else GB (Run.trail P.1) (Run.lead S.1)

variable {X : Type} (φ : X → M)

lemma lastS_endsS {u : List X} (h : EndsS s φ u) (hu : u ≠ []) (α : Cut θO) :
    Cut.lastS (α * val (thC s θO ∘ φ) u) = true := by
  rcases h with h | ⟨u', x, rfl, hx⟩
  · exact absurd h hu
  · rw [lastS_last]; simp [hx]

lemma firstS_startsNS {u : List X} (h : StartsNS s φ u) (hu : u ≠ []) (β : Cut θO) :
    Cut.firstS (val (thC s θO ∘ φ) u * β) = false := by
  rcases h with h | ⟨x, u', rfl, hx⟩
  · exact absurd h hu
  · rw [firstS_first]; simp [hx]

omit [DecidableEq M] in
lemma mem_left_of_append {u₁ u₂ u : List X} (h : u₁ ++ u₂ = u) {x : X} (hx : x ∈ u₁) : x ∈ u :=
  h ▸ List.mem_append_left _ hx

omit [DecidableEq M] in
lemma mem_right_of_append {u₁ u₂ u : List X} (h : u₁ ++ u₂ = u) {x : X} (hx : x ∈ u₂) : x ∈ u :=
  h ▸ List.mem_append_right _ hx

/-- A run of letters of other values than `s`, in a context that ends and starts there. -/
lemma rep_run {u : List X} (hns : ∀ x ∈ u, φ x ≠ s) {t : FactTree X}
    (ht : Rep φ (θB ∘ φ) GB KB 1 1 t u) {α β : Run NB × Cut θO}
    (hα : Run.trail α.1 = 1) (hβ : Run.lead β.1 = 1) :
    Rep φ (thS s θB θO ∘ φ) (GS θO GB GO KB KO) KB α β t u := by
  refine ht.congr fun u₁ u₂ h₁ h₂ h => ?_
  have hns₁ : ∀ x ∈ u₁, φ x ≠ s := fun x hx => hns x (mem_left_of_append h hx)
  have hns₂ : ∀ x ∈ u₂, φ x ≠ s := fun x hx => hns x (mem_right_of_append h hx)
  rw [val_thS, val_thS, valR_ns s θB φ u₁ hns₁, valR_ns s θB φ u₂ hns₂,
    valC_ns s θO φ u₁ h₁ hns₁, valC_ns s θO φ u₂ h₂ hns₂]
  simp [GS, Cut.lastS_mul_pc, Cut.firstS_pc_mul, Run.trail_mul_ns, Run.lead_ns_mul, hα, hβ]

/-- A run of letters of value `s`, as a flat node. -/
lemma rep_flat {c : List X} (hc : c ≠ []) (hs : ∀ x ∈ c, φ x = s) (α β : Run NB × Cut θO) :
    Rep φ (thS s θB θO ∘ φ) (GS θO GB GO KB KO) 0 α β (flat c) c := by
  refine Rep.flat hc hs fun u v hu hv h => ?_
  obtain ⟨u', x, rfl⟩ := (List.eq_nil_or_concat u).resolve_left hu
  obtain ⟨y, v', rfl⟩ := List.exists_cons_of_ne_nil hv
  simp only [List.concat_eq_append] at *
  have hx : φ x = s := hs x (mem_left_of_append h (by simp))
  have hy : φ y = s := hs y (mem_right_of_append h (by simp))
  rw [val_thS, val_thS]
  simp only [GS, Prod.snd_mul, lastS_last, firstS_first, hx, hy, decide_true, if_true]

/-- A block `b c`. -/
lemma rep_block {b c : List X} (hb : b ≠ []) (hc : c ≠ []) (hbs : ∀ x ∈ b, φ x ≠ s)
    (hcs : ∀ x ∈ c, φ x = s) {tb : FactTree X} (htb : Rep φ (θB ∘ φ) GB KB 1 1 tb b)
    {α β : Run NB × Cut θO} (hα : Run.trail α.1 = 1) :
    Rep φ (thS s θB θO ∘ φ) (GS θO GB GO KB KO) (KB + 1) α β
      (.node [tb, padT KB (flat c)]) (b ++ c) := by
  obtain ⟨y, c', rfl⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨b', x, rfl⟩ := (List.eq_nil_or_concat b).resolve_left hb
  simp only [List.concat_eq_append] at *
  have hy : φ y = s := hcs y (by simp)
  have hx : φ x ≠ s := hbs x (by simp)
  refine Rep.two (rep_run s θB θO GB GO KB KO φ hbs htb hα ?_) ?_ ?_
  · rw [val_thS, Prod.fst_mul]
    exact lead_startsS s θB φ hy _
  · have := (rep_flat s θB θO GB GO KB KO φ hc hcs (α * val (thS s θB θO ∘ φ) (b' ++ [x])) β).padN
      KB
    rwa [zero_add] at this
  · rw [val_thS, val_thS]
    simp only [GS, Prod.snd_mul, lastS_last, firstS_first, hx, hy, decide_true, decide_false,
      if_true, Bool.false_eq_true, if_false]

omit [Monoid M] [DecidableEq M] in
lemma exists_s_of_blocks {post : List (List X)} (hpost : post ≠ [])
    (hb : ∀ y ∈ post, IsBlock s φ y) : ∃ x ∈ post.flatten, φ x = s := by
  obtain ⟨z, post', rfl⟩ := List.exists_cons_of_ne_nil hpost
  obtain ⟨b, c, rfl, -, hc, -, hcs⟩ := hb z (by simp)
  obtain ⟨x, c', rfl⟩ := List.exists_cons_of_ne_nil hc
  exact ⟨x, by simp, hcs x (by simp)⟩

omit [Monoid M] [DecidableEq M] in
lemma flatten_ne_nil_of_blocks {post : List (List X)} (hpost : post ≠ [])
    (hb : ∀ y ∈ post, IsBlock s φ y) : post.flatten ≠ [] := by
  obtain ⟨z, post', rfl⟩ := List.exists_cons_of_ne_nil hpost
  obtain ⟨b, c, rfl, hb', -, -, -⟩ := hb z (by simp)
  simp [hb']

/-- **The induction step**, for one alphabet: from the trees of the runs of letters of other values
than `s` and the outer trees over strings of blocks, a tree for every string. -/
lemma shrink_rep (Q : X → Prop)
    (hKB : ∀ u : List X, u ≠ [] → (∀ x ∈ u, Q x ∧ φ x ≠ s) →
      ∃ t, Rep φ (θB ∘ φ) GB KB 1 1 t u)
    (hKO : ∀ v : List (List X), v ≠ [] → (∀ y ∈ v, IsBlock s φ y ∧ ∀ x ∈ y, Q x) →
      ∃ T, Rep (val φ) (θO ∘ val φ) GO KO 1 1 T v)
    (w : List X) (hw : w ≠ []) (hQ : ∀ x ∈ w, Q x) :
    ∃ t, Rep φ (thS s θB θO ∘ φ) (GS θO GB GO KB KO) (KO + KB + 4) 1 1 t w := by
  classical
  have hKB' : ∀ u : List X, ∃ t, u ≠ [] → (∀ x ∈ u, Q x ∧ φ x ≠ s) →
      Rep φ (θB ∘ φ) GB KB 1 1 t u := by
    intro u
    by_cases h : u ≠ [] ∧ ∀ x ∈ u, Q x ∧ φ x ≠ s
    · obtain ⟨t, ht⟩ := hKB u h.1 h.2
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨.node [], fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose tB htB using hKB'
  set ψ := thS s θB θO ∘ φ with hψ
  set G := GS θO GB GO KB KO with hG
  set p : X → Bool := fun x => decide (φ x ≠ s) with hp
  set f : List X → FactTree X :=
    fun y => .node [tB (y.takeWhile p), padT KB (flat (y.dropWhile p))] with hf
  have hfrep : ∀ y, IsBlock s φ y → (∀ x ∈ y, Q x) → ∀ α β : Run NB × Cut θO,
      Run.trail α.1 = 1 → Rep φ ψ G (KB + 1) α β (f y) y := by
    rintro y ⟨b, c, rfl, hb, hc, hbs, hcs⟩ hyQ α β hα
    obtain ⟨y0, c', rfl⟩ := List.exists_cons_of_ne_nil hc
    have hTD := takeWhile_dropWhile_block p (b := b) (c := y0 :: c')
      (fun x hx => by simp [hp, hbs x hx]) (fun x hx => by
        have hx' : x = y0 := by simpa using hx.symm
        simp [hp, show φ x = s by rw [hx']; exact hcs y0 (by simp)])
    simp only [hf, hTD.2.1, hTD.2.2]
    exact rep_block s θB θO GB GO KB KO φ hb hc hbs hcs
      (htB b hb fun x hx => ⟨hyQ x (by simp [hx]), hbs x hx⟩) hα
  obtain ⟨c₀, ps, bl, hdec, hc₀, hps, hbl⟩ := exists_decomp (fun x => φ x = s) w
  have hmem : ∀ x, x ∈ c₀ ∨ (∃ p ∈ ps, x ∈ p.1 ∨ x ∈ p.2) ∨ x ∈ bl → x ∈ w := by
    intro x hx'
    rw [hdec]
    rcases hx' with h | ⟨p, hp, h⟩ | h
    · simp [h]
    · simp only [List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨p, hp, h⟩)
    · simp [h]
  set v := ps.map (fun p => p.1 ++ p.2) with hv
  have hvflat : ps.flatMap (fun p => p.1 ++ p.2) = v.flatten := by
    rw [hv, List.flatMap_def]
  have hvb : ∀ y ∈ v, IsBlock s φ y ∧ ∀ x ∈ y, Q x := by
    intro y hy
    obtain ⟨⟨b, c⟩, hpc, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hb, hc, hbs, hcs⟩ := hps (b, c) hpc
    refine ⟨⟨b, c, rfl, hb, hc, hbs, hcs⟩, fun x hx => hQ x (hmem x ?_)⟩
    rcases List.mem_append.mp hx with h | h
    · exact Or.inr (Or.inl ⟨(b, c), hpc, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨(b, c), hpc, Or.inr h⟩)
  have hblQ : ∀ x ∈ bl, Q x := fun x hx => hQ x (hmem x (Or.inr (Or.inr hx)))
  have hvE : EndsS s φ v.flatten := EndsS.flatten s φ fun z hz => (hvb z hz).1.endsS s φ
  have hvS : StartsNS s φ v.flatten := StartsNS.flatten s φ fun z hz => (hvb z hz).1.startsNS s φ
  have hc₀E : EndsS s φ c₀ := endsS_of_all_s s φ hc₀
  -- the outer level: the blocks
  have hblocks : v ≠ [] → ∃ tb, Rep φ ψ G (KO + KB + 2) (val ψ c₀) (val ψ bl) tb v.flatten := by
    intro hv0
    obtain ⟨T, hTy, hTws, hTh, v0, vs, hv0', hTe⟩ := hKO v hv0 hvb
    refine ⟨_, (Rep.subst (Kb := KB + 1) f hTy hTws hTh ⟨v0, vs, hv0', hTe⟩ ?_ ?_).castK (by omega)⟩
    · intro pre y post h
      have hyv : y ∈ v := h ▸ by simp
      have hpre : ∀ z ∈ pre, z ∈ v := fun z hz => h ▸ List.mem_append_left _ hz
      refine hfrep y (hvb y hyv).1 (hvb y hyv).2 _ _ ?_
      rw [hψ, val_thS, val_thS, Prod.fst_mul, ← val_append]
      exact (ctxL s θB θO φ (hc₀E.append s φ
        (EndsS.flatten s φ fun z hz => (hvb z (hpre z hz)).1.endsS s φ))).1
    · intro pre post hpre hpost h
      have hpre' : ∀ z ∈ pre, IsBlock s φ z := fun z hz =>
        (hvb z (h ▸ List.mem_append_left _ hz)).1
      have hpost' : ∀ z ∈ post, IsBlock s φ z := fun z hz =>
        (hvb z (h ▸ List.mem_append_right _ hz)).1
      obtain ⟨hc1, hc2, -⟩ := blocksL_allS s θO φ hc₀
      obtain ⟨hL1, hL2⟩ := blocksL_blocks s θO φ pre _ hc2 hpre'
      obtain ⟨hL3, hL4⟩ := hL2 hpre
      obtain ⟨hR1, -⟩ := blocksR_blocks s θO φ post _ (ctxR s θO φ (startsNS_of_all_ns s φ hbl))
        hpost'
      have hfirst := firstS_startsNS s θO φ (StartsNS.flatten s φ fun z hz => (hpost' z hz).startsNS s φ)
        (flatten_ne_nil_of_blocks s φ hpost hpost') (val (thC s θO ∘ φ) bl)
      have hhasS : Run.hasS (val (thR s θB ∘ φ) post.flatten * val (thR s θB ∘ φ) bl) = true := by
        rw [← val_append]
        obtain ⟨x, hx, hxs⟩ := exists_s_of_blocks s φ hpost hpost'
        exact hasS_of_mem s θB φ ⟨x, List.mem_append_left _ hx, hxs⟩
      rw [hψ, val_thS, val_thS, val_thS, val_thS]
      simp only [hG, GS, Prod.mk_mul_mk, hL3, hfirst, hhasS, hL4,
        if_true, Bool.false_eq_true, if_false, hL1, hR1, hc1, blocksR_allNS s θO φ hbl, one_mul,
        mul_one]
      omega
  -- the level of `c₀` and the blocks
  have hmid : c₀ ++ v.flatten ≠ [] →
      ∃ tm, Rep φ ψ G (KO + KB + 3) 1 (val ψ bl) tm (c₀ ++ v.flatten) := by
    intro hne
    by_cases hc0 : c₀ = []
    · subst hc0
      have hv0 : v ≠ [] := by rintro h; simp [h] at hne
      obtain ⟨tb, htb⟩ := hblocks hv0
      exact ⟨_, (htb.pad.castK (by omega)).ctx (by simp) rfl⟩
    · by_cases hv0 : v = []
      · have := (rep_flat s θB θO GB GO KB KO φ hc0 hc₀ 1 (val ψ bl)).padN (KO + KB + 3)
        rw [hv0]
        exact ⟨_, by simpa using this⟩
      · obtain ⟨tb, htb⟩ := hblocks hv0
        have h1 := (rep_flat s θB θO GB GO KB KO φ hc0 hc₀ 1
          (val ψ v.flatten * val ψ bl)).padN (KO + KB + 2)
        refine ⟨_, (Rep.two (h1.castK (by omega)) (htb.ctx (by rw [one_mul]) rfl) ?_).castK
          (by omega)⟩
        have hfirst := firstS_startsNS s θO φ hvS (by
          obtain ⟨z, v', hz⟩ := List.exists_cons_of_ne_nil hv0
          exact flatten_ne_nil_of_blocks s φ hv0 fun y hy => (hvb y hy).1)
          (val (thC s θO ∘ φ) bl)
        have hhasS : Run.hasS (val (thR s θB ∘ φ) v.flatten * val (thR s θB ∘ φ) bl) = true := by
          rw [← val_append]
          obtain ⟨x, hx, hxs⟩ := exists_s_of_blocks s φ hv0 fun y hy => (hvb y hy).1
          exact hasS_of_mem s θB φ ⟨x, List.mem_append_left _ hx, hxs⟩
        have hlast := lastS_endsS s θO φ hc₀E hc0 1
        obtain ⟨-, -, hns⟩ := blocksL_allS s θO φ hc₀
        rw [hψ, val_thS, val_thS, val_thS]
        simp only [one_mul] at hlast
        simp only [GS, Prod.mk_mul_mk, one_mul, hlast, hfirst, hhasS, hns, if_true,
          Bool.false_eq_true, if_false]
  -- the root
  rw [hdec, hvflat]
  by_cases hm : c₀ ++ v.flatten = []
  · rw [hm, List.nil_append]
    have hbl0 : bl ≠ [] := by rintro rfl; apply hw; rw [hdec, hvflat, hm]; rfl
    have h1 := rep_run s θB θO GB GO KB KO φ hbl
      (htB bl hbl0 fun x hx => ⟨hblQ x hx, hbl x hx⟩) (α := 1) (β := 1) (by rfl) (by rfl)
    exact ⟨_, (h1.padN (KO + 4)).castK (K' := KO + KB + 4) (by omega)⟩
  · obtain ⟨tm, htm⟩ := hmid hm
    by_cases hb0 : bl = []
    · subst hb0
      rw [List.append_nil]
      exact ⟨_, (htm.pad.castK (K' := KO + KB + 4) (by omega)).ctx rfl rfl⟩
    · have hmE : EndsS s φ (c₀ ++ v.flatten) := hc₀E.append s φ hvE
      have h1 := rep_run s θB θO GB GO KB KO φ hbl
        (htB bl hb0 fun x hx => ⟨hblQ x hx, hbl x hx⟩) (α := 1 * val ψ (c₀ ++ v.flatten))
        (β := 1) (by
          rw [one_mul, hψ, val_thS]
          exact (ctxL s θB θO φ hmE).1) rfl
      refine ⟨_, (Rep.two (htm.ctx rfl (by simp)) ((h1.padN (KO + 3)).castK (by omega))
        ?_).castK (by omega)⟩
      have hlast := lastS_endsS s θO φ hmE hm 1
      have hfirst := firstS_startsNS s θO φ (startsNS_of_all_ns s φ hbl) hb0 1
      have hhasS := hasS_of_all_ns s θB φ hbl
      rw [hψ, val_thS, val_thS]
      simp only [one_mul, mul_one] at hlast hfirst
      simp only [hG, GS, one_mul, mul_one, hlast, hfirst, hhasS, if_true, Bool.false_eq_true,
        if_false]

end Shrink

end Transducers.Exercises
