/-
Part D, Section *Evaluation*: the combinatorics of Simon trees of bounded height.

The proof of the Factorisation Forest Theorem (`thm:factorisation-forest`) builds Simon trees by
gluing smaller ones together, and the cleanest way to formalise that is not to manipulate trees
but an inductive predicate on strings, `Transducers.Simon.Bnd φ n w`: *the string `w` has a Simon
tree of height at most `n`*, for a valuation `φ : X → M` of the letters in a monoid.  The three
constructors are the three kinds of node of a Simon tree: a leaf, a node with two children, and a
node with at least three children whose values are one and the same idempotent.  (A node with one
child adds nothing, and is accounted for by monotonicity in the height, `Bnd.mono`.)

`Transducers.Simon.Bnd.exists_tree` turns a derivation of `Bnd` back into a Simon tree in the sense
of `Transducers.FactTree.IsSimon`.  The letters are arbitrary (`X` need not be finite), because the
proof replaces factors of a string by single letters of a new, infinite, alphabet; that is what the
substitution lemma `Transducers.Simon.Bnd.subst` is for.
-/
import RequestProject.PartD.SimonTree

namespace Transducers

namespace Simon

universe u v w'

variable {M : Type u} [Monoid M] {X : Type v}

/-- The value of a string under a valuation of the letters in a monoid. -/
def val (φ : X → M) (w : List X) : M := (w.map φ).prod

@[simp] lemma val_nil (φ : X → M) : val φ [] = 1 := rfl

@[simp] lemma val_cons (φ : X → M) (x : X) (w : List X) : val φ (x :: w) = φ x * val φ w := by
  simp [val]

@[simp] lemma val_singleton (φ : X → M) (x : X) : val φ [x] = φ x := by simp [val]

@[simp] lemma val_append (φ : X → M) (u w : List X) : val φ (u ++ w) = val φ u * val φ w := by
  simp [val]

lemma val_flatten (φ : X → M) (us : List (List X)) :
    val φ us.flatten = (us.map (val φ)).prod := by
  induction us with
  | nil => simp
  | cons u us ih => simp [ih]

/-- `Bnd φ n w`: the string `w` has a Simon tree of height at most `n`, for the valuation `φ` of
the letters. -/
inductive Bnd (φ : X → M) : ℕ → List X → Prop
  | leaf (n : ℕ) (x : X) : Bnd φ n [x]
  | two {n : ℕ} {u w : List X} : Bnd φ n u → Bnd φ n w → Bnd φ (n + 1) (u ++ w)
  | idem {n : ℕ} (us : List (List X)) (e : M) : IsIdempotentElem e → 3 ≤ us.length →
      (∀ u ∈ us, Bnd φ n u) → (∀ u ∈ us, val φ u = e) → Bnd φ (n + 1) us.flatten

lemma flatMap_flatten {α β : Type*} (f : α → List β) :
    ∀ us : List (List α), us.flatten.flatMap f = (us.map (fun u => u.flatMap f)).flatten
  | [] => rfl
  | u :: us => by simp [List.flatMap_append, flatMap_flatten f us]

lemma flatMap_singleton_eq_map {α β : Type*} (f : α → β) :
    ∀ w : List α, w.flatMap (fun x => [f x]) = w.map f
  | [] => rfl
  | x :: w => by simp [flatMap_singleton_eq_map f w]

namespace Bnd

variable {φ : X → M}

lemma ne_nil {n : ℕ} {w : List X} (h : Bnd φ n w) : w ≠ [] := by
  induction h with
  | leaf => simp
  | two _ _ ihu _ => simp [ihu]
  | idem us e _ hlen _ _ ih =>
    intro hnil
    obtain ⟨u, us', rfl⟩ : ∃ u us', us = u :: us' := by
      cases us with
      | nil => simp at hlen
      | cons u us' => exact ⟨u, us', rfl⟩
    simp only [List.flatten_cons, List.append_eq_nil_iff] at hnil
    exact ih u (by simp) hnil.1

lemma mono {n : ℕ} {w : List X} (h : Bnd φ n w) {m : ℕ} (hnm : n ≤ m) : Bnd φ m w := by
  induction h generalizing m with
  | leaf n x => exact leaf m x
  | two _ _ ihu ihw =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact two (ihu (by omega)) (ihw (by omega))
  | idem us e he hlen _ hval ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact idem us e he hlen (fun u hu => ih u hu (by omega)) hval

lemma append {n m : ℕ} {u w : List X} (hu : Bnd φ n u) (hw : Bnd φ m w) :
    Bnd φ (max n m + 1) (u ++ w) :=
  two (hu.mono (le_max_left _ _)) (hw.mono (le_max_right _ _))

/-- Grouping: a nonempty list of factors, each of height at most `n` and all with the same
idempotent value, can be put under one node. -/
lemma group {n : ℕ} {us : List (List X)} {e : M} (hne : us ≠ []) (he : IsIdempotentElem e)
    (hb : ∀ u ∈ us, Bnd φ n u) (hv : ∀ u ∈ us, val φ u = e) : Bnd φ (n + 1) us.flatten := by
  match us, hne with
  | [u], _ => simpa using (hb u (by simp)).mono (Nat.le_succ n)
  | [u, u'], _ =>
    simpa using two (hb u (by simp)) (hb u' (by simp))
  | u :: u' :: u'' :: us', _ =>
    exact idem _ e he (by simp) hb hv

/-- Every nonempty string has a Simon tree of height at most its length minus one. -/
lemma of_ne_nil : ∀ {w : List X}, w ≠ [] → Bnd φ (w.length - 1) w
  | [], h => absurd rfl h
  | [x], _ => leaf _ x
  | x :: y :: w, _ => by
    have ih : Bnd φ ((y :: w).length - 1) (y :: w) := of_ne_nil (by simp)
    have := two (leaf ((y :: w).length - 1) x) ih
    simpa using this

/-- Appending a short string costs at most its length in height. -/
lemma append_short {n : ℕ} {u : List X} (hu : Bnd φ n u) (w : List X) :
    Bnd φ (n + w.length) (u ++ w) := by
  rcases eq_or_ne w [] with rfl | hw
  · simpa using hu
  · have := hu.append (of_ne_nil (φ := φ) hw)
    refine this.mono ?_
    have : 0 < w.length := List.length_pos_iff.mpr hw
    omega

/-- Prepending a short string costs at most its length in height. -/
lemma short_append {n : ℕ} {u : List X} (hu : Bnd φ n u) (w : List X) :
    Bnd φ (n + w.length) (w ++ u) := by
  rcases eq_or_ne w [] with rfl | hw
  · simpa using hu
  · have := (of_ne_nil (φ := φ) hw).append hu
    refine this.mono ?_
    have : 0 < w.length := List.length_pos_iff.mpr hw
    omega

lemma val_flatMap {Y : Type w'} (χ : Y → M) (ψ : Y → List X) {w : List Y}
    (hv : ∀ y ∈ w, val φ (ψ y) = χ y) : val φ (w.flatMap ψ) = val χ w := by
  induction w with
  | nil => simp
  | cons y w ih =>
    rw [List.flatMap_cons, val_append, val_cons, hv y (by simp),
      ih (fun z hz => hv z (by simp [hz]))]

/-- **Substitution.**  If a string `w` over a new alphabet `Y` has a Simon tree of height at most
`n`, and every letter `y` of `w` stands for a string `ψ y` over `X` with the same value and a Simon
tree of height at most `m`, then the string obtained by substitution has a Simon tree of height at
most `n + m`. -/
lemma subst {Y : Type w'} {χ : Y → M} {n : ℕ} {w : List Y} (h : Bnd χ n w) (ψ : Y → List X)
    {m : ℕ} (hb : ∀ y ∈ w, Bnd φ m (ψ y)) (hv : ∀ y ∈ w, val φ (ψ y) = χ y) :
    Bnd φ (n + m) (w.flatMap ψ) := by
  induction h with
  | leaf n y =>
    simpa using (hb y (by simp)).mono (by omega)
  | two _ _ ihu ihw =>
    rw [List.flatMap_append]
    have := two (ihu (fun y hy => hb y (by simp [hy])) (fun y hy => hv y (by simp [hy])))
      (ihw (fun y hy => hb y (by simp [hy])) (fun y hy => hv y (by simp [hy])))
    simpa [Nat.add_right_comm] using this
  | @idem n us e he hlen hus hval ih =>
    rw [flatMap_flatten]
    have := idem (φ := φ) (n := n + m) (us.map (fun u => u.flatMap ψ)) e he (by simpa using hlen)
      (by
        intro u' hu'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
        exact ih u hu (fun y hy => hb y (List.mem_flatten.mpr ⟨u, hu, hy⟩))
          (fun y hy => hv y (List.mem_flatten.mpr ⟨u, hu, hy⟩)))
      (by
        intro u' hu'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
        rw [val_flatMap χ ψ (fun y hy => hv y (List.mem_flatten.mpr ⟨u, hu, hy⟩))]
        exact hval u hu)
    simpa [Nat.add_right_comm] using this

/-- Renaming the letters along a map that respects the valuation. -/
lemma map {Y : Type w'} {χ : Y → M} (f : X → Y) (hf : ∀ x, χ (f x) = φ x) {n : ℕ} {w : List X}
    (h : Bnd φ n w) : Bnd χ n (w.map f) := by
  have hb := subst (φ := χ) h (fun x => [f x]) (m := 0) (fun x _ => leaf 0 (f x))
    (fun x _ => by simp [hf])
  simpa [flatMap_singleton_eq_map] using hb

/-- Reversal: a Simon tree of the reverse string, for the opposite monoid. -/
lemma reverse {n : ℕ} {w : List X} (h : Bnd φ n w) :
    Bnd (fun x => MulOpposite.op (φ x)) n w.reverse := by
  have hval : ∀ u : List X, val (fun x => MulOpposite.op (φ x)) u.reverse =
      MulOpposite.op (val φ u) := by
    intro u
    induction u with
    | nil => simp
    | cons x u ih => simp [ih]
  induction h with
  | leaf n x => simpa using leaf n _
  | two _ _ ihu ihw => simpa using two ihw ihu
  | @idem n us e he hlen _ hv ih =>
    have hrev : us.flatten.reverse = (us.map List.reverse).reverse.flatten := by
      rw [List.reverse_flatten]
    rw [hrev]
    refine idem _ (MulOpposite.op e) ?_ (by simpa using hlen) ?_ ?_
    · show MulOpposite.op e * MulOpposite.op e = MulOpposite.op e
      rw [← MulOpposite.op_mul, he.eq]
    · intro u hu
      simp only [List.mem_reverse, List.mem_map] at hu
      obtain ⟨u, hu, rfl⟩ := hu
      exact ih u hu
    · intro u hu
      simp only [List.mem_reverse, List.mem_map] at hu
      obtain ⟨u, hu, rfl⟩ := hu
      rw [hval, hv u hu]

/-- Transport along a monoid homomorphism. -/
lemma hom {N : Type w'} [Monoid N] (g : M →* N) {n : ℕ} {w : List X} (h : Bnd φ n w) :
    Bnd (fun x => g (φ x)) n w := by
  have hval : ∀ u : List X, val (fun x => g (φ x)) u = g (val φ u) := by
    intro u
    induction u with
    | nil => simp
    | cons x u ih => simp [ih]
  induction h with
  | leaf n x => exact leaf n x
  | two _ _ ihu ihw => exact two ihu ihw
  | idem us e he hlen _ hv ih =>
    refine idem us (g e) ?_ hlen ih ?_
    · show g e * g e = g e
      rw [← map_mul, he.eq]
    · intro u hu
      rw [hval, hv u hu]

/-- Reversal, the other way round. -/
lemma of_reverse {n : ℕ} {w : List X} (h : Bnd (fun x => MulOpposite.op (φ x)) n w.reverse) :
    Bnd φ n w := by
  have := (h.reverse).hom (MulEquiv.opOp M).symm.toMonoidHom
  simpa using this

end Bnd

/-! ## From the predicate to trees -/

variable {A : Type v}

lemma hom_ofList (h : FreeMonoid A →* M) (w : List A) :
    h (FreeMonoid.ofList w) = val (fun a => h (FreeMonoid.of a)) w := by
  induction w with
  | nil => simp
  | cons a w ih => rw [FreeMonoid.ofList_cons, map_mul, ih, val_cons]

lemma exists_forall₂ {α β : Type*} {P : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, P a b) → ∃ l' : List β, List.Forall₂ P l l'
  | [], _ => ⟨[], List.Forall₂.nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := exists_forall₂ (l := l) (fun a ha => h a (by simp [ha]))
    exact ⟨b :: l', List.Forall₂.cons hb hl'⟩

lemma forall₂_mem_right {α β : Type*} {P : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ P l l') : ∀ b ∈ l', ∃ a ∈ l, P a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hP⟩ := ih b hb
      exact ⟨a, by simp [ha], hP⟩

lemma forall₂_map_eq {α β : Type*} {f : β → α} {Q : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ (fun a b => f b = a ∧ Q a b) l l') : l'.map f = l := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [ih, hab.1]

/-- A derivation of `Bnd` gives a Simon tree of the same string, of at most the same height. -/
theorem Bnd.exists_tree (h : FreeMonoid A →* M) {n : ℕ} {w : List A}
    (hb : Bnd (fun a => h (FreeMonoid.of a)) n w) :
    ∃ t : FactTree A, t.yield = w ∧ t.IsSimon h ∧ t.height ≤ n := by
  induction hb with
  | leaf n a => exact ⟨.leaf a, by simp, .leaf a, by simp⟩
  | two _ _ ihu ihw =>
    obtain ⟨t₁, h₁, s₁, k₁⟩ := ihu
    obtain ⟨t₂, h₂, s₂, k₂⟩ := ihw
    refine ⟨.node [t₁, t₂], by simp [h₁, h₂], .node _ ?_ ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    · intro hlen; simp at hlen
    · refine FactTree.height_node_le ?_
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
  | @idem n us e he hlen _ hv ih =>
    obtain ⟨ts, hts⟩ := exists_forall₂ ih
    have hyield : ts.map FactTree.yield = us := forall₂_map_eq hts
    have hmem : ∀ c ∈ ts, ∃ u ∈ us, c.yield = u ∧ c.IsSimon h ∧ c.height ≤ n := by
      intro c hc
      obtain ⟨u, hu, hP⟩ := forall₂_mem_right hts c hc
      exact ⟨u, hu, hP⟩
    refine ⟨.node ts, ?_, .node _ ?_ ?_, ?_⟩
    · simp [hyield]
    · intro c hc
      obtain ⟨u, -, -, hs, -⟩ := hmem c hc
      exact hs
    · intro _
      refine ⟨e, he, fun c hc => ?_⟩
      obtain ⟨u, hu, hy, -, -⟩ := hmem c hc
      rw [FactTree.label, hy, hom_ofList, hv u hu]
    · refine FactTree.height_node_le ?_
      intro c hc
      obtain ⟨u, -, -, -, hk⟩ := hmem c hc
      exact hk

lemma flatten_map_filter_ne_nil {α β : Type*} (f : α → List β) :
    ∀ l : List α, (l.map f).flatten = ((l.filter (fun c => f c ≠ [])).map f).flatten
  | [] => rfl
  | c :: l => by
    by_cases hc : f c = []
    · simp [hc, flatten_map_filter_ne_nil f l]
    · simp [hc, flatten_map_filter_ne_nil f l]

/-- Conversely, a Simon tree with a nonempty underlying string gives a derivation of `Bnd` of the
same height.  (Subtrees with an empty underlying string are simply dropped.)  Together with
`Transducers.Simon.Bnd.exists_tree`, this says that `Bnd` is exactly the existence of a Simon tree
of bounded height. -/
theorem Bnd.of_isSimon (h : FreeMonoid A →* M) {t : FactTree A} (ht : t.IsSimon h)
    (hne : t.yield ≠ []) : Bnd (fun a => h (FreeMonoid.of a)) t.height t.yield := by
  induction ht with
  | leaf a => simpa using Bnd.leaf (φ := fun a => h (FreeMonoid.of a)) 0 a
  | node cs _ hidem ih =>
    set cs' := cs.filter (fun c => c.yield ≠ []) with hcs'
    set H := (FactTree.node cs).height - 1 with hH
    have hHc : ∀ c ∈ cs, c.height ≤ H := by
      intro c hc
      have := FactTree.height_le_of_mem hc
      omega
    have hHn : (FactTree.node cs).height = H + 1 := by
      have : 1 ≤ (FactTree.node cs).height := by rw [FactTree.height_node]; omega
      omega
    have hmem' : ∀ c ∈ cs', c ∈ cs ∧ c.yield ≠ [] := by
      intro c hc
      have := List.mem_filter.mp hc
      exact ⟨this.1, by simpa using this.2⟩
    have hb : ∀ c ∈ cs', Bnd (fun a => h (FreeMonoid.of a)) H c.yield := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := hmem' c hc
      exact (ih c hc1 hc2).mono (hHc c hc1)
    rw [FactTree.yield_node, flatten_map_filter_ne_nil, ← hcs'] at hne ⊢
    rw [hHn]
    have hcs'ne : cs' ≠ [] := by rintro h; rw [h] at hne; simp at hne
    by_cases hlen : 3 ≤ cs.length
    · obtain ⟨e, he, hlab⟩ := hidem hlen
      refine Bnd.group (by simpa using hcs'ne) he ?_ ?_
      · intro u hu
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
        exact hb c hc
      · intro u hu
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
        rw [← hom_ofList]
        exact hlab c (hmem' c hc).1
    · have hlen' : cs'.length ≤ 2 := le_trans (List.length_filter_le _ _) (by omega)
      match cs', hcs'ne, hlen', hb with
      | [c], _, _, hb => simpa using (hb c (by simp)).mono (Nat.le_succ H)
      | [c, c'], _, _, hb => simpa using Bnd.two (hb c (by simp)) (hb c' (by simp))

end Simon

end Transducers
