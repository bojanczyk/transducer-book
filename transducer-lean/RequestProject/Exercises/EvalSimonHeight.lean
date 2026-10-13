/-
Exercise `exer:height-of-simon-tree` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): the height of a Simon tree can be linear in the size of the
semigroup.

The Simon trees are those of `Transducers.FactTree.IsSimon` (`PartD/SimonTree.lean`), stated for
monoid homomorphisms `h : A* → M`.  The book's example is the semigroup `{1, …, n}` under maximum,
with the homomorphism `max : {1, …, n}* → {1, …, n}`.  A semigroup homomorphism is turned into a
monoid homomorphism by adjoining an identity (see `Transducers.semigroupHom`); here the adjoined
identity is `0`, so the monoid is `{0, 1, …, n}` under maximum (`Transducers.Exercises.MaxMon n`,
with `n + 1` elements), and the input letters are its elements.

The words are the book's `w₀ = ε`, `wᵢ = wᵢ₋₁ · i · wᵢ₋₁` (`Transducers.Exercises.simonNat`), of
length `2ⁿ - 1`.  The argument is the book's: no factor of `wₙ` splits into three consecutive
nonempty factors with the same maximum (between two occurrences of the letter `i` there is always a
larger letter), so in a Simon tree for `wₙ` no node with at least three children has a nonempty
subtree, and a tree in which every node has at most two nonempty children has at most `2^height`
leaves.  Hence every Simon tree for `wₙ` has height at least `n - 1`.
-/
import RequestProject.PartD.SimonTree

namespace Transducers.Exercises

open FactTree

/-! ## The monoid `({0, …, n}, max)` -/

/-- The monoid `{0, 1, …, n}` under maximum, with identity `0`: the book's semigroup
`({1, …, n}, max)` with an identity adjoined. -/
def MaxMon (n : ℕ) : Type := Fin (n + 1)

namespace MaxMon

variable {n : ℕ}

/-- The underlying number of an element of `MaxMon n`. -/
def toFin (x : MaxMon n) : Fin (n + 1) := x

/-- An element of `MaxMon n` from an element of `Fin (n + 1)`. -/
def ofFin (x : Fin (n + 1)) : MaxMon n := x

instance : Fintype (MaxMon n) := inferInstanceAs (Fintype (Fin (n + 1)))

instance : DecidableEq (MaxMon n) := inferInstanceAs (DecidableEq (Fin (n + 1)))

instance : CommMonoid (MaxMon n) where
  mul a b := ofFin (max (toFin a) (toFin b))
  one := ofFin 0
  mul_assoc a b c := max_assoc (toFin a) (toFin b) (toFin c)
  one_mul a := max_eq_right (Fin.zero_le (toFin a))
  mul_one a := max_eq_left (Fin.zero_le (toFin a))
  mul_comm a b := max_comm (toFin a) (toFin b)

lemma card : Fintype.card (MaxMon n) = n + 1 := Fintype.card_fin (n + 1)

lemma val_mul (a b : MaxMon n) : (toFin (a * b)).val = max (toFin a).val (toFin b).val := by
  change (max (toFin a) (toFin b)).val = _
  rcases le_total (toFin a) (toFin b) with h | h
  · rw [max_eq_right h, max_eq_right (Fin.le_def.mp h)]
  · rw [max_eq_left h, max_eq_left (Fin.le_def.mp h)]

lemma val_one : (toFin (1 : MaxMon n)).val = 0 := rfl

lemma toFin_injective : Function.Injective (toFin : MaxMon n → Fin (n + 1)) := fun _ _ h => h

end MaxMon

open MaxMon

/-- The homomorphism `max : {0, …, n}* → {0, …, n}`. -/
def maxHom (n : ℕ) : FreeMonoid (MaxMon n) →* MaxMon n := FreeMonoid.lift id

/-- The largest number in a list of numbers (`0` for the empty list). -/
def listMax (v : List ℕ) : ℕ := v.foldr max 0

lemma le_listMax {v : List ℕ} {x : ℕ} (hx : x ∈ v) : x ≤ listMax v := le_foldr_max hx

lemma listMax_mem {v : List ℕ} (hv : 0 < listMax v) : listMax v ∈ v := by
  induction v with
  | nil => simp [listMax] at hv
  | cons y ys ih =>
    simp only [listMax, List.foldr_cons] at hv ⊢
    rcases le_total y (ys.foldr max 0) with h | h
    · rw [max_eq_right h] at hv ⊢
      exact List.mem_cons_of_mem _ (ih hv)
    · rw [max_eq_left h]
      exact List.mem_cons_self

lemma listMax_le {v : List ℕ} {m : ℕ} (h : ∀ x ∈ v, x ≤ m) : listMax v ≤ m := by
  induction v with
  | nil => simp [listMax]
  | cons y ys ih =>
    simp only [listMax, List.foldr_cons]
    exact max_le (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma maxHom_val (n : ℕ) :
    ∀ v : List (MaxMon n), (toFin (maxHom n (FreeMonoid.ofList v))).val =
      listMax (v.map fun x => (toFin x).val)
  | [] => by simp [listMax]; rfl
  | x :: v => by
    rw [FreeMonoid.ofList_cons, map_mul, val_mul, maxHom_val n v]
    simp [maxHom, listMax]

/-! ## The words `wₙ` -/

/-- The book's words `w₀ = ε`, `wᵢ₊₁ = wᵢ · (i+1) · wᵢ`, as lists of numbers. -/
def simonNat : ℕ → List ℕ
  | 0 => []
  | k + 1 => simonNat k ++ [k + 1] ++ simonNat k

lemma simonNat_bounds : ∀ (k : ℕ), ∀ x ∈ simonNat k, 1 ≤ x ∧ x ≤ k
  | 0 => by simp [simonNat]
  | k + 1 => by
    intro x hx
    simp only [simonNat, List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · have := simonNat_bounds k x hx; omega
    · omega
    · have := simonNat_bounds k x hx; omega

lemma simonNat_length : ∀ k : ℕ, (simonNat k).length = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    simp only [simonNat, List.length_append, List.length_singleton, simonNat_length k, pow_succ]
    have := Nat.one_le_two_pow (n := k)
    omega

/-- The word `wₙ` over the alphabet `{0, …, n}` (it uses the letters `1, …, n`). -/
def simonWord (n : ℕ) : List (MaxMon n) :=
  (simonNat n).map fun x => ofFin ⟨x % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

lemma simonWord_map_val (n : ℕ) : (simonWord n).map (fun x => (toFin x).val) = simonNat n := by
  rw [simonWord, List.map_map]
  conv_rhs => rw [← List.map_id (simonNat n)]
  apply List.map_congr_left
  intro x hx
  have := simonNat_bounds n x hx
  exact Nat.mod_eq_of_lt (by omega)

lemma simonWord_length (n : ℕ) : (simonWord n).length = 2 ^ n - 1 := by
  rw [simonWord, List.length_map, simonNat_length]

/-! ## No three consecutive factors with the same maximum -/

lemma infix_of_not_mem {α : Type*} {u X Y : List α} {m : α} (h : u <:+: X ++ [m] ++ Y)
    (hm : m ∉ u) : u <:+: X ∨ u <:+: Y := by
  obtain ⟨s, t, hst⟩ := h
  rw [List.append_assoc X] at hst
  rcases List.append_eq_append_iff.mp hst with ⟨a, h1, -⟩ | ⟨c, h1, h2⟩
  · exact Or.inl ⟨s, a, h1.symm⟩
  · rcases c with _ | ⟨c0, c'⟩
    · exact Or.inl ⟨s, [], by simpa using h1⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rcases List.append_eq_append_iff.mp h1 with ⟨a, -, h3⟩ | ⟨c, -, h4⟩
      · exact absurd (h3 ▸ List.mem_append_right a List.mem_cons_self) hm
      · rcases c with _ | ⟨c1, c''⟩
        · simp only [List.nil_append] at h4
          exact absurd (h4 ▸ List.mem_cons_self) hm
        · simp only [List.cons_append, List.cons.injEq] at h4
          obtain ⟨-, rfl⟩ := h4
          exact Or.inr ⟨c'', t, by simp⟩

/-- In `wₖ`, no factor splits into three consecutive nonempty factors with the same maximum. -/
theorem simonNat_noTriple : ∀ (k : ℕ) (v₁ v₂ v₃ : List ℕ), v₁ ++ v₂ ++ v₃ <:+: simonNat k →
    v₁ ≠ [] → v₂ ≠ [] → v₃ ≠ [] → listMax v₁ = listMax v₂ → listMax v₂ = listMax v₃ → False
  | 0, v₁, v₂, v₃, h, h₁, _, _, _, _ => by
    have := List.eq_nil_of_infix_nil h
    simp_all
  | k + 1, v₁, v₂, v₃, h, h₁, h₂, h₃, e₁, e₂ => by
    by_cases hk : k + 1 ∈ v₁ ++ v₂ ++ v₃
    · have hle : ∀ x ∈ v₁ ++ v₂ ++ v₃, x ≤ k + 1 := fun x hx =>
        (simonNat_bounds (k + 1) x (h.subset hx)).2
      have hmax : ∀ v, v ⊆ v₁ ++ v₂ ++ v₃ → k + 1 ∈ v → listMax v = k + 1 := fun v hv hkv =>
        le_antisymm (listMax_le fun x hx => hle x (hv hx)) (le_listMax hkv)
      have hall : listMax v₁ = k + 1 := by
        simp only [List.mem_append] at hk
        rcases hk with (hk | hk) | hk
        · exact hmax v₁ (fun x hx => by simp [hx]) hk
        · rw [e₁]; exact hmax v₂ (fun x hx => by simp [hx]) hk
        · rw [e₁, e₂]; exact hmax v₃ (fun x hx => by simp [hx]) hk
      have m₁ : k + 1 ∈ v₁ := hall ▸ listMax_mem (by omega)
      have m₂ : k + 1 ∈ v₂ := (e₁ ▸ hall) ▸ listMax_mem (by omega)
      have m₃ : k + 1 ∈ v₃ := (e₂ ▸ e₁ ▸ hall) ▸ listMax_mem (by omega)
      have hc : 3 ≤ (v₁ ++ v₂ ++ v₃).count (k + 1) := by
        simp only [List.count_append]
        have := List.count_pos_iff.mpr m₁
        have := List.count_pos_iff.mpr m₂
        have := List.count_pos_iff.mpr m₃
        omega
      have h0 : (simonNat k).count (k + 1) = 0 :=
        List.count_eq_zero.mpr fun hm => by have := simonNat_bounds k _ hm; omega
      have hc' : (simonNat (k + 1)).count (k + 1) = 1 := by
        simp [simonNat, List.count_append, h0]
      have := h.sublist.count_le (k + 1)
      omega
    · rw [simonNat] at h
      have hinf : v₁ ++ v₂ ++ v₃ <:+: simonNat k := (infix_of_not_mem h hk).elim id id
      exact simonNat_noTriple k v₁ v₂ v₃ hinf h₁ h₂ h₃ e₁ e₂

/-! ## Simon trees whose underlying string has no such triple -/

/-- If the underlying string of a Simon tree has no factor that splits into three consecutive
nonempty factors with the same value, and no nonempty factor with value `1`, then every node with at
least three children has only empty subtrees, so the tree has at most `2^height` leaves. -/
theorem yield_length_le_of_noTriple {A M : Type*} [Monoid M] (h : FreeMonoid A →* M) :
    ∀ t : FactTree A, t.IsSimon h →
      (∀ v₁ v₂ v₃ : List A, v₁ ++ v₂ ++ v₃ <:+: t.yield → v₁ ≠ [] → v₂ ≠ [] → v₃ ≠ [] →
        h (FreeMonoid.ofList v₁) = h (FreeMonoid.ofList v₂) →
        h (FreeMonoid.ofList v₂) = h (FreeMonoid.ofList v₃) → False) →
      (∀ v : List A, v <:+: t.yield → v ≠ [] → h (FreeMonoid.ofList v) ≠ 1) →
      t.yield.length ≤ 2 ^ t.height := by
  intro t ht
  induction ht with
  | leaf a => intro _ _; simp
  | node cs hcs hidem ih =>
    intro hT hU
    have hsub : ∀ c ∈ cs, c.yield <:+: (node cs).yield := fun c hc => by
      rw [yield_node]
      exact List.infix_of_mem_flatten (List.mem_map_of_mem hc)
    by_cases h3 : 3 ≤ cs.length
    · obtain ⟨e, -, hlab⟩ := hidem h3
      by_cases he : e = 1
      · have hnil : ∀ c ∈ cs, c.yield = [] := fun c hc => by
          by_contra hne
          have h1 := hlab c hc
          rw [he] at h1
          exact hU _ (hsub c hc) hne h1
        have : (node cs).yield = [] := by
          rw [yield_node, List.flatten_eq_nil_iff]
          intro l hl
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
          exact hnil c hc
        rw [this]; simp
      · exfalso
        obtain ⟨c₁, c₂, c₃, rest, rfl⟩ : ∃ c₁ c₂ c₃ rest, cs = c₁ :: c₂ :: c₃ :: rest := by
          match cs, h3 with
          | c₁ :: c₂ :: c₃ :: rest, _ => exact ⟨c₁, c₂, c₃, rest, rfl⟩
          | [], h | [_], h | [_, _], h => simp at h
        have hne : ∀ c ∈ c₁ :: c₂ :: c₃ :: rest, c.yield ≠ [] := fun c hc hnil => by
          apply he
          rw [← hlab c hc, label, hnil]
          exact map_one h
        apply hT c₁.yield c₂.yield c₃.yield ?_ (hne _ (by simp)) (hne _ (by simp))
          (hne _ (by simp))
        · exact (hlab c₁ (by simp)).trans (hlab c₂ (by simp)).symm
        · exact (hlab c₂ (by simp)).trans (hlab c₃ (by simp)).symm
        · refine ⟨[], (rest.map yield).flatten, ?_⟩
          simp [List.append_assoc]
    · have hH : ∀ c ∈ cs, c.height + 1 ≤ (node cs).height := fun c hc => height_le_of_mem hc
      have hpos : 1 ≤ (node cs).height := by rw [height_node]; omega
      have hc : ∀ x ∈ cs.map (fun c => c.yield.length), x ≤ 2 ^ ((node cs).height - 1) := by
        intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        have h1 := ih c hc (fun v₁ v₂ v₃ hv => hT v₁ v₂ v₃ (hv.trans (hsub c hc)))
          (fun v hv => hU v (hv.trans (hsub c hc)))
        exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by have := hH c hc; omega))
      have hsum := List.sum_le_card_nsmul _ _ hc
      rw [yield_node, List.length_flatten, List.map_map]
      simp only [List.length_map, smul_eq_mul] at hsum
      have h2 : 2 ^ (node cs).height = 2 * 2 ^ ((node cs).height - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h4 : cs.length ≤ 2 := by omega
      calc ((cs.map (List.length ∘ yield)).sum) = (cs.map fun c => c.yield.length).sum := rfl
        _ ≤ cs.length * 2 ^ ((node cs).height - 1) := hsum
        _ ≤ 2 * 2 ^ ((node cs).height - 1) := Nat.mul_le_mul_right _ h4
        _ = 2 ^ (node cs).height := h2.symm

/-! ## The exercise -/

lemma simonWord_noTriple (n : ℕ) (v₁ v₂ v₃ : List (MaxMon n))
    (hv : v₁ ++ v₂ ++ v₃ <:+: simonWord n) (h₁ : v₁ ≠ []) (h₂ : v₂ ≠ []) (h₃ : v₃ ≠ [])
    (e₁ : maxHom n (FreeMonoid.ofList v₁) = maxHom n (FreeMonoid.ofList v₂))
    (e₂ : maxHom n (FreeMonoid.ofList v₂) = maxHom n (FreeMonoid.ofList v₃)) : False := by
  have hv' := hv.map (fun x => (toFin x).val)
  rw [simonWord_map_val, List.map_append, List.map_append] at hv'
  refine simonNat_noTriple n _ _ _ hv' (by simpa using h₁) (by simpa using h₂) (by simpa using h₃)
    ?_ ?_
  · rw [← maxHom_val, ← maxHom_val, e₁]
  · rw [← maxHom_val, ← maxHom_val, e₂]

lemma simonWord_noUnit (n : ℕ) (v : List (MaxMon n)) (hv : v <:+: simonWord n) (hne : v ≠ []) :
    maxHom n (FreeMonoid.ofList v) ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil v hne
  have hval := maxHom_val n v
  rw [h1, val_one] at hval
  have hle : (toFin x).val ≤ 0 := hval ▸ le_listMax (List.mem_map_of_mem hx)
  have hmem : (toFin x).val ∈ simonNat n := by
    rw [← simonWord_map_val]
    exact List.mem_map_of_mem (hv.subset hx)
  have := simonNat_bounds n _ hmem
  omega

/-- **Exercise `exer:height-of-simon-tree`.**  The height of a Simon tree can be linear in the size
of the semigroup.  For the monoid `MaxMon n = ({0, 1, …, n}, max)` -- the book's semigroup
`({1, …, n}, max)` with the identity `0` adjoined, which has `n + 1` elements -- and the homomorphism
`max : {0, …, n}* → {0, …, n}`, the book's word `wₙ` (of length `2ⁿ - 1`) has no Simon tree of
height less than `n - 1`.  In particular the constant `k` of the Factorisation Forest Theorem
(`thm:factorisation-forest`) for this homomorphism is at least `n - 1`. -/
theorem height_of_simon_tree (n : ℕ) :
    Fintype.card (MaxMon n) = n + 1 ∧ (simonWord n).length = 2 ^ n - 1 ∧
      ∀ t : FactTree (MaxMon n), t.yield = simonWord n → t.IsSimon (maxHom n) →
        n ≤ t.height + 1 := by
  refine ⟨MaxMon.card, simonWord_length n, fun t ht hs => ?_⟩
  have hlen := yield_length_le_of_noTriple (maxHom n) t hs
    (fun v₁ v₂ v₃ hv => simonWord_noTriple n v₁ v₂ v₃ (ht ▸ hv))
    (fun v hv => simonWord_noUnit n v (ht ▸ hv))
  rw [ht, simonWord_length] at hlen
  by_contra hlt
  have h1 : 2 ^ (t.height + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := Nat.one_le_two_pow (n := t.height)
  rw [pow_add] at h1
  omega

end Transducers.Exercises
