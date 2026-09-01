/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

The *strings of order `n`* of the solution of that exercise, and their
combinatorics.  The counting definitions `PolyBounded`, `expTower`, `numOrder`
and `lenOrder` were originally stated in
`RequestProject/Exercises/FONonElementary.lean`; they have been moved here,
unchanged, so that the strings of order `n` and the first-order formulas
defining them can be developed before the statement of the exercise.
`RequestProject/Exercises/FONonElementary.lean` imports this file, so all names
are unchanged.
-/
import Mathlib

namespace Transducers.Exercises

/-! ## The counting of the solution -/

/-- A function of `ℕ` is bounded by a polynomial. -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, p n ≤ C * (n + 1) ^ d

/-- The tower of exponentials `exp` of the exercise: `exp 1 = 1` and `exp (n+1) = 2 ^ exp n`.
The value at `0` is irrelevant to the exercise and is set to `0`. -/
def expTower : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 ^ expTower (n + 1)

/-- The number of strings of order `n`: there is one string of order `0`, and a string of order
`n+1` is a choice of one bit in front of each string of order `n`. -/
def numOrder : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ numOrder n

/-- The length of a string of order `n`: a string of order `n+1` consists of one bit followed by
a string of order `n`, once for each string of order `n`. -/
def lenOrder : ℕ → ℕ
  | 0 => 0
  | n + 1 => numOrder n * (1 + lenOrder n)

lemma numOrder_eq_expTower (n : ℕ) : numOrder n = expTower (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [numOrder, ih]; rfl

lemma numOrder_pos (n : ℕ) : 0 < numOrder n := by
  cases n with
  | zero => norm_num [numOrder]
  | succ n => exact Nat.two_pow_pos _

/-- **A string of order `n` is at least `exp n` long.** -/
theorem expTower_le_lenOrder (n : ℕ) : expTower n ≤ lenOrder n := by
  cases n with
  | zero => simp [expTower, lenOrder]
  | succ n =>
      have h : numOrder n = expTower (n + 1) := numOrder_eq_expTower n
      calc expTower (n + 1) = numOrder n := h.symm
        _ ≤ numOrder n * (1 + lenOrder n) := Nat.le_mul_of_pos_right _ (by omega)
        _ = lenOrder (n + 1) := rfl

/-- The size of one block of a string of order `k+1`: a marker letter followed by a string of
order `k`. -/
def blkSize (k : ℕ) : ℕ := 1 + lenOrder k

lemma blkSize_pos (k : ℕ) : 0 < blkSize k := by simp [blkSize]

lemma lenOrder_succ (k : ℕ) : lenOrder (k + 1) = numOrder k * blkSize k := rfl

/-! ## A general lemma on flattening a list of blocks of equal length -/

section Blocks

variable {α : Type}

/-- The concatenation of `l` blocks of length `c`, cut at the `t`-th block. -/
lemma flatMap_range_drop_take (f : ℕ → List α) (c : ℕ) (hc : ∀ i, (f i).length = c)
    (l t : ℕ) (ht : t < l) :
    (((List.range l).flatMap f).drop (t * c)).take c = f t := by
  induction l generalizing t f with
  | zero => omega
  | succ l ih =>
      rw [List.range_succ_eq_map, List.flatMap_cons]
      have hmap : ((List.range l).map Nat.succ).flatMap f
          = (List.range l).flatMap (fun i => f (i + 1)) := by
        simp [List.flatMap_map]
      have h0 : (f 0).length = c := hc 0
      cases t with
      | zero => simp [h0]
      | succ t =>
          have he : (t + 1) * c = c + t * c := by ring
          have hd : c + t * c - (f 0).length = t * c := by omega
          rw [he, List.drop_append, hd, List.drop_eq_nil_of_le (by omega), List.nil_append, hmap]
          exact ih (fun i => f (i + 1)) (fun i => hc (i + 1)) t (by omega)

lemma flatMap_range_length (f : ℕ → List α) (c : ℕ) (hc : ∀ i, (f i).length = c) (l : ℕ) :
    ((List.range l).flatMap f).length = l * c := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.length_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil, hc]
      ring

lemma flatMap_range_getElem? (f : ℕ → List α) (c : ℕ) (hc : ∀ i, (f i).length = c)
    (l t r : ℕ) (ht : t < l) (hr : r < c) :
    ((List.range l).flatMap f)[t * c + r]? = (f t)[r]? := by
  have h := flatMap_range_drop_take f c hc l t ht
  have h2 : ((List.range l).flatMap f)[t * c + r]?
      = (((List.range l).flatMap f).drop (t * c))[r]? := by
    rw [List.getElem?_drop]
  rw [h2, ← h, List.getElem?_take_of_lt hr]

end Blocks

/-! ## Binary representations -/

section Bits

lemma testBit_split_low {A r c j : ℕ} (hr : r < 2 ^ c) (hj : j < c) :
    (A * 2 ^ c + r).testBit j = r.testBit j := by
  have h1 : (A * 2 ^ c + r) % 2 ^ c = r := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hr]
  have h2 := Nat.testBit_mod_two_pow (A * 2 ^ c + r) c j
  rw [h1] at h2
  simp [hj] at h2
  exact h2.symm

lemma testBit_split_high {A r c j : ℕ} (hr : r < 2 ^ c) (hj : c ≤ j) :
    (A * 2 ^ c + r).testBit j = A.testBit (j - c) := by
  have h1 : (A * 2 ^ c + r) / 2 ^ c = A := by
    rw [Nat.add_div_of_dvd_right ⟨A, by ring⟩, Nat.div_eq_of_lt hr,
      Nat.mul_div_cancel _ (Nat.two_pow_pos c), Nat.add_zero]
  have h2 := Nat.testBit_div_two_pow (n := c) (A * 2 ^ c + r) (j - c)
  rw [h1, Nat.sub_add_cancel hj] at h2
  exact h2.symm

lemma testBit_eq_false_of_le {x l j : ℕ} (hx : x < 2 ^ l) (hj : l ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))

lemma eq_of_testBit_below {x y l : ℕ} (hx : x < 2 ^ l) (hy : y < 2 ^ l)
    (h : ∀ j < l, x.testBit j = y.testBit j) : x = y := by
  refine Nat.eq_of_testBit_eq (fun j => ?_)
  rcases lt_or_ge j l with hj | hj
  · exact h j hj
  · rw [testBit_eq_false_of_le hx hj, testBit_eq_false_of_le hy hj]

/-- A number whose bits below `j₀` are all `1` and whose bit `j₀` is `0` ends in `2 ^ j₀ - 1`. -/
lemma mod_eq_of_low_ones {x j0 : ℕ} (h1 : ∀ j < j0, x.testBit j = true)
    (h0 : x.testBit j0 = false) : x % 2 ^ (j0 + 1) = 2 ^ j0 - 1 := by
  refine Nat.eq_of_testBit_eq (fun j => ?_)
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  rcases lt_trichotomy j j0 with h | h | h
  · simp [h, h1 j h, Nat.lt_succ_of_lt h]
  · subst h; simp [h0]
  · simp [Nat.not_lt.2 h.le, Nat.not_lt.2 (by omega : j0 + 1 ≤ j)]

lemma eq_split_of_low_ones {x j0 : ℕ} (h1 : ∀ j < j0, x.testBit j = true)
    (h0 : x.testBit j0 = false) :
    x = (x / 2 ^ (j0 + 1)) * 2 ^ (j0 + 1) + (2 ^ j0 - 1) := by
  conv_lhs => rw [← Nat.div_add_mod x (2 ^ (j0 + 1)), mod_eq_of_low_ones h1 h0]
  ring

/-- Adding one to a number whose bits below `j₀` are all `1` and whose bit `j₀` is `0`. -/
lemma testBit_succ_of_low_ones {x j0 : ℕ} (h1 : ∀ j < j0, x.testBit j = true)
    (h0 : x.testBit j0 = false) :
    (∀ j < j0, (x + 1).testBit j = false) ∧ (x + 1).testBit j0 = true ∧
      (∀ j, j0 < j → (x + 1).testBit j = x.testBit j) := by
  set A := x / 2 ^ (j0 + 1) with hA
  have hsplit : x = A * 2 ^ (j0 + 1) + (2 ^ j0 - 1) := eq_split_of_low_ones h1 h0
  have hone : 1 ≤ 2 ^ j0 := Nat.one_le_two_pow
  have hlt1 : 2 ^ j0 < 2 ^ (j0 + 1) := by
    have : 2 ^ (j0 + 1) = 2 ^ j0 + 2 ^ j0 := by ring
    omega
  have hlt2 : 2 ^ j0 - 1 < 2 ^ (j0 + 1) := by omega
  have hy : x + 1 = A * 2 ^ (j0 + 1) + 2 ^ j0 := by
    conv_lhs => rw [hsplit]
    omega
  refine ⟨fun j hj => ?_, ?_, fun j hj => ?_⟩
  · rw [hy, testBit_split_low hlt1 (by omega), Nat.testBit_two_pow]
    simp; omega
  · rw [hy, testBit_split_low hlt1 (by omega), Nat.testBit_two_pow]
    simp
  · rw [hy, testBit_split_high hlt1 (by omega)]
    conv_rhs => rw [hsplit]
    rw [testBit_split_high hlt2 (by omega)]

end Bits

/-! ## The alphabet -/

/-- The alphabet of the strings of order at most `N`: a letter is a *level* between `0` and `N`
together with a bit.  Only the levels `1, …, N` are used: a string of order `k` uses the levels
`1, …, k`, the level `k` being that of its own `numOrder (k-1)` marker letters. -/
abbrev Lett (N : ℕ) : Type := Fin (N + 1) × Bool

/-- The level `k` as an index of the alphabet `Lett N`; levels above `N` are clamped to `N` and
are never used. -/
def lv (N k : ℕ) : Fin (N + 1) := ⟨min k N, by omega⟩

lemma lv_inj {N j j' : ℕ} (hj : j ≤ N) (hj' : j' ≤ N) (h : lv N j = lv N j') : j = j' := by
  have := congrArg Fin.val h
  simp [lv, Nat.min_eq_left hj, Nat.min_eq_left hj'] at this
  exact this

lemma lv_ne {N j j' : ℕ} (hj : j ≤ N) (hj' : j' ≤ N) (h : j ≠ j') : lv N j ≠ lv N j' :=
  fun hc => h (lv_inj hj hj' hc)

/-! ## The strings of order `k` -/

/-- The `i`-th bit, most significant first, of the `l`-bit binary representation of `m`. -/
def bitAt (l m i : ℕ) : Bool := m.testBit (l - 1 - i)

lemma bitAt_eq_testBit (l m t : ℕ) : bitAt l m t = m.testBit (l - 1 - t) := rfl

/-- Two numbers with `l` bits that have the same `l` bits are equal. -/
lemma eq_of_bitAt {l x y : ℕ} (hx : x < 2 ^ l) (hy : y < 2 ^ l)
    (h : ∀ t < l, bitAt l x t = bitAt l y t) : x = y := by
  refine eq_of_testBit_below hx hy (fun j hj => ?_)
  have := h (l - 1 - j) (by omega)
  rwa [bitAt_eq_testBit, bitAt_eq_testBit, show l - 1 - (l - 1 - j) = j by omega] at this

/-- If the `l`-bit representations of `x` and `y` show the pattern of a binary increment at the
position `t₀`, then `y = x + 1`. -/
lemma eq_succ_of_bitAt {l x y t0 : ℕ} (hx : x < 2 ^ l) (hy : y < 2 ^ l) (ht0 : t0 < l)
    (hx0 : bitAt l x t0 = false) (hy0 : bitAt l y t0 = true)
    (hlt : ∀ t < t0, bitAt l x t = bitAt l y t)
    (hgt : ∀ t, t0 < t → t < l → bitAt l x t = true ∧ bitAt l y t = false) :
    y = x + 1 := by
  set j0 := l - 1 - t0 with hj0
  have hxj0 : x.testBit j0 = false := hx0
  have hyj0 : y.testBit j0 = true := hy0
  have hlow : ∀ j < j0, x.testBit j = true ∧ y.testBit j = false := by
    intro j hj
    have h := hgt (l - 1 - j) (by omega) (by omega)
    rwa [bitAt_eq_testBit, bitAt_eq_testBit, show l - 1 - (l - 1 - j) = j by omega] at h
  have hhigh : ∀ j, j0 < j → j < l → x.testBit j = y.testBit j := by
    intro j hj hjl
    have h := hlt (l - 1 - j) (by omega)
    rwa [bitAt_eq_testBit, bitAt_eq_testBit, show l - 1 - (l - 1 - j) = j by omega] at h
  obtain ⟨e1, e2, e3⟩ := testBit_succ_of_low_ones (fun j hj => (hlow j hj).1) hxj0
  refine (Nat.eq_of_testBit_eq (fun j => ?_)).symm
  rcases lt_trichotomy j j0 with h | h | h
  · rw [e1 j h, (hlow j h).2]
  · rw [h, e2, hyj0]
  · rw [e3 j h]
    rcases lt_or_ge j l with hjl | hjl
    · exact hhigh j h hjl
    · rw [testBit_eq_false_of_le hx hjl, testBit_eq_false_of_le hy hjl]

/-- The pattern of a binary increment in the `l`-bit representations of `x` and `x + 1`. -/
lemma bitAt_of_succ {l x : ℕ} (hx : x + 1 < 2 ^ l) :
    ∃ t0 < l, bitAt l x t0 = false ∧ bitAt l (x + 1) t0 = true ∧
      (∀ t < t0, bitAt l x t = bitAt l (x + 1) t) ∧
      (∀ t, t0 < t → t < l → bitAt l x t = true ∧ bitAt l (x + 1) t = false) := by
  have hx' : x < 2 ^ l := by omega
  have hex : ∃ j, x.testBit j = false := ⟨l, testBit_eq_false_of_le hx' le_rfl⟩
  set j0 := Nat.find hex with hj0def
  have h0 : x.testBit j0 = false := Nat.find_spec hex
  have h1 : ∀ j < j0, x.testBit j = true := by
    intro j hj
    have := Nat.find_min hex hj
    simpa using this
  have hj0l : j0 < l := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ j < l, x.testBit j = true := fun j hj => h1 j (by omega)
    have hmod := mod_eq_of_low_ones hall (testBit_eq_false_of_le hx' le_rfl)
    have hpow : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
    have hone : (1:ℕ) ≤ 2 ^ l := Nat.one_le_two_pow
    rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  obtain ⟨e1, e2, e3⟩ := testBit_succ_of_low_ones h1 h0
  refine ⟨l - 1 - j0, by omega, ?_, ?_, ?_, ?_⟩
  · rw [bitAt_eq_testBit, show l - 1 - (l - 1 - j0) = j0 by omega]; exact h0
  · rw [bitAt_eq_testBit, show l - 1 - (l - 1 - j0) = j0 by omega]; exact e2
  · intro t ht
    rw [bitAt_eq_testBit, bitAt_eq_testBit]
    exact (e3 (l - 1 - t) (by omega)).symm
  · intro t ht htl
    rw [bitAt_eq_testBit, bitAt_eq_testBit]
    exact ⟨h1 (l - 1 - t) (by omega), e1 (l - 1 - t) (by omega)⟩

lemma bitAt_zero (l t : ℕ) : bitAt l 0 t = false := by simp [bitAt]

lemma bitAt_two_pow_sub_one {l t : ℕ} (ht : t < l) : bitAt l (2 ^ l - 1) t = true := by
  rw [bitAt_eq_testBit, Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  omega

/-- A number with `l` bits is `0` exactly if all its bits are `0`. -/
lemma eq_zero_iff_bitAt {l m : ℕ} (hm : m < 2 ^ l) : m = 0 ↔ ∀ t, t < l → bitAt l m t = false := by
  constructor
  · rintro rfl t _; exact bitAt_zero l t
  · intro h
    exact eq_of_bitAt hm (Nat.two_pow_pos l) (fun t ht => by rw [h t ht, bitAt_zero])

/-- A number with `l` bits is `2 ^ l - 1` exactly if all its bits are `1`. -/
lemma eq_last_iff_bitAt {l m : ℕ} (hm : m < 2 ^ l) :
    m = 2 ^ l - 1 ↔ ∀ t, t < l → bitAt l m t = true := by
  have hone : (1:ℕ) ≤ 2 ^ l := Nat.one_le_two_pow
  constructor
  · rintro rfl t ht; exact bitAt_two_pow_sub_one ht
  · intro h
    refine eq_of_bitAt hm (by omega) (fun t ht => ?_)
    rw [h t ht, bitAt_two_pow_sub_one ht]

/-- The number with the prescribed `l` bits, least significant first. -/
def bitsToNat : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | l + 1, f => (if f l then 2 ^ l else 0) + bitsToNat l f

lemma bitsToNat_lt (l : ℕ) (f : ℕ → Bool) : bitsToNat l f < 2 ^ l := by
  induction l with
  | zero => simp [bitsToNat]
  | succ l ih =>
      have h2 : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
      have : bitsToNat (l + 1) f ≤ 2 ^ l + bitsToNat l f := by
        rw [bitsToNat]; split <;> omega
      omega

lemma testBit_bitsToNat {l : ℕ} (f : ℕ → Bool) {j : ℕ} (hj : j < l) :
    (bitsToNat l f).testBit j = f j := by
  induction l with
  | zero => omega
  | succ l ih =>
      have hlt := bitsToNat_lt l f
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · rw [bitsToNat]
        cases hf : f l with
        | false => simpa using ih h
        | true =>
            simp only [if_pos]
            rw [Nat.testBit_two_pow_add_gt h]
            exact ih h
      · subst h
        rw [bitsToNat]
        cases hf : f j with
        | false => simpa using Nat.testBit_lt_two_pow hlt
        | true =>
            simp only [if_pos]
            rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
            rfl

/-- The number whose `l` bits, most significant first, are given by `β`. -/
def natOfBitAt (l : ℕ) (β : ℕ → Bool) : ℕ := bitsToNat l (fun j => β (l - 1 - j))

lemma natOfBitAt_lt (l : ℕ) (β : ℕ → Bool) : natOfBitAt l β < 2 ^ l := bitsToNat_lt l _

lemma bitAt_natOfBitAt {l : ℕ} (β : ℕ → Bool) {t : ℕ} (ht : t < l) :
    bitAt l (natOfBitAt l β) t = β t := by
  rw [bitAt_eq_testBit, natOfBitAt, testBit_bitsToNat _ (by omega : l - 1 - t < l),
    show l - 1 - (l - 1 - t) = t by omega]

/-- The `m`-th string of order `k` over the alphabet `Lett N`.  There is no string of order `0`
but the empty one; the `m`-th string of order `k+1` is obtained by putting, in front of the
`i`-th string of order `k`, a marker letter of level `k+1` carrying the `i`-th bit of `m`. -/
def ordStr (N : ℕ) : ℕ → ℕ → List (Lett N)
  | 0, _ => []
  | k + 1, m => (List.range (numOrder k)).flatMap
      (fun i => (lv N (k + 1), bitAt (numOrder k) m i) :: ordStr N k i)

lemma ordStr_zero (N m : ℕ) : ordStr N 0 m = [] := rfl

lemma ordStr_succ (N k m : ℕ) :
    ordStr N (k + 1) m = (List.range (numOrder k)).flatMap
      (fun i => (lv N (k + 1), bitAt (numOrder k) m i) :: ordStr N k i) := rfl

lemma ordStr_length (N k m : ℕ) : (ordStr N k m).length = lenOrder k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
      rw [ordStr_succ,
        flatMap_range_length _ (blkSize k) (fun i => by rw [List.length_cons, ih, blkSize,
          Nat.add_comm]), lenOrder_succ]

/-- Every letter of a string of order `k` has a level between `1` and `k`. -/
lemma ordStr_level {N k m : ℕ} {x : Lett N} (hx : x ∈ ordStr N k m) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ x.1 = lv N j := by
  induction k generalizing m with
  | zero => simp [ordStr_zero] at hx
  | succ k ih =>
      rw [ordStr_succ, List.mem_flatMap] at hx
      obtain ⟨i, _, hx⟩ := hx
      rcases List.mem_cons.1 hx with h | h
      · exact ⟨k + 1, by omega, by omega, by rw [h]⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih h
        exact ⟨j, h1, by omega, h3⟩

/-- A marker letter of level `k+1` does not occur in a string of order `k`. -/
lemma ordStr_not_mem_marker {N k m : ℕ} (hk : k + 1 ≤ N) (b : Bool) :
    (lv N (k + 1), b) ∉ ordStr N k m := by
  intro hx
  obtain ⟨j, h1, h2, h3⟩ := ordStr_level hx
  exact absurd (lv_inj (by omega) (by omega) h3) (by omega)

lemma blkSize_eq (k : ℕ) : blkSize k = lenOrder k + 1 := by simp [blkSize, Nat.add_comm]

lemma ordStr_block_length (N k m : ℕ) :
    ((lv N (k + 1), bitAt (numOrder k) m 0) :: ordStr N k 0).length = blkSize k := by
  rw [List.length_cons, ordStr_length, blkSize_eq]

/-- The marker letter that starts the `t`-th block of the `m`-th string of order `k+1`. -/
lemma ordStr_succ_getElem?_marker {N k m t : ℕ} (ht : t < numOrder k) :
    (ordStr N (k + 1) m)[t * blkSize k]? = some (lv N (k + 1), bitAt (numOrder k) m t) := by
  have h := flatMap_range_getElem?
    (fun i => (lv N (k + 1), bitAt (numOrder k) m i) :: ordStr N k i) (blkSize k)
    (fun i => by rw [List.length_cons, ordStr_length, blkSize_eq]) (numOrder k) t 0 ht
    (blkSize_pos k)
  rw [ordStr_succ]
  simpa using h

/-- The letters inside the `t`-th block of the `m`-th string of order `k+1`. -/
lemma ordStr_succ_getElem?_inner {N k m t r : ℕ} (ht : t < numOrder k) (hr : r < lenOrder k) :
    (ordStr N (k + 1) m)[t * blkSize k + (r + 1)]? = (ordStr N k t)[r]? := by
  have h := flatMap_range_getElem?
    (fun i => (lv N (k + 1), bitAt (numOrder k) m i) :: ordStr N k i) (blkSize k)
    (fun i => by rw [List.length_cons, ordStr_length, blkSize_eq]) (numOrder k) t (r + 1) ht
    (by rw [blkSize_eq]; omega)
  rw [ordStr_succ]
  simpa using h

/-- The positions of the marker letters of level `k+1` in the `m`-th string of order `k+1`. -/
lemma ordStr_succ_marker_iff {N k : ℕ} (hk : k + 1 ≤ N) (m i : ℕ) (b : Bool)
    (hi : i < lenOrder (k + 1)) :
    (ordStr N (k + 1) m)[i]? = some (lv N (k + 1), b) ↔
      ∃ t, t < numOrder k ∧ i = t * blkSize k ∧ b = bitAt (numOrder k) m t := by
  have hS : 0 < blkSize k := blkSize_pos k
  constructor
  · intro h
    obtain ⟨t, r, hrS, hir⟩ : ∃ t r, r < blkSize k ∧ i = t * blkSize k + r :=
      ⟨i / blkSize k, i % blkSize k, Nat.mod_lt _ hS,
        by rw [Nat.mul_comm]; exact (Nat.div_add_mod i (blkSize k)).symm⟩
    have htl : t < numOrder k := by
      by_contra hcon
      push_neg at hcon
      have hle : numOrder k * blkSize k ≤ t * blkSize k := Nat.mul_le_mul_right _ hcon
      rw [lenOrder_succ] at hi
      omega
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hir
      subst hr0
      simp only [Nat.add_zero] at h ⊢
      rw [ordStr_succ_getElem?_marker htl] at h
      exact ⟨t, htl, rfl, ((Prod.mk.injEq _ _ _ _ ▸ (Option.some.injEq _ _ ▸ h)).2).symm⟩
    · exfalso
      rw [hir, show r = (r - 1) + 1 by omega,
        ordStr_succ_getElem?_inner htl (by rw [blkSize_eq] at hrS; omega)] at h
      exact ordStr_not_mem_marker hk b (List.mem_of_getElem? h)
  · rintro ⟨t, htl, rfl, rfl⟩
    exact ordStr_succ_getElem?_marker htl

/-- Distinct indices give distinct strings of order `k`. -/
lemma ordStr_index_inj {N k t t' : ℕ} (ht : t < numOrder k) (ht' : t' < numOrder k)
    (h : ordStr N k t = ordStr N k t') : t = t' := by
  cases k with
  | zero => simp [numOrder] at ht ht'; omega
  | succ k =>
      refine eq_of_bitAt (l := numOrder k) ht ht' (fun s hs => ?_)
      have h1 := ordStr_succ_getElem?_marker (N := N) (m := t) hs
      have h2 := ordStr_succ_getElem?_marker (N := N) (m := t') hs
      rw [h, h2] at h1
      exact ((Prod.mk.injEq _ _ _ _ ▸ (Option.some.injEq _ _ ▸ h1)).2).symm

/-! ## Infixes of a string -/

/-- The infix of `u` consisting of the positions `a, a+1, …, b`. -/
def segI {A : Type} (u : List A) (a b : ℕ) : List A := (u.take (b + 1)).drop a

lemma segI_length {A : Type} {u : List A} {a b : ℕ} (hb : b < u.length) :
    (segI u a b).length = b + 1 - a := by
  simp [segI, hb]

lemma segI_getElem?_of_lt {A : Type} (u : List A) (a b i : ℕ) (hi : a + i < b + 1) :
    (segI u a b)[i]? = u[a + i]? := by
  simp [segI, List.getElem?_drop, List.getElem?_take_of_lt hi]

/-- An infix of `u` is a given list exactly if it has the right length and the right letters. -/
lemma segI_eq_iff {A : Type} {u : List A} {a b : ℕ} {w : List A} (hb : b < u.length) :
    segI u a b = w ↔ (w.length = b + 1 - a ∧ ∀ i, i < w.length → u[a + i]? = w[i]?) := by
  constructor
  · rintro rfl
    refine ⟨segI_length hb, fun i hi => ?_⟩
    rw [segI_length hb] at hi
    exact (segI_getElem?_of_lt u a b i (by omega)).symm
  · rintro ⟨hl, h⟩
    refine List.ext_getElem? (fun i => ?_)
    rcases lt_or_ge i w.length with hi | hi
    · rw [segI_getElem?_of_lt u a b i (by omega), h i hi]
    · rw [List.getElem?_eq_none (by rw [segI_length hb]; omega), List.getElem?_eq_none hi]

end Transducers.Exercises
