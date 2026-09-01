/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

Reading an infix of a string as a string of order `k+1`: the block structure of
the strings of order `k+1`, in both directions.  This is the combinatorial
content of the induction step of the Claim in the solution of the exercise.
-/
import RequestProject.Exercises.FONonElemOrder

namespace Transducers.Exercises

variable {N : ℕ}

/-! ## Infixes, markers and blocks -/

/-- The position `p` of `u` carries a marker letter of level `k+1`. -/
def MkAt (u : List (Lett N)) (k p : ℕ) : Prop := ∃ b : Bool, u[p]? = some (lv N (k + 1), b)

/-- The position `p` of `u` carries the marker letter of level `k+1` with the bit `b`. -/
def BitPos (u : List (Lett N)) (k p : ℕ) (b : Bool) : Prop := u[p]? = some (lv N (k + 1), b)

/-- The infix `[a, b]` of `u` is the `m`-th string of order `k`. -/
def IsOrdAt (u : List (Lett N)) (k m a b : ℕ) : Prop :=
  a ≤ b + 1 ∧ b < u.length ∧ segI u a b = ordStr N k m

/-- `q` is the last position of the block of level `k+1` that starts at the marker `p`, inside
an infix that ends at `b`: there is no marker of level `k+1` in `(p, q]`, and either `q` is the
end `b` of the infix or the next position carries a marker. -/
def IsBE (u : List (Lett N)) (k p q b : ℕ) : Prop :=
  p ≤ q ∧ q ≤ b ∧ (∀ r, p < r → r ≤ q → ¬ MkAt u k r) ∧ (q = b ∨ MkAt u k (q + 1))

lemma bitPos_mkAt {u : List (Lett N)} {k p : ℕ} {b : Bool} (h : BitPos u k p b) :
    MkAt u k p := ⟨b, h⟩

lemma bitPos_inj {u : List (Lett N)} {k p : ℕ} {b b' : Bool} (h : BitPos u k p b)
    (h' : BitPos u k p b') : b = b' := by
  rw [BitPos, h'] at h
  exact ((Prod.mk.injEq _ _ _ _ ▸ (Option.some.injEq _ _ ▸ h)).2).symm

/-- The length of an infix that is a string of order `k`. -/
lemma isOrdAt_length {u : List (Lett N)} {k m a b : ℕ} (h : IsOrdAt u k m a b) :
    b + 1 = a + lenOrder k := by
  obtain ⟨hab, hbl, hseg⟩ := h
  have := congrArg List.length hseg
  rw [segI_length hbl, ordStr_length] at this
  omega

lemma isOrdAt_zero_iff {u : List (Lett N)} {m a b : ℕ} :
    IsOrdAt u 0 m a b ↔ (a = b + 1 ∧ b < u.length) := by
  constructor
  · intro h
    have hl := isOrdAt_length h
    rw [show lenOrder 0 = 0 from rfl] at hl
    exact ⟨by omega, h.2.1⟩
  · rintro ⟨rfl, hbl⟩
    refine ⟨le_rfl, hbl, ?_⟩
    rw [segI_eq_iff hbl, ordStr_zero]
    exact ⟨by simp, by simp⟩

/-- An infix determines the index of the string of order `k` that it is. -/
lemma isOrdAt_unique {u : List (Lett N)} {k m m' a b : ℕ} (hm : m < numOrder k)
    (hm' : m' < numOrder k) (h : IsOrdAt u k m a b) (h' : IsOrdAt u k m' a b) : m = m' :=
  ordStr_index_inj hm hm' (h.2.2.symm.trans h'.2.2)

/-- Every marker has a block end. -/
lemma exists_isBE (u : List (Lett N)) (k p b : ℕ) (hpb : p ≤ b) : ∃ q, IsBE u k p q b := by
  by_cases hex : ∃ r, p < r ∧ r ≤ b ∧ MkAt u k r
  · classical
    have hex' : ∃ r, p < r ∧ r ≤ b ∧ MkAt u k r := hex
    obtain ⟨r0, hr0⟩ := hex'
    let P : ℕ → Prop := fun r => p < r ∧ r ≤ b ∧ MkAt u k r
    have hfind : P (Nat.find ⟨r0, hr0⟩ : ℕ) := Nat.find_spec (⟨r0, hr0⟩ : ∃ r, P r)
    refine ⟨Nat.find (⟨r0, hr0⟩ : ∃ r, P r) - 1, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro r hr hr2 hmk
      have : ¬ P r := Nat.find_min (⟨r0, hr0⟩ : ∃ r, P r) (by omega)
      exact this ⟨by omega, by omega, hmk⟩
    · right
      rw [show Nat.find (⟨r0, hr0⟩ : ∃ r, P r) - 1 + 1 = Nat.find (⟨r0, hr0⟩ : ∃ r, P r) by omega]
      exact hfind.2.2
  · push_neg at hex
    exact ⟨b, hpb, le_rfl, fun r hr hr2 hmk => (hex r hr hr2) hmk, Or.inl rfl⟩

/-- The block end is unique. -/
lemma isBE_unique {u : List (Lett N)} {k p q q' b : ℕ} (h : IsBE u k p q b)
    (h' : IsBE u k p q' b) : q = q' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_ge q q' with hlt | hge
  · rcases h4 with rfl | hm
    · omega
    · exact h3' (q + 1) (by omega) (by omega) hm
  · have hlt : q' < q := by omega
    rcases h4' with rfl | hm
    · omega
    · exact h3 (q' + 1) (by omega) (by omega) hm

/-! ## From a string of order `k+1` to its blocks -/

theorem isOrdAt_succ_fwd {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {m a b : ℕ}
    (h : IsOrdAt u (k + 1) m a b) :
    b + 1 = a + numOrder k * blkSize k ∧
    (∀ p, a ≤ p → p ≤ b → (MkAt u k p ↔ ∃ t, t < numOrder k ∧ p = a + t * blkSize k)) ∧
    (∀ t, t < numOrder k →
      BitPos u k (a + t * blkSize k) (bitAt (numOrder k) m t) ∧
      IsOrdAt u k t (a + t * blkSize k + 1) (a + t * blkSize k + lenOrder k) ∧
      IsBE u k (a + t * blkSize k) (a + t * blkSize k + lenOrder k) b) := by
  obtain ⟨hab, hbl, hseg⟩ := h
  have hlength : (ordStr N (k + 1) m).length = numOrder k * blkSize k := by
    rw [ordStr_length, lenOrder_succ]
  rw [segI_eq_iff hbl] at hseg
  obtain ⟨hlen, hpt⟩ := hseg
  rw [hlength] at hlen hpt
  have hb1 : b + 1 = a + numOrder k * blkSize k := by omega
  -- the markers
  have hbit : ∀ t, t < numOrder k →
      BitPos u k (a + t * blkSize k) (bitAt (numOrder k) m t) := by
    intro t ht
    have hi : t * blkSize k < numOrder k * blkSize k :=
      Nat.mul_lt_mul_of_lt_of_le ht le_rfl (blkSize_pos k)
    have h1 := hpt (t * blkSize k) hi
    rw [ordStr_succ_getElem?_marker ht] at h1
    exact h1
  have hmark : ∀ p, a ≤ p → p ≤ b →
      (MkAt u k p ↔ ∃ t, t < numOrder k ∧ p = a + t * blkSize k) := by
    intro p hap hpb
    have hi : p - a < numOrder k * blkSize k := by omega
    constructor
    · rintro ⟨bb, hbb⟩
      have h1 := hpt (p - a) hi
      rw [show a + (p - a) = p by omega, hbb] at h1
      obtain ⟨t, ht, hteq, -⟩ :=
        (ordStr_succ_marker_iff hk m (p - a) bb (by rw [lenOrder_succ]; exact hi)).1 h1.symm
      exact ⟨t, ht, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, hbit t ht⟩
  refine ⟨hb1, hmark, fun t ht => ⟨hbit t ht, ?_, ?_⟩⟩
  · -- the content of the block
    have hstep : (t + 1) * blkSize k ≤ numOrder k * blkSize k := Nat.mul_le_mul_right _ ht
    have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
    have hS : blkSize k = lenOrder k + 1 := blkSize_eq k
    have hble : a + t * blkSize k + lenOrder k < u.length := by omega
    refine ⟨by omega, hble, ?_⟩
    rw [segI_eq_iff hble]
    refine ⟨by rw [ordStr_length]; omega, fun r hr => ?_⟩
    rw [ordStr_length] at hr
    have hi : t * blkSize k + (r + 1) < numOrder k * blkSize k := by omega
    have h1 := hpt (t * blkSize k + (r + 1)) hi
    rw [ordStr_succ_getElem?_inner ht hr] at h1
    rw [show a + t * blkSize k + 1 + r = a + (t * blkSize k + (r + 1)) by omega]
    exact h1
  · -- the block end
    have hstep : (t + 1) * blkSize k ≤ numOrder k * blkSize k := Nat.mul_le_mul_right _ ht
    have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
    have hS : blkSize k = lenOrder k + 1 := blkSize_eq k
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro r hr1 hr2 hmk
      obtain ⟨t', ht', hteq⟩ := (hmark r (by omega) (by omega)).1 hmk
      have h1 : t * blkSize k < t' * blkSize k := by omega
      have h2 : t' * blkSize k < (t + 1) * blkSize k := by omega
      have h3 : t < t' := by
        by_contra hcon
        exact absurd (Nat.mul_le_mul_right (blkSize k) (Nat.le_of_not_lt hcon)) (by omega)
      have h4 : t' < t + 1 := by
        by_contra hcon
        exact absurd (Nat.mul_le_mul_right (blkSize k) (Nat.le_of_not_lt hcon)) (by omega)
      omega
    · rcases Nat.lt_or_ge (t + 1) (numOrder k) with hlt | hge
      · right
        have := hbit (t + 1) hlt
        rw [hexp] at this
        exact ⟨_, by rw [show a + t * blkSize k + lenOrder k + 1 = a + (t * blkSize k + blkSize k)
          by omega]; exact this⟩
      · left
        have : t + 1 = numOrder k := by omega
        have h5 : (t + 1) * blkSize k = numOrder k * blkSize k := by rw [this]
        omega

/-! ## From the blocks to a string of order `k+1` -/

/-- The bit carried by the letter at the position `p`. -/
def bitOfPos (u : List (Lett N)) (p : ℕ) : Bool := (u[p]?.map Prod.snd).getD false

lemma bitOfPos_eq {u : List (Lett N)} {k p : ℕ} {b : Bool} (h : BitPos u k p b) :
    bitOfPos u p = b := by
  simp [bitOfPos, show u[p]? = some (lv N (k + 1), b) from h]

/-- If the blocks of the infix `[a, b]` are the strings of order `k` in order, then the infix is
a string of order `k+1`. -/
lemma isOrdAt_succ_of_blocks {k : ℕ} {u : List (Lett N)} {a b : ℕ} (hbl : b < u.length)
    (hb1 : b + 1 = a + numOrder k * blkSize k)
    (hall : ∀ t, t < numOrder k → MkAt u k (a + t * blkSize k) ∧
      IsOrdAt u k t (a + t * blkSize k + 1) (a + t * blkSize k + lenOrder k)) :
    ∃ m, m < numOrder (k + 1) ∧ IsOrdAt u (k + 1) m a b := by
  refine ⟨natOfBitAt (numOrder k) (fun t => bitOfPos u (a + t * blkSize k)),
    natOfBitAt_lt _ _, by omega, hbl, ?_⟩
  rw [segI_eq_iff hbl]
  have hlength : (ordStr N (k + 1)
      (natOfBitAt (numOrder k) (fun t => bitOfPos u (a + t * blkSize k)))).length
      = numOrder k * blkSize k := by rw [ordStr_length, lenOrder_succ]
  rw [hlength]
  refine ⟨by omega, fun i hi => ?_⟩
  obtain ⟨t, r, hrS, hir⟩ : ∃ t r, r < blkSize k ∧ i = t * blkSize k + r :=
    ⟨i / blkSize k, i % blkSize k, Nat.mod_lt _ (blkSize_pos k),
      by rw [Nat.mul_comm]; exact (Nat.div_add_mod i (blkSize k)).symm⟩
  have htl : t < numOrder k := by
    by_contra hcon
    push_neg at hcon
    have hle : numOrder k * blkSize k ≤ t * blkSize k := Nat.mul_le_mul_right _ hcon
    omega
  have hSL : blkSize k = lenOrder k + 1 := blkSize_eq k
  obtain ⟨hmkt, hcontt⟩ := hall t htl
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · obtain ⟨bb, hbb⟩ := hmkt
    rw [show i = t * blkSize k by omega, ordStr_succ_getElem?_marker htl,
      bitAt_natOfBitAt _ htl, bitOfPos_eq (k := k) hbb]
    exact hbb
  · have hrL : r - 1 < lenOrder k := by omega
    have hcl := hcontt.2.2
    rw [segI_eq_iff hcontt.2.1] at hcl
    obtain ⟨-, hcpt⟩ := hcl
    have hval := hcpt (r - 1) (by rw [ordStr_length]; omega)
    rw [hir, show r = (r - 1) + 1 by omega, ordStr_succ_getElem?_inner htl hrL,
      show a + (t * blkSize k + (r - 1 + 1)) = a + t * blkSize k + 1 + (r - 1) by omega]
    exact hval

/-- **The blocks determine the string of order `k+1`.**  If the infix `[a, b]` starts with a
marker of level `k+1`, if the first block is the first string of order `k`, if consecutive
blocks are consecutive strings of order `k`, and if the last block is the last string of order
`k` (in the weak form: the index of a block that ends at the end of the infix is the last one),
then the infix is a string of order `k+1`. -/
theorem isOrdAt_succ_bwd {k : ℕ} {u : List (Lett N)} {a b : ℕ}
    (hab : a ≤ b) (hbl : b < u.length) (hmk : MkAt u k a)
    (hfirst : ∀ q, IsBE u k a q b → IsOrdAt u k 0 (a + 1) q)
    (hlast : ∀ p q t, a ≤ p → p ≤ b → MkAt u k p → IsBE u k p q b → q = b →
      t < numOrder k → IsOrdAt u k t (p + 1) q → t = numOrder k - 1)
    (hsucc : ∀ p q q', a ≤ p → p ≤ b → MkAt u k p → IsBE u k p q b → q < b →
      IsBE u k (q + 1) q' b →
      ∃ t, t + 1 < numOrder k ∧ IsOrdAt u k t (p + 1) q ∧ IsOrdAt u k (t + 1) (q + 2) q') :
    ∃ m, m < numOrder (k + 1) ∧ IsOrdAt u (k + 1) m a b := by
  set S := blkSize k with hS
  set L := lenOrder k with hL
  set l := numOrder k with hl
  have hSL : S = L + 1 := blkSize_eq k
  have hlpos : 0 < l := numOrder_pos k
  -- the chain of blocks, by downward induction on the index
  have key : ∀ d t, l - 1 - t = d → t < l → MkAt u k (a + t * S) →
      IsOrdAt u k t (a + t * S + 1) (a + t * S + L) → IsBE u k (a + t * S) (a + t * S + L) b →
      b + 1 = a + l * S ∧ ∀ t', t ≤ t' → t' < l →
        (MkAt u k (a + t' * S) ∧ IsOrdAt u k t' (a + t' * S + 1) (a + t' * S + L)) := by
    intro d
    induction d with
    | zero =>
        intro t hd htl hmkt hcont hbe
        -- `t` is the last index
        have htlast : t = l - 1 := by omega
        have hq : a + t * S + L = b := by
          by_contra hne
          have hqlt : a + t * S + L < b := lt_of_le_of_ne hbe.2.1 hne
          exfalso
          obtain ⟨q', hq'⟩ := exists_isBE u k (a + t * S + L + 1) b (by omega)
          obtain ⟨t0, ht0, hc0, hc1⟩ :=
            hsucc (a + t * S) (a + t * S + L) q' (by omega) (by omega) hmkt hbe hqlt hq'
          have : t0 = t := isOrdAt_unique (by omega) htl hc0 hcont
          omega
        refine ⟨?_, ?_⟩
        · have hmul : (t + 1) * S = l * S := by rw [show t + 1 = l by omega]
          have hexp : (t + 1) * S = t * S + S := by ring
          omega
        · intro t' ht' ht'l
          have : t' = t := by omega
          subst this
          exact ⟨hmkt, hcont⟩
    | succ d ih =>
        intro t hd htl hmkt hcont hbe
        have hqlt : a + t * S + L < b := by
          rcases Nat.lt_or_ge (a + t * S + L) b with h | h
          · exact h
          · exfalso
            have hq : a + t * S + L = b := le_antisymm hbe.2.1 h
            have := hlast (a + t * S) (a + t * S + L) t (by omega) (by omega) hmkt hbe hq
              htl hcont
            omega
        obtain ⟨q', hq'⟩ := exists_isBE u k (a + t * S + L + 1) b (by omega)
        obtain ⟨t0, ht0, hc0, hc1⟩ :=
          hsucc (a + t * S) (a + t * S + L) q' (by omega) (by omega) hmkt hbe hqlt hq'
        have ht0t : t0 = t := isOrdAt_unique (by omega) htl hc0 hcont
        subst ht0t
        have hnext : a + t0 * S + L + 1 = a + (t0 + 1) * S := by
          have : (t0 + 1) * S = t0 * S + S := by ring
          omega
        have hq'val : q' = a + (t0 + 1) * S + L := by
          have := isOrdAt_length hc1
          have h2 : a + t0 * S + L + 2 = a + (t0 + 1) * S + 1 := by omega
          omega
        have hmknext : MkAt u k (a + (t0 + 1) * S) := by
          rcases hbe.2.2.2 with hqb | hmk'
          · omega
          · rwa [hnext] at hmk'
        have hcontnext : IsOrdAt u k (t0 + 1) (a + (t0 + 1) * S + 1) (a + (t0 + 1) * S + L) := by
          rw [← hq'val, show a + (t0 + 1) * S + 1 = a + t0 * S + L + 2 by omega]
          exact hc1
        have hbenext : IsBE u k (a + (t0 + 1) * S) (a + (t0 + 1) * S + L) b := by
          rw [← hq'val, ← hnext]; exact hq'
        obtain ⟨hb1, hall⟩ := ih (t0 + 1) (by omega) (by omega) hmknext hcontnext hbenext
        refine ⟨hb1, fun t' ht' ht'l => ?_⟩
        rcases Nat.eq_or_lt_of_le ht' with rfl | hlt
        · exact ⟨hmkt, hcont⟩
        · exact hall t' (by omega) ht'l
  -- the data of the first block
  obtain ⟨q0, hq0⟩ := exists_isBE u k a b hab
  have hc0 := hfirst q0 hq0
  have hq0val : q0 = a + L := by have := isOrdAt_length hc0; omega
  subst hq0val
  obtain ⟨hb1, hall⟩ := key (l - 1) 0 (by omega) hlpos (by simpa using hmk)
    (by simpa using hc0) (by simpa using hq0)
  -- the string of order `k+1`
  exact isOrdAt_succ_of_blocks hbl hb1 (fun t ht => hall t (Nat.zero_le _) ht)

/-! ## The first and the last string of order `k` -/

/-- No position of the infix `[a, b]` carries the letter of level `k` with the bit `c`. -/
def NoBitAt (u : List (Lett N)) (k : ℕ) (c : Bool) (a b : ℕ) : Prop :=
  ∀ p, a ≤ p → p ≤ b → u[p]? ≠ some (lv N k, c)

lemma noBitAt_of_empty {u : List (Lett N)} {k : ℕ} {c : Bool} {a b : ℕ} (h : a = b + 1) :
    NoBitAt u k c a b := fun p h1 h2 => absurd h1 (by omega)

lemma isOrdAt_succ_noBitAt_iff {j : ℕ} (hj : j + 1 ≤ N) {u : List (Lett N)} {m a b : ℕ}
    (h : IsOrdAt u (j + 1) m a b) (c : Bool) :
    NoBitAt u (j + 1) c a b ↔ ∀ t, t < numOrder j → bitAt (numOrder j) m t = !c := by
  obtain ⟨hab, hbl, hseg⟩ := h
  have hlength : (ordStr N (j + 1) m).length = lenOrder (j + 1) := ordStr_length N (j + 1) m
  rw [segI_eq_iff hbl] at hseg
  obtain ⟨hlen, hpt⟩ := hseg
  rw [hlength] at hlen hpt
  constructor
  · intro hno t ht
    by_contra hcon
    have hct : bitAt (numOrder j) m t = c := by
      cases c <;> cases hb : bitAt (numOrder j) m t <;> simp_all
    have hi : t * blkSize j < lenOrder (j + 1) := by
      rw [lenOrder_succ]
      exact Nat.mul_lt_mul_of_lt_of_le ht le_rfl (blkSize_pos j)
    have h1 := hpt (t * blkSize j) hi
    rw [ordStr_succ_getElem?_marker ht, hct] at h1
    exact hno (a + t * blkSize j) (by omega) (by omega) h1
  · intro hbits p hap hpb hc
    have hi : p - a < lenOrder (j + 1) := by omega
    have h1 := hpt (p - a) hi
    rw [show a + (p - a) = p by omega, hc] at h1
    obtain ⟨t, ht, hteq, hbeq⟩ :=
      (ordStr_succ_marker_iff hj m (p - a) c hi).1 h1.symm
    rw [hbits t ht] at hbeq
    cases c <;> simp at hbeq

/-- Among the strings of order `k`, the first one is the one with no marker bit `1`. -/
lemma isOrdAt_first_iff {k : ℕ} (hk : k ≤ N) {u : List (Lett N)} {m a b : ℕ}
    (hm : m < numOrder k) (h : IsOrdAt u k m a b) :
    m = 0 ↔ NoBitAt u k true a b := by
  cases k with
  | zero =>
      have : numOrder 0 = 1 := rfl
      have hz := isOrdAt_zero_iff.1 h
      simp only [iff_iff_implies_and_implies]
      exact ⟨fun _ => noBitAt_of_empty hz.1, fun _ => by omega⟩
  | succ j =>
      rw [isOrdAt_succ_noBitAt_iff hk h true, eq_zero_iff_bitAt hm]
      simp

/-- Among the strings of order `k`, the last one is the one with no marker bit `0`. -/
lemma isOrdAt_last_iff {k : ℕ} (hk : k ≤ N) {u : List (Lett N)} {m a b : ℕ}
    (hm : m < numOrder k) (h : IsOrdAt u k m a b) :
    m = numOrder k - 1 ↔ NoBitAt u k false a b := by
  cases k with
  | zero =>
      have hz := isOrdAt_zero_iff.1 h
      simp only [iff_iff_implies_and_implies]
      exact ⟨fun _ => noBitAt_of_empty hz.1, fun _ => by
        have : numOrder 0 = 1 := rfl
        omega⟩
  | succ j =>
      rw [isOrdAt_succ_noBitAt_iff hk h false, show numOrder (j + 1) = 2 ^ numOrder j from rfl,
        eq_last_iff_bitAt hm]
      simp

end Transducers.Exercises
