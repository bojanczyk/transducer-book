/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

The combinatorial content of the induction step of the Claim in the solution of
that exercise, stated in the exact form in which the first-order formula of
`RequestProject/Exercises/FONonElemForm.lean` expresses it: an infix of a string
is a string of order `k+1`, and two such infixes carry the same index or
consecutive indices, exactly if their blocks satisfy a list of conditions each
of which speaks about strings of order `k` only.
-/
import RequestProject.Exercises.FONonElemParse

namespace Transducers.Exercises

variable {N : ℕ}

/-! ## The relations defined by the formulas -/

/-- The two infixes `(z₁, z₂]` and `(z₃, z₄]` are strings of order `k` with the same index. -/
def EqBlk (u : List (Lett N)) (k z1 z2 z3 z4 : ℕ) : Prop :=
  ∃ m, m < numOrder k ∧ IsOrdAt u k m (z1 + 1) z2 ∧ IsOrdAt u k m (z3 + 1) z4

/-- The two infixes `(z₁, z₂]` and `(z₃, z₄]` are strings of order `k` with consecutive
indices. -/
def SuccBlk (u : List (Lett N)) (k z1 z2 z3 z4 : ℕ) : Prop :=
  ∃ m, m + 1 < numOrder k ∧ IsOrdAt u k m (z1 + 1) z2 ∧ IsOrdAt u k (m + 1) (z3 + 1) z4

/-- The relation defined by the formula of order `k`: the equality of indices if the mode `e`
holds, the successor relation otherwise. -/
def Mean (u : List (Lett N)) (k z1 z2 z3 z4 : ℕ) (e : Prop) : Prop :=
  (e ∧ EqBlk u k z1 z2 z3 z4) ∨ (¬ e ∧ SuccBlk u k z1 z2 z3 z4)

/-- `p` is a position of the infix `(A, B]` carrying a marker of level `k+1`. -/
def MkIn (u : List (Lett N)) (k A B p : ℕ) : Prop := A < p ∧ p ≤ B ∧ MkAt u k p

/-- The part of the block structure of the infix `(A, B]` that does not mention the strings of
order `k`: the infix is nonempty and starts with a marker of level `k+1`, the first block
carries no marker bit `1`, and a block that ends at the end of the infix carries no marker
bit `0`. -/
def BCheap (u : List (Lett N)) (k A B : ℕ) : Prop :=
  A < B ∧ B < u.length ∧ MkAt u k (A + 1) ∧
  (∀ q, IsBE u k (A + 1) q B → NoBitAt u k true (A + 2) q) ∧
  (∀ p q, MkIn u k A B p → IsBE u k p q B → q = B → NoBitAt u k false (p + 1) q)

/-- The part of the block structure of the infix `(A, B]` that mentions the strings of order
`k`: the first block is one, and consecutive blocks are consecutive ones. -/
def BDeep (u : List (Lett N)) (k A B : ℕ) : Prop :=
  (∀ q, IsBE u k (A + 1) q B → EqBlk u k (A + 1) q (A + 1) q) ∧
  (∀ p q q', MkIn u k A B p → IsBE u k p q B → q < B → IsBE u k (q + 1) q' B →
      SuccBlk u k p q (q + 1) q')

/-- The infix `(A, B]` has the block structure of a string of order `k+1`. -/
def BlkStruct (u : List (Lett N)) (k A B : ℕ) : Prop := BCheap u k A B ∧ BDeep u k A B

/-- The marker `p` of the infix `(A, B]` and the marker `p'` of the infix `(C, D]` start blocks
that carry the same string of order `k`. -/
def BlkMatch (u : List (Lett N)) (k B C D p p' : ℕ) : Prop :=
  MkIn u k C D p' ∧ ∃ q q', IsBE u k p q B ∧ IsBE u k p' q' D ∧ EqBlk u k p q p' q'

/-- Corresponding markers of the two infixes carry the same bit. -/
def EqCorr (u : List (Lett N)) (k A B C D : ℕ) : Prop :=
  ∀ p, MkIn u k A B p → ∃ p', BlkMatch u k B C D p p' ∧ bitOfPos u p = bitOfPos u p'

/-- The bits of the second infix are those of the first one plus one, in binary. -/
def SuccCorr (u : List (Lett N)) (k A B C D : ℕ) : Prop :=
  ∃ p0, MkIn u k A B p0 ∧ bitOfPos u p0 = false ∧
    ∀ p, MkIn u k A B p → ∃ p', BlkMatch u k B C D p p' ∧
      (p < p0 → bitOfPos u p = bitOfPos u p') ∧
      (p = p0 → bitOfPos u p' = true) ∧
      (p0 < p → bitOfPos u p = true ∧ bitOfPos u p' = false)

/-! ## The block structure of an infix of order `k+1` -/

/-- The data attached to an infix that is a string of order `k+1`, in the form used below. -/
theorem ordAt_succ_data {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {m A B : ℕ}
    (h : IsOrdAt u (k + 1) m (A + 1) B) :
    B = A + numOrder k * blkSize k ∧
    (∀ p, MkIn u k A B p ↔ ∃ t, t < numOrder k ∧ p = A + 1 + t * blkSize k) ∧
    (∀ t, t < numOrder k →
      bitOfPos u (A + 1 + t * blkSize k) = bitAt (numOrder k) m t ∧
      IsOrdAt u k t (A + 1 + t * blkSize k + 1) (A + 1 + t * blkSize k + lenOrder k) ∧
      IsBE u k (A + 1 + t * blkSize k) (A + 1 + t * blkSize k + lenOrder k) B) := by
  obtain ⟨hb1, hmark, hblk⟩ := isOrdAt_succ_fwd hk h
  refine ⟨by omega, fun p => ?_, fun t ht => ?_⟩
  · constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨t, ht, hteq⟩ := (hmark p (by omega) h2).1 h3
      exact ⟨t, ht, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      have hle : (t + 1) * blkSize k ≤ numOrder k * blkSize k := Nat.mul_le_mul_right _ ht
      have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
      have hS : 0 < blkSize k := blkSize_pos k
      refine ⟨by omega, by omega, ?_⟩
      exact ((hmark (A + 1 + t * blkSize k) (by omega) (by omega)).2 ⟨t, ht, by omega⟩)
  · obtain ⟨hbit, hcont, hbe⟩ := hblk t ht
    exact ⟨bitOfPos_eq hbit, hcont, hbe⟩

/-- The block structure characterises the infixes that are strings of order `k+1`. -/
theorem blkStruct_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {A B : ℕ} :
    BlkStruct u k A B ↔ ∃ m, m < numOrder (k + 1) ∧ IsOrdAt u (k + 1) m (A + 1) B := by
  constructor
  · rintro ⟨⟨hAB, hBl, hmk, hno1, hno0⟩, hfirstb, hsuccb⟩
    refine isOrdAt_succ_bwd (by omega) hBl hmk ?_ ?_ ?_
    · intro q hq
      obtain ⟨m, hm, hc, -⟩ := hfirstb q hq
      have h0 : m = 0 := (isOrdAt_first_iff (by omega) hm hc).2 (hno1 q hq)
      exact h0 ▸ hc
    · intro p q t h1 h2 h3 h4 h5 h6 h7
      exact (isOrdAt_last_iff (k := k) (by omega) h6 h7).2 (hno0 p q ⟨by omega, h2, h3⟩ h4 h5)
    · intro p q q' h1 h2 h3 h4 h5 h6
      obtain ⟨m, hm, hc1, hc2⟩ := hsuccb p q q' ⟨by omega, h2, h3⟩ h4 h5 h6
      exact ⟨m, hm, hc1, by simpa [show q + 1 + 1 = q + 2 from rfl] using hc2⟩
  · rintro ⟨m, hm, h⟩
    obtain ⟨hB, hmark, hblk⟩ := ordAt_succ_data hk h
    have hS : 0 < blkSize k := blkSize_pos k
    have hSL : blkSize k = lenOrder k + 1 := blkSize_eq k
    have hl : 0 < numOrder k := numOrder_pos k
    have hlS : numOrder k * blkSize k ≥ blkSize k := Nat.le_mul_of_pos_left _ hl
    have hBl : B < u.length := h.2.1
    have hmk0 : MkAt u k (A + 1) := by
      have := (hmark (A + 1)).2 ⟨0, hl, by omega⟩
      exact this.2.2
    -- the first block
    have hbe0 : IsBE u k (A + 1) (A + 1 + lenOrder k) B := by
      have := (hblk 0 hl).2.2; simpa using this
    have hcont0 : IsOrdAt u k 0 (A + 1 + 1) (A + 1 + lenOrder k) := by
      have := (hblk 0 hl).2.1; simpa using this
    refine ⟨⟨by omega, hBl, hmk0, ?_, ?_⟩, ?_, ?_⟩
    · intro q hq
      have : q = A + 1 + lenOrder k := isBE_unique hq hbe0
      subst this
      exact (isOrdAt_first_iff (k := k) (by omega) hl hcont0).1 rfl
    · rintro p q hp hbe hqB
      obtain ⟨t, ht, rfl⟩ := (hmark p).1 hp
      obtain ⟨hbit, hcont, hbe'⟩ := hblk t ht
      have hq : q = A + 1 + t * blkSize k + lenOrder k := isBE_unique hbe hbe'
      subst hq
      have htl : t = numOrder k - 1 := by
        have h1 : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
        have h2 : (t + 1) * blkSize k ≤ numOrder k * blkSize k := Nat.mul_le_mul_right _ ht
        have h3 : ¬ ((t + 2) * blkSize k ≤ numOrder k * blkSize k) := by
          intro hc
          have : (t + 2) * blkSize k = t * blkSize k + blkSize k + blkSize k := by ring
          omega
        have h4 : ¬ (t + 2 ≤ numOrder k) := fun hc => h3 (Nat.mul_le_mul_right _ hc)
        omega
      exact (isOrdAt_last_iff (k := k) (by omega) ht hcont).1 htl
    · intro q hq
      have : q = A + 1 + lenOrder k := isBE_unique hq hbe0
      subst this
      exact ⟨0, hl, hcont0, hcont0⟩
    · rintro p q q' hp hbe hqB hbe'
      obtain ⟨t, ht, rfl⟩ := (hmark p).1 hp
      obtain ⟨hbit, hcont, hbeq⟩ := hblk t ht
      have hq : q = A + 1 + t * blkSize k + lenOrder k := isBE_unique hbe hbeq
      subst hq
      have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
      have ht1 : t + 1 < numOrder k := by
        by_contra hc
        have : numOrder k ≤ t + 1 := by omega
        have := Nat.mul_le_mul_right (blkSize k) this
        omega
      obtain ⟨hbit1, hcont1, hbeq1⟩ := hblk (t + 1) ht1
      have hq' : q' = A + 1 + (t + 1) * blkSize k + lenOrder k := by
        refine isBE_unique hbe' ?_
        have : A + 1 + t * blkSize k + lenOrder k + 1 = A + 1 + (t + 1) * blkSize k := by omega
        rw [this]; exact hbeq1
      subst hq'
      refine ⟨t, ht1, hcont, ?_⟩
      have he : A + 1 + t * blkSize k + lenOrder k + 1 + 1 = A + 1 + (t + 1) * blkSize k + 1 := by
        omega
      rw [he]
      exact hcont1

/-- The block of a marker determines the index it carries, hence the matching marker in another
infix of order `k+1`. -/
theorem blkMatch_index {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {mX mY A B C D : ℕ}
    (hoX : IsOrdAt u (k + 1) mX (A + 1) B) (hoY : IsOrdAt u (k + 1) mY (C + 1) D)
    {t p' : ℕ} (ht : t < numOrder k)
    (h : BlkMatch u k B C D (A + 1 + t * blkSize k) p') :
    p' = C + 1 + t * blkSize k := by
  obtain ⟨-, hmarkX, hblkX⟩ := ordAt_succ_data hk hoX
  obtain ⟨-, hmarkY, hblkY⟩ := ordAt_succ_data hk hoY
  obtain ⟨hp', q, q', hbe1, hbe2, m, hm, hc1, hc2⟩ := h
  obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
  obtain ⟨t', ht', rfl⟩ := (hmarkY p').1 hp'
  obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t' ht'
  have hq : q = A + 1 + t * blkSize k + lenOrder k := isBE_unique hbe1 hbeX
  have hq' : q' = C + 1 + t' * blkSize k + lenOrder k := isBE_unique hbe2 hbeY
  subst hq; subst hq'
  have e1 : m = t := isOrdAt_unique hm ht hc1 hcontX
  have e2 : m = t' := isOrdAt_unique hm ht' hc2 hcontY
  have htt : t' = t := by omega
  rw [htt]

/-- A marker of the first infix has at most one matching marker in the second one. -/
theorem blkMatch_eq {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {A B C D : ℕ}
    (hX : BlkStruct u k A B) (hY : BlkStruct u k C D) {p p1 p2 : ℕ}
    (hp : MkIn u k A B p) (h1 : BlkMatch u k B C D p p1) (h2 : BlkMatch u k B C D p p2) :
    p1 = p2 := by
  obtain ⟨mX, hmX, hoX⟩ := (blkStruct_iff hk).1 hX
  obtain ⟨mY, hmY, hoY⟩ := (blkStruct_iff hk).1 hY
  obtain ⟨-, hmarkX, -⟩ := ordAt_succ_data hk hoX
  obtain ⟨t, ht, rfl⟩ := (hmarkX p).1 hp
  rw [blkMatch_index hk hoX hoY ht h1, blkMatch_index hk hoX hoY ht h2]

/-! ## The two infixes -/

theorem eqBlk_succ_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {A B C D : ℕ}
    (hX : BlkStruct u k A B) (hY : BlkStruct u k C D) :
    EqBlk u (k + 1) A B C D ↔ EqCorr u k A B C D := by
  obtain ⟨mX, hmX, hoX⟩ := (blkStruct_iff hk).1 hX
  obtain ⟨mY, hmY, hoY⟩ := (blkStruct_iff hk).1 hY
  obtain ⟨hBX, hmarkX, hblkX⟩ := ordAt_succ_data hk hoX
  obtain ⟨hBY, hmarkY, hblkY⟩ := ordAt_succ_data hk hoY
  have hS : 0 < blkSize k := blkSize_pos k
  constructor
  · rintro ⟨m, hm, h1, h2⟩
    have e1 : m = mX := isOrdAt_unique hm hmX h1 hoX
    have e2 : m = mY := isOrdAt_unique hm hmY h2 hoY
    intro p hp
    obtain ⟨t, ht, rfl⟩ := (hmarkX p).1 hp
    obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
    obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t ht
    refine ⟨C + 1 + t * blkSize k, ⟨(hmarkY _).2 ⟨t, ht, rfl⟩, _, _, hbeX, hbeY, ?_⟩, ?_⟩
    · exact ⟨t, ht, hcontX, hcontY⟩
    · rw [hbitX, hbitY, ← e1, ← e2]
  · intro hcorr
    have hbits : ∀ t, t < numOrder k → bitAt (numOrder k) mX t = bitAt (numOrder k) mY t := by
      intro t ht
      obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
      obtain ⟨p', ⟨hp', q, q', hbe1, hbe2, m, hm, hc1, hc2⟩, hbit⟩ :=
        hcorr (A + 1 + t * blkSize k) ((hmarkX _).2 ⟨t, ht, rfl⟩)
      obtain ⟨t', ht', rfl⟩ := (hmarkY p').1 hp'
      obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t' ht'
      have hq : q = A + 1 + t * blkSize k + lenOrder k := isBE_unique hbe1 hbeX
      have hq' : q' = C + 1 + t' * blkSize k + lenOrder k := isBE_unique hbe2 hbeY
      subst hq; subst hq'
      have e1 : m = t := isOrdAt_unique hm ht hc1 hcontX
      have e2 : m = t' := isOrdAt_unique hm ht' hc2 hcontY
      have htt : t' = t := by omega
      subst htt
      rw [← hbitX, ← hbitY]
      exact hbit
    have : mX = mY := by
      refine eq_of_bitAt (l := numOrder k) ?_ ?_ hbits
      · simpa [numOrder] using hmX
      · simpa [numOrder] using hmY
    exact ⟨mX, hmX, hoX, this ▸ hoY⟩

theorem succBlk_succ_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {A B C D : ℕ}
    (hX : BlkStruct u k A B) (hY : BlkStruct u k C D) :
    SuccBlk u (k + 1) A B C D ↔ SuccCorr u k A B C D := by
  obtain ⟨mX, hmX, hoX⟩ := (blkStruct_iff hk).1 hX
  obtain ⟨mY, hmY, hoY⟩ := (blkStruct_iff hk).1 hY
  obtain ⟨hBX, hmarkX, hblkX⟩ := ordAt_succ_data hk hoX
  obtain ⟨hBY, hmarkY, hblkY⟩ := ordAt_succ_data hk hoY
  have hS : 0 < blkSize k := blkSize_pos k
  have hpowX : mX < 2 ^ numOrder k := by simpa [numOrder] using hmX
  have hpowY : mY < 2 ^ numOrder k := by simpa [numOrder] using hmY
  -- the matching of markers is determined
  have hmatch : ∀ p p', BlkMatch u k B C D p p' → ∀ t, t < numOrder k →
      p = A + 1 + t * blkSize k → p' = C + 1 + t * blkSize k := by
    rintro p p' ⟨hp', q, q', hbe1, hbe2, m, hm, hc1, hc2⟩ t ht rfl
    obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
    obtain ⟨t', ht', rfl⟩ := (hmarkY p').1 hp'
    obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t' ht'
    have hq : q = A + 1 + t * blkSize k + lenOrder k := isBE_unique hbe1 hbeX
    have hq' : q' = C + 1 + t' * blkSize k + lenOrder k := isBE_unique hbe2 hbeY
    subst hq; subst hq'
    have e1 : m = t := isOrdAt_unique hm ht hc1 hcontX
    have e2 : m = t' := isOrdAt_unique hm ht' hc2 hcontY
    have htt : t' = t := by omega
    rw [htt]
  constructor
  · rintro ⟨m, hm, h1, h2⟩
    have e1 : m = mX := isOrdAt_unique (by omega) hmX h1 hoX
    have e2 : m + 1 = mY := isOrdAt_unique hm hmY h2 hoY
    have e3 : mX + 1 = mY := by omega
    obtain ⟨t0, ht0, hb1, hb2, hb3, hb4⟩ :=
      bitAt_of_succ (l := numOrder k) (x := mX) (by rw [e3]; exact hpowY)
    obtain ⟨hbitX0, -, -⟩ := hblkX t0 ht0
    refine ⟨A + 1 + t0 * blkSize k, (hmarkX _).2 ⟨t0, ht0, rfl⟩, by rw [hbitX0, hb1], ?_⟩
    intro p hp
    obtain ⟨t, ht, rfl⟩ := (hmarkX p).1 hp
    obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
    obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t ht
    have hmul : ∀ s s' : ℕ, s < s' → s * blkSize k < s' * blkSize k := by
      intro s s' hss
      exact Nat.mul_lt_mul_of_lt_of_le hss le_rfl hS
    refine ⟨C + 1 + t * blkSize k, ⟨(hmarkY _).2 ⟨t, ht, rfl⟩, _, _, hbeX, hbeY,
      ⟨t, ht, hcontX, hcontY⟩⟩, ?_, ?_, ?_⟩
    · intro hlt
      have htt : t < t0 := by
        by_contra hc
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hc) with h | h
        · subst h; omega
        · have := hmul t0 t h; omega
      rw [hbitX, hbitY, hb3 t htt, e3]
    · intro heq
      have htt : t = t0 := by
        by_contra hc
        rcases Nat.lt_or_ge t t0 with h | h
        · have := hmul t t0 h; omega
        · have := hmul t0 t (by omega); omega
      subst htt
      rw [hbitY, ← e3, hb2]
    · intro hlt
      have htt : t0 < t := by
        by_contra hc
        rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hc) with h | h
        · subst h; omega
        · have := hmul t t0 h; omega
      obtain ⟨hg1, hg2⟩ := hb4 t htt ht
      rw [hbitX, hbitY, hg1, ← e3, hg2]
      exact ⟨rfl, rfl⟩
  · rintro ⟨p0, hp0, hbit0, hall⟩
    obtain ⟨t0, ht0, rfl⟩ := (hmarkX p0).1 hp0
    obtain ⟨hbitX0, -, -⟩ := hblkX t0 ht0
    have hmul : ∀ s s' : ℕ, s < s' → s * blkSize k < s' * blkSize k := by
      intro s s' hss
      exact Nat.mul_lt_mul_of_lt_of_le hss le_rfl hS
    have key : ∀ t, t < numOrder k →
        (t < t0 → bitAt (numOrder k) mX t = bitAt (numOrder k) mY t) ∧
        (t = t0 → bitAt (numOrder k) mY t = true) ∧
        (t0 < t → bitAt (numOrder k) mX t = true ∧ bitAt (numOrder k) mY t = false) := by
      intro t ht
      obtain ⟨hbitX, hcontX, hbeX⟩ := hblkX t ht
      obtain ⟨hbitY, hcontY, hbeY⟩ := hblkY t ht
      obtain ⟨p', hmt, hlt, heq, hgt⟩ := hall (A + 1 + t * blkSize k) ((hmarkX _).2 ⟨t, ht, rfl⟩)
      have hp'eq : p' = C + 1 + t * blkSize k := hmatch _ _ hmt t ht rfl
      subst hp'eq
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [← hbitX, ← hbitY]; exact hlt (by have := hmul t t0 h; omega)
      · subst h; rw [← hbitY]; exact heq rfl
      · have := hgt (by have := hmul t0 t h; omega)
        rw [← hbitX, ← hbitY]; exact this
    have hb0 : bitAt (numOrder k) mX t0 = false := by rw [← hbitX0]; exact hbit0
    have hb1 : bitAt (numOrder k) mY t0 = true := (key t0 ht0).2.1 rfl
    have : mY = mX + 1 :=
      eq_succ_of_bitAt hpowX hpowY ht0 hb0 hb1
        (fun t hts => (key t (by omega)).1 hts)
        (fun t h1 h2 => (key t h2).2.2 h1)
    refine ⟨mX, ?_, hoX, this ▸ hoY⟩
    omega

/-- **The induction step of the Claim.** -/
theorem mean_succ_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {A B C D : ℕ} {e : Prop} :
    Mean u (k + 1) A B C D e ↔
      BlkStruct u k A B ∧ BlkStruct u k C D ∧
        ((e → EqCorr u k A B C D) ∧ (¬ e → SuccCorr u k A B C D)) := by
  rw [Mean]
  constructor
  · rintro (⟨he, hEq⟩ | ⟨he, hSc⟩)
    · obtain ⟨m, hm, h1, h2⟩ := id hEq
      have hX : BlkStruct u k A B := (blkStruct_iff hk).2 ⟨m, hm, h1⟩
      have hY : BlkStruct u k C D := (blkStruct_iff hk).2 ⟨m, hm, h2⟩
      exact ⟨hX, hY, fun _ => (eqBlk_succ_iff hk hX hY).1 hEq, fun hc => absurd he hc⟩
    · obtain ⟨m, hm, h1, h2⟩ := id hSc
      have hX : BlkStruct u k A B := (blkStruct_iff hk).2 ⟨m, by omega, h1⟩
      have hY : BlkStruct u k C D := (blkStruct_iff hk).2 ⟨m + 1, hm, h2⟩
      exact ⟨hX, hY, fun hc => absurd hc he, fun _ => (succBlk_succ_iff hk hX hY).1 hSc⟩
  · rintro ⟨hX, hY, h1, h2⟩
    by_cases he : e
    · exact Or.inl ⟨he, (eqBlk_succ_iff hk hX hY).2 (h1 he)⟩
    · exact Or.inr ⟨he, (succBlk_succ_iff hk hX hY).2 (h2 he)⟩

/-! ## The shape of the formula

The formula of order `k+1` is a conjunction of two cheap conditions on the block structure of
the two infixes, followed by a prefix `∃ p₀ ∀ p ∃ p'` of quantifiers over positions, a further
cheap condition, and a *single* copy of the formula of order `k` applied to universally
quantified arguments and guarded by a cheap condition.  The lemma `formSem_iff` below says that
what this expresses is exactly the relation of order `k+1`. -/

/-- Two positions carry markers of level `k+1` with the same bit. -/
def SameBit (u : List (Lett N)) (k p p' : ℕ) : Prop :=
  (BitPos u k p false ∧ BitPos u k p' false) ∨ (BitPos u k p true ∧ BitPos u k p' true)

lemma sameBit_iff {u : List (Lett N)} {k p p' : ℕ} (hp : MkAt u k p) (hp' : MkAt u k p') :
    SameBit u k p p' ↔ bitOfPos u p = bitOfPos u p' := by
  obtain ⟨b, hb⟩ := hp
  obtain ⟨b', hb'⟩ := hp'
  rw [bitOfPos_eq hb, bitOfPos_eq hb']
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      rw [bitPos_inj hb h1, bitPos_inj hb' h2]
  · rintro rfl
    cases b with
    | false => exact Or.inl ⟨hb, hb'⟩
    | true => exact Or.inr ⟨hb, hb'⟩

lemma bitPos_iff_bitOfPos {u : List (Lett N)} {k p : ℕ} {b : Bool} (hp : MkAt u k p) :
    BitPos u k p b ↔ bitOfPos u p = b := by
  obtain ⟨c, hc⟩ := hp
  rw [bitOfPos_eq hc]
  exact ⟨fun h => bitPos_inj hc h, fun h => h ▸ hc⟩

/-- The guard that selects the instances of the formula of order `k` describing the block
structure of the infix `(A, B]`. -/
def GuardB (u : List (Lett N)) (k A B z1 z2 z3 z4 : ℕ) (e : Prop) : Prop :=
  (e ∧ z1 = A + 1 ∧ z3 = A + 1 ∧ z2 = z4 ∧ IsBE u k (A + 1) z2 B) ∨
  (¬ e ∧ MkIn u k A B z1 ∧ IsBE u k z1 z2 B ∧ z2 < B ∧ z3 = z2 + 1 ∧ IsBE u k z3 z4 B)

/-- The guard that selects the instance of the formula of order `k` matching the block of the
marker `p` of the first infix with the block of the marker `p'` of the second one. -/
def GuardC (u : List (Lett N)) (k A B C D p p' z1 z2 z3 z4 : ℕ) (e : Prop) : Prop :=
  e ∧ MkIn u k A B p ∧ MkIn u k C D p' ∧ z1 = p ∧ z3 = p' ∧
    IsBE u k p z2 B ∧ IsBE u k p' z4 D

/-- The cheap condition on the quantified positions `p₀`, `p` and `p'`. -/
def MCheap (u : List (Lett N)) (k A B C D : ℕ) (o : Prop) (p0 p p' : ℕ) : Prop :=
  (o → MkIn u k A B p → MkIn u k C D p' ∧ SameBit u k p p') ∧
  (¬ o → MkIn u k A B p0 ∧ BitPos u k p0 false ∧
     (MkIn u k A B p → MkIn u k C D p' ∧
        (p < p0 → SameBit u k p p') ∧
        (p = p0 → BitPos u k p' true) ∧
        (p0 < p → BitPos u k p true ∧ BitPos u k p' false)))

/-- **What the formula of order `k+1` expresses.** -/
theorem formSem_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} (hu : 2 ≤ u.length)
    {A B C D : ℕ} {o : Prop} :
    (BCheap u k A B ∧ BCheap u k C D ∧
      ∃ p0 < u.length, ∀ p < u.length, ∃ p' < u.length,
        MCheap u k A B C D o p0 p p' ∧
        (∀ z1 < u.length, ∀ z2 < u.length, ∀ z3 < u.length, ∀ z4 < u.length,
          ∀ n1 < u.length, ∀ n2 < u.length,
          (GuardB u k A B z1 z2 z3 z4 (n1 ≤ n2) ∨ GuardB u k C D z1 z2 z3 z4 (n1 ≤ n2) ∨
            GuardC u k A B C D p p' z1 z2 z3 z4 (n1 ≤ n2)) →
          Mean u k z1 z2 z3 z4 (n1 ≤ n2)))
    ↔ Mean u (k + 1) A B C D o := by
  rw [mean_succ_iff hk]
  constructor
  · rintro ⟨hcX, hcY, p0, hp0l, hmain⟩
    obtain ⟨pz, hpzl, hmc0, hg0⟩ := hmain 0 (by omega)
    -- the deep part of the block structure of an infix, from the guards
    have hdeep : ∀ (E F : ℕ), BCheap u k E F →
        (∀ z1 z2 z3 z4 n1 n2, z1 < u.length → z2 < u.length → z3 < u.length →
          z4 < u.length → n1 < u.length → n2 < u.length →
          GuardB u k E F z1 z2 z3 z4 (n1 ≤ n2) → Mean u k z1 z2 z3 z4 (n1 ≤ n2)) →
        BDeep u k E F := by
      intro E F hc hg
      have hFl : F < u.length := hc.2.1
      constructor
      · intro q hq
        have h1 : E + 1 ≤ q := hq.1
        have h2 : q ≤ F := hq.2.1
        have := hg (E + 1) q (E + 1) q 0 0 (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (Or.inl ⟨le_rfl, rfl, rfl, rfl, hq⟩)
        rcases this with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd le_rfl h
      · intro p q q' hp hbe hqF hbe'
        have h1 : p ≤ F := hp.2.1
        have h2 : q ≤ F := hbe.2.1
        have h3 : q' ≤ F := hbe'.2.1
        have := hg p q (q + 1) q' 1 0 (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (Or.inr ⟨by omega, hp, hbe, hqF, rfl, hbe'⟩)
        rcases this with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by omega)
        · exact h
    have hX : BlkStruct u k A B :=
      ⟨hcX, hdeep A B hcX (fun z1 z2 z3 z4 n1 n2 h1 h2 h3 h4 h5 h6 hgg =>
        hg0 z1 h1 z2 h2 z3 h3 z4 h4 n1 h5 n2 h6 (Or.inl hgg))⟩
    have hY : BlkStruct u k C D :=
      ⟨hcY, hdeep C D hcY (fun z1 z2 z3 z4 n1 n2 h1 h2 h3 h4 h5 h6 hgg =>
        hg0 z1 h1 z2 h2 z3 h3 z4 h4 n1 h5 n2 h6 (Or.inr (Or.inl hgg)))⟩
    -- the matching of the markers
    have hmatch : ∀ p, MkIn u k A B p → ∃ p', MkIn u k C D p' ∧
        BlkMatch u k B C D p p' ∧
        ((o → SameBit u k p p') ∧
         (¬ o → (p < p0 → SameBit u k p p') ∧ (p = p0 → BitPos u k p' true) ∧
                (p0 < p → BitPos u k p true ∧ BitPos u k p' false))) := by
      intro p hp
      have hpB : p ≤ B := hp.2.1
      have hpl : p < u.length := by have := hcX.2.1; omega
      obtain ⟨p', hp'l, hmc, hg⟩ := hmain p hpl
      have hp'in : MkIn u k C D p' := by
        by_cases ho : o
        · exact (hmc.1 ho hp).1
        · exact ((hmc.2 ho).2.2 hp).1
      obtain ⟨q, hq⟩ := exists_isBE u k p B hp.2.1
      obtain ⟨q', hq'⟩ := exists_isBE u k p' D hp'in.2.1
      have hDl : D < u.length := hcY.2.1
      have hBl : B < u.length := hcX.2.1
      have hqB : q ≤ B := hq.2.1
      have hp'D : p' ≤ D := hp'in.2.1
      have hq'D : q' ≤ D := hq'.2.1
      have := hg p (by omega) q (by omega) p' (by omega) q' (by omega) 0 (by omega) 0 (by omega)
        (Or.inr (Or.inr ⟨le_rfl, hp, hp'in, rfl, rfl, hq, hq'⟩))
      have heq : EqBlk u k p q p' q' := by
        rcases this with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd le_rfl h
      refine ⟨p', hp'in, ⟨hp'in, q, q', hq, hq', heq⟩, fun ho => (hmc.1 ho hp).2, fun ho => ?_⟩
      exact ((hmc.2 ho).2.2 hp).2
    refine ⟨hX, hY, fun ho p hp => ?_, fun ho => ?_⟩
    · obtain ⟨p', hp'in, hbm, h1, -⟩ := hmatch p hp
      exact ⟨p', hbm, (sameBit_iff hp.2.2 hp'in.2.2).1 (h1 ho)⟩
    · obtain ⟨hp0in, hb0, -⟩ := hmc0.2 ho
      refine ⟨p0, hp0in, (bitPos_iff_bitOfPos hp0in.2.2).1 hb0, fun p hp => ?_⟩
      obtain ⟨p', hp'in, hbm, -, h2⟩ := hmatch p hp
      obtain ⟨h2a, h2b, h2c⟩ := h2 ho
      refine ⟨p', hbm, fun h => (sameBit_iff hp.2.2 hp'in.2.2).1 (h2a h), fun h => ?_, fun h => ?_⟩
      · exact (bitPos_iff_bitOfPos hp'in.2.2).1 (h2b h)
      · exact ⟨(bitPos_iff_bitOfPos hp.2.2).1 (h2c h).1,
          (bitPos_iff_bitOfPos hp'in.2.2).1 (h2c h).2⟩
  · rintro ⟨hX, hY, h1, h2⟩
    have hBl : B < u.length := hX.1.2.1
    have hDl : D < u.length := hY.1.2.1
    -- the choice of `p₀` and of the correspondent of a marker
    have hchoice : ∀ p, ∃ p', p' < u.length ∧ (MkIn u k A B p → BlkMatch u k B C D p p') := by
      intro p
      by_cases hp : MkIn u k A B p
      · by_cases ho : o
        · obtain ⟨p', hbm, -⟩ := h1 ho p hp
          exact ⟨p', by have := hbm.1.2.1; omega, fun _ => hbm⟩
        · obtain ⟨p00, -, -, hall⟩ := h2 ho
          obtain ⟨p', hbm, -⟩ := hall p hp
          exact ⟨p', by have := hbm.1.2.1; omega, fun _ => hbm⟩
      · exact ⟨0, by omega, fun hc => absurd hc hp⟩
    have hguard : ∀ p p', (MkIn u k A B p → BlkMatch u k B C D p p') →
        ∀ z1 < u.length, ∀ z2 < u.length, ∀ z3 < u.length, ∀ z4 < u.length,
        ∀ n1 < u.length, ∀ n2 < u.length,
        (GuardB u k A B z1 z2 z3 z4 (n1 ≤ n2) ∨ GuardB u k C D z1 z2 z3 z4 (n1 ≤ n2) ∨
          GuardC u k A B C D p p' z1 z2 z3 z4 (n1 ≤ n2)) →
        Mean u k z1 z2 z3 z4 (n1 ≤ n2) := by
      rintro p p' hbm z1 - z2 - z3 - z4 - n1 - n2 - (hg | hg | hg)
      · rcases hg with ⟨he, rfl, rfl, rfl, hbe⟩ | ⟨he, hin, hbe, hlt, rfl, hbe'⟩
        · exact Or.inl ⟨he, hX.2.1 _ hbe⟩
        · exact Or.inr ⟨he, hX.2.2 _ _ _ hin hbe hlt hbe'⟩
      · rcases hg with ⟨he, rfl, rfl, rfl, hbe⟩ | ⟨he, hin, hbe, hlt, rfl, hbe'⟩
        · exact Or.inl ⟨he, hY.2.1 _ hbe⟩
        · exact Or.inr ⟨he, hY.2.2 _ _ _ hin hbe hlt hbe'⟩
      · obtain ⟨he, hp, hp', rfl, rfl, hbe, hbe'⟩ := hg
        obtain ⟨-, q, q', hq, hq', heq⟩ := hbm hp
        have e1 : q = z2 := isBE_unique hq hbe
        have e2 : q' = z4 := isBE_unique hq' hbe'
        subst e1; subst e2
        exact Or.inl ⟨he, heq⟩
    refine ⟨hX.1, hY.1, ?_⟩
    by_cases ho : o
    · refine ⟨0, by omega, fun p hp => ?_⟩
      obtain ⟨p', hp'l, hbm⟩ := hchoice p
      refine ⟨p', hp'l, ⟨fun _ hpin => ?_, fun hc => absurd ho hc⟩, hguard p p' hbm⟩
      obtain ⟨p'', hbm2, hbit⟩ := h1 ho p hpin
      have : p' = p'' := blkMatch_eq hk hX hY hpin (hbm hpin) hbm2
      subst this
      exact ⟨hbm2.1, (sameBit_iff hpin.2.2 hbm2.1.2.2).2 hbit⟩
    · obtain ⟨p0, hp0, hb0, hall⟩ := h2 ho
      refine ⟨p0, by have := hp0.2.1; omega, fun p hp => ?_⟩
      obtain ⟨p', hp'l, hbm⟩ := hchoice p
      refine ⟨p', hp'l, ⟨fun hc => absurd hc ho, fun _ => ⟨hp0,
        (bitPos_iff_bitOfPos hp0.2.2).2 hb0, fun hpin => ?_⟩⟩, hguard p p' hbm⟩
      obtain ⟨p'', hbm2, hlt, heq, hgt⟩ := hall p hpin
      have : p' = p'' := blkMatch_eq hk hX hY hpin (hbm hpin) hbm2
      subst this
      refine ⟨hbm2.1, fun h => (sameBit_iff hpin.2.2 hbm2.1.2.2).2 (hlt h), fun h => ?_, fun h => ?_⟩
      · exact (bitPos_iff_bitOfPos hbm2.1.2.2).2 (heq h)
      · exact ⟨(bitPos_iff_bitOfPos hpin.2.2).2 (hgt h).1,
          (bitPos_iff_bitOfPos hbm2.1.2.2).2 (hgt h).2⟩

end Transducers.Exercises
