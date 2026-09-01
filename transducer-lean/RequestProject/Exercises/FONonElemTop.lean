/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

The formulas of `RequestProject/Exercises/FONonElemForm.lean` speak about an
infix `(A, B]` of the string, which never contains the first position.  The
sentence that defines the first string of order `n` has to speak about the whole
string, so the block structure is repeated here in the left-inclusive form
`[a, B]`, and the case `a = 0` is the one that is used.
-/
import RequestProject.Exercises.FONonElemForm

namespace Transducers.Exercises

variable {N : ℕ}

/-! ## The block structure of a left-inclusive infix -/

/-- `p` is a position of the infix `[a, B]` carrying a marker of level `k+1`. -/
def MkFrom (u : List (Lett N)) (k a B p : ℕ) : Prop := a ≤ p ∧ p ≤ B ∧ MkAt u k p

/-- The infix `[a, B]` has the block structure of a string of order `k+1`. -/
def BlkStructA (u : List (Lett N)) (k a B : ℕ) : Prop :=
  a ≤ B ∧ B < u.length ∧ MkAt u k a ∧
  (∀ q, IsBE u k a q B → NoBitAt u k true (a + 1) q) ∧
  (∀ p q, MkFrom u k a B p → IsBE u k p q B → q = B → NoBitAt u k false (p + 1) q) ∧
  (∀ q, IsBE u k a q B → EqBlk u k a q a q) ∧
  (∀ p q q', MkFrom u k a B p → IsBE u k p q B → q < B → IsBE u k (q + 1) q' B →
    SuccBlk u k p q (q + 1) q')

/-- The data attached to a left-inclusive infix that is a string of order `k+1`. -/
theorem ordAtA_data {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {m a B : ℕ}
    (h : IsOrdAt u (k + 1) m a B) :
    B + 1 = a + numOrder k * blkSize k ∧
    (∀ p, MkFrom u k a B p ↔ ∃ t, t < numOrder k ∧ p = a + t * blkSize k) ∧
    (∀ t, t < numOrder k →
      IsOrdAt u k t (a + t * blkSize k + 1) (a + t * blkSize k + lenOrder k) ∧
      IsBE u k (a + t * blkSize k) (a + t * blkSize k + lenOrder k) B) := by
  obtain ⟨hb1, hmark, hblk⟩ := isOrdAt_succ_fwd hk h
  refine ⟨hb1, fun p => ?_, fun t ht => ?_⟩
  · constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨t, ht, hteq⟩ := (hmark p h1 h2).1 h3
      exact ⟨t, ht, hteq⟩
    · rintro ⟨t, ht, rfl⟩
      have hle : (t + 1) * blkSize k ≤ numOrder k * blkSize k := Nat.mul_le_mul_right _ ht
      have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
      have hS : 0 < blkSize k := blkSize_pos k
      refine ⟨by omega, by omega, ?_⟩
      exact ((hmark (a + t * blkSize k) (by omega) (by omega)).2 ⟨t, ht, by omega⟩)
  · obtain ⟨-, hcont, hbe⟩ := hblk t ht
    exact ⟨hcont, hbe⟩

/-- The block structure characterises the left-inclusive infixes that are strings of order
`k+1`. -/
theorem blkStructA_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} {a B : ℕ} :
    BlkStructA u k a B ↔ ∃ m, m < numOrder (k + 1) ∧ IsOrdAt u (k + 1) m a B := by
  constructor
  · rintro ⟨haB, hBl, hmk, hno1, hno0, hfirstb, hsuccb⟩
    refine isOrdAt_succ_bwd haB hBl hmk ?_ ?_ ?_
    · intro q hq
      obtain ⟨m, hm, hc, -⟩ := hfirstb q hq
      have h0 : m = 0 := (isOrdAt_first_iff (by omega) hm hc).2 (hno1 q hq)
      exact h0 ▸ hc
    · intro p q t h1 h2 h3 h4 h5 h6 h7
      exact (isOrdAt_last_iff (k := k) (by omega) h6 h7).2 (hno0 p q ⟨h1, h2, h3⟩ h4 h5)
    · intro p q q' h1 h2 h3 h4 h5 h6
      obtain ⟨m, hm, hc1, hc2⟩ := hsuccb p q q' ⟨h1, h2, h3⟩ h4 h5 h6
      exact ⟨m, hm, hc1, by simpa [show q + 1 + 1 = q + 2 from rfl] using hc2⟩
  · rintro ⟨m, hm, h⟩
    obtain ⟨hB, hmark, hblk⟩ := ordAtA_data hk h
    have hS : 0 < blkSize k := blkSize_pos k
    have hSL : blkSize k = lenOrder k + 1 := blkSize_eq k
    have hl : 0 < numOrder k := numOrder_pos k
    have hlS : numOrder k * blkSize k ≥ blkSize k := Nat.le_mul_of_pos_left _ hl
    have hBl : B < u.length := h.2.1
    have hmk0 : MkAt u k a := by
      have := (hmark a).2 ⟨0, hl, by omega⟩
      exact this.2.2
    have hbe0 : IsBE u k a (a + lenOrder k) B := by
      have := (hblk 0 hl).2; simpa using this
    have hcont0 : IsOrdAt u k 0 (a + 1) (a + lenOrder k) := by
      have := (hblk 0 hl).1; simpa using this
    refine ⟨by omega, hBl, hmk0, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have : q = a + lenOrder k := isBE_unique hq hbe0
      subst this
      exact (isOrdAt_first_iff (k := k) (by omega) hl hcont0).1 rfl
    · rintro p q hp hbe hqB
      obtain ⟨t, ht, rfl⟩ := (hmark p).1 hp
      obtain ⟨hcont, hbe'⟩ := hblk t ht
      have hq : q = a + t * blkSize k + lenOrder k := isBE_unique hbe hbe'
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
      have : q = a + lenOrder k := isBE_unique hq hbe0
      subst this
      exact ⟨0, hl, hcont0, hcont0⟩
    · rintro p q q' hp hbe hqB hbe'
      obtain ⟨t, ht, rfl⟩ := (hmark p).1 hp
      obtain ⟨hcont, hbeq⟩ := hblk t ht
      have hq : q = a + t * blkSize k + lenOrder k := isBE_unique hbe hbeq
      subst hq
      have hexp : (t + 1) * blkSize k = t * blkSize k + blkSize k := by ring
      have ht1 : t + 1 < numOrder k := by
        by_contra hc
        have : numOrder k ≤ t + 1 := by omega
        have := Nat.mul_le_mul_right (blkSize k) this
        omega
      obtain ⟨hcont1, hbeq1⟩ := hblk (t + 1) ht1
      have hq' : q' = a + (t + 1) * blkSize k + lenOrder k := by
        refine isBE_unique hbe' ?_
        have : a + t * blkSize k + lenOrder k + 1 = a + (t + 1) * blkSize k := by omega
        rw [this]; exact hbeq1
      subst hq'
      refine ⟨t, ht1, hcont, ?_⟩
      have he : a + t * blkSize k + lenOrder k + 1 + 1 = a + (t + 1) * blkSize k + 1 := by omega
      rw [he]
      exact hcont1

/-! ## The whole string -/

lemma segI_zero_self {A : Type} {u : List A} : segI u 0 (u.length - 1) = u := by
  rcases u.length.eq_zero_or_pos with h | h
  · simp [segI, List.length_eq_zero_iff.1 h]
  · simp [segI, show u.length - 1 + 1 = u.length by omega]

/-- **The whole string is the first string of order `k+1`** exactly if it has the block
structure of a string of order `k+1` and no marker of level `k+1` carries the bit `1`. -/
theorem eq_ordStr_iff {k : ℕ} (hk : k + 1 ≤ N) {u : List (Lett N)} :
    (BlkStructA u k 0 (u.length - 1) ∧ NoBitAt u (k + 1) true 0 (u.length - 1)) ↔
      u = ordStr N (k + 1) 0 := by
  constructor
  · rintro ⟨hbs, hno⟩
    obtain ⟨m, hm, ho⟩ := (blkStructA_iff hk).1 hbs
    have h0 : m = 0 := (isOrdAt_first_iff (by omega) hm ho).2 hno
    subst h0
    have := ho.2.2
    rwa [segI_zero_self] at this
  · rintro rfl
    have hlen : (ordStr N (k + 1) 0).length = lenOrder (k + 1) := ordStr_length N (k + 1) 0
    have hpos : 0 < lenOrder (k + 1) := by
      rw [lenOrder_succ]
      exact Nat.mul_pos (numOrder_pos k) (blkSize_pos k)
    have ho : IsOrdAt (ordStr N (k + 1) 0) (k + 1) 0 0
        ((ordStr N (k + 1) 0).length - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      exact segI_zero_self
    refine ⟨(blkStructA_iff hk).2 ⟨0, ?_, ho⟩, ?_⟩
    · exact numOrder_pos (k + 1)
    · exact (isOrdAt_first_iff (by omega) (numOrder_pos (k + 1)) ho).1 rfl

/-! ## The sentence defining the first string of order `k+2` -/

open Transducers

/-- `p` is a position of the infix `[e₁, e₂]` carrying a marker of level `k+1`. -/
def fMkFromF (N k e1 e2 p : ℕ) : MSO (Lett N) :=
  .and (MSO.le e1 p) (.and (MSO.le p e2) (fMkL N k p))

/-- The guard selecting the first block of the whole string. -/
def fTopG1 (N k : ℕ) : MSO (Lett N) :=
  .and (MSO.le (va k 4) (va k 5))
    (.and (fEqV (va k 0) (va (k + 1) 0))
      (.and (fEqV (va k 2) (va (k + 1) 0))
        (.and (fEqV (va k 1) (va k 3))
          (fIsBEF N k (va (k + 1) 0) (va k 1) (va (k + 1) 1)))))

/-- The guard selecting two consecutive blocks of the whole string. -/
def fTopG2 (N k : ℕ) : MSO (Lett N) :=
  .and (.not (MSO.le (va k 4) (va k 5)))
    (.and (fMkFromF N k (va (k + 1) 0) (va (k + 1) 1) (va k 0))
      (.and (fIsBEF N k (va k 0) (va k 1) (va (k + 1) 1))
        (.and (fLtV (va k 1) (va (k + 1) 1))
          (.and (fSuccF N (va k 1) (va k 2))
            (fIsBEF N k (va k 2) (va k 3) (va (k + 1) 1))))))

/-- The disjunction of the two guards of the sentence. -/
def fTopGuards (N k : ℕ) : MSO (Lett N) := .or (fTopG1 N k) (fTopG2 N k)

/-- The single copy of the formula `ψ` of order `k` used by the sentence. -/
def fTopBody (N k : ℕ) (ψ : MSO (Lett N)) : MSO (Lett N) :=
  fAll (va k 0) (fAll (va k 1) (fAll (va k 2) (fAll (va k 3) (fAll (va k 4) (fAll (va k 5)
    (fImp (fTopGuards N k) ψ))))))

/-- The variable `va (k+1) 0` is the first position. -/
def fTopFirst (N k : ℕ) : MSO (Lett N) :=
  .and (fInR N (va (k + 1) 0)) (fAll (va (k + 1) 8) (MSO.le (va (k + 1) 0) (va (k + 1) 8)))

/-- The variable `va (k+1) 1` is the last position. -/
def fTopLast (N k : ℕ) : MSO (Lett N) :=
  .and (fInR N (va (k + 1) 1)) (fAll (va (k + 1) 8) (MSO.le (va (k + 1) 8) (va (k + 1) 1)))

/-- The first block of the whole string carries no marker bit `1`. -/
def fTopNo1 (N k : ℕ) : MSO (Lett N) :=
  fAll (va (k + 1) 2) (fImp (fIsBEF N k (va (k + 1) 0) (va (k + 1) 2) (va (k + 1) 1))
    (fNoBitF N k true (va (k + 1) 0) (va (k + 1) 2)))

/-- A block that ends at the end of the whole string carries no marker bit `0`. -/
def fTopNo0 (N k : ℕ) : MSO (Lett N) :=
  fAll (va (k + 1) 3) (fAll (va (k + 1) 2)
    (fImp (.and (fMkFromF N k (va (k + 1) 0) (va (k + 1) 1) (va (k + 1) 3))
      (.and (fIsBEF N k (va (k + 1) 3) (va (k + 1) 2) (va (k + 1) 1))
        (fEqV (va (k + 1) 2) (va (k + 1) 1))))
      (fNoBitF N k false (va (k + 1) 3) (va (k + 1) 2))))

/-- No marker of level `k+1` carries the bit `1`. -/
def fTopNoBit (N k : ℕ) : MSO (Lett N) :=
  fAll (va (k + 1) 4) (.not (fBitL N k true (va (k + 1) 4)))

/-- The string has at least two positions. -/
def fTopTwo (N k : ℕ) : MSO (Lett N) :=
  MSO.exFO (va (k + 1) 6) (MSO.exFO (va (k + 1) 7) (fLtV (va (k + 1) 6) (va (k + 1) 7)))

/-- **The sentence of the exercise**: the string is the first string of order `k+2`. -/
def fTop (N k : ℕ) : MSO (Lett N) :=
  MSO.exFO (va (k + 1) 0) (MSO.exFO (va (k + 1) 1)
    (.and (fTopFirst N k) (.and (fTopLast N k)
      (.and (fMkL N k (va (k + 1) 0)) (.and (fTopNo1 N k) (.and (fTopNo0 N k)
        (.and (fTopNoBit N k) (.and (fTopTwo N k) (fTopBody N k (phiOrd N k))))))))))

section SatTop

variable {u : List (Lett N)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} {k : ℕ}

local macro "updsimp" : tactic =>
  `(tactic| simp only [Nat.succ_ne_self, false_and, if_false, if_true, true_and,
      Nat.reduceEqDiff, Function.update_apply, va_eq_va])

lemma sat_fMkFromF {e1 e2 p : ℕ} :
    MSO.Sat u fo so (fMkFromF N k e1 e2 p) ↔ MkFrom u k (fo e1) (fo e2) (fo p) := by
  simp only [fMkFromF, MSO.Sat, sat_fMkL, MkFrom]

lemma sat_fTopGuards (h3 : fo (va k 2) < u.length) :
    MSO.Sat u fo so (fTopGuards N k) ↔
      (((fo (va k 4) ≤ fo (va k 5)) ∧ fo (va k 0) = fo (va (k + 1) 0) ∧
          fo (va k 2) = fo (va (k + 1) 0) ∧ fo (va k 1) = fo (va k 3) ∧
          IsBE u k (fo (va (k + 1) 0)) (fo (va k 1)) (fo (va (k + 1) 1))) ∨
        (¬ (fo (va k 4) ≤ fo (va k 5)) ∧
          MkFrom u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va k 0)) ∧
          IsBE u k (fo (va k 0)) (fo (va k 1)) (fo (va (k + 1) 1)) ∧
          fo (va k 1) < fo (va (k + 1) 1) ∧ fo (va k 2) = fo (va k 1) + 1 ∧
          IsBE u k (fo (va k 2)) (fo (va k 3)) (fo (va (k + 1) 1)))) := by
  simp only [fTopGuards, fTopG1, fTopG2, MSO.Sat, sat_fEqV, sat_fLtV, sat_fMkFromF,
    sat_fIsBEF (vfree_va _ _) (vfree_va _ _),
    sat_fSuccF' (u := u) (vfree_va _ _ 0) (vfree_va _ _ 0) h3]

lemma sat_fTopBody {ψ : MSO (Lett N)}
    (hpsi : ∀ g : ℕ → ℕ, MSO.Sat u g so ψ ↔
      Mean u k (g (va k 0)) (g (va k 1)) (g (va k 2)) (g (va k 3)) (g (va k 4) ≤ g (va k 5))) :
    MSO.Sat u fo so (fTopBody N k ψ) ↔
      (∀ z1 < u.length, ∀ z2 < u.length, ∀ z3 < u.length, ∀ z4 < u.length,
        ∀ n1 < u.length, ∀ n2 < u.length,
        (((n1 ≤ n2) ∧ z1 = fo (va (k + 1) 0) ∧ z3 = fo (va (k + 1) 0) ∧ z2 = z4 ∧
            IsBE u k (fo (va (k + 1) 0)) z2 (fo (va (k + 1) 1))) ∨
          (¬ (n1 ≤ n2) ∧
            MkFrom u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) z1 ∧
            IsBE u k z1 z2 (fo (va (k + 1) 1)) ∧ z2 < fo (va (k + 1) 1) ∧ z3 = z2 + 1 ∧
            IsBE u k z3 z4 (fo (va (k + 1) 1)))) →
        Mean u k z1 z2 z3 z4 (n1 ≤ n2)) := by
  simp only [fTopBody, sat_fAll, sat_fImp]
  refine forall_congr' fun z1 => imp_congr_right fun _ => ?_
  refine forall_congr' fun z2 => imp_congr_right fun _ => ?_
  refine forall_congr' fun z3 => imp_congr_right fun h3 => ?_
  refine forall_congr' fun z4 => imp_congr_right fun _ => ?_
  refine forall_congr' fun n1 => imp_congr_right fun _ => ?_
  refine forall_congr' fun n2 => imp_congr_right fun _ => ?_
  refine imp_congr ?_ ?_
  · rw [sat_fTopGuards (by updsimp; exact h3)]
    updsimp
  · rw [hpsi]; updsimp

lemma sat_fTopFirst :
    MSO.Sat u fo so (fTopFirst N k) ↔
      (fo (va (k + 1) 0) < u.length ∧ ∀ p < u.length, fo (va (k + 1) 0) ≤ p) := by
  simp only [fTopFirst, MSO.Sat, sat_fInR (vfree_va _ _), sat_fAll]
  updsimp

lemma sat_fTopLast :
    MSO.Sat u fo so (fTopLast N k) ↔
      (fo (va (k + 1) 1) < u.length ∧ ∀ p < u.length, p ≤ fo (va (k + 1) 1)) := by
  simp only [fTopLast, MSO.Sat, sat_fInR (vfree_va _ _), sat_fAll]
  updsimp

lemma sat_fTopNo1 :
    MSO.Sat u fo so (fTopNo1 N k) ↔
      ∀ q < u.length, IsBE u k (fo (va (k + 1) 0)) q (fo (va (k + 1) 1)) →
        NoBitAt u k true (fo (va (k + 1) 0) + 1) q := by
  simp only [fTopNo1, sat_fAll, sat_fImp, sat_fIsBEF (vfree_va _ _) (vfree_va _ _),
    sat_fNoBitF (vfree_va _ _ 3) (vfree_va _ _ 3)]
  updsimp

lemma sat_fTopNo0 :
    MSO.Sat u fo so (fTopNo0 N k) ↔
      ∀ p < u.length, ∀ q < u.length,
        MkFrom u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) p →
        IsBE u k p q (fo (va (k + 1) 1)) → q = fo (va (k + 1) 1) →
        NoBitAt u k false (p + 1) q := by
  simp only [fTopNo0, MSO.Sat, sat_fAll, sat_fImp, sat_fMkFromF, sat_fEqV,
    sat_fIsBEF (vfree_va _ _) (vfree_va _ _),
    sat_fNoBitF (vfree_va _ _ 3) (vfree_va _ _ 3)]
  updsimp
  constructor
  · intro h p hp q hq h1 h2 h3
    exact h p hp q hq ⟨h1, h2, h3⟩
  · rintro h p hp q hq ⟨h1, h2, h3⟩
    exact h p hp q hq h1 h2 h3

lemma sat_fTopNoBit :
    MSO.Sat u fo so (fTopNoBit N k) ↔ ∀ p < u.length, ¬ BitPos u k p true := by
  simp only [fTopNoBit, MSO.Sat, sat_fAll, sat_fBitL]
  updsimp

lemma sat_fTopTwo :
    MSO.Sat u fo so (fTopTwo N k) ↔ ∃ x < u.length, ∃ y < u.length, x < y := by
  simp only [fTopTwo, MSO.Sat, sat_fLtV]
  updsimp

end SatTop

/-! ## The sentence defines the first string of order `k+2` -/

section Main

variable {u : List (Lett N)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} {k : ℕ}

local macro "updsimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Nat.succ_ne_self, false_and, if_false, if_true, true_and,
      Nat.reduceEqDiff, Function.update_apply, va_eq_va] $(loc)?)

/-- The unfolding of the sentence. -/
lemma sat_fTop_iff :
    MSO.Sat u fo so (fTop N k) ↔
      ∃ f < u.length, ∃ b < u.length,
        (f < u.length ∧ ∀ p < u.length, f ≤ p) ∧
        (b < u.length ∧ ∀ p < u.length, p ≤ b) ∧
        MkAt u k f ∧
        (∀ q < u.length, IsBE u k f q b → NoBitAt u k true (f + 1) q) ∧
        (∀ p < u.length, ∀ q < u.length, MkFrom u k f b p → IsBE u k p q b → q = b →
          NoBitAt u k false (p + 1) q) ∧
        (∀ p < u.length, ¬ BitPos u k p true) ∧
        (∃ x < u.length, ∃ y < u.length, x < y) ∧
        MSO.Sat u (Function.update (Function.update fo (va (k + 1) 0) f) (va (k + 1) 1) b) so
          (fTopBody N k (phiOrd N k)) := by
  simp only [fTop, MSO.Sat, sat_fTopFirst, sat_fTopLast, sat_fMkL, sat_fTopNo1, sat_fTopNo0,
    sat_fTopNoBit, sat_fTopTwo]
  updsimp

/-- **The sentence of the exercise has exactly one model**, the first string of order `k+2`. -/
theorem sat_fTop (hk1 : 1 ≤ k) (hk : k + 1 ≤ N) :
    MSO.Sat u fo so (fTop N k) ↔ u = ordStr N (k + 1) 0 := by
  rw [sat_fTop_iff]
  constructor
  · rintro ⟨f, hfl, b, hbl, ⟨-, hfmin⟩, ⟨-, hbmax⟩, hmk, hno1, hno0, hnobit, ⟨x, hx, y, hy, hxy⟩,
      hbody⟩
    have hu : 2 ≤ u.length := by omega
    have hf0 : f = 0 := Nat.le_zero.1 (hfmin 0 (by omega))
    have hbL : b = u.length - 1 := by
      have := hbmax (u.length - 1) (by omega)
      omega
    subst hf0; subst hbL
    rw [sat_fTopBody (fun g => sat_phiOrd hu k (by omega) g so)] at hbody
    updsimp at hbody
    rw [← eq_ordStr_iff hk]
    refine ⟨⟨by omega, hbl, hmk, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q hq
      exact hno1 q (by have := hq.2.1; omega) hq
    · rintro p q ⟨-, hp2, hp3⟩ hbe hqB
      exact hno0 p (by omega) q (by have := hbe.2.1; omega) ⟨Nat.zero_le _, hp2, hp3⟩ hbe hqB
    · intro q hq
      have hql : q < u.length := by have := hq.2.1; omega
      have := hbody 0 (by omega) q hql 0 (by omega) q hql 0 (by omega) 0 (by omega)
        (Or.inl ⟨le_rfl, rfl, rfl, rfl, hq⟩)
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd le_rfl h
    · rintro p q q' ⟨-, hp2, hp3⟩ hbe hqB hbe'
      have hpl : p < u.length := by omega
      have hql : q < u.length := by omega
      have hq'l : q' < u.length := by have := hbe'.2.1; omega
      have := hbody p hpl q hql (q + 1) (by omega) q' hq'l 1 (by omega) 0 (by omega)
        (Or.inr ⟨by omega, ⟨Nat.zero_le _, hp2, hp3⟩, hbe, hqB, rfl, hbe'⟩)
      rcases this with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (by omega)
      · exact h
    · intro p _ hple
      exact hnobit p (by omega)
  · rintro rfl
    set w := ordStr N (k + 1) 0 with hw
    have hwlen : w.length = lenOrder (k + 1) := ordStr_length N (k + 1) 0
    have hn2 : 2 ≤ numOrder k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have : numOrder (j + 1) = 2 ^ numOrder j := rfl
      have := Nat.one_le_two_pow (n := numOrder j)
      have h2 : 2 ^ 1 ≤ 2 ^ numOrder j := Nat.pow_le_pow_right (by omega) (numOrder_pos j)
      omega
    have hl1 : 1 ≤ lenOrder k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [lenOrder_succ]
      exact Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (numOrder_pos j).ne' (blkSize_pos j).ne')
    have hu : 2 ≤ w.length := by
      rw [hwlen, lenOrder_succ, blkSize_eq]
      calc 2 = 2 * 1 := rfl
        _ ≤ numOrder k * (lenOrder k + 1) := Nat.mul_le_mul hn2 (by omega)
    obtain ⟨hbs, hnb⟩ := (eq_ordStr_iff (u := w) hk).2 rfl
    obtain ⟨-, hbl, hmk, hno1, hno0, hfirstb, hsuccb⟩ := hbs
    refine ⟨0, by omega, w.length - 1, by omega, ⟨by omega, fun p _ => Nat.zero_le _⟩,
      ⟨by omega, fun p hp => by omega⟩, hmk, fun q _ hq => hno1 q hq,
      fun p _ q _ h1 h2 h3 => hno0 p q h1 h2 h3, fun p hp hb => hnb p (by omega) (by omega) hb,
      ⟨0, by omega, 1, by omega, by omega⟩, ?_⟩
    rw [sat_fTopBody (fun g => sat_phiOrd hu k (by omega) g so)]
    updsimp
    rintro z1 hz1 z2 hz2 z3 hz3 z4 hz4 n1 hn1 n2 hn2'
      (⟨he, e1, e3, e24, hbe⟩ | ⟨he, hmf, hbe, hzb, e3, hbe'⟩)
    · subst e1; subst e3; subst e24
      exact Or.inl ⟨he, hfirstb z2 hbe⟩
    · subst e3
      exact Or.inr ⟨he, hsuccb z1 z2 z4 hmf hbe hzb hbe'⟩

end Main

/-! ## The size of the sentence, and that it is first order -/

/-- All the definitions of the derived syntax, for the computation of the size and of the
first-orderness of the sentence. -/
local macro "unfoldAll" : tactic =>
  `(tactic| simp only [fTop, fTopFirst, fTopLast, fTopNo1, fTopNo0, fTopNoBit, fTopTwo,
      fTopBody, fTopGuards, fTopG1, fTopG2, fMkFromF, phiOrd, fBodyF, fGuardsF, fBCheapF,
      fBC1, fBC2, fBC3, fBC4, fMCheapF, fMCEq, fMCSucc, fMCSuccBody, fSameBitF, fBGuardF,
      fBG1, fBG2, fCGuardF, fMkL, fBitL, fInR, fSuccF, fNoBitF, fNextMkF, fIsBEF, fMkInF,
      fImp, fAll, fEqV, fLtV, fsize, MSO.IsFO, and_true, true_and, and_self])

/-- The size of the formula of order `k` grows by a constant at each step. -/
lemma fsize_phiOrd (N k : ℕ) : fsize (phiOrd N k) = 19 + 943 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : fsize (phiOrd N (k + 1)) = fsize (phiOrd N k) + 943 := by
        unfoldAll
        omega
      omega

/-- **The sentence has linear size.** -/
lemma fsize_fTop (N k : ℕ) : fsize (fTop N k) = 363 + 943 * k := by
  have h : fsize (fTop N k) = fsize (phiOrd N k) + 344 := by
    unfoldAll
    omega
  rw [h, fsize_phiOrd]
  omega

/-- The formula of order `k` is first order. -/
lemma isFO_phiOrd (N k : ℕ) : (phiOrd N k).IsFO := by
  induction k with
  | zero => unfoldAll
  | succ k ih =>
      unfoldAll
      exact ih

/-- **The sentence is first order.** -/
lemma isFO_fTop (N k : ℕ) : (fTop N k).IsFO := by
  have h := isFO_phiOrd N k
  unfoldAll
  exact h

end Transducers.Exercises
