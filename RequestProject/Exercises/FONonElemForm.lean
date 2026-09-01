/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

The first-order formula `phiOrd N k` of the Claim in the solution of that
exercise: it has six free position variables and says that the two infixes they
mark are strings of order `k` with the same index, or with consecutive indices,
according to the mode given by the last two variables.  Each formula contains
exactly one copy of the previous one, so that the size grows by a constant at
each step.
-/
import RequestProject.Exercises.FONonElemDSL

namespace Transducers.Exercises

open Transducers

variable {N : ℕ}

/-! ## The pieces of the cheap part of the block structure -/

/-- The infix `(x_{i₁}, x_{i₂}]` is nonempty. -/
def fBC1 (N k i1 i2 : ℕ) : MSO (Lett N) := fLtV (va (k + 1) i1) (va (k + 1) i2)

/-- The right end of the infix is a position of the string. -/
def fBC2 (N k i2 : ℕ) : MSO (Lett N) := fInR N (va (k + 1) i2)

/-- The infix starts with a marker of level `k+1`, whose block carries no marker bit `1`. -/
def fBC3 (N k i1 i2 : ℕ) : MSO (Lett N) :=
  MSO.exFO (va k 9) (.and (fSuccF N (va (k + 1) i1) (va k 9))
    (.and (fMkL N k (va k 9))
      (fAll (va k 10) (fImp (fIsBEF N k (va k 9) (va k 10) (va (k + 1) i2))
        (fNoBitF N k true (va k 9) (va k 10))))))

/-- A block that ends at the end of the infix carries no marker bit `0`. -/
def fBC4 (N k i1 i2 : ℕ) : MSO (Lett N) :=
  fAll (va k 12) (fAll (va k 10)
    (fImp (.and (fMkInF N k (va (k + 1) i1) (va (k + 1) i2) (va k 12))
      (.and (fIsBEF N k (va k 12) (va k 10) (va (k + 1) i2)) (fEqV (va k 10) (va (k + 1) i2))))
      (fNoBitF N k false (va k 12) (va k 10))))

/-- The cheap part of the block structure of the infix `(x_{i₁}, x_{i₂}]`. -/
def fBCheapF (N k i1 i2 : ℕ) : MSO (Lett N) :=
  .and (fBC1 N k i1 i2) (.and (fBC2 N k i2) (.and (fBC3 N k i1 i2) (fBC4 N k i1 i2)))

/-! ## The guards -/

/-- The guard selecting the first block of the infix `(x_{i₁}, x_{i₂}]`. -/
def fBG1 (N k i1 i2 : ℕ) : MSO (Lett N) :=
  MSO.exFO (va k 9) (.and (fSuccF N (va (k + 1) i1) (va k 9))
    (MSO.exFO (va k 10) (.and (fIsBEF N k (va k 9) (va k 10) (va (k + 1) i2))
      (.and (fEqV (va k 0) (va k 9)) (.and (fEqV (va k 1) (va k 10))
        (.and (fEqV (va k 2) (va k 9)) (.and (fEqV (va k 3) (va k 10))
          (MSO.le (va k 4) (va k 5)))))))))

/-- The guard selecting two consecutive blocks of the infix `(x_{i₁}, x_{i₂}]`. -/
def fBG2 (N k i1 i2 : ℕ) : MSO (Lett N) :=
  MSO.exFO (va k 12) (.and (fMkInF N k (va (k + 1) i1) (va (k + 1) i2) (va k 12))
    (MSO.exFO (va k 10) (.and (fIsBEF N k (va k 12) (va k 10) (va (k + 1) i2))
      (.and (fLtV (va k 10) (va (k + 1) i2))
        (MSO.exFO (va k 9) (.and (fSuccF N (va k 10) (va k 9))
          (MSO.exFO (va k 11) (.and (fIsBEF N k (va k 9) (va k 11) (va (k + 1) i2))
            (.and (fEqV (va k 0) (va k 12)) (.and (fEqV (va k 1) (va k 10))
              (.and (fEqV (va k 2) (va k 9)) (.and (fEqV (va k 3) (va k 11))
                (.not (MSO.le (va k 4) (va k 5)))))))))))))))

/-- The guard describing the block structure of the infix `(x_{i₁}, x_{i₂}]`. -/
def fBGuardF (N k i1 i2 : ℕ) : MSO (Lett N) := .or (fBG1 N k i1 i2) (fBG2 N k i1 i2)

/-- The guard matching the block of the marker `p` of the first infix with the block of the
marker `p'` of the second one. -/
def fCGuardF (N k : ℕ) : MSO (Lett N) :=
  .and (fMkInF N k (va (k + 1) 0) (va (k + 1) 1) (va k 7))
    (.and (fMkInF N k (va (k + 1) 2) (va (k + 1) 3) (va k 8))
      (MSO.exFO (va k 10) (.and (fIsBEF N k (va k 7) (va k 10) (va (k + 1) 1))
        (MSO.exFO (va k 11) (.and (fIsBEF N k (va k 8) (va k 11) (va (k + 1) 3))
          (.and (fEqV (va k 0) (va k 7)) (.and (fEqV (va k 1) (va k 10))
            (.and (fEqV (va k 2) (va k 8)) (.and (fEqV (va k 3) (va k 11))
              (MSO.le (va k 4) (va k 5)))))))))))

/-! ## The cheap condition on the quantified positions -/

/-- Two positions carry markers of level `k+1` with the same bit. -/
def fSameBitF (N k i j : ℕ) : MSO (Lett N) :=
  .or (.and (fBitL N k false i) (fBitL N k false j))
    (.and (fBitL N k true i) (fBitL N k true j))

/-- The cheap condition in the mode of equality of indices. -/
def fMCEq (N k : ℕ) : MSO (Lett N) :=
  fImp (fMkInF N k (va (k + 1) 0) (va (k + 1) 1) (va k 7))
    (.and (fMkInF N k (va (k + 1) 2) (va (k + 1) 3) (va k 8))
      (fSameBitF N k (va k 7) (va k 8)))

/-- The condition relating the marker `p` to the marker `p'` in the mode of consecutive
indices. -/
def fMCSuccBody (N k : ℕ) : MSO (Lett N) :=
  fImp (fMkInF N k (va (k + 1) 0) (va (k + 1) 1) (va k 7))
    (.and (fMkInF N k (va (k + 1) 2) (va (k + 1) 3) (va k 8))
      (.and (fImp (fLtV (va k 7) (va k 6)) (fSameBitF N k (va k 7) (va k 8)))
        (.and (fImp (fEqV (va k 7) (va k 6)) (fBitL N k true (va k 8)))
          (fImp (fLtV (va k 6) (va k 7))
            (.and (fBitL N k true (va k 7)) (fBitL N k false (va k 8)))))))

/-- The cheap condition in the mode of consecutive indices. -/
def fMCSucc (N k : ℕ) : MSO (Lett N) :=
  .and (fMkInF N k (va (k + 1) 0) (va (k + 1) 1) (va k 6))
    (.and (fBitL N k false (va k 6)) (fMCSuccBody N k))

/-- The cheap condition on the quantified positions `p₀`, `p` and `p'`. -/
def fMCheapF (N k : ℕ) : MSO (Lett N) :=
  .and (fImp (MSO.le (va (k + 1) 4) (va (k + 1) 5)) (fMCEq N k))
    (fImp (.not (MSO.le (va (k + 1) 4) (va (k + 1) 5))) (fMCSucc N k))

/-! ## Satisfaction of the formulas above

All the formulas of this file quantify over the variables `va k i`, and the valuation is
therefore repeatedly updated at such names.  Since `va` is injective, the resulting case
distinctions are decided by `simp`; the tactic below performs the whole computation. -/

section Sat

variable {N : ℕ} {u : List (Lett N)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} {k : ℕ}

/-- Unfold the satisfaction of the derived syntax and compute the updated valuations. -/
local macro "satsimp" : tactic =>
  `(tactic| simp only [MSO.Sat, sat_fAll, sat_fImp, sat_fEqV, sat_fLtV, sat_fMkL, sat_fBitL,
      sat_fSuccF (vfree_va _ _ 0) (vfree_va _ _ 0), sat_fMkInF, sat_fInR (vfree_va _ _),
      sat_fIsBEF (vfree_va _ _) (vfree_va _ _),
      sat_fNoBitF (vfree_va _ _ 3) (vfree_va _ _ 3),
      Nat.succ_ne_self, false_and, if_false, if_true, true_and, Nat.reduceEqDiff,
      Function.update_apply, va_eq_va])

/-- Compute the updated valuations only. -/
local macro "updsimp" : tactic =>
  `(tactic| simp only [Nat.succ_ne_self, false_and, if_false, if_true, true_and,
      Nat.reduceEqDiff, Function.update_apply, va_eq_va])

lemma sat_fBC1 {i1 i2 : ℕ} :
    MSO.Sat u fo so (fBC1 N k i1 i2) ↔ fo (va (k + 1) i1) < fo (va (k + 1) i2) := sat_fLtV

lemma sat_fBC2 {i2 : ℕ} :
    MSO.Sat u fo so (fBC2 N k i2) ↔ fo (va (k + 1) i2) < u.length :=
  sat_fInR (vfree_va _ _)

lemma sat_fBC3 {i1 i2 : ℕ} (hB : fo (va (k + 1) i2) < u.length) :
    MSO.Sat u fo so (fBC3 N k i1 i2) ↔
      MkAt u k (fo (va (k + 1) i1) + 1) ∧
        ∀ q, IsBE u k (fo (va (k + 1) i1) + 1) q (fo (va (k + 1) i2)) →
          NoBitAt u k true (fo (va (k + 1) i1) + 2) q := by
  simp only [fBC3]
  satsimp
  constructor
  · rintro ⟨p, hpl, ⟨h1, h2⟩, hmk, hrest⟩
    have hp : p = fo (va (k + 1) i1) + 1 := by
      by_contra hc
      exact h2 (fo (va (k + 1) i1) + 1) (by omega) ⟨by omega, by omega⟩
    subst hp
    exact ⟨hmk, fun q hq => hrest q (by have := hq.2.1; omega) hq⟩
  · rintro ⟨hmk, hrest⟩
    exact ⟨fo (va (k + 1) i1) + 1, mkAt_lt hmk, ⟨by omega, fun p _ hp => by omega⟩, hmk,
      fun q _ hq => hrest q hq⟩

lemma sat_fBC4 {i1 i2 : ℕ} (hB : fo (va (k + 1) i2) < u.length) :
    MSO.Sat u fo so (fBC4 N k i1 i2) ↔
      ∀ p q, MkIn u k (fo (va (k + 1) i1)) (fo (va (k + 1) i2)) p →
        IsBE u k p q (fo (va (k + 1) i2)) → q = fo (va (k + 1) i2) →
        NoBitAt u k false (p + 1) q := by
  simp only [fBC4]
  satsimp
  constructor
  · intro h p q hmk hbe hqB
    exact h p (by have := hmk.2.1; omega) q (by omega) ⟨hmk, hbe, hqB⟩
  · rintro h p _ q _ ⟨h1, h2, h3⟩
    exact h p q h1 h2 h3

lemma sat_fBCheapF {i1 i2 : ℕ} :
    MSO.Sat u fo so (fBCheapF N k i1 i2) ↔
      BCheap u k (fo (va (k + 1) i1)) (fo (va (k + 1) i2)) := by
  simp only [fBCheapF, MSO.Sat, sat_fBC1, sat_fBC2, BCheap]
  refine and_congr_right fun _ => and_congr_right fun hB => ?_
  rw [sat_fBC3 hB, sat_fBC4 hB, and_assoc]

lemma sat_fBG1 {i1 i2 : ℕ} (hB : fo (va (k + 1) i2) < u.length) :
    MSO.Sat u fo so (fBG1 N k i1 i2) ↔
      ((fo (va k 4) ≤ fo (va k 5)) ∧ fo (va k 0) = fo (va (k + 1) i1) + 1 ∧
        fo (va k 2) = fo (va (k + 1) i1) + 1 ∧ fo (va k 1) = fo (va k 3) ∧
        IsBE u k (fo (va (k + 1) i1) + 1) (fo (va k 1)) (fo (va (k + 1) i2))) := by
  simp only [fBG1]
  satsimp
  constructor
  · rintro ⟨s, hsl, ⟨h1, h2⟩, q, hql, hbe, e1, e2, e3, e4, he⟩
    have hs : s = fo (va (k + 1) i1) + 1 := by
      by_contra hc
      exact h2 (fo (va (k + 1) i1) + 1) (by omega) ⟨by omega, by omega⟩
    subst hs
    exact ⟨he, e1, e3, e2.trans e4.symm, by rw [e2]; exact hbe⟩
  · rintro ⟨he, h1, h3, h24, hbe⟩
    have hq : fo (va k 1) ≤ fo (va (k + 1) i2) := hbe.2.1
    have hA : fo (va (k + 1) i1) + 1 ≤ fo (va k 1) := hbe.1
    refine ⟨fo (va (k + 1) i1) + 1, by omega, ⟨by omega, fun p _ hp => by omega⟩,
      fo (va k 1), by omega, hbe, h1, rfl, h3, h24.symm, he⟩

lemma sat_fBG2 {i1 i2 : ℕ} (hB : fo (va (k + 1) i2) < u.length) :
    MSO.Sat u fo so (fBG2 N k i1 i2) ↔
      (¬ (fo (va k 4) ≤ fo (va k 5)) ∧
        MkIn u k (fo (va (k + 1) i1)) (fo (va (k + 1) i2)) (fo (va k 0)) ∧
        IsBE u k (fo (va k 0)) (fo (va k 1)) (fo (va (k + 1) i2)) ∧
        fo (va k 1) < fo (va (k + 1) i2) ∧ fo (va k 2) = fo (va k 1) + 1 ∧
        IsBE u k (fo (va k 2)) (fo (va k 3)) (fo (va (k + 1) i2))) := by
  simp only [fBG2]
  satsimp
  constructor
  · rintro ⟨pp, hppl, hmk, q, hql, hbe, hqB, s, hsl, ⟨h1, h2⟩, q', hq'l, hbe', e1, e2, e3, e4, he⟩
    have hs : s = q + 1 := by
      by_contra hc
      exact h2 (q + 1) (by omega) ⟨by omega, by omega⟩
    subst hs; subst e1; subst e2
    exact ⟨he, hmk, hbe, hqB, e3, e3 ▸ e4 ▸ hbe'⟩
  · rintro ⟨he, hmk, hbe, hqB, h3, hbe'⟩
    have h1 : fo (va k 0) ≤ fo (va (k + 1) i2) := hmk.2.1
    have h2 : fo (va k 1) ≤ fo (va (k + 1) i2) := hbe.2.1
    have h4 : fo (va k 2) ≤ fo (va k 3) := hbe'.1
    have h5 : fo (va k 3) ≤ fo (va (k + 1) i2) := hbe'.2.1
    exact ⟨fo (va k 0), by omega, hmk, fo (va k 1), by omega, hbe, hqB,
      fo (va k 1) + 1, by omega, ⟨by omega, fun p _ hp => by omega⟩,
      fo (va k 3), by omega, h3 ▸ hbe', rfl, rfl, h3, rfl, he⟩

lemma sat_fBGuardF {i1 i2 : ℕ} (hB : fo (va (k + 1) i2) < u.length) :
    MSO.Sat u fo so (fBGuardF N k i1 i2) ↔
      GuardB u k (fo (va (k + 1) i1)) (fo (va (k + 1) i2))
        (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3))
        (fo (va k 4) ≤ fo (va k 5)) := by
  simp only [fBGuardF, MSO.Sat, sat_fBG1 hB, sat_fBG2 hB, GuardB]

lemma sat_fCGuardF (hB : fo (va (k + 1) 1) < u.length) (hD : fo (va (k + 1) 3) < u.length) :
    MSO.Sat u fo so (fCGuardF N k) ↔
      GuardC u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va (k + 1) 2))
        (fo (va (k + 1) 3)) (fo (va k 7)) (fo (va k 8))
        (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3))
        (fo (va k 4) ≤ fo (va k 5)) := by
  simp only [fCGuardF, GuardC]
  satsimp
  constructor
  · rintro ⟨hp, hp', q, hql, hbe, q', hq'l, hbe', e1, e2, e3, e4, he⟩
    exact ⟨he, hp, hp', e1, e3, e2 ▸ hbe, e4 ▸ hbe'⟩
  · rintro ⟨he, hp, hp', e1, e3, hbe, hbe'⟩
    have h2 : fo (va k 1) ≤ fo (va (k + 1) 1) := hbe.2.1
    have h4 : fo (va k 3) ≤ fo (va (k + 1) 3) := hbe'.2.1
    exact ⟨hp, hp', fo (va k 1), by omega, hbe, fo (va k 3), by omega, hbe',
      e1, rfl, e3, rfl, he⟩

lemma sat_fSameBitF {i j : ℕ} :
    MSO.Sat u fo so (fSameBitF N k i j) ↔ SameBit u k (fo i) (fo j) := Iff.rfl

lemma sat_fMCheapF :
    MSO.Sat u fo so (fMCheapF N k) ↔
      MCheap u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va (k + 1) 2))
        (fo (va (k + 1) 3)) (fo (va (k + 1) 4) ≤ fo (va (k + 1) 5))
        (fo (va k 6)) (fo (va k 7)) (fo (va k 8)) := by
  simp only [fMCheapF, fMCEq, fMCSucc, fMCSuccBody, MSO.Sat, sat_fImp, sat_fMkInF,
    sat_fSameBitF, sat_fBitL, sat_fLtV, sat_fEqV, MCheap]

end Sat

/-! ## The formula -/

/-- The disjunction of the three guards. -/
def fGuardsF (N k : ℕ) : MSO (Lett N) :=
  .or (.or (fBGuardF N k 0 1) (fBGuardF N k 2 3)) (fCGuardF N k)

/-- The body of the formula of order `k+1`: a single copy of the formula `ψ` of order `k`,
applied to universally quantified arguments. -/
def fBodyF (N k : ℕ) (ψ : MSO (Lett N)) : MSO (Lett N) :=
  MSO.exFO (va k 6) (fAll (va k 7) (MSO.exFO (va k 8)
    (.and (fMCheapF N k)
      (fAll (va k 0) (fAll (va k 1) (fAll (va k 2) (fAll (va k 3)
        (fAll (va k 4) (fAll (va k 5) (fImp (fGuardsF N k) ψ))))))))))

/-- **The formula of the Claim.**  `phiOrd N k` has the six free position variables
`va k 0, …, va k 5`; the first four mark two infixes and the last two give the mode. -/
def phiOrd (N : ℕ) : ℕ → MSO (Lett N)
  | 0 => .and (MSO.le (va 0 4) (va 0 5))
      (.and (fEqV (va 0 0) (va 0 1)) (.and (fInR N (va 0 1))
        (.and (fEqV (va 0 2) (va 0 3)) (fInR N (va 0 3)))))
  | k + 1 => .and (fBCheapF N k 0 1) (.and (fBCheapF N k 2 3) (fBodyF N k (phiOrd N k)))

/-! ## Satisfaction of the formula -/

section Body

variable {N : ℕ} {u : List (Lett N)} {so : ℕ → Set ℕ} {k : ℕ}

/-- Compute the updated valuations. -/
local macro "updsimp" : tactic =>
  `(tactic| simp only [Nat.succ_ne_self, false_and, if_false, if_true, true_and,
      Nat.reduceEqDiff, Function.update_apply, va_eq_va])

lemma sat_fGuardsF {fo : ℕ → ℕ} (hB : fo (va (k + 1) 1) < u.length)
    (hD : fo (va (k + 1) 3) < u.length) :
    MSO.Sat u fo so (fGuardsF N k) ↔
      (GuardB u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1))
          (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3)) (fo (va k 4) ≤ fo (va k 5)) ∨
        GuardB u k (fo (va (k + 1) 2)) (fo (va (k + 1) 3))
          (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3)) (fo (va k 4) ≤ fo (va k 5)) ∨
        GuardC u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va (k + 1) 2))
          (fo (va (k + 1) 3)) (fo (va k 7)) (fo (va k 8))
          (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3))
          (fo (va k 4) ≤ fo (va k 5))) := by
  simp only [fGuardsF, MSO.Sat, sat_fBGuardF hB, sat_fBGuardF hD, sat_fCGuardF hB hD, or_assoc]

/-- **What the body of the formula of order `k+1` expresses**, in terms of the relation
defined by the formula `ψ` of order `k`. -/
lemma sat_fBodyF {fo : ℕ → ℕ} {ψ : MSO (Lett N)}
    (hB : fo (va (k + 1) 1) < u.length) (hD : fo (va (k + 1) 3) < u.length)
    (hpsi : ∀ g : ℕ → ℕ, MSO.Sat u g so ψ ↔
      Mean u k (g (va k 0)) (g (va k 1)) (g (va k 2)) (g (va k 3)) (g (va k 4) ≤ g (va k 5))) :
    MSO.Sat u fo so (fBodyF N k ψ) ↔
      (∃ p0 < u.length, ∀ p < u.length, ∃ p' < u.length,
        MCheap u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va (k + 1) 2))
          (fo (va (k + 1) 3)) (fo (va (k + 1) 4) ≤ fo (va (k + 1) 5)) p0 p p' ∧
        (∀ z1 < u.length, ∀ z2 < u.length, ∀ z3 < u.length, ∀ z4 < u.length,
          ∀ n1 < u.length, ∀ n2 < u.length,
          (GuardB u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) z1 z2 z3 z4 (n1 ≤ n2) ∨
            GuardB u k (fo (va (k + 1) 2)) (fo (va (k + 1) 3)) z1 z2 z3 z4 (n1 ≤ n2) ∨
            GuardC u k (fo (va (k + 1) 0)) (fo (va (k + 1) 1)) (fo (va (k + 1) 2))
              (fo (va (k + 1) 3)) p p' z1 z2 z3 z4 (n1 ≤ n2)) →
          Mean u k z1 z2 z3 z4 (n1 ≤ n2))) := by
  simp only [fBodyF, MSO.Sat, sat_fAll, sat_fImp]
  refine exists_congr fun p0 => and_congr_right fun _ => ?_
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  refine exists_congr fun p' => and_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · rw [sat_fMCheapF]; updsimp
  · refine forall_congr' fun z1 => imp_congr_right fun _ => ?_
    refine forall_congr' fun z2 => imp_congr_right fun _ => ?_
    refine forall_congr' fun z3 => imp_congr_right fun _ => ?_
    refine forall_congr' fun z4 => imp_congr_right fun _ => ?_
    refine forall_congr' fun n1 => imp_congr_right fun _ => ?_
    refine forall_congr' fun n2 => imp_congr_right fun _ => ?_
    refine imp_congr ?_ ?_
    · rw [sat_fGuardsF (by updsimp; exact hB) (by updsimp; exact hD)]
      updsimp
    · rw [hpsi]; updsimp

/-- **The Claim.**  The formula `phiOrd N k` says of its six free variables that the two
infixes they mark are strings of order `k` with the same index, or with consecutive indices,
according to the mode. -/
theorem sat_phiOrd (hu : 2 ≤ u.length) :
    ∀ k, k ≤ N → ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat u fo so (phiOrd N k) ↔
        Mean u k (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3))
          (fo (va k 4) ≤ fo (va k 5)) := by
  intro k
  induction k with
  | zero =>
      intro _ fo so
      simp only [phiOrd, MSO.Sat, sat_fEqV, sat_fInR (vfree_va _ _), Mean, EqBlk, SuccBlk,
        isOrdAt_zero_iff, show numOrder 0 = 1 from rfl]
      constructor
      · rintro ⟨he, h1, h2, h3, h4⟩
        exact Or.inl ⟨he, 0, by omega, ⟨by omega, h2⟩, ⟨by omega, h4⟩⟩
      · rintro (⟨he, m, hm, ⟨e1, hl1⟩, ⟨e2, hl2⟩⟩ | ⟨he, m, hm, -⟩)
        · exact ⟨he, by omega, hl1, by omega, hl2⟩
        · omega
  | succ k ih =>
      intro hk fo so
      rw [← formSem_iff (N := N) (by omega) hu]
      simp only [phiOrd, MSO.Sat]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [sat_fBCheapF] at h1
        rw [sat_fBCheapF] at h2
        exact ⟨h1, h2, (sat_fBodyF h1.2.1 h2.2.1 (fun g => ih (by omega) g so)).mp h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨sat_fBCheapF.mpr h1, sat_fBCheapF.mpr h2,
          (sat_fBodyF h1.2.1 h2.2.1 (fun g => ih (by omega) g so)).mpr h3⟩

end Body

end Transducers.Exercises
