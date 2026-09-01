/-
Auxiliary file for Exercise `exer:fo-non-elementary` of the chapter on logic
(`logic.tex`) of *Transducers* (M. Bojańczyk).

A small layer of derived first-order syntax over `Transducers.MSO`, together
with the elementary formulas used by the construction of the solution of that
exercise: a position carries a marker of a given level, a position is the
successor of another one, a position is the last position of a block.
-/
import RequestProject.Exercises.FONonElemCore
import RequestProject.Exercises.ForFO

namespace Transducers.Exercises

open Transducers

/-! ## Derived syntax -/

variable {A : Type}

/-- Implication. -/
def fImp (φ ψ : MSO A) : MSO A := .or (.not φ) ψ

/-- Universal quantification. -/
def fAll (i : ℕ) (φ : MSO A) : MSO A := .not (.exFO i (.not φ))

/-- Equality of two position variables. -/
def fEqV (i j : ℕ) : MSO A := .and (.le i j) (.le j i)

/-- Strict order of two position variables. -/
def fLtV (i j : ℕ) : MSO A := .not (.le j i)

/-! ## Variable names

Two disjoint families of variable names are used: the names `va k i` carry the position
variables of the formulas of the construction, indexed by the order `k` of the formula and by a
slot `i`, and the names `vb n` are the variables bound inside the elementary formulas below.
Because `Nat.pair` is injective, a name of one family is never a name of the other. -/

/-- The position variable with slot `i` of the formula of order `k`. -/
def va (k i : ℕ) : ℕ := Nat.pair 0 (Nat.pair k i)

/-- The `n`-th variable bound inside an elementary formula. -/
def vb (n : ℕ) : ℕ := Nat.pair 1 n

@[simp] lemma va_eq_va {k l i j : ℕ} : (va k i = va l j) = (k = l ∧ i = j) := by
  simp [va, Nat.pair_eq_pair]

@[simp] lemma vb_eq_vb {n m : ℕ} : (vb n = vb m) = (n = m) := by
  simp [vb, Nat.pair_eq_pair]

@[simp] lemma va_ne_vb {k i n : ℕ} : (va k i = vb n) = False := by
  simp [va, vb, Nat.pair_eq_pair]

@[simp] lemma vb_ne_va {k i n : ℕ} : (vb n = va k i) = False := by
  simp [va, vb, Nat.pair_eq_pair]

/-- A variable name that is not bound inside an elementary formula. -/
def VFree (i : ℕ) : Prop := ∀ n, i ≠ vb n

lemma vfree_va (k i : ℕ) : VFree (va k i) := by simp [VFree]

/-! ## Satisfaction of the derived syntax -/

variable {u : List A} {fo : ℕ → ℕ} {so : ℕ → Set ℕ}

lemma sat_fImp {φ ψ : MSO A} :
    MSO.Sat u fo so (fImp φ ψ) ↔ (MSO.Sat u fo so φ → MSO.Sat u fo so ψ) := by
  simp [fImp, MSO.Sat, imp_iff_not_or]

lemma sat_fAll {i : ℕ} {φ : MSO A} :
    MSO.Sat u fo so (fAll i φ) ↔ ∀ p < u.length, MSO.Sat u (Function.update fo i p) so φ := by
  simp [fAll, MSO.Sat]

lemma sat_fEqV {i j : ℕ} : MSO.Sat u fo so (fEqV i j) ↔ fo i = fo j := by
  simp [fEqV, MSO.Sat]; omega

lemma sat_fLtV {i j : ℕ} : MSO.Sat u fo so (fLtV i j) ↔ fo i < fo j := by
  simp [fLtV, MSO.Sat]

/-! ## The elementary formulas of the construction -/

section Elementary

variable {N : ℕ}

/-- The position `i` carries a marker of level `k+1`. -/
def fMkL (N k i : ℕ) : MSO (Lett N) :=
  .or (.lab (lv N (k + 1), false) i) (.lab (lv N (k + 1), true) i)

/-- The position `i` carries the marker of level `k+1` with the bit `b`. -/
def fBitL (N k : ℕ) (b : Bool) (i : ℕ) : MSO (Lett N) := .lab (lv N (k + 1), b) i

/-- The value of the variable `i` is a position of the string. -/
def fInR (N i : ℕ) : MSO (Lett N) := .exFO (vb 4) (fEqV (vb 4) i)

/-- The value of `j` is the position after the value of `i`. -/
def fSuccF (N i j : ℕ) : MSO (Lett N) :=
  .and (fLtV i j) (fAll (vb 0) (.not (.and (fLtV i (vb 0)) (fLtV (vb 0) j))))

/-- No position of the infix `(lo, hi]` carries the letter of level `k` with the bit `c`. -/
def fNoBitF (N k : ℕ) (c : Bool) (lo hi : ℕ) : MSO (Lett N) :=
  fAll (vb 3) (fImp (.and (fLtV lo (vb 3)) (.le (vb 3) hi)) (.not (.lab (lv N k, c) (vb 3))))

/-- The position after the value of `q` carries a marker of level `k+1`. -/
def fNextMkF (N k q : ℕ) : MSO (Lett N) :=
  .exFO (vb 2) (.and (fSuccF N q (vb 2)) (fMkL N k (vb 2)))

/-- The value of `q` is the last position of the block of level `k+1` that starts at `p`, inside
an infix that ends at `b`. -/
def fIsBEF (N k p q b : ℕ) : MSO (Lett N) :=
  .and (.le p q) (.and (.le q b)
    (.and (fAll (vb 1) (fImp (.and (fLtV p (vb 1)) (.le (vb 1) q)) (.not (fMkL N k (vb 1)))))
      (.or (fEqV q b) (fNextMkF N k q))))

/-- The value of `p` is a position of the infix `(e₁, e₂]` carrying a marker of level `k+1`. -/
def fMkInF (N k e1 e2 p : ℕ) : MSO (Lett N) :=
  .and (fLtV e1 p) (.and (.le p e2) (fMkL N k p))

variable {u : List (Lett N)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} {k : ℕ}

lemma sat_fMkL {i : ℕ} : MSO.Sat u fo so (fMkL N k i) ↔ MkAt u k (fo i) := by
  simp only [fMkL, MSO.Sat, MkAt]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, hb⟩
    cases b with
    | false => exact Or.inl hb
    | true => exact Or.inr hb

lemma sat_fBitL {i : ℕ} {b : Bool} : MSO.Sat u fo so (fBitL N k b i) ↔ BitPos u k (fo i) b :=
  Iff.rfl

lemma sat_fInR {i : ℕ} (hi : VFree i) : MSO.Sat u fo so (fInR N i) ↔ fo i < u.length := by
  simp only [fInR, MSO.Sat, sat_fEqV, Function.update_self, Function.update_of_ne (hi 4)]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro h; exact ⟨fo i, h, rfl⟩

lemma sat_fSuccF {i j : ℕ} (hi : i ≠ vb 0) (hj : j ≠ vb 0) :
    MSO.Sat u fo so (fSuccF N i j) ↔
      (fo i < fo j ∧ ∀ p < u.length, ¬ (fo i < p ∧ p < fo j)) := by
  simp only [fSuccF, MSO.Sat, sat_fAll, sat_fLtV, Function.update_self,
    Function.update_of_ne hi, Function.update_of_ne hj]

/-- The formula `fSuccF` says that `j` is the successor of `i`, as soon as `j` is a position. -/
lemma sat_fSuccF' {i j : ℕ} (hi : i ≠ vb 0) (hj : j ≠ vb 0) (hjl : fo j < u.length) :
    MSO.Sat u fo so (fSuccF N i j) ↔ fo j = fo i + 1 := by
  rw [sat_fSuccF hi hj]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hc
    exact h2 (fo i + 1) (by omega) ⟨by omega, by omega⟩
  · rintro h
    exact ⟨by omega, fun p _ hp => by omega⟩

lemma sat_fNoBitF {c : Bool} {lo hi : ℕ} (hlo : lo ≠ vb 3) (hhi : hi ≠ vb 3) :
    MSO.Sat u fo so (fNoBitF N k c lo hi) ↔ NoBitAt u k c (fo lo + 1) (fo hi) := by
  simp only [fNoBitF, MSO.Sat, sat_fAll, sat_fImp, sat_fLtV, Function.update_self,
    Function.update_of_ne hlo, Function.update_of_ne hhi, NoBitAt]
  constructor
  · intro h p h1 h2
    rcases lt_or_ge p u.length with hp | hp
    · exact h p hp ⟨by omega, h2⟩
    · rw [List.getElem?_eq_none hp]
      simp
  · intro h p _ hp
    exact h p (by omega) hp.2

lemma sat_fMkInF {e1 e2 p : ℕ} :
    MSO.Sat u fo so (fMkInF N k e1 e2 p) ↔ MkIn u k (fo e1) (fo e2) (fo p) := by
  simp only [fMkInF, MSO.Sat, sat_fLtV, sat_fMkL, MkIn]

/-- A marker sits at a position of the string. -/
lemma mkAt_lt {p : ℕ} (h : MkAt u k p) : p < u.length := by
  obtain ⟨b, hb⟩ := h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at hb
  simp at hb

lemma sat_fNextMkF {q : ℕ} (hq : VFree q) :
    MSO.Sat u fo so (fNextMkF N k q) ↔ MkAt u k (fo q + 1) := by
  have hb2 : (vb 2 : ℕ) ≠ vb 0 := by simp
  simp only [fNextMkF, MSO.Sat]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rw [sat_fSuccF' (u := u) (hq 0) hb2 (by simpa using hp)] at h1
    simp only [Function.update_self, Function.update_of_ne (hq 2)] at h1
    rw [sat_fMkL] at h2
    simp only [Function.update_self] at h2
    rwa [← h1]
  · intro h
    refine ⟨fo q + 1, mkAt_lt h, ?_, ?_⟩
    · rw [sat_fSuccF' (u := u) (hq 0) hb2 (by rw [Function.update_self]; exact mkAt_lt h)]
      rw [Function.update_self, Function.update_of_ne (hq 2)]
    · rw [sat_fMkL]
      simpa using h

lemma sat_fIsBEF {p q b : ℕ} (hp : VFree p) (hq : VFree q) :
    MSO.Sat u fo so (fIsBEF N k p q b) ↔ IsBE u k (fo p) (fo q) (fo b) := by
  have hmk : ∀ (g : ℕ → ℕ) (i : ℕ), MSO.Sat u g so (fMkL N k i) ↔ MkAt u k (g i) :=
    fun g i => sat_fMkL
  simp only [fIsBEF, MSO.Sat, sat_fAll, sat_fImp, sat_fLtV, sat_fEqV, sat_fNextMkF hq, hmk,
    Function.update_self, Function.update_of_ne (hp 1), Function.update_of_ne (hq 1), IsBE]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
  constructor
  · intro h r h1 h2 hmr
    exact h r (mkAt_lt hmr) ⟨h1, h2⟩ hmr
  · intro h r _ hr
    exact h r hr.1 hr.2

end Elementary

end Transducers.Exercises
