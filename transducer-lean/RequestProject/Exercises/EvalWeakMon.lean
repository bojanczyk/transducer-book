/-
Exercise `exer:weak-simon-tree-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): the finite aperiodic monoids that compute the ranks.

The ranks of the weak Simon trees built in the proof are computed from the values of the prefix and
of the suffix in a finite aperiodic monoid.  Two monoids are needed for the induction step that
splits a string at a letter value `s`:

* `Transducers.Exercises.Run N`: the value in `N` of the first and of the last maximal factor without
  the letter value `s` (the *runs*), and whether `s` occurs at all;
* `Transducers.Exercises.Cut θ`: the decomposition of a string into *pieces* at the gaps where a
  letter of value `s` is followed by a letter of another value (the *cuts*): the value in `M` of the
  first and of the last piece, the product in `N` of the images under `θ` of the values of the
  pieces in between, and whether the first and the last letter have value `s`.

Both are aperiodic when `M` and `N` are (`Transducers.Exercises.aper_run`,
`Transducers.Exercises.aper_cut`).
-/
import Mathlib

namespace Transducers.Exercises

/-- A monoid is **aperiodic** if the powers of every element are eventually constant. -/
def Aper (N : Type) [Monoid N] : Prop := ∀ x : N, ∃ n : ℕ, x ^ (n + 1) = x ^ n

lemma pow_stable {N : Type} [Monoid N] {x : N} {n : ℕ} (h : x ^ (n + 1) = x ^ n) :
    ∀ m, n ≤ m → x ^ m = x ^ n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [pow_succ, ih, ← pow_succ, h]

lemma Aper.prod {N N' : Type} [Monoid N] [Monoid N'] (h : Aper N) (h' : Aper N') :
    Aper (N × N') := by
  intro x
  obtain ⟨n, hn⟩ := h x.1
  obtain ⟨n', hn'⟩ := h' x.2
  refine ⟨max n n', Prod.ext ?_ ?_⟩
  · simp only [Prod.pow_fst]
    rw [pow_stable hn (max n n' + 1) (by omega), pow_stable hn (max n n') (by omega)]
  · simp only [Prod.pow_snd]
    rw [pow_stable hn' (max n n' + 1) (by omega), pow_stable hn' (max n n') (by omega)]

lemma Aper.mul_pow_mul {N : Type} [Monoid N] (h : Aper N) (x c : N) :
    ∃ n : ℕ, (x * c) ^ (n + 1) * x = (x * c) ^ n * x := by
  obtain ⟨n, hn⟩ := h (x * c)
  exact ⟨n, by rw [hn]⟩

/-! ## The monoid of runs -/

/-- The first and last run: `ns x` -- no letter of value `s`, and value `x`; `sv l t` -- some letter
of value `s`, the first run has value `l` and the last run value `t`. -/
inductive Run (N : Type) : Type
  | ns : N → Run N
  | sv : N → N → Run N

namespace Run

variable {N : Type} [Monoid N]

/-- The product of `Run N`. -/
def mul : Run N → Run N → Run N
  | ns x, ns y => ns (x * y)
  | ns x, sv l t => sv (x * l) t
  | sv l t, ns y => sv l (t * y)
  | sv l _, sv _ t' => sv l t'

instance : Mul (Run N) := ⟨mul⟩

@[simp] lemma ns_mul_ns (x y : N) : ns x * ns y = ns (x * y) := rfl
@[simp] lemma ns_mul_sv (x l t : N) : ns x * sv l t = sv (x * l) t := rfl
@[simp] lemma sv_mul_ns (l t y : N) : sv l t * ns y = sv l (t * y) := rfl
@[simp] lemma sv_mul_sv (l t l' t' : N) : sv l t * sv l' t' = sv l t' := rfl

instance : Monoid (Run N) where
  one := ns 1
  mul_assoc := by
    rintro (_ | _) (_ | _) (_ | _) <;> simp [mul_assoc]
  one_mul := by
    rintro (_ | _)
    · exact congrArg _ (one_mul _)
    · show sv _ _ = _
      rw [one_mul]
  mul_one := by
    rintro (_ | _)
    · exact congrArg _ (mul_one _)
    · show sv _ _ = _
      rw [mul_one]

@[simp] lemma one_def : (1 : Run N) = ns 1 := rfl

/-- Whether the letter value `s` occurs. -/
def hasS : Run N → Bool
  | ns _ => false
  | sv _ _ => true

/-- The value of the last run. -/
def trail : Run N → N
  | ns x => x
  | sv _ t => t

/-- The value of the first run. -/
def lead : Run N → N
  | ns x => x
  | sv l _ => l

lemma ns_pow (x : N) (n : ℕ) : (ns x) ^ n = ns (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, ih, ns_mul_ns, pow_succ]

end Run

lemma aper_run {N : Type} [Monoid N] (h : Aper N) : Aper (Run N) := by
  rintro (x | ⟨l, t⟩)
  · obtain ⟨n, hn⟩ := h x
    exact ⟨n, by rw [Run.ns_pow, Run.ns_pow, hn]⟩
  · exact ⟨1, by simp [pow_succ]⟩

/-! ## The monoid of cuts -/

variable {M NO : Type} [Monoid M] [Monoid NO]

/-- The decomposition into pieces at the cuts (`θ` maps the value of a piece to `NO`): `e` -- the
empty string; `pc m f l` -- a single piece of value `m`, whose first letter has value `s` iff
`f` and whose last letter has value `s` iff `l`; `ct f a x b l` -- at least one cut, the first piece
has value `a`, the last piece value `b`, and `x` is the product of the images of the pieces in
between. -/
inductive Cut (θ : M → NO) : Type
  | e : Cut θ
  | pc (m : M) (f l : Bool) : Cut θ
  | ct (f : Bool) (a : M) (x : NO) (b : M) (l : Bool) : Cut θ

namespace Cut

variable {θ : M → NO}

/-- The product of `Cut θ`: there is a cut between the two factors iff the last letter of the
first one has value `s` and the first letter of the second one has not. -/
def mul : Cut θ → Cut θ → Cut θ
  | e, y => y
  | x, e => x
  | pc m f l, pc m' f' l' => if l && !f' then ct f m 1 m' l' else pc (m * m') f l'
  | pc m f l, ct f' a x b l' => if l && !f' then ct f m (θ a * x) b l' else ct f (m * a) x b l'
  | ct f a x b l, pc m' f' l' => if l && !f' then ct f a (x * θ b) m' l' else ct f a x (b * m') l'
  | ct f a x b l, ct f' a' x' b' l' =>
      if l && !f' then ct f a (x * θ b * (θ a' * x')) b' l' else ct f a (x * θ (b * a') * x') b' l'

lemma mul_e (x : Cut θ) : mul x e = x := by cases x <;> rfl

instance : Mul (Cut θ) := ⟨mul⟩

@[simp] lemma e_mul (x : Cut θ) : e * x = x := rfl
@[simp] lemma mul_e' (x : Cut θ) : x * e = x := mul_e x
lemma pc_mul_pc (m m' : M) (f l f' l' : Bool) :
    (pc m f l : Cut θ) * pc m' f' l' =
      if l && !f' then ct f m 1 m' l' else pc (m * m') f l' := rfl
lemma pc_mul_ct (m a b : M) (x : NO) (f l f' l' : Bool) :
    (pc m f l : Cut θ) * ct f' a x b l' =
      if l && !f' then ct f m (θ a * x) b l' else ct f (m * a) x b l' := rfl
lemma ct_mul_pc (m a b : M) (x : NO) (f l f' l' : Bool) :
    (ct f a x b l : Cut θ) * pc m f' l' =
      if l && !f' then ct f a (x * θ b) m l' else ct f a x (b * m) l' := rfl
lemma ct_mul_ct (a b a' b' : M) (x x' : NO) (f l f' l' : Bool) :
    (ct f a x b l : Cut θ) * ct f' a' x' b' l' =
      if l && !f' then ct f a (x * θ b * (θ a' * x')) b' l'
      else ct f a (x * θ (b * a') * x') b' l' := rfl

instance : Monoid (Cut θ) where
  one := e
  mul_assoc := by
    rintro (_ | ⟨m₁, f₁, l₁⟩ | ⟨f₁, a₁, x₁, b₁, l₁⟩) (_ | ⟨m₂, f₂, l₂⟩ | ⟨f₂, a₂, x₂, b₂, l₂⟩)
      (_ | ⟨m₃, f₃, l₃⟩ | ⟨f₃, a₃, x₃, b₃, l₃⟩) <;>
    simp only [e_mul, mul_e', pc_mul_pc, pc_mul_ct, ct_mul_pc, ct_mul_ct] <;>
    split_ifs <;>
    simp only [pc_mul_pc, pc_mul_ct, ct_mul_pc, ct_mul_ct] <;> split_ifs <;> simp_all [mul_assoc]
  one_mul := e_mul
  mul_one := mul_e'

@[simp] lemma one_def : (1 : Cut θ) = e := rfl

/-- Whether the last letter has value `s`. -/
def lastS : Cut θ → Bool
  | e => false
  | pc _ _ l => l
  | ct _ _ _ _ l => l

/-- Whether the first letter has value `s`. -/
def firstS : Cut θ → Bool
  | e => false
  | pc _ f _ => f
  | ct f _ _ _ _ => f

/-- Whether some letter has a value other than `s` (for the elements that come from strings). -/
def hasNS : Cut θ → Bool
  | e => false
  | pc _ f _ => !f
  | ct _ _ _ _ _ => true

/-- The product of the images of the pieces that are blocks, for a prefix ending with `s`: the
first piece is not a block if it starts with `s`. -/
def blocksL : Cut θ → NO
  | e => 1
  | pc m f _ => if f then 1 else θ m
  | ct f a x b _ => (if f then 1 else θ a) * x * θ b

/-- The product of the images of the pieces that are blocks, for a suffix starting with another
value than `s`: the last piece is not a block if it does not end with `s`. -/
def blocksR : Cut θ → NO
  | e => 1
  | pc m _ l => if l then θ m else 1
  | ct _ a x b l => θ a * x * (if l then θ b else 1)

lemma pc_pow_merge (m : M) (f l : Bool) (h : (l && !f) = false) :
    ∀ n : ℕ, (pc m f l : Cut θ) ^ (n + 1) = pc (m ^ (n + 1)) f l
  | 0 => by rw [pow_one, pow_one]
  | n + 1 => by rw [pow_succ, pc_pow_merge m f l h n, pc_mul_pc, h, if_neg (by simp), ← pow_succ]

lemma pc_pow_junction (m : M) :
    ∀ n : ℕ, (pc m false true : Cut θ) ^ (n + 2) = ct false m (θ m ^ n) m true
  | 0 => by rw [pow_two, pc_mul_pc]; simp
  | n + 1 => by
    rw [pow_succ, pc_pow_junction m n, ct_mul_pc]
    simp [pow_succ]

lemma ct_pow (f l : Bool) (a b : M) (x : NO) :
    ∀ n : ℕ, (ct f a x b l : Cut θ) ^ (n + 1) =
      ct f a ((x * (if l && !f then θ b * θ a else θ (b * a))) ^ n * x) b l
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, ct_pow f l a b x n, ct_mul_ct]
    split_ifs with hc <;> simp [pow_succ, mul_assoc]

lemma lastS_mul_pc (X : Cut θ) (m : M) (f l : Bool) : lastS (X * pc m f l) = l := by
  rcases X with _ | ⟨m', f', l'⟩ | ⟨f', a, x, b, l'⟩
  · rfl
  · rw [pc_mul_pc]; split_ifs <;> rfl
  · rw [ct_mul_pc]; split_ifs <;> rfl

lemma firstS_pc_mul (X : Cut θ) (m : M) (f l : Bool) : firstS (pc m f l * X) = f := by
  rcases X with _ | ⟨m', f', l'⟩ | ⟨f', a, x, b, l'⟩
  · rfl
  · rw [pc_mul_pc]; split_ifs <;> rfl
  · rw [pc_mul_ct]; split_ifs <;> rfl

/-- Appending a block (a piece starting with another value than `s` and ending with `s`) to a
string that is empty or ends with `s`. -/
lemma blocksL_mul_block {α : Cut θ} (hα : α = e ∨ lastS α = true) (m : M) :
    blocksL (α * pc m false true) = blocksL α * θ m ∧ lastS (α * pc m false true) = true ∧
      hasNS (α * pc m false true) = true := by
  rcases hα with rfl | hα
  · simp [blocksL, lastS, hasNS]
  rcases α with _ | ⟨m', f', l'⟩ | ⟨f', a, x, b, l'⟩
  · simp [lastS] at hα
  · simp only [lastS] at hα
    subst hα
    rw [pc_mul_pc]
    cases f' <;> simp [blocksL, lastS, hasNS]
  · simp only [lastS] at hα
    subst hα
    rw [ct_mul_pc]
    simp [blocksL, lastS, hasNS, mul_assoc]

/-- Prepending a block to a string that is empty or starts with another value than `s`. -/
lemma blocksR_block_mul {β : Cut θ} (hβ : β = e ∨ firstS β = false) (m : M) :
    blocksR (pc m false true * β) = θ m * blocksR β ∧ firstS (pc m false true * β) = false := by
  rcases hβ with rfl | hβ
  · simp [blocksR, firstS]
  rcases β with _ | ⟨m', f', l'⟩ | ⟨f', a, x, b, l'⟩
  · simp [blocksR, firstS]
  · simp only [firstS] at hβ
    subst hβ
    rw [pc_mul_pc]
    cases l' <;> simp [blocksR, firstS]
  · simp only [firstS] at hβ
    subst hβ
    rw [pc_mul_ct]
    simp [blocksR, firstS, mul_assoc]

end Cut

open Cut in
lemma aper_cut {θ : M → NO} (hM : Aper M) (hN : Aper NO) : Aper (Cut θ) := by
  rintro (_ | ⟨m, f, l⟩ | ⟨f, a, x, b, l⟩)
  · exact ⟨0, rfl⟩
  · by_cases hj : (l && !f) = true
    · have hl : l = true := by revert hj; cases l <;> simp
      have hf : f = false := by revert hj; cases f <;> simp [hl]
      subst hl hf
      obtain ⟨n, hn⟩ := hN (θ m)
      exact ⟨n + 2, by rw [pc_pow_junction, pc_pow_junction, hn]⟩
    · have hj' : (l && !f) = false := by simpa using hj
      obtain ⟨n, hn⟩ := hM m
      refine ⟨n + 1, ?_⟩
      rw [pc_pow_merge m f l hj', pc_pow_merge m f l hj', pow_stable hn (n + 1 + 1) (by omega),
        pow_stable hn (n + 1) (by omega)]
  · obtain ⟨n, hn⟩ := hN.mul_pow_mul x (if l && !f then θ b * θ a else θ (b * a))
    exact ⟨n + 1, by rw [ct_pow, ct_pow, hn]⟩

namespace Run

variable {N : Type} [Monoid N]

lemma trail_mul_ns (X : Run N) (y : N) : trail (X * ns y) = trail X * y := by
  cases X <;> rfl

lemma lead_ns_mul (X : Run N) (y : N) : lead (ns y * X) = y * lead X := by
  cases X <;> rfl

lemma trail_mul_sv (X : Run N) (l t : N) : trail (X * sv l t) = t := by
  cases X <;> rfl

lemma lead_sv_mul (X : Run N) (l t : N) : lead (sv l t * X) = l := by
  cases X <;> rfl

lemma hasS_mul (X Y : Run N) : hasS (X * Y) = (hasS X || hasS Y) := by
  cases X <;> cases Y <;> rfl

end Run

end Transducers.Exercises
