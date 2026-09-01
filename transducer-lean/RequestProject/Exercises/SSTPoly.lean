/-
Exercise `exer:copyful-sst-decidable` of the chapter *Streaming string transducers* (`sst.tex`) of
*Transducers* (M. Bojańczyk): the reduction of the equivalence problem for copyful ssts to the
equivalence problem for polynomial automata.

The author's solution encodes a string `w` over the output alphabet `{0,1}` by the two numbers
`α w`, the number it denotes in binary, and `β w = 2^{|w|}`, both of which a polynomial automaton
can maintain because concatenation acts on them polynomially, and it then replaces the output
string by the injective quantity `α w + 2 · β w`.  That is what is formalised here.
-/
import RequestProject.Exercises.SSTAux

namespace Transducers.Exercises

open Transducers

/-! ## The numerical encoding of a string over a two-letter alphabet -/

/-- The number denoted in binary by a string over `{0,1}` (the `α` of the author's solution). -/
def binNum (w : List Bool) : ℕ := w.foldl (fun n b => 2 * n + if b then 1 else 0) 0

lemma binNum_foldl (n : ℕ) (w : List Bool) :
    w.foldl (fun n b => 2 * n + if b then 1 else 0) n = n * 2 ^ w.length + binNum w := by
  induction w generalizing n with
  | nil => simp [binNum]
  | cons b w ih =>
      rw [List.foldl_cons, ih]
      have h0 : binNum (b :: w) = (if b then 1 else 0) * 2 ^ w.length + binNum w := by
        rw [binNum, List.foldl_cons, ih]
        simp
      rw [List.length_cons, h0]
      ring

lemma binNum_cons (b : Bool) (w : List Bool) :
    binNum (b :: w) = (if b then 1 else 0) * 2 ^ w.length + binNum w := by
  rw [binNum, List.foldl_cons, binNum_foldl]
  simp

lemma binNum_append (u v : List Bool) :
    binNum (u ++ v) = binNum u * 2 ^ v.length + binNum v := by
  rw [binNum, List.foldl_append, binNum_foldl]
  rfl

lemma binNum_lt (w : List Bool) : binNum w < 2 ^ w.length := by
  induction w with
  | nil => simp [binNum]
  | cons b w ih =>
      rw [binNum_cons, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

lemma binNum_inj_of_length : ∀ w v : List Bool, w.length = v.length → binNum w = binNum v → w = v
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: w, c :: v, hlen, hnum => by
      have hl : w.length = v.length := by simpa using hlen
      rw [binNum_cons, binNum_cons, hl] at hnum
      have hw := binNum_lt w
      have hv := binNum_lt v
      rw [hl] at hw
      have hbc : b = c := by
        cases b <;> cases c <;> simp at hnum ⊢ <;> omega
      subst hbc
      have : binNum w = binNum v := by
        cases b <;> simp at hnum <;> omega
      rw [binNum_inj_of_length w v hl this]

/-- The injective quantity `α w + 2 · β w` of the author's solution. -/
def encodeOut (w : List Bool) : ℕ := binNum w + 2 * 2 ^ w.length

lemma encodeOut_lt (w : List Bool) : encodeOut w < 2 ^ (w.length + 2) := by
  have h := binNum_lt w
  rw [encodeOut, pow_succ, pow_succ]
  omega

lemma le_encodeOut (w : List Bool) : 2 ^ (w.length + 1) ≤ encodeOut w := by
  rw [encodeOut, pow_succ]
  omega

lemma encodeOut_length_eq {w v : List Bool} (h : encodeOut w = encodeOut v) :
    w.length = v.length := by
  by_contra hne
  rcases Nat.lt_or_ge w.length v.length with hlt | hge
  · have h1 : 2 ^ (w.length + 2) ≤ 2 ^ (v.length + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have := encodeOut_lt w
    have := le_encodeOut v
    omega
  · have hlt : v.length < w.length := by omega
    have h1 : 2 ^ (v.length + 2) ≤ 2 ^ (w.length + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have := encodeOut_lt v
    have := le_encodeOut w
    omega

lemma encodeOut_injective : Function.Injective encodeOut := by
  intro w v h
  have hlen := encodeOut_length_eq h
  refine binNum_inj_of_length w v hlen ?_
  rw [encodeOut, encodeOut, hlen] at h
  omega

/-! ## The polynomial automaton simulating a copyful sst -/

section Simulation

variable {A Q X : Type} [Fintype X]

/-- `β` of the string obtained by substituting the registers, as a polynomial in the registers of
the simulating polynomial automaton: `Sum.inl x` holds `α` of the register `x`, and `Sum.inr x`
holds `β` of it. -/
noncomputable def betaPoly : List (X ⊕ Bool) → MvPolynomial (X ⊕ X) ℚ
  | [] => 1
  | Sum.inl x :: t => MvPolynomial.X (Sum.inr x) * betaPoly t
  | Sum.inr _ :: t => 2 * betaPoly t

/-- `α` of the string obtained by substituting the registers, as a polynomial in the registers of
the simulating polynomial automaton. -/
noncomputable def alphaPoly : List (X ⊕ Bool) → MvPolynomial (X ⊕ X) ℚ
  | [] => 0
  | Sum.inl x :: t => MvPolynomial.X (Sum.inl x) * betaPoly t + alphaPoly t
  | Sum.inr b :: t => (if b then 1 else 0) * betaPoly t + alphaPoly t

/-- The values of the registers of the simulating automaton that correspond to a register
valuation of the copyful sst. -/
def encodeVals (η : X → List Bool) : X ⊕ X → ℚ
  | Sum.inl x => (binNum (η x) : ℚ)
  | Sum.inr x => (2 : ℚ) ^ (η x).length

omit [Fintype X] in
lemma eval_betaPoly (η : X → List Bool) (s : List (X ⊕ Bool)) :
    MvPolynomial.eval (encodeVals η) (betaPoly s) = (2 : ℚ) ^ (SST.subst η s).length := by
  induction s with
  | nil => simp [betaPoly, SST.subst]
  | cons z s ih =>
      rcases z with x | b
      · have h0 : SST.subst η (Sum.inl x :: s) = η x ++ SST.subst η s := by simp [SST.subst]
        rw [betaPoly, h0]
        simp only [map_mul, MvPolynomial.eval_X, ih, encodeVals, List.length_append]
        rw [pow_add]
      · have h0 : SST.subst η (Sum.inr b :: s) = b :: SST.subst η s := by simp [SST.subst]
        rw [betaPoly, h0]
        simp only [map_mul, map_ofNat, ih, List.length_cons]
        rw [pow_succ]
        ring

omit [Fintype X] in
lemma eval_alphaPoly (η : X → List Bool) (s : List (X ⊕ Bool)) :
    MvPolynomial.eval (encodeVals η) (alphaPoly s) = (binNum (SST.subst η s) : ℚ) := by
  induction s with
  | nil => simp [alphaPoly, SST.subst, binNum]
  | cons z s ih =>
      rcases z with x | b
      · have h0 : SST.subst η (Sum.inl x :: s) = η x ++ SST.subst η s := by simp [SST.subst]
        rw [alphaPoly, h0, binNum_append]
        simp only [map_add, map_mul, MvPolynomial.eval_X, ih, eval_betaPoly, encodeVals]
        push_cast
        ring
      · have h0 : SST.subst η (Sum.inr b :: s) = b :: SST.subst η s := by simp [SST.subst]
        rw [alphaPoly, h0, binNum_cons]
        simp only [map_add, map_mul, ih, eval_betaPoly]
        cases b <;> push_cast <;> simp

/-- The polynomial automaton of the author's solution: it keeps, for every register of the copyful
sst, the two numbers `α` and `β` of the string that the register holds. -/
noncomputable def CopyfulSST.encodeAut (T : CopyfulSST A Bool Q X) : PolyAut A Q (X ⊕ X) where
  init := T.init
  initVal := fun z => match z with | Sum.inl _ => 0 | Sum.inr _ => 1
  step := fun q a => ((T.step q a).1, fun z => match z with
      | Sum.inl x => alphaPoly ((T.step q a).2 x)
      | Sum.inr x => betaPoly ((T.step q a).2 x))
  final := fun q => alphaPoly (T.final q) + 2 * betaPoly (T.final q)

lemma CopyfulSST.encodeAut_runConfig (T : CopyfulSST A Bool Q X) (w : List A)
    (q : Q) (η : X → List Bool) :
    w.foldl T.encodeAut.stepVal (q, encodeVals η)
      = ((w.foldl T.stepConfig (q, η)).1, encodeVals (w.foldl T.stepConfig (q, η)).2) := by
  induction w generalizing q η with
  | nil => rfl
  | cons a w ih =>
      have hstep : T.encodeAut.stepVal (q, encodeVals η) a
          = ((T.stepConfig (q, η) a).1, encodeVals (T.stepConfig (q, η) a).2) := by
        refine Prod.ext rfl ?_
        funext z
        rcases z with x | x
        · show MvPolynomial.eval (encodeVals η) (alphaPoly ((T.step q a).2 x)) = _
          rw [eval_alphaPoly]
          rfl
        · show MvPolynomial.eval (encodeVals η) (betaPoly ((T.step q a).2 x)) = _
          rw [eval_betaPoly]
          rfl
      rw [List.foldl_cons, hstep]
      exact ih _ _

lemma CopyfulSST.encodeAut_eval (T : CopyfulSST A Bool Q X) (w : List A) :
    T.encodeAut.eval w = ((encodeOut (T.eval w) : ℕ) : ℚ) := by
  have hinit : T.encodeAut.initVal = encodeVals (fun _ : X => ([] : List Bool)) := by
    funext z
    rcases z with x | x <;> simp [CopyfulSST.encodeAut, encodeVals, binNum]
  have hrun : T.encodeAut.runConfig w
      = ((T.runConfig w).1, encodeVals (T.runConfig w).2) := by
    rw [PolyAut.runConfig, hinit]
    exact T.encodeAut_runConfig w T.init (fun _ => [])
  rw [PolyAut.eval, hrun]
  show MvPolynomial.eval (encodeVals (T.runConfig w).2)
      (alphaPoly (T.final (T.runConfig w).1) + 2 * betaPoly (T.final (T.runConfig w).1)) = _
  rw [map_add, map_mul, eval_alphaPoly, eval_betaPoly, map_ofNat]
  show _ = ((binNum (T.eval w) + 2 * 2 ^ (T.eval w).length : ℕ) : ℚ)
  push_cast
  rfl

end Simulation

/-- **Exercise `exer:copyful-sst-decidable`.**  The equivalence problem for copyful ssts reduces to
the equivalence problem for polynomial automata: for any two copyful ssts with output alphabet
`{0,1}` there are two polynomial automata that are equivalent exactly when the two ssts are.  So
if equivalence is decidable for polynomial automata, then it is decidable for copyful ssts.

The proof is the author's: the output string `w` is replaced by the number `α w + 2 · β w`, where
`α w` is the number that `w` denotes in binary and `β w = 2^{|w|}`; concatenation acts on the pair
`(α, β)` polynomially, so a polynomial automaton can maintain these two numbers for every register
of the sst, and the resulting number determines the output string
(`Transducers.Exercises.encodeOut_injective`).

The reduction, and not a statement about decision procedures, is what is formalised: the book's
"equivalence is decidable" is a statement about *descriptions* of machines, and this project has no
system of finite codes for copyful ssts or for polynomial automata, so a `Decidable` statement
about them could not be stated faithfully.  The assumption of the exercise -- that equivalence is
decidable for polynomial automata -- is therefore not needed here, and does not appear. -/
theorem copyfulSST_equivalence_reduces_to_polyAut
    {A Q₁ Q₂ X₁ X₂ : Type} [Finite Q₁] [Finite Q₂] [Fintype X₁] [Fintype X₂]
    (T₁ : CopyfulSST A Bool Q₁ X₁) (T₂ : CopyfulSST A Bool Q₂ X₂) :
    ∃ f₁ f₂ : List A → ℚ, IsPolyAut f₁ ∧ IsPolyAut f₂ ∧ (f₁ = f₂ ↔ T₁.eval = T₂.eval) := by
  refine ⟨T₁.encodeAut.eval, T₂.encodeAut.eval,
    ⟨Q₁, X₁ ⊕ X₁, inferInstance, inferInstance, T₁.encodeAut, rfl⟩,
    ⟨Q₂, X₂ ⊕ X₂, inferInstance, inferInstance, T₂.encodeAut, rfl⟩, ?_⟩
  constructor
  · intro h
    funext w
    have h1 := congrFun h w
    rw [T₁.encodeAut_eval, T₂.encodeAut_eval] at h1
    exact encodeOut_injective (Nat.cast_injective h1)
  · intro h
    funext w
    rw [T₁.encodeAut_eval, T₂.encodeAut_eval, congrFun h w]

end Transducers.Exercises
