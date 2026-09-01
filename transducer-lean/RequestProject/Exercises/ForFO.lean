/-
The exercise `exer:for-transducers-simulate-fo` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk).

A first-order sentence defining a language can be turned into a for-transducer,
of size linear in the size of the sentence, which outputs `yes` or `no`
according to whether the sentence holds in the input string.  This is exactly
the author's solution: quantifiers become for loops, the truth value of each
subformula is kept in a Boolean variable, the atomic tests of first-order logic
(order and label tests) are already available as tests of a for-transducer, and
the epilogue outputs `yes` or `no` depending on the Boolean variable of the
whole sentence.

The alphabet of outputs is `Bool`, with `true` for `yes` and `false` for `no`.
The size of a program is measured by `Transducers.Exercises.progSize`, the
number of nodes of its syntax tree, and the size of a formula by
`Transducers.Exercises.fsize`; the bound proved is `10 * fsize φ + 5`, which is
linear, as the solution claims.
-/
import RequestProject.PartC.MSODef
import RequestProject.PartD.ForDef

namespace Transducers
namespace Exercises

variable {A : Type}

/-! ## Sizes -/

/-- The number of nodes in the syntax tree of a test of a for-transducer. -/
def testSize : ForTest A → ℕ
  | .boolVar _ => 1
  | .eqPos _ _ => 1
  | .lePos _ _ => 1
  | .label _ _ => 1
  | .not t => testSize t + 1
  | .and t s => testSize t + testSize s + 1
  | .or t s => testSize t + testSize s + 1

/-- The number of nodes in the syntax tree of a program of a for-transducer;
this is the size of its source code. -/
def progSize {B : Type} : ForProg A B → ℕ
  | .skip => 1
  | .output _ => 1
  | .assign _ _ => 1
  | .seq P Q => progSize P + progSize Q + 1
  | .ite t P Q => testSize t + progSize P + progSize Q + 1
  | .loop _ _ P => progSize P + 1

/-- The number of nodes in the syntax tree of a formula. -/
def fsize : MSO A → ℕ
  | .le _ _ => 1
  | .lab _ _ => 1
  | .mem _ _ => 1
  | .not φ => fsize φ + 1
  | .and φ ψ => fsize φ + fsize ψ + 1
  | .or φ ψ => fsize φ + fsize ψ + 1
  | .exFO _ φ => fsize φ + 1
  | .exSO _ φ => fsize φ + 1

lemma fsize_pos (φ : MSO A) : 0 < fsize φ := by
  cases φ <;> simp [fsize]

/-! ## The translation -/

/-- The body of the loop that is used for an existential quantifier: run the
translation `P` of the subformula, which stores its truth value in the Boolean
variable `b + 1`, and, if it came out true, set the Boolean variable `b` of the
quantified formula to true. -/
def exBody {B : Type} (b : ℕ) (P : ForProg A B) : ForProg A B :=
  .seq P (.ite (.boolVar (b + 1)) (.assign b true) .skip)

/-- The translation of a formula into a for-transducer program.  The program
`trans φ b` stores the truth value of `φ` in the Boolean variable `b`, and only
touches the Boolean variables in `[b, b + fsize φ)`.  Position variables are
kept: the loop introduced for `∃ xᵢ` binds the position variable `i`.

On the two clauses of monadic second-order logic that are not first order — set
membership and set quantification — the translation is a dummy; the
specification `trans_spec` only speaks about first-order formulas. -/
def trans : MSO A → ℕ → ForProg A Bool
  | .le i j, b => .ite (.lePos i j) (.assign b true) (.assign b false)
  | .lab a i, b => .ite (.label i a) (.assign b true) (.assign b false)
  | .mem _ _, b => .assign b false
  | .not φ, b =>
      .seq (trans φ (b + 1))
        (.ite (.boolVar (b + 1)) (.assign b false) (.assign b true))
  | .and φ ψ, b =>
      .seq (.seq (trans φ (b + 1)) (trans ψ (b + 1 + fsize φ)))
        (.ite (.and (.boolVar (b + 1)) (.boolVar (b + 1 + fsize φ)))
          (.assign b true) (.assign b false))
  | .or φ ψ, b =>
      .seq (.seq (trans φ (b + 1)) (trans ψ (b + 1 + fsize φ)))
        (.ite (.or (.boolVar (b + 1)) (.boolVar (b + 1 + fsize φ)))
          (.assign b true) (.assign b false))
  | .exFO x φ, b =>
      .seq (.assign b false) (.loop true x (exBody b (trans φ (b + 1))))
  | .exSO _ _, b => .assign b false

/-- The translation is linear in the size of the formula. -/
lemma progSize_trans (φ : MSO A) : ∀ b, progSize (trans φ b) ≤ 10 * fsize φ := by
  induction φ with
  | le i j => intro b; simp [trans, progSize, testSize, fsize]
  | lab a i => intro b; simp [trans, progSize, testSize, fsize]
  | mem i j => intro b; simp [trans, progSize, fsize]
  | not φ ih =>
      intro b
      have := ih (b + 1)
      simp only [trans, progSize, testSize, fsize]
      omega
  | and φ ψ ihφ ihψ =>
      intro b
      have h1 := ihφ (b + 1)
      have h2 := ihψ (b + 1 + fsize φ)
      simp only [trans, progSize, testSize, fsize]
      omega
  | or φ ψ ihφ ihψ =>
      intro b
      have h1 := ihφ (b + 1)
      have h2 := ihψ (b + 1 + fsize φ)
      simp only [trans, progSize, testSize, fsize]
      omega
  | exFO x φ ih =>
      intro b
      have := ih (b + 1)
      simp only [trans, exBody, progSize, testSize, fsize]
      omega
  | exSO x φ _ =>
      intro b
      simp only [trans, progSize, fsize]
      omega

/-! ## Correctness of the translation -/

/-- **The specification of `trans`.**  For a first-order formula `φ`, the
program `trans φ b` produces no output, leaves every Boolean variable outside
`[b, b + fsize φ)` unchanged, and sets the Boolean variable `b` to the truth
value of `φ` under the current valuation of the position variables. -/
theorem trans_spec (w : List A) (so : ℕ → Set ℕ) (φ : MSO A) :
    ∀ (b : ℕ) (pos : ℕ → ℕ) (bv : ℕ → Bool), φ.IsFO →
      (ForProg.exec w (trans φ b) pos bv).2 = [] ∧
      ((ForProg.exec w (trans φ b) pos bv).1 b = true ↔ MSO.Sat w pos so φ) ∧
      (∀ m, (m < b ∨ b + fsize φ ≤ m) →
        (ForProg.exec w (trans φ b) pos bv).1 m = bv m) := by
  induction φ with
  | le i j =>
      intro b pos bv _
      by_cases h : pos i ≤ pos j
      · have hex : ForProg.exec w (trans (MSO.le (A := A) i j) b) pos bv
            = (Function.update bv b true, []) := by
          simp [trans, ForProg.exec, ForTest.Holds, h]
        refine ⟨by rw [hex], ?_, ?_⟩
        · rw [hex]; simp [MSO.Sat, h]
        · intro m hm
          simp only [fsize] at hm
          rw [hex]
          exact Function.update_of_ne (by omega) _ _
      · have hex : ForProg.exec w (trans (MSO.le (A := A) i j) b) pos bv
            = (Function.update bv b false, []) := by
          simp [trans, ForProg.exec, ForTest.Holds, h]
        refine ⟨by rw [hex], ?_, ?_⟩
        · rw [hex]; simp [MSO.Sat, h]
        · intro m hm
          simp only [fsize] at hm
          rw [hex]
          exact Function.update_of_ne (by omega) _ _
  | lab a i =>
      intro b pos bv _
      by_cases h : w[pos i]? = some a
      · have hex : ForProg.exec w (trans (MSO.lab (A := A) a i) b) pos bv
            = (Function.update bv b true, []) := by
          simp [trans, ForProg.exec, ForTest.Holds, h]
        refine ⟨by rw [hex], ?_, ?_⟩
        · rw [hex]; simp [MSO.Sat, h]
        · intro m hm
          simp only [fsize] at hm
          rw [hex]
          exact Function.update_of_ne (by omega) _ _
      · have hex : ForProg.exec w (trans (MSO.lab (A := A) a i) b) pos bv
            = (Function.update bv b false, []) := by
          simp [trans, ForProg.exec, ForTest.Holds, h]
        refine ⟨by rw [hex], ?_, ?_⟩
        · rw [hex]; simp [MSO.Sat, h]
        · intro m hm
          simp only [fsize] at hm
          rw [hex]
          exact Function.update_of_ne (by omega) _ _
  | mem i j => intro b pos bv hφ; exact absurd hφ (by simp [MSO.IsFO])
  | exSO x φ _ => intro b pos bv hφ; exact absurd hφ (by simp [MSO.IsFO])
  | not φ ih =>
      intro b pos bv hφ
      have hφ' : φ.IsFO := hφ
      obtain ⟨ho, hb, hu⟩ := ih (b + 1) pos bv hφ'
      set r := ForProg.exec w (trans φ (b + 1)) pos bv with hr
      by_cases h : r.1 (b + 1) = true
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr, ho, h]
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr, h, MSO.Sat, hb.1 h]
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr, h, if_pos]
          rw [Function.update_of_ne hmb]
          exact hu m (by omega)
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr, ho, h]
        · simp only [trans, ForProg.exec, ForTest.Holds, ← hr, if_neg h, MSO.Sat]
          simp only [Function.update_self, true_iff]
          exact fun hs => h (hb.2 hs)
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr, if_neg h]
          rw [Function.update_of_ne hmb]
          exact hu m (by omega)
  | and φ ψ ihφ ihψ =>
      intro b pos bv hφ
      obtain ⟨hφ1, hφ2⟩ := hφ
      obtain ⟨ho1, hb1, hu1⟩ := ihφ (b + 1) pos bv hφ1
      set r₁ := ForProg.exec w (trans φ (b + 1)) pos bv with hr₁
      obtain ⟨ho2, hb2, hu2⟩ := ihψ (b + 1 + fsize φ) pos r₁.1 hφ2
      set r₂ := ForProg.exec w (trans ψ (b + 1 + fsize φ)) pos r₁.1 with hr₂
      have hkeep : r₂.1 (b + 1) = r₁.1 (b + 1) :=
        hu2 (b + 1) (Or.inl (by have := fsize_pos φ; omega))
      have hbφ : r₂.1 (b + 1) = true ↔ MSO.Sat w pos so φ := by rw [hkeep]; exact hb1
      by_cases h : r₂.1 (b + 1) = true ∧ r₂.1 (b + 1 + fsize φ) = true
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, ho1, ho2, h]
        · simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_pos h]
          rw [Function.update_self]
          simp only [MSO.Sat]
          exact iff_of_true trivial ⟨hbφ.1 h.1, hb2.1 h.2⟩
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_pos h]
          rw [Function.update_of_ne hmb]
          rw [hu2 m (by have := fsize_pos ψ; omega)]
          exact hu1 m (by have := fsize_pos ψ; omega)
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, ho1, ho2, h]
        · simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_neg h]
          rw [Function.update_self]
          simp only [MSO.Sat]
          refine iff_of_false (by simp) ?_
          rintro ⟨s1, s2⟩
          exact h ⟨hbφ.2 s1, hb2.2 s2⟩
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_neg h]
          rw [Function.update_of_ne hmb]
          rw [hu2 m (by have := fsize_pos ψ; omega)]
          exact hu1 m (by have := fsize_pos ψ; omega)
  | or φ ψ ihφ ihψ =>
      intro b pos bv hφ
      obtain ⟨hφ1, hφ2⟩ := hφ
      obtain ⟨ho1, hb1, hu1⟩ := ihφ (b + 1) pos bv hφ1
      set r₁ := ForProg.exec w (trans φ (b + 1)) pos bv with hr₁
      obtain ⟨ho2, hb2, hu2⟩ := ihψ (b + 1 + fsize φ) pos r₁.1 hφ2
      set r₂ := ForProg.exec w (trans ψ (b + 1 + fsize φ)) pos r₁.1 with hr₂
      have hkeep : r₂.1 (b + 1) = r₁.1 (b + 1) :=
        hu2 (b + 1) (Or.inl (by have := fsize_pos φ; omega))
      have hbφ : r₂.1 (b + 1) = true ↔ MSO.Sat w pos so φ := by rw [hkeep]; exact hb1
      by_cases h : r₂.1 (b + 1) = true ∨ r₂.1 (b + 1 + fsize φ) = true
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, ho1, ho2, h]
        · simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_pos h]
          rw [Function.update_self]
          simp only [MSO.Sat]
          exact iff_of_true trivial (h.imp hbφ.1 hb2.1)
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_pos h]
          rw [Function.update_of_ne hmb]
          rw [hu2 m (by have := fsize_pos ψ; omega)]
          exact hu1 m (by have := fsize_pos ψ; omega)
      · refine ⟨?_, ?_, ?_⟩
        · simp [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, ho1, ho2, h]
        · simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_neg h]
          rw [Function.update_self]
          simp only [MSO.Sat]
          refine iff_of_false (by simp) ?_
          rintro (s1 | s1)
          · exact h (Or.inl (hbφ.2 s1))
          · exact h (Or.inr (hb2.2 s1))
        · intro m hm
          simp only [fsize] at hm
          have hmb : m ≠ b := by omega
          simp only [trans, ForProg.exec, ForTest.Holds, ← hr₁, ← hr₂, if_neg h]
          rw [Function.update_of_ne hmb]
          rw [hu2 m (by have := fsize_pos ψ; omega)]
          exact hu1 m (by have := fsize_pos ψ; omega)
  | exFO x φ ih =>
      intro b pos bv hφ
      have hφ' : φ.IsFO := hφ
      -- the body of the loop, as a function of the Boolean valuation and the position
      set F : (ℕ → Bool) → ℕ → (ℕ → Bool) × List Bool :=
        fun bv' p => ForProg.exec w (exBody b (trans φ (b + 1)))
          (Function.update pos x p) bv' with hF
      have hstep : ∀ (bv1 : ℕ → Bool) (p : ℕ),
          (F bv1 p).2 = [] ∧
          ((F bv1 p).1 b = true ↔
            (bv1 b = true ∨ MSO.Sat w (Function.update pos x p) so φ)) ∧
          (∀ m, (m < b ∨ b + fsize φ + 1 ≤ m) → (F bv1 p).1 m = bv1 m) := by
        intro bv1 p
        obtain ⟨ho, hb, hu⟩ := ih (b + 1) (Function.update pos x p) bv1 hφ'
        set s := ForProg.exec w (trans φ (b + 1)) (Function.update pos x p) bv1 with hs
        by_cases h : s.1 (b + 1) = true
        · refine ⟨?_, ?_, ?_⟩
          · simp [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, ho, h]
          · simp only [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, if_pos h,
              Function.update_self, true_iff]
            exact Or.inr (hb.1 h)
          · intro m hm
            have hmb : m ≠ b := by omega
            simp only [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, if_pos h]
            rw [Function.update_of_ne hmb]
            exact hu m (by omega)
        · refine ⟨?_, ?_, ?_⟩
          · simp [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, ho, h]
          · simp only [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, if_neg h]
            rw [hu b (Or.inl (by omega))]
            constructor
            · exact fun hh => Or.inl hh
            · rintro (hh | hh)
              · exact hh
              · exact absurd (hb.2 hh) h
          · intro m hm
            simp only [hF, exBody, ForProg.exec, ForTest.Holds, ← hs, if_neg h]
            exact hu m (by omega)
      have key : ∀ (ps : List ℕ) (bv1 : ℕ → Bool),
          (forLoopRun F ps bv1).2 = [] ∧
          ((forLoopRun F ps bv1).1 b = true ↔
            (bv1 b = true ∨ ∃ p ∈ ps, MSO.Sat w (Function.update pos x p) so φ)) ∧
          (∀ m, (m < b ∨ b + fsize φ + 1 ≤ m) →
            (forLoopRun F ps bv1).1 m = bv1 m) := by
        intro ps
        induction ps with
        | nil => intro bv1; simp [forLoopRun]
        | cons p ps ihps =>
            intro bv1
            obtain ⟨hs0, hs1, hs2⟩ := hstep bv1 p
            obtain ⟨ht0, ht1, ht2⟩ := ihps (F bv1 p).1
            refine ⟨?_, ?_, ?_⟩
            · simp [forLoopRun, hs0, ht0]
            · simp only [forLoopRun, ht1, hs1, List.mem_cons]
              constructor
              · rintro (h | ⟨q, hq, hsat⟩)
                · rcases h with h | h
                  · exact Or.inl h
                  · exact Or.inr ⟨p, Or.inl rfl, h⟩
                · exact Or.inr ⟨q, Or.inr hq, hsat⟩
              · rintro (h | ⟨q, hq | hq, hsat⟩)
                · exact Or.inl (Or.inl h)
                · subst hq; exact Or.inl (Or.inr hsat)
                · exact Or.inr ⟨q, hq, hsat⟩
            · intro m hm
              simp only [forLoopRun]
              rw [ht2 m hm, hs2 m hm]
      have hloop : ForProg.exec w (trans (MSO.exFO x φ) b) pos bv
          = forLoopRun F (List.range w.length) (Function.update bv b false) := by
        simp [trans, ForProg.exec, hF]
      refine ⟨?_, ?_, ?_⟩
      · rw [hloop]; exact (key _ _).1
      · rw [hloop, (key (List.range w.length) (Function.update bv b false)).2.1]
        simp only [MSO.Sat, Function.update_self, List.mem_range]
        constructor
        · rintro (h | ⟨p, hp, hsat⟩)
          · exact absurd h (by simp)
          · exact ⟨p, hp, hsat⟩
        · rintro ⟨p, hp, hsat⟩
          exact Or.inr ⟨p, hp, hsat⟩
      · intro m hm
        simp only [fsize] at hm
        have hmb : m ≠ b := by omega
        rw [hloop, (key (List.range w.length) (Function.update bv b false)).2.2 m (by omega)]
        exact Function.update_of_ne hmb _ _

/-! ## The exercise -/

/-- The program of the exercise: run the translation of `φ`, storing its truth
value in the Boolean variable `0`, and then output `yes` or `no`. -/
def foProg (φ : MSO A) : ForProg A Bool :=
  .seq (trans φ 0) (.ite (.boolVar 0) (.output true) (.output false))

/-- **Exercise `exer:for-transducers-simulate-fo`.**  A language defined by a
first-order sentence, viewed as a string-to-string function with outputs `yes`
(`true`) and `no` (`false`), is computed by a for-transducer whose source code
has size linear — in particular polynomial — in the size of the formula.

The valuation of the free variables is the default one; for a sentence, which
is what the exercise is about, satisfaction does not depend on it. -/
theorem exists_forProg_of_isFO (φ : MSO A) (hφ : φ.IsFO) :
    ∃ P : ForProg A Bool,
      (∀ w : List A, P.eval w = [true] ∨ P.eval w = [false]) ∧
      (∀ w : List A, P.eval w = [true] ↔ MSO.Sat w (fun _ => 0) (fun _ => ∅) φ) ∧
      progSize P ≤ 10 * fsize φ + 5 := by
  refine ⟨foProg φ, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨ho, hb, _⟩ := trans_spec w (fun _ => ∅) φ 0 (fun _ => 0) (fun _ => false) hφ
    by_cases h : (ForProg.exec w (trans φ 0) (fun _ => 0) (fun _ => false)).1 0 = true
    · exact Or.inl (by simp [ForProg.eval, foProg, ForProg.exec, ForTest.Holds, ho, h])
    · exact Or.inr (by simp [ForProg.eval, foProg, ForProg.exec, ForTest.Holds, ho, h])
  · intro w
    obtain ⟨ho, hb, _⟩ := trans_spec w (fun _ => ∅) φ 0 (fun _ => 0) (fun _ => false) hφ
    by_cases h : (ForProg.exec w (trans φ 0) (fun _ => 0) (fun _ => false)).1 0 = true
    · simp only [ForProg.eval, foProg, ForProg.exec, ForTest.Holds, ho, if_pos h,
        List.nil_append, true_iff]
      exact hb.1 h
    · simp only [ForProg.eval, foProg, ForProg.exec, ForTest.Holds, ho, if_neg h,
        List.nil_append]
      constructor
      · intro hcon; exact absurd hcon (by simp)
      · intro hsat; exact absurd (hb.2 hsat) h
  · have := progSize_trans φ 0
    simp only [foProg, progSize, testSize]
    omega

end Exercises
end Transducers
