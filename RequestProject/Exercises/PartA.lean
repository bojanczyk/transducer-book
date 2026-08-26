/-
The exercises of Part A of *Transducers* (M. Bojańczyk): the exercises of the sections
*Mealy machines* (`mealy.tex`) and *The Krohn-Rhodes Decomposition Theorem* (`krohn-rhodes.tex`).

Exercises are not numbered results of the book, so they are not listed in `THEOREMS.md`; they are
recorded in `EXERCISES.md` instead.  The exercises that carry a LaTeX `\label` are referred to by
that label, exactly as the numbered results are; those that do not are referred to by their position
in the chapter.

Each statement follows the exercise, and each proof follows the author's own solution, unless the
docstring says otherwise.
-/
import RequestProject.PartA
import RequestProject.PartC.Statements
import RequestProject.PartC.FOMealy

namespace Transducers

/-! ## Mealy machines (`mealy.tex`) -/

/-! ### Exercise `exer:letter-to-letter-not-mealy` -/

/-- **Exercise `exer:letter-to-letter-not-mealy`.**  A function that is continuous and
letter-to-letter but is not computed by a Mealy machine: the author's solution is string
reversal, whose continuity is Lemma `nolabel:lem-reverse-and-duplicate-continuous` of the book
(`Transducers.continuous_reverse`).  Reversal is not computed by a Mealy machine as soon as the
alphabet has two distinct letters, since the semantics of a Mealy machine is prefix preserving. -/
theorem reverse_continuous_lengthPreserving_not_mealy {A : Type} {a b : A} (hab : a ≠ b) :
    Continuous (List.reverse : List A → List A) ∧
      LengthPreserving (List.reverse : List A → List A) ∧
      ¬ IsMealy (List.reverse : List A → List A) := by
  refine ⟨continuous_reverse, fun w => by simp, ?_⟩
  rintro ⟨Q, hQ, M, hM⟩
  have h1 : M.eval [a] <+: M.eval [a, b] := M.eval_prefix ⟨[b], rfl⟩
  rw [hM] at h1
  simp at h1
  exact hab h1

/-! ### Exercise `exer:composition-needs-many-states` -/

/-- `MealyChain s k A B f` says that `f : A* → B*` is a composition of `k` Mealy machines, each
one with at most `s` states.  The machines are applied from left to right, as in the book. -/
inductive MealyChain (s : ℕ) : ℕ → ∀ (A B : Type), (List A → List B) → Prop
  | nil (A : Type) : MealyChain s 0 A A _root_.id
  | cons {A B C : Type} {Q : Type} [Finite Q] (M : Mealy A B Q) (hQ : Nat.card Q ≤ s)
      {k : ℕ} {g : List B → List C} :
      MealyChain s k B C g → MealyChain s (k + 1) A C (g ∘ M.eval)

/-- The two-state machine of the binary counter: its state is the parity of the number of marks
seen so far, and it marks every second mark of its input. -/
def toggleM : Mealy Bool Bool Bool := ⟨false, fun s b => (xor s b, b && s)⟩

lemma toggleM_step_true (s : Bool) : toggleM.step s true = (!s, s) := by cases s <;> rfl

lemma toggleM_step_false (s : Bool) : toggleM.step s false = (s, false) := by cases s <;> rfl

/-- The word of length `m` which marks the positions `i0 + 1, i0 + 2, …` that are divisible by
`d`. -/
def divListFrom (d i0 m : ℕ) : List Bool :=
  (List.range m).map (fun i => decide (d ∣ (i0 + i + 1)))

lemma divListFrom_succ (d i0 m : ℕ) :
    divListFrom d i0 (m + 1) = decide (d ∣ (i0 + 1)) :: divListFrom d (i0 + 1) m := by
  simp [divListFrom, List.range_succ_eq_map]
  intro a _
  rw [show i0 + (a + 1) + 1 = i0 + 1 + a + 1 from by omega]

@[simp] lemma divListFrom_zero (d i0 : ℕ) : divListFrom d i0 0 = [] := by simp [divListFrom]

lemma divListFrom_getLast (d m : ℕ) :
    (divListFrom d 0 (m + 1)).getLast? = some (decide (d ∣ (m + 1))) := by
  simp [divListFrom, List.range_succ]

/-- A position divisible by `d` is divisible by `2 * d` exactly when the number of positions
divisible by `d` before it is odd. -/
lemma div_two_dvd (d i0 : ℕ) (hd : 0 < d) (hdvd : d ∣ i0 + 1) :
    (2 * d ∣ i0 + 1) ↔ (i0 / d) % 2 = 1 := by
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc0
  simp only [Nat.succ_eq_add_one] at hc
  have hexp : d * (c' + 1) = d * c' + d := by ring
  have hi0 : i0 = d * c' + (d - 1) := by omega
  have hdiv : i0 / d = c' := by
    rw [hi0, Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega)]
    omega
  rw [hdiv, hc, show 2 * d = d * 2 from by ring, mul_dvd_mul_iff_left (by omega : d ≠ 0)]
  omega

/-- Running `Transducers.toggleM` on the marks of the multiples of `d` produces the marks of the
multiples of `2 * d`. -/
lemma toggle_run (d : ℕ) (hd : 0 < d) (m i0 : ℕ) :
    toggleM.run (decide ((i0 / d) % 2 = 1)) (divListFrom d i0 m) = divListFrom (2 * d) i0 m := by
  induction m generalizing i0 with
  | zero => simp
  | succ m ih =>
      rw [divListFrom_succ, divListFrom_succ]
      by_cases h : d ∣ i0 + 1
      · have hsd : (i0 + 1) / d = i0 / d + 1 := by rw [Nat.succ_div]; simp [h]
        simp only [h, decide_true, Mealy.run_cons, toggleM_step_true]
        congr 1
        · exact (decide_eq_decide.mpr (div_two_dvd d i0 hd h)).symm
        · have hnext : (!decide ((i0 / d) % 2 = 1)) = decide (((i0 + 1) / d) % 2 = 1) := by
            rw [hsd]
            have : i0 / d % 2 = 0 ∨ i0 / d % 2 = 1 := by omega
            rcases this with h' | h' <;> simp [h', Nat.add_mod]
          rw [hnext]
          exact ih (i0 + 1)
      · have h2 : ¬ (2 * d ∣ i0 + 1) := fun hh => h (dvd_trans ⟨2, by ring⟩ hh)
        have hsd : (i0 + 1) / d = i0 / d := by rw [Nat.succ_div]; simp [h]
        simp only [h, h2, decide_false, Mealy.run_cons, toggleM_step_false]
        congr 1
        rw [← hsd]
        exact ih (i0 + 1)

lemma toggle_eval (d : ℕ) (hd : 0 < d) (m : ℕ) :
    toggleM.eval (divListFrom d 0 m) = divListFrom (2 * d) 0 m := by
  have := toggle_run d hd m 0
  simpa [Mealy.eval, toggleM, Nat.zero_div] using this

/-- After `n` copies of `Transducers.toggleM`, the word `trueⁿ` becomes the word marking the
positions divisible by `2ⁿ`. -/
lemma toggle_iterate (n m : ℕ) :
    (toggleM.eval)^[n] (List.replicate m true) = divListFrom (2 ^ n) 0 m := by
  induction n with
  | zero => simp [divListFrom]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, toggle_eval _ (Nat.two_pow_pos n), ← pow_succ']

lemma toggleChain (n : ℕ) : MealyChain 2 n Bool Bool (toggleM.eval)^[n] := by
  induction n with
  | zero => exact MealyChain.nil Bool
  | succ n ih =>
      rw [Function.iterate_succ]
      exact MealyChain.cons toggleM (by simp) ih

/-- **Exercise `exer:composition-needs-many-states`.**  A composition of `n` Mealy machines, each
one with at most `n` states, may require a number of states that is exponential in `n`: for every
`n` there is a composition of `n` Mealy machines with two states each which is not computed by any
Mealy machine with fewer than `2 ^ n` states.

The construction is a binary counter, and not the one of the author's solution, which uses the
first `n` prime numbers `p₁ < ⋯ < pₙ` and marks the positions divisible by `pᵢ` in the `i`-th
machine: there the `i`-th machine has `pᵢ` states, so that the resulting lower bound
`p₁ ⋯ pₙ` is exponential in the *number* of machines but not in the number `pₙ` of their states
unless one invokes Chebyshev-type bounds on the primorial.  The counter below marks the positions
divisible by `2ⁱ` and gets the same lower bound with two states per machine; the argument for the
lower bound is the one of the author's solution: the shortest input producing an output letter with
all bits set has length `2ⁿ`. -/
theorem mealy_composition_state_blowup (n : ℕ) :
    ∃ f : List Bool → List Bool,
      MealyChain 2 n Bool Bool f ∧
        ∀ (Q : Type) (_ : Finite Q) (M : Mealy Bool Bool Q), M.eval = f → 2 ^ n ≤ Nat.card Q := by
  refine ⟨(toggleM.eval)^[n], toggleChain n, ?_⟩
  intro Q hQ M hM
  set N := 2 ^ n with hN
  have hNpos : 0 < N := Nat.two_pow_pos n
  have hlast : ∀ m : ℕ, (M.eval (List.replicate (m + 1) true)).getLast? =
      some (decide (N ∣ (m + 1))) := by
    intro m
    rw [hM, toggle_iterate, divListFrom_getLast]
  have hlast' : ∀ m : ℕ, 0 < m →
      (M.eval (List.replicate m true)).getLast? = some (decide (N ∣ m)) := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact hlast m'
  have hsplit : ∀ i k : ℕ, 0 < k →
      (M.eval (List.replicate (i + k) true)).getLast? =
        (M.run (M.trans (List.replicate i true) M.init) (List.replicate k true)).getLast? := by
    intro i k hk
    rw [List.replicate_add, Mealy.eval_append]
    refine List.getLast?_append_of_ne_nil _ ?_
    have hlen : (M.run (M.trans (List.replicate i true) M.init) (List.replicate k true)).length
        = k := by simp
    intro hc
    rw [hc] at hlen
    simp at hlen
    omega
  -- the states reached by `trueⁱ` for `i < 2ⁿ` are pairwise distinct
  have key : ∀ i j : ℕ, i < j → j < N →
      M.trans (List.replicate i true) M.init ≠ M.trans (List.replicate j true) M.init := by
    intro i j hij hjN heq
    obtain ⟨k, hk, hjk⟩ : ∃ k, 0 < k ∧ j + k = N := ⟨N - j, by omega, by omega⟩
    have h1 := hsplit i k hk
    have h2 := hsplit j k hk
    rw [heq] at h1
    have hcomb : (M.eval (List.replicate (i + k) true)).getLast? =
        (M.eval (List.replicate N true)).getLast? := by rw [h1, ← h2, hjk]
    rw [hlast' _ (by omega), hlast' _ hNpos] at hcomb
    have hnd : ¬ N ∣ (i + k) := fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega
    simp [hnd] at hcomb
  have hinj :
      Function.Injective (fun i : Fin N => M.trans (List.replicate (i : ℕ) true) M.init) := by
    intro i j hij
    by_cases h : (i : ℕ) = (j : ℕ)
    · exact Fin.ext h
    · rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt | hge
      · exact absurd hij (key i j hlt j.isLt)
      · exact absurd hij.symm (key j i (by omega) i.isLt)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

/-! ### Exercise `exer:invertible` -/

namespace Mealy

variable {A Q : Type}

/-- A Mealy machine `f : A* → A*` is *invertible* if some Mealy machine `f⁻¹ : A* → A*` satisfies
`f · f⁻¹ = id` (Exercise `exer:invertible`). -/
def Invertible (M : Mealy A A Q) : Prop :=
  ∃ (P : Type) (_ : Finite P) (N : Mealy A A P), N.eval ∘ M.eval = id

/-- All the states of a Mealy machine are reachable from the initial state. -/
def AllReachable (M : Mealy A A Q) : Prop := ∀ q : Q, ∃ w : List A, M.trans w M.init = q

end Mealy

/-- **Exercise `exer:invertible`, the criterion.**  A Mealy machine all of whose states are
reachable is invertible if and only if, in every state, the output letters of the outgoing
transitions are a bijective function of the input letter.  This is condition (*) of the author's
solution, which also assumes that all states are reachable. -/
theorem mealy_invertible_iff {A Q : Type} [Finite A] [Finite Q] (M : Mealy A A Q)
    (hreach : M.AllReachable) :
    M.Invertible ↔ ∀ q : Q, Function.Bijective (fun a : A => (M.step q a).2) := by
  classical
  constructor
  · rintro ⟨P, hP, N, hN⟩ q
    obtain ⟨w, hw⟩ := hreach q
    rw [← Finite.injective_iff_bijective]
    intro x y hxy
    have hx : M.eval (w ++ [x]) = M.eval (w ++ [y]) := by
      rw [M.eval_append, M.eval_append, hw]
      simpa [Mealy.run] using hxy
    have h2 := congrFun hN (w ++ [x])
    rw [Function.comp_apply, hx, ← Function.comp_apply (f := N.eval), hN] at h2
    simpa using h2.symm
  · intro hbij
    set st : Q → A → Q × A := fun q b =>
      ((M.step q (Function.surjInv (hbij q).2 b)).1, Function.surjInv (hbij q).2 b) with hst
    have key : ∀ (q : Q) (w : List A), Mealy.run ⟨M.init, st⟩ q (M.run q w) = w := by
      intro q w
      induction w generalizing q with
      | nil => rfl
      | cons a w ih =>
          have hinv : Function.surjInv (hbij q).2 ((M.step q a).2) = a :=
            (hbij q).1 (Function.surjInv_eq (hbij q).2 _)
          show (st q (M.step q a).2).2 :: Mealy.run ⟨M.init, st⟩ (st q (M.step q a).2).1 _ = _
          rw [hst]
          simp only [hinv]
          exact congrArg _ (ih _)
    exact ⟨Q, inferInstance, ⟨M.init, st⟩, funext fun w => key M.init w⟩

/-- **Exercise `exer:invertible`, decidability.**  Invertibility of a Mealy machine all of whose
states are reachable is decidable: the criterion of `Transducers.mealy_invertible_iff` is a finite
check. -/
def decidableInvertible {A Q : Type} [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    (M : Mealy A A Q) (hreach : M.AllReachable) : Decidable M.Invertible :=
  decidable_of_iff _ (mealy_invertible_iff M hreach).symm

/-! ### Exercise `exer:invertible-mealy-group` -/

/-- The machine of the author's solution to Exercise `exer:invertible-mealy-group`: it adds one to
a binary number, written with the least significant bit first.  Its state records whether a carry
is pending. -/
def addOne : Mealy Bool Bool Bool := ⟨true, fun s b => (b && s, xor b s)⟩

/-- The `n` low bits of a natural number, least significant bit first. -/
def bits (n x : ℕ) : List Bool := (List.range n).map (fun i => x.testBit i)

lemma bits_succ (n x : ℕ) : bits (n + 1) x = x.testBit 0 :: bits n (x / 2) := by
  simp [bits, List.range_succ_eq_map, Nat.testBit_succ]

lemma addOne_run_false (l : List Bool) : addOne.run false l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [addOne, Mealy.run] using ih

lemma addOne_run_true (n x : ℕ) : addOne.run true (bits n x) = bits n (x + 1) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [bits_succ, bits_succ]
      have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
      have hb : (x + 1).testBit 0 = !x.testBit 0 := by
        rcases hmod with h | h <;> simp [Nat.testBit_zero, h, Nat.add_mod]
      show (addOne.step true (x.testBit 0)).2 :: addOne.run (addOne.step true (x.testBit 0)).1 _ = _
      rw [hb]
      cases hx : x.testBit 0 with
      | true =>
          have hd : (x + 1) / 2 = x / 2 + 1 := by
            have : x % 2 = 1 := by simpa [Nat.testBit_zero] using hx
            omega
          rw [hd]
          show (true ^^ true) :: addOne.run (true && true) (bits n (x / 2)) = _
          simpa using ih (x / 2)
      | false =>
          have hd : (x + 1) / 2 = x / 2 := by
            have h0 : x % 2 = 0 := by
              have hx' := hx
              simp [Nat.testBit_zero] at hx'
              omega
            omega
          rw [hd]
          show (false ^^ true) :: addOne.run (false && true) (bits n (x / 2)) = _
          simpa using addOne_run_false (bits n (x / 2))

lemma addOne_eval_bits (n x : ℕ) : addOne.eval (bits n x) = bits n (x + 1) := addOne_run_true n x

lemma addOne_iterate_bits (n k : ℕ) : (addOne.eval)^[k] (bits n 0) = bits n k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, addOne_eval_bits]

lemma bits_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : bits n x = bits n y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have h2 := congrArg (fun l => l[i]?) h
    simpa [bits, List.getElem?_map, hi] using h2
  · rw [Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Exercise `exer:invertible-mealy-group`.**  The subgroup of the group of invertible Mealy
machines generated by a finite set of generators need not be finite: already a single invertible
Mealy machine can generate an infinite subgroup.  The machine of the author's solution adds one to
a binary number modulo `2ⁿ`; here binary numbers are written with the least significant bit first,
so that the carry travels from left to right and the machine has two states.  Its powers are
pairwise distinct, and hence the group that it generates is infinite. -/
theorem exists_invertible_mealy_infinite_order :
    ∃ (Q : Type) (_ : Finite Q) (M : Mealy Bool Bool Q),
      M.Invertible ∧ Function.Injective (fun n : ℕ => (M.eval)^[n]) := by
  have hreach : addOne.AllReachable := by
    intro q
    cases q with
    | false => exact ⟨[false], rfl⟩
    | true => exact ⟨[], rfl⟩
  refine ⟨Bool, inferInstance, addOne, (mealy_invertible_iff addOne hreach).2 (by decide), ?_⟩
  intro m k h
  have h2 := congrFun h (bits (m + k + 1) 0)
  simp only [addOne_iterate_bits] at h2
  have hm : m < 2 ^ (m + k + 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hk : k < 2 ^ (m + k + 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact bits_inj hm hk h2

/-! ### Exercise `exer:polynomial-image-growth-decidable` -/

/-- The growth of the image of a string-to-string function: the number of outputs on inputs of
length at most `n`. -/
noncomputable def imageGrowth {A B : Type} (f : List A → List B) (n : ℕ) : ℕ :=
  Nat.card {v : List B | ∃ w : List A, w.length ≤ n ∧ f w = v}

/-- A function `ℕ → ℕ` is bounded by a polynomial. -/
def PolyBounded (g : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n : ℕ, g n ≤ c * (n + 1) ^ d

/-- Condition (*) of the author's solution to Exercise `exer:polynomial-image-growth-decidable`,
transported from the automaton for the image language back to the Mealy machine: there is a
reachable state with two cycles of the same length whose outputs differ. -/
def Mealy.AmbiguousCycle {A B Q : Type} (M : Mealy A B Q) : Prop :=
  ∃ (q : Q) (u v : List A), (∃ z : List A, M.trans z M.init = q) ∧ u.length = v.length ∧
    M.trans u q = q ∧ M.trans v q = q ∧ M.run q u ≠ M.run q v

/-! The two directions of the criterion.  For the exponential lower bound, the two cycles are
combined into `2ᵐ` different inputs of the same length. -/

/-- The input word obtained by concatenating copies of the two words `u` and `v`, following a
sequence of bits. -/
def cycleWord {A : Type} (u v : List A) : List Bool → List A
  | [] => []
  | b :: s => (if b then u else v) ++ cycleWord u v s

@[simp] lemma cycleWord_nil {A : Type} (u v : List A) : cycleWord u v [] = [] := rfl

lemma cycleWord_cons {A : Type} (u v : List A) (b : Bool) (s : List Bool) :
    cycleWord u v (b :: s) = (if b then u else v) ++ cycleWord u v s := rfl

@[simp] lemma cycleWord_cons_true {A : Type} (u v : List A) (s : List Bool) :
    cycleWord u v (true :: s) = u ++ cycleWord u v s := rfl

@[simp] lemma cycleWord_cons_false {A : Type} (u v : List A) (s : List Bool) :
    cycleWord u v (false :: s) = v ++ cycleWord u v s := rfl

lemma cycleWord_length {A : Type} {u v : List A} (h : u.length = v.length) (s : List Bool) :
    (cycleWord u v s).length = s.length * u.length := by
  induction s with
  | nil => simp
  | cons b s ih => cases b <;> simp [ih, h] <;> ring

lemma cycleWord_run {A B Q : Type} {M : Mealy A B Q} {q : Q} {u v : List A}
    (hu : M.trans u q = q) (hv : M.trans v q = q) (s : List Bool) :
    M.run q (cycleWord u v s) = cycleWord (M.run q u) (M.run q v) s := by
  induction s with
  | nil => simp
  | cons b s ih =>
      cases b
      · rw [cycleWord_cons_false, M.run_append, hv, ih, cycleWord_cons_false]
      · rw [cycleWord_cons_true, M.run_append, hu, ih, cycleWord_cons_true]

lemma cycleWord_trans {A B Q : Type} {M : Mealy A B Q} {q : Q} {u v : List A}
    (hu : M.trans u q = q) (hv : M.trans v q = q) (s : List Bool) :
    M.trans (cycleWord u v s) q = q := by
  induction s with
  | nil => simp
  | cons b s ih =>
      cases b
      · rw [cycleWord_cons_false, M.trans_append, hv, ih]
      · rw [cycleWord_cons_true, M.trans_append, hu, ih]

lemma cycleWord_injective {A : Type} {u v : List A} (hlen : u.length = v.length)
    (hpos : 0 < u.length) (hne : u ≠ v) : Function.Injective (cycleWord u v) := by
  intro s
  induction s with
  | nil =>
      intro s' h
      cases s' with
      | nil => rfl
      | cons b t =>
          exfalso
          have hc := congrArg List.length h
          rw [cycleWord_length hlen, cycleWord_length hlen] at hc
          simp only [List.length_nil, List.length_cons, Nat.zero_mul] at hc
          rcases Nat.mul_eq_zero.mp hc.symm with h' | h' <;> omega
  | cons b t ih =>
      intro s' h
      cases s' with
      | nil =>
          exfalso
          have hc := congrArg List.length h
          rw [cycleWord_length hlen, cycleWord_length hlen] at hc
          simp only [List.length_nil, List.length_cons, Nat.zero_mul] at hc
          rcases Nat.mul_eq_zero.mp hc with h' | h' <;> omega
      | cons b' t' =>
          rw [cycleWord_cons, cycleWord_cons] at h
          have hl : (if b then u else v).length = (if b' then u else v).length := by
            cases b <;> cases b' <;> simp [hlen]
          obtain ⟨h1, h2⟩ := List.append_inj h hl
          have hbb : b = b' := by
            cases b <;> cases b' <;> simp at h1 ⊢
            · exact hne h1.symm
            · exact hne h1
          subst hbb
          exact congrArg _ (ih h2)

/-- An exponential eventually overtakes any polynomial. -/
lemma exists_poly_lt_two_pow (C d : ℕ) : ∃ m : ℕ, 1 ≤ m ∧ C * m ^ d < 2 ^ m := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (r := 2) (by norm_num)).def
    (c := 1 / (C + 1)) (by positivity)
  obtain ⟨m, hm1, hm⟩ := (h.and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨m, hm, ?_⟩
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ d),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)] at hm1
  have hC : (0 : ℝ) < C + 1 := by positivity
  have key : ((C : ℝ) + 1) * (m : ℝ) ^ d ≤ 2 ^ m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hC] at hm1
    linarith [hm1]
  have hmd : (1 : ℝ) ≤ (m : ℝ) ^ d := one_le_pow₀ hmr
  have : (C : ℝ) * (m : ℝ) ^ d < 2 ^ m := by nlinarith
  exact_mod_cast this

/-- If a Mealy machine has two cycles of the same length and different outputs around a common
reachable state, then its image grows exponentially, hence not polynomially. -/
theorem imageGrowth_not_polyBounded_of_ambiguousCycle {A B Q : Type} [Finite A]
    (M : Mealy A B Q) (h : M.AmbiguousCycle) : ¬ PolyBounded (imageGrowth M.eval) := by
  obtain ⟨q, u, v, ⟨z, hz⟩, hlen, hu, hv, hne⟩ := h
  have hposu : 0 < u.length := by
    rcases Nat.eq_zero_or_pos u.length with h0 | h0
    · exfalso
      have hu0 : u = [] := List.length_eq_zero_iff.mp h0
      have hv0 : v = [] := List.length_eq_zero_iff.mp (by omega)
      exact hne (by rw [hu0, hv0])
    · exact h0
  have hrlen : (M.run q u).length = (M.run q v).length := by simp [hlen]
  have hrpos : 0 < (M.run q u).length := by simpa using hposu
  have hlb : ∀ m : ℕ, 2 ^ m ≤ imageGrowth M.eval (z.length + m * u.length) := by
    intro m
    set n := z.length + m * u.length with hn
    set S : Set (List B) := {y : List B | ∃ w : List A, w.length ≤ n ∧ M.eval w = y} with hS
    have hset : S = M.eval '' {w : List A | w.length ≤ n} := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
    have hfin : S.Finite := by rw [hset]; exact (List.finite_length_le A n).image _
    haveI : Finite S := hfin.to_subtype
    have hmem : ∀ s : Fin m → Bool, M.eval (z ++ cycleWord u v (List.ofFn s)) ∈ S :=
      fun s => ⟨_, by simp [cycleWord_length hlen, hn], rfl⟩
    have hinj : Function.Injective
        (fun s : Fin m → Bool => (⟨M.eval (z ++ cycleWord u v (List.ofFn s)), hmem s⟩ : S)) := by
      intro s s' hss
      have h1 : M.eval (z ++ cycleWord u v (List.ofFn s))
          = M.eval (z ++ cycleWord u v (List.ofFn s')) := congrArg Subtype.val hss
      rw [M.eval_append, M.eval_append, hz, cycleWord_run hu hv, cycleWord_run hu hv] at h1
      exact List.ofFn_injective (cycleWord_injective hrlen hrpos hne (List.append_cancel_left h1))
    have hcard : Nat.card (Fin m → Bool) = 2 ^ m := by simp [Nat.card_eq_fintype_card]
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [hcard] at hle
  rintro ⟨c, d, hcd⟩
  obtain ⟨m, hm1, hm⟩ := exists_poly_lt_two_pow (c * (z.length + u.length + 1) ^ d) d
  have h1 := hlb m
  have h2 := hcd (z.length + m * u.length)
  have h3 : z.length + m * u.length + 1 ≤ (z.length + u.length + 1) * m := by
    have : z.length * 1 ≤ z.length * m := Nat.mul_le_mul_left _ hm1
    nlinarith
  have h4 : c * (z.length + m * u.length + 1) ^ d ≤ c * ((z.length + u.length + 1) * m) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 d)
  have h5 : c * ((z.length + u.length + 1) * m) ^ d
      = c * (z.length + u.length + 1) ^ d * m ^ d := by rw [mul_pow, ← mul_assoc]
  omega

namespace Mealy

variable {A B Q : Type}

/-- `M.Reach q r` says that the state `r` is reachable from the state `q`. -/
def Reach (M : Mealy A B Q) (q r : Q) : Prop := ∃ w : List A, M.trans w q = r

lemma reach_refl (M : Mealy A B Q) (q : Q) : M.Reach q q := ⟨[], rfl⟩

lemma reach_word (M : Mealy A B Q) (q : Q) (w : List A) : M.Reach q (M.trans w q) := ⟨w, rfl⟩

lemma reach_step (M : Mealy A B Q) (q : Q) (a : A) : M.Reach q (M.transFun q a) := ⟨[a], rfl⟩

lemma reach_trans {M : Mealy A B Q} {q r s : Q} (h1 : M.Reach q r) (h2 : M.Reach r s) :
    M.Reach q s := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  exact ⟨u ++ v, by rw [M.trans_append, hu, hv]⟩

/-- The set of states reachable from `q`. -/
def reachSet (M : Mealy A B Q) (q : Q) : Set Q := {r | M.Reach q r}

lemma reachSet_subset {M : Mealy A B Q} {q r : Q} (h : M.Reach q r) :
    M.reachSet r ⊆ M.reachSet q := fun _ hs => reach_trans h hs

/-- Leaving the region of states that can come back to `q` strictly decreases the number of
reachable states. -/
lemma reachSet_card_lt [Finite Q] {M : Mealy A B Q} {q r : Q} (h : M.Reach q r)
    (hn : ¬ M.Reach r q) : Nat.card (M.reachSet r) < Nat.card (M.reachSet q) := by
  have hsub : M.reachSet r ⊆ M.reachSet q := reachSet_subset h
  have hne : M.reachSet r ≠ M.reachSet q := by
    intro he
    have hq : q ∈ M.reachSet q := reach_refl M q
    rw [← he] at hq
    exact hn hq
  exact Set.ncard_lt_ncard ⟨hsub, fun hc => hne (subset_antisymm hsub hc)⟩ (Set.toFinite _)

lemma one_le_reachSet_card [Finite Q] (M : Mealy A B Q) (q : Q) :
    1 ≤ Nat.card (M.reachSet q) := by
  haveI : Nonempty (M.reachSet q) := ⟨⟨q, reach_refl M q⟩⟩
  have hne : (M.reachSet q).ncard ≠ 0 := by
    rw [Ne, Set.ncard_eq_zero (Set.toFinite _)]
    exact (Set.nonempty_coe_sort.mp ‹Nonempty (M.reachSet q)›).ne_empty
  exact Nat.one_le_iff_ne_zero.2 hne

lemma reachSet_card_le [Finite Q] (M : Mealy A B Q) (q : Q) :
    Nat.card (M.reachSet q) ≤ Nat.card Q :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- If the machine has no ambiguous cycle, then the output produced along a path is determined by
the starting state, the ending state and the length, provided the starting state is reachable from
the initial state and the ending state can come back to it. -/
lemma run_eq_of_no_ambiguousCycle {M : Mealy A B Q} (h : ¬ M.AmbiguousCycle) {p q : Q}
    (hp : M.Reach M.init p) (hback : M.Reach q p) {u v : List A} (hlen : u.length = v.length)
    (hu : M.trans u p = q) (hv : M.trans v p = q) : M.run p u = M.run p v := by
  by_contra hne
  obtain ⟨w, hw⟩ := hback
  refine h ⟨p, u ++ w, v ++ w, hp, by simp [hlen], ?_, ?_, ?_⟩
  · rw [M.trans_append, hu, hw]
  · rw [M.trans_append, hv, hw]
  · rw [M.run_append, M.run_append, hu, hv]
    intro hc
    exact hne (List.append_inj_left hc (by simp [hlen]))

/-- Either the whole run from `q` stays among the states which can come back to `p`, or it leaves
that region at a first position. -/
lemma reach_split {M : Mealy A B Q} (p : Q) :
    ∀ (w : List A) (q : Q), M.Reach q p →
      M.Reach (M.trans w q) p ∨
        (∃ (u : List A) (a : A) (z : List A), w = u ++ a :: z ∧ M.Reach (M.trans u q) p ∧
          ¬ M.Reach (M.transFun (M.trans u q) a) p) := by
  intro w
  induction w with
  | nil => intro q hq; exact Or.inl (by simpa using hq)
  | cons a w ih =>
      intro q hq
      by_cases hc : M.Reach (M.transFun q a) p
      · rcases ih (M.transFun q a) hc with hl | ⟨u, a2, z, hw, h1, h2⟩
        · left
          rw [M.trans_cons]
          exact hl
        · right
          refine ⟨a :: u, a2, z, by simp [hw], ?_, ?_⟩
          · rw [M.trans_cons]; exact h1
          · rw [M.trans_cons]; exact h2
      · exact Or.inr ⟨[], a, w, rfl, by simpa using hq, by simpa using hc⟩

open Classical in
/-- The outputs of the runs of length at most `n` which start in a reachable state `p` are covered
by a finite set whose size is polynomial in `n`; the degree is governed by the number of states
reachable from `p`.  This is the counting behind the author's argument on the directed acyclic
graph of strongly connected components. -/
lemma exists_cover [Finite A] [Finite Q] {M : Mealy A B Q} (h : ¬ M.AmbiguousCycle) (n : ℕ) :
    ∀ (k : ℕ) (p : Q), M.Reach M.init p → Nat.card (M.reachSet p) ≤ k →
      ∃ S : Finset (List B),
        S.card ≤ ((n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) + 1) ^ (2 * k + 2) ∧
          ∀ w : List A, w.length ≤ n → M.run p w ∈ S := by
  set C := (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) + 1 with hC
  have hC2 : 2 ≤ C := by
    have : 1 ≤ (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hCb1 : (n + 1) * Nat.card Q ≤ C := by
    rw [hC]
    have h1 : (n + 1) * Nat.card Q ≤ (n + 1) * (Nat.card Q + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (n + 1) * (Nat.card Q + 1) ≤ (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hCb2 : (n + 1) * Nat.card Q * Nat.card A ≤ C := by
    rw [hC]
    have h1 : (n + 1) * Nat.card Q * Nat.card A
        ≤ (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  intro k
  induction k with
  | zero =>
      intro p _ hk
      exact absurd (one_le_reachSet_card M p) (by omega)
  | succ k ih =>
      intro p hp hk
      letI : Fintype Q := Fintype.ofFinite Q
      letI : Fintype A := Fintype.ofFinite A
      -- the outputs of the runs that can come back, determined by the length and the endpoint
      have hchoice : ∀ x : ℕ × Q, ∃ y : List B, ∀ w : List A, w.length = x.1 →
          M.trans w p = x.2 → M.Reach x.2 p → M.run p w = y := by
        intro x
        by_cases hx : ∃ w : List A, w.length = x.1 ∧ M.trans w p = x.2 ∧ M.Reach x.2 p
        · obtain ⟨w0, h1, h2, h3⟩ := hx
          exact ⟨M.run p w0, fun w hw1 hw2 _ =>
            run_eq_of_no_ambiguousCycle h hp h3 (by omega) hw2 h2⟩
        · exact ⟨[], fun w hw1 hw2 hw3 => absurd ⟨w, hw1, hw2, hw3⟩ hx⟩
      choose f0 hf0 using hchoice
      set S0 : Finset (List B) := (Finset.univ : Finset (Fin (n + 1) × Q)).image
        (fun x => f0 ((x.1 : ℕ), x.2)) with hS0
      have hS0card : S0.card ≤ (n + 1) * Nat.card Q := by
        refine le_trans Finset.card_image_le ?_
        simp [Nat.card_eq_fintype_card]
      have hS0mem : ∀ w : List A, w.length ≤ n → M.Reach (M.trans w p) p → M.run p w ∈ S0 := by
        intro w hw hr
        rw [hf0 (w.length, M.trans w p) w rfl rfl hr, hS0]
        exact Finset.mem_image.2 ⟨(⟨w.length, by omega⟩, M.trans w p), Finset.mem_univ _, rfl⟩
      -- the covers for the states outside the region, given by the induction hypothesis
      have hfam : ∀ x : Q × A, ∃ T : Finset (List B), T.card ≤ C ^ (2 * k + 2) ∧
          ((M.Reach M.init (M.transFun x.1 x.2) ∧
              Nat.card (M.reachSet (M.transFun x.1 x.2)) ≤ k) →
            ∀ z : List A, z.length ≤ n → M.run (M.transFun x.1 x.2) z ∈ T) := by
        intro x
        by_cases hx : M.Reach M.init (M.transFun x.1 x.2) ∧
            Nat.card (M.reachSet (M.transFun x.1 x.2)) ≤ k
        · obtain ⟨T, hT1, hT2⟩ := ih _ hx.1 hx.2
          exact ⟨T, hT1, fun _ => hT2⟩
        · exact ⟨∅, by simp, fun hc => absurd hc hx⟩
      choose T hT1 hT2 using hfam
      refine ⟨S0 ∪ (Finset.univ : Finset (Fin (n + 1) × Q × A)).biUnion
        (fun x => (T (x.2.1, x.2.2)).image
          (fun y => f0 ((x.1 : ℕ), x.2.1) ++ (M.step x.2.1 x.2.2).2 :: y)), ?_, ?_⟩
      · refine le_trans (Finset.card_union_le _ _) ?_
        have hbu : ((Finset.univ : Finset (Fin (n + 1) × Q × A)).biUnion
            (fun x => (T (x.2.1, x.2.2)).image
              (fun y => f0 ((x.1 : ℕ), x.2.1) ++ (M.step x.2.1 x.2.2).2 :: y))).card
            ≤ (n + 1) * Nat.card Q * Nat.card A * C ^ (2 * k + 2) := by
          refine le_trans Finset.card_biUnion_le ?_
          refine le_trans (Finset.sum_le_sum (fun x _ =>
            le_trans Finset.card_image_le (hT1 (x.2.1, x.2.2)))) ?_
          rw [Finset.sum_const, smul_eq_mul]
          have hcard : (Finset.univ : Finset (Fin (n + 1) × Q × A)).card
              = (n + 1) * Nat.card Q * Nat.card A := by
            simp [Nat.card_eq_fintype_card, mul_assoc]
          rw [hcard]
        have hX : 1 ≤ C ^ (2 * k + 2) := Nat.one_le_pow _ _ (by omega)
        have hpow : C ^ (2 * (k + 1) + 2) = C * C * C ^ (2 * k + 2) := by
          rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 by ring, pow_add]
          ring
        rw [hpow]
        have h1 : (n + 1) * Nat.card Q * Nat.card A * C ^ (2 * k + 2) ≤ C * C ^ (2 * k + 2) :=
          Nat.mul_le_mul_right _ hCb2
        nlinarith [hS0card, hbu, hCb1, hX, hC2, h1]
      · intro w hw
        rcases reach_split p w p (reach_refl M p) with hl | ⟨u, a, z, rfl, h1, h2⟩
        · exact Finset.mem_union_left _ (hS0mem w hw hl)
        · refine Finset.mem_union_right _ ?_
          set q := M.trans u p with hq
          have hlu : u.length ≤ n := by simp at hw; omega
          have hlz : z.length ≤ n := by simp at hw; omega
          have hrun : M.run p (u ++ a :: z)
              = f0 (u.length, q) ++ (M.step q a).2 :: M.run (M.transFun q a) z := by
            rw [M.run_append, ← hq, M.run_cons, hf0 (u.length, q) u rfl rfl h1]
            rfl
          have hreach' : M.Reach M.init (M.transFun q a) :=
            reach_trans hp (reach_trans (reach_word M p u) (reach_step M q a))
          have hmeas : Nat.card (M.reachSet (M.transFun q a)) ≤ k := by
            have := reachSet_card_lt (M := M)
              (reach_trans (reach_word M p u) (reach_step M q a)) h2
            omega
          have hz := hT2 (q, a) ⟨hreach', hmeas⟩ z hlz
          rw [hrun]
          refine Finset.mem_biUnion.2 ⟨(⟨u.length, by omega⟩, q, a), Finset.mem_univ _, ?_⟩
          exact Finset.mem_image.2 ⟨_, hz, rfl⟩

end Mealy

/-- If a Mealy machine has no two cycles of the same length and different outputs around a common
reachable state, then its image grows polynomially. -/
theorem polyBounded_imageGrowth_of_not_ambiguousCycle {A B Q : Type} [Finite A] [Finite Q]
    (M : Mealy A B Q) (h : ¬ M.AmbiguousCycle) : PolyBounded (imageGrowth M.eval) := by
  set N := Nat.card Q with hN
  set K := (Nat.card Q + 1) * (Nat.card A + 1) + 1 with hK
  refine ⟨K ^ (2 * N + 2), 2 * N + 2, fun n => ?_⟩
  obtain ⟨S, hS1, hS2⟩ :=
    Mealy.exists_cover h n N M.init (Mealy.reach_refl M M.init) (Mealy.reachSet_card_le M M.init)
  have hsub : {y : List B | ∃ w : List A, w.length ≤ n ∧ M.eval w = y} ⊆ (↑S : Set (List B)) := by
    rintro y ⟨w, hw, rfl⟩
    exact hS2 w hw
  have h1 : imageGrowth M.eval n ≤ S.card := by
    have hle := Set.ncard_le_ncard hsub S.finite_toSet
    rwa [Set.ncard_coe_finset] at hle
  have hCK : (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) + 1 ≤ K * (n + 1) := by
    rw [hK]
    have he : (n + 1) * (Nat.card Q + 1) * (Nat.card A + 1)
        = (Nat.card Q + 1) * (Nat.card A + 1) * (n + 1) := by ring
    rw [he]
    nlinarith [Nat.zero_le n]
  have h2 : ((n + 1) * (Nat.card Q + 1) * (Nat.card A + 1) + 1) ^ (2 * N + 2)
      ≤ (K * (n + 1)) ^ (2 * N + 2) := Nat.pow_le_pow_left hCK _
  rw [mul_pow] at h2
  omega

/-- **Exercise `exer:polynomial-image-growth-decidable`, the criterion.**  The number of outputs of
a Mealy machine on inputs of length at most `n` is bounded by a polynomial in `n` if and only if the
machine has no two cycles around a common reachable state which have the same length and different
outputs. -/
theorem mealy_imageGrowth_polyBounded_iff {A B Q : Type} [Finite A] [Finite Q]
    (M : Mealy A B Q) : PolyBounded (imageGrowth M.eval) ↔ ¬ M.AmbiguousCycle :=
  ⟨fun hp hamb => imageGrowth_not_polyBounded_of_ambiguousCycle M hamb hp,
    polyBounded_imageGrowth_of_not_ambiguousCycle M⟩

/-! The criterion is decidable: it is a reachability question, first in the machine itself and then
in the automaton which runs two copies of the machine side by side and remembers whether their
outputs have already differed. -/

lemma strTrans_append_eq {A X : Type} (f : X → A → X) (u v : List A) (x : X) :
    strTrans f (u ++ v) x = strTrans f v (strTrans f u x) := by
  simp [strTrans, List.foldl_append]

lemma strTrans_cons_eq {A X : Type} (f : X → A → X) (a : A) (w : List A) (x : X) :
    strTrans f (a :: w) x = strTrans f w (f x a) := by simp [strTrans]

/-- A reachable state is reachable by a word shorter than the number of states: a repetition in
the run can be cut out. -/
lemma strTrans_short {A X : Type} [Finite X] (f : X → A → X) (x y : X)
    (h : ∃ w : List A, strTrans f w x = y) :
    ∃ w : List A, w.length < Nat.card X ∧ strTrans f w x = y := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hex : ∃ n : ℕ, ∃ w : List A, w.length = n ∧ strTrans f w x = y := by
    obtain ⟨w, hw⟩ := h
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hwl, hw⟩ := Nat.find_spec hex
  refine ⟨w, ?_, hw⟩
  by_contra hlt
  push_neg at hlt
  have hcard : Fintype.card X < Fintype.card (Fin (w.length + 1)) := by
    rw [Fintype.card_fin]
    have : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    omega
  obtain ⟨i, j, hij, hgij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (w.length + 1) => strTrans f (w.take (i : ℕ)) x) hcard
  rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt2 | hge
  · have hjle : (j : ℕ) ≤ w.length := by omega
    have hlen' : (w.take (i : ℕ) ++ w.drop (j : ℕ)).length < w.length := by
      simp [List.length_take, List.length_drop]
      omega
    have heq : strTrans f (w.take (i : ℕ) ++ w.drop (j : ℕ)) x = y := by
      rw [strTrans_append_eq, hgij, ← strTrans_append_eq, List.take_append_drop, hw]
    exact absurd ⟨_, rfl, heq⟩ (Nat.find_min hex (by omega))
  · have hlt2 : (j : ℕ) < (i : ℕ) := by
      rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with h | h
      · exact h
      · exact absurd (Fin.ext (by omega)) hij
    have hile : (i : ℕ) ≤ w.length := by omega
    have hlen' : (w.take (j : ℕ) ++ w.drop (i : ℕ)).length < w.length := by
      simp [List.length_take, List.length_drop]
      omega
    have heq : strTrans f (w.take (j : ℕ) ++ w.drop (i : ℕ)) x = y := by
      rw [strTrans_append_eq, ← hgij, ← strTrans_append_eq, List.take_append_drop, hw]
    exact absurd ⟨_, rfl, heq⟩ (Nat.find_min hex (by omega))

/-- The states reachable in at most `n` steps, computed by iteration. -/
def reachFinset {A X : Type} [Fintype A] [DecidableEq X] (f : X → A → X) (x : X) : ℕ → Finset X
  | 0 => {x}
  | n + 1 => reachFinset f x n ∪ (reachFinset f x n).biUnion
      (fun z => (Finset.univ : Finset A).image (f z))

lemma mem_reachFinset {A X : Type} [Fintype A] [DecidableEq X] (f : X → A → X) (x y : X) (n : ℕ) :
    y ∈ reachFinset f x n ↔ ∃ w : List A, w.length ≤ n ∧ strTrans f w x = y := by
  induction n generalizing y with
  | zero =>
      simp only [reachFinset, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨[], le_refl _, rfl⟩
      · rintro ⟨w, hw, hwx⟩
        rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)] at hwx
        exact hwx.symm ▸ rfl
  | succ n ih =>
      simp only [reachFinset, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (h | ⟨z, hz, a, rfl⟩)
        · obtain ⟨w, hw, hwx⟩ := (ih y).mp h
          exact ⟨w, by omega, hwx⟩
        · obtain ⟨w, hw, hwx⟩ := (ih z).mp hz
          refine ⟨w ++ [a], by simp; omega, ?_⟩
          rw [strTrans_append_eq, hwx]
          rfl
      · rintro ⟨w, hw, hwx⟩
        rcases Nat.lt_or_ge w.length (n + 1) with hlt | hge
        · exact Or.inl ((ih y).mpr ⟨w, by omega, hwx⟩)
        · rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
          · simp at hge
          · right
            refine ⟨strTrans f u x, (ih _).mpr ⟨u, by simp at hw ⊢; omega, rfl⟩, a, ?_⟩
            rw [List.concat_eq_append, strTrans_append_eq] at hwx
            exact hwx

lemma reach_iff_mem_reachFinset {A X : Type} [Fintype A] [Fintype X] [DecidableEq X]
    (f : X → A → X) (x y : X) :
    (∃ w : List A, strTrans f w x = y) ↔ y ∈ reachFinset f x (Fintype.card X) := by
  have hcard : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
  constructor
  · intro h
    obtain ⟨w, hw1, hw2⟩ := strTrans_short f x y h
    exact (mem_reachFinset f x y _).mpr ⟨w, by omega, hw2⟩
  · intro h
    obtain ⟨w, _, hw⟩ := (mem_reachFinset f x y _).mp h
    exact ⟨w, hw⟩

/-- The transition function of the automaton which runs two copies of `M` side by side and
remembers whether the two outputs have already differed. -/
def pairStep {A B Q : Type} [DecidableEq B] (M : Mealy A B Q) :
    Q × Q × Bool → A × A → Q × Q × Bool :=
  fun s ab => (M.transFun s.1 ab.1, M.transFun s.2.1 ab.2,
    s.2.2 || decide ((M.step s.1 ab.1).2 ≠ (M.step s.2.1 ab.2).2))

lemma strTrans_pairStep {A B Q : Type} [DecidableEq B] (M : Mealy A B Q) :
    ∀ (u v : List A), u.length = v.length → ∀ (r1 r2 : Q) (d : Bool),
      strTrans (pairStep M) (u.zip v) (r1, r2, d)
        = (M.trans u r1, M.trans v r2, d || decide (M.run r1 u ≠ M.run r2 v)) := by
  intro u
  induction u with
  | nil => intro v hv r1 r2 d; simp [List.length_eq_zero_iff.mp hv.symm, strTrans]
  | cons a u ih =>
      intro v hv r1 r2 d
      cases v with
      | nil => simp at hv
      | cons b v =>
          simp only [List.zip_cons_cons, strTrans_cons_eq, pairStep]
          rw [ih v (by simpa using hv)]
          simp only [Mealy.trans_cons, Mealy.run_cons]
          refine Prod.ext rfl (Prod.ext rfl ?_)
          by_cases h1 : (M.step r1 a).2 = (M.step r2 b).2
          · simp [h1, Mealy.transFun]
          · simp [h1, Mealy.transFun]

/-- Two cycles of the same length with different outputs around `q` are exactly a run of the pair
automaton from `(q, q, false)` to `(q, q, true)`. -/
lemma ambiguous_at_iff {A B Q : Type} [DecidableEq B] (M : Mealy A B Q) (q : Q) :
    (∃ u v : List A, u.length = v.length ∧ M.trans u q = q ∧ M.trans v q = q ∧
        M.run q u ≠ M.run q v) ↔
      ∃ w : List (A × A), strTrans (pairStep M) w (q, q, false) = (q, q, true) := by
  constructor
  · rintro ⟨u, v, hlen, hu, hv, hne⟩
    refine ⟨u.zip v, ?_⟩
    rw [strTrans_pairStep M u v hlen]
    simp [hu, hv, hne]
  · rintro ⟨w, hw⟩
    have hz : (w.map Prod.fst).zip (w.map Prod.snd) = w := by simpa using List.zip_unzip w
    have key := strTrans_pairStep M (w.map Prod.fst) (w.map Prod.snd) (by simp) q q false
    rw [hz, hw] at key
    have h1 : M.trans (w.map Prod.fst) q = q := (congrArg Prod.fst key).symm
    have h2 : M.trans (w.map Prod.snd) q = q := (congrArg (fun s => s.2.1) key).symm
    have h3 : M.run q (w.map Prod.fst) ≠ M.run q (w.map Prod.snd) := by
      have h4 := congrArg (fun s => s.2.2) key
      simpa using h4
    exact ⟨_, _, by simp, h1, h2, h3⟩

/-- The criterion, as a reachability question in two finite automata. -/
lemma ambiguousCycle_iff_reachFinset {A B Q : Type} [Fintype A] [Fintype Q] [DecidableEq Q]
    [DecidableEq B] (M : Mealy A B Q) :
    M.AmbiguousCycle ↔ ∃ q : Q,
      q ∈ reachFinset M.transFun M.init (Fintype.card Q) ∧
        (q, q, true) ∈ reachFinset (pairStep M) (q, q, false) (Fintype.card (Q × Q × Bool)) := by
  constructor
  · rintro ⟨q, u, v, hz, hlen, hu, hv, hne⟩
    exact ⟨q, (reach_iff_mem_reachFinset _ _ _).mp hz,
      (reach_iff_mem_reachFinset _ _ _).mp ((ambiguous_at_iff M q).mp ⟨u, v, hlen, hu, hv, hne⟩)⟩
  · rintro ⟨q, h1, h2⟩
    obtain ⟨u, v, hlen, hu, hv, hne⟩ :=
      (ambiguous_at_iff M q).mpr ((reach_iff_mem_reachFinset _ _ _).mpr h2)
    exact ⟨q, u, v, (reach_iff_mem_reachFinset _ _ _).mpr h1, hlen, hu, hv, hne⟩

/-- The condition of Exercise `exer:polynomial-image-growth-decidable` is decidable. -/
instance decidableAmbiguousCycle {A B Q : Type} [Fintype A] [Fintype Q] [DecidableEq Q]
    [DecidableEq B] (M : Mealy A B Q) : Decidable M.AmbiguousCycle :=
  decidable_of_iff _ (ambiguousCycle_iff_reachFinset M).symm

/-- **Exercise `exer:polynomial-image-growth-decidable`, decidability.**  Whether the image of a
Mealy machine has polynomial growth is decidable: it suffices to look for two cycles of the same
length and with different outputs around a common reachable state, which is a reachability question
in two finite automata.  The alphabets and the state space are given as concrete finite types with
decidable equality, since the statement is about an algorithm which inputs a machine. -/
def decidableImageGrowthPolyBounded {A B Q : Type} [Fintype A] [Fintype Q] [DecidableEq Q]
    [DecidableEq B] (M : Mealy A B Q) : Decidable (PolyBounded (imageGrowth M.eval)) :=
  decidable_of_iff _ (mealy_imageGrowth_polyBounded_iff M).symm

/-! ### Exercises `exer:regular-complete-mealy` and `exer:regular-complete-mealy-2` -/

/-- A regular language `L ⊆ A*` is *regular-complete under Mealy reductions* if every regular
language `K ⊆ B*` reduces to it by a Mealy machine, on nonempty inputs (Exercise
`exer:regular-complete-mealy`). -/
def RegularCompleteMealy {A : Type} (L : Language A) : Prop :=
  ∀ (B : Type) (_ : Finite B) (K : Language B), K.IsRegular →
    ∃ f : List B → List A, IsMealy f ∧ ∀ w : List B, w ≠ [] → (w ∈ K ↔ f w ∈ L)

/-- The language of the author's solution to Exercise `exer:regular-complete-mealy`: the binary
strings whose last letter is `true`. -/
def lastLetterTrue : Language Bool := {w : List Bool | w.getLast? = some true}

/-- The two-state automaton recognising `Transducers.lastLetterTrue`. -/
def lastDfa : DFA Bool Bool := ⟨fun _ x => x, false, {true}⟩

lemma lastDfa_eval (w : List Bool) : lastDfa.eval w = w.getLast?.getD false := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
      show lastDfa.evalFrom lastDfa.start (u ++ [x]) = _
      rw [DFA.evalFrom_append_singleton]
      simp [lastDfa]

lemma isMealy_lengthPreserving {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    LengthPreserving f := by
  obtain ⟨Q, hQ, M, rfl⟩ := hf
  exact fun w => M.eval_length w

/-- A Mealy machine appends exactly one output letter when the input is extended by one letter. -/
lemma isMealy_concat {A B : Type} {f : List A → List B} (hf : IsMealy f) (w : List A) (x : A) :
    ∃ c : B, f (w ++ [x]) = f w ++ [c] := by
  obtain ⟨Q, hQ, M, rfl⟩ := hf
  exact ⟨(M.step (M.trans w M.init) x).2, by rw [M.eval_append]; rfl⟩

/-! The reduction of the author's solution to Exercise `exer:regular-complete-mealy` is the Mealy
machine which marks every position by whether the prefix ending at that position is accepted by a
given deterministic automaton.  That machine is already in the project, as
`Transducers.dfaMealy` (`PartC/FOMealy.lean`), and is reused here. -/

lemma dfaMealy_trans {B σ : Type} (D : DFA B σ) (u : List B) (q : σ) :
    (dfaMealy D).trans u q = D.evalFrom q u := rfl

open Classical in
lemma dfaMealy_getLast {B σ : Type} (D : DFA B σ) (u : List B) (x : B) :
    ((dfaMealy D).eval (u ++ [x])).getLast? =
      some (decide (D.evalFrom D.start (u ++ [x]) ∈ D.accept)) := by
  rw [Mealy.eval_append, dfaMealy_trans]
  show ((dfaMealy D).eval u ++ [((dfaMealy D).step (D.evalFrom D.start u) x).2]).getLast? = _
  rw [List.getLast?_concat, DFA.evalFrom_append_singleton]
  rfl

/-- Every nonempty string is a string with one letter appended. -/
lemma exists_concat_of_ne_nil {A : Type} {w : List A} (hw : w ≠ []) : ∃ u x, w = u ++ [x] := by
  rcases List.eq_nil_or_concat w with h | ⟨u, x, h⟩
  · exact absurd h hw
  · exact ⟨u, x, by simpa using h⟩

/-- **Exercise `exer:regular-complete-mealy`.**  The language of those nonempty binary strings whose
last letter is `true` is regular and regular-complete under Mealy reductions. -/
theorem lastLetterTrue_regularCompleteMealy :
    lastLetterTrue.IsRegular ∧ RegularCompleteMealy lastLetterTrue := by
  classical
  constructor
  · refine ⟨Bool, inferInstance, lastDfa, ?_⟩
    ext w
    rw [DFA.mem_accepts, lastDfa_eval]
    show _ ∈ ({true} : Set Bool) ↔ w.getLast? = some true
    cases h : w.getLast? with
    | none => simp
    | some b => cases b <;> simp
  · intro B hB K hK
    obtain ⟨σ, hσ, D, rfl⟩ := hK
    refine ⟨(dfaMealy D).eval, ⟨σ, inferInstance, dfaMealy D, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨u, x, rfl⟩ := exists_concat_of_ne_nil hw
    rw [DFA.mem_accepts]
    show _ ↔ ((dfaMealy D).eval (u ++ [x])).getLast? = some true
    rw [dfaMealy_getLast]
    simp [DFA.eval]

/-- The reduction of `Transducers.lastLetterTrue` to a language whose automaton satisfies the
criterion of the author's solution to Exercise `exer:regular-complete-mealy-2`: the machine stays
inside `P` and chooses, at every position, the letter that makes the current state accepting or
rejecting according to the input bit. -/
lemma reduction_of_dfa_criterion {A Q : Type} [Finite A] [Finite Q] (D : DFA A Q)
    (P : Set Q) (hstart : D.start ∈ P)
    (hP : ∀ q ∈ P, ∃ a b : A,
      D.step q a ∈ P ∧ D.step q b ∈ P ∧ (D.step q a ∈ D.accept ↔ D.step q b ∉ D.accept)) :
    ∃ g : List Bool → List A, IsMealy g ∧
      ∀ w : List Bool, w ≠ [] → (w ∈ lastLetterTrue ↔ g w ∈ D.accepts) := by
  classical
  have hP' : ∀ q : ↥P, ∃ a b : A,
      D.step ↑q a ∈ P ∧ D.step ↑q b ∈ P ∧ (D.step ↑q a ∈ D.accept ↔ D.step ↑q b ∉ D.accept) :=
    fun q => hP q q.2
  choose acc rej h1 h2 h3 using hP'
  set pick : ↥P → Bool → A := fun q x =>
    if D.step ↑q (acc q) ∈ D.accept then (if x then acc q else rej q)
    else (if x then rej q else acc q) with hpick
  have hpickP : ∀ (q : ↥P) (x : Bool), D.step ↑q (pick q x) ∈ P := by
    intro q x
    rw [hpick]
    by_cases hc : D.step ↑q (acc q) ∈ D.accept <;> cases x <;> simp [hc, h1 q, h2 q]
  have hpickacc : ∀ (q : ↥P) (x : Bool), (D.step ↑q (pick q x) ∈ D.accept ↔ x = true) := by
    intro q x
    rw [hpick]
    by_cases hc : D.step ↑q (acc q) ∈ D.accept
    · have hr : D.step ↑q (rej q) ∉ D.accept := (h3 q).1 hc
      cases x <;> simp [hc, hr]
    · have hr : D.step ↑q (rej q) ∈ D.accept := by
        by_contra hr
        exact hc ((h3 q).2 hr)
      cases x <;> simp [hc, hr]
  set G : Mealy Bool A ↥P :=
    ⟨⟨D.start, hstart⟩, fun q x => (⟨D.step ↑q (pick q x), hpickP q x⟩, pick q x)⟩ with hG
  have hrun : ∀ (w : List Bool) (q : ↥P), D.evalFrom ↑q (G.run q w) = ↑(G.trans w q) := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons x w ih =>
        intro q
        rw [Mealy.run_cons, Mealy.trans_cons, DFA.evalFrom_cons]
        exact ih ((G.step q x).1)
  refine ⟨G.eval, ⟨↥P, inferInstance, G, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨u, x, rfl⟩ := exists_concat_of_ne_nil hw
  rw [DFA.mem_accepts]
  show _ ↔ D.evalFrom (↑G.init) (G.run G.init (u ++ [x])) ∈ D.accept
  rw [hrun, Mealy.trans_append]
  show _ ↔ (D.step ↑(G.trans u G.init) (pick (G.trans u G.init) x) ∈ D.accept)
  rw [hpickacc]
  show (u ++ [x]).getLast? = some true ↔ (x = true)
  simp

/-- **Exercise `exer:regular-complete-mealy-2`, the criterion.**  A regular language, given by a
deterministic automaton, is regular-complete under Mealy reductions if and only if the automaton has
a set of states `P` containing the initial state such that from every state of `P` two letters lead
back into `P`, exactly one of them into an accepting state. -/
theorem regularCompleteMealy_dfa_iff {A Q : Type} [Finite A] [Finite Q] (D : DFA A Q) :
    RegularCompleteMealy D.accepts ↔
      ∃ P : Set Q, D.start ∈ P ∧ ∀ q ∈ P, ∃ a b : A,
        D.step q a ∈ P ∧ D.step q b ∈ P ∧ (D.step q a ∈ D.accept ↔ D.step q b ∉ D.accept) := by
  classical
  constructor
  · intro hcomp
    obtain ⟨f, hf, hred⟩ :=
      hcomp Bool inferInstance lastLetterTrue lastLetterTrue_regularCompleteMealy.1
    have hnil : f [] = [] := List.eq_nil_of_length_eq_zero (by
      rw [isMealy_lengthPreserving hf []]; rfl)
    refine ⟨{q | ∃ w : List Bool, D.evalFrom D.start (f w) = q}, ⟨[], by rw [hnil]; rfl⟩, ?_⟩
    rintro q ⟨w, rfl⟩
    obtain ⟨ct, hct⟩ := isMealy_concat hf w true
    obtain ⟨cf, hcf⟩ := isMealy_concat hf w false
    have hstept : D.evalFrom D.start (f (w ++ [true])) =
        D.step (D.evalFrom D.start (f w)) ct := by
      rw [hct, DFA.evalFrom_append_singleton]
    have hstepf : D.evalFrom D.start (f (w ++ [false])) =
        D.step (D.evalFrom D.start (f w)) cf := by
      rw [hcf, DFA.evalFrom_append_singleton]
    have hmemt : (w ++ [true]) ∈ lastLetterTrue := by
      show (w ++ [true]).getLast? = some true
      simp
    have hmemf : (w ++ [false]) ∉ lastLetterTrue := by
      show ¬ ((w ++ [false]).getLast? = some true)
      simp
    have hacct : D.step (D.evalFrom D.start (f w)) ct ∈ D.accept := by
      rw [← hstept]
      exact (DFA.mem_accepts D).1 ((hred _ (by simp)).1 hmemt)
    have haccf : D.step (D.evalFrom D.start (f w)) cf ∉ D.accept := by
      rw [← hstepf]
      intro hc
      exact hmemf ((hred _ (by simp)).2 ((DFA.mem_accepts D).2 hc))
    exact ⟨ct, cf, ⟨w ++ [true], hstept⟩, ⟨w ++ [false], hstepf⟩,
      ⟨fun _ => haccf, fun _ => hacct⟩⟩
  · rintro ⟨P, hstart, hP⟩
    obtain ⟨g, hg, hgred⟩ := reduction_of_dfa_criterion D P hstart hP
    intro B hB K hK
    obtain ⟨f, hf, hfred⟩ := lastLetterTrue_regularCompleteMealy.2 B hB K hK
    refine ⟨g ∘ f, mealy_comp hf hg, ?_⟩
    intro w hw
    have hfw : f w ≠ [] := by
      intro hc
      apply hw
      have := isMealy_lengthPreserving hf w
      rw [hc] at this
      exact List.eq_nil_of_length_eq_zero this.symm
    rw [hfred w hw, hgred (f w) hfw]
    rfl

/-- **Exercise `exer:regular-complete-mealy-2`, decidability.**  Regular-completeness under Mealy
reductions is decidable for a language given by a deterministic automaton: the criterion of
`Transducers.regularCompleteMealy_dfa_iff` quantifies over the subsets of the state space. -/
noncomputable def decidableRegularCompleteMealy {A Q : Type} [Finite A] [Finite Q] (D : DFA A Q) :
    Decidable (RegularCompleteMealy D.accepts) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Fintype A := Fintype.ofFinite A
  exact decidable_of_iff _ (regularCompleteMealy_dfa_iff D).symm

/-! ## The Krohn-Rhodes Decomposition Theorem (`krohn-rhodes.tex`) -/

/-! ### Exercise `exer:flip-flop-from-sequential-composition` -/

/-- The family of the functions computed by flip-flop Mealy machines with at most two states. -/
def TwoStateFlipFlopFam : ∀ (A B : Type), (List A → List B) → Prop :=
  fun A B f => ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q),
    M.eval = f ∧ M.FlipFlop ∧ Nat.card Q ≤ 2

section FlipFlopBits

variable {A B Q : Type} [DecidableEq Q]

/-- The states of `M` before each position of the input, when the input is read from the state
`q`. -/
def statesBefore (M : Mealy A B Q) : Q → List A → List Q
  | _, [] => []
  | q, a :: w => q :: statesBefore M (M.letterTrans a q) w

/-- Every position of the input, annotated with the bits, for the states listed in `l`, of the
state of `M` before that position. -/
def annot (M : Mealy A B Q) (l : List Q) (q : Q) (w : List A) : List (A × (Q → Bool)) :=
  List.zipWith (fun a r => (a, fun p => decide (p ∈ l ∧ r = p))) w (statesBefore M q w)

open Classical in
/-- The constant value of the state transformation of a letter, when it has one. -/
noncomputable def ffConst (M : Mealy A B Q) (a : A) : Option Q :=
  if h : ∃ q₀ : Q, ∀ q, M.letterTrans a q = q₀ then some h.choose else none

omit [DecidableEq Q] in
lemma ffConst_spec (M : Mealy A B Q) (hM : M.FlipFlop) (a : A) (q : Q) :
    M.letterTrans a q = (ffConst M a).getD q := by
  classical
  unfold ffConst
  by_cases h : ∃ q₀ : Q, ∀ q, M.letterTrans a q = q₀
  · rw [dif_pos h]
    exact h.choose_spec q
  · rw [dif_neg h]
    rcases hM a with h' | hc
    · show M.letterTrans a q = q
      rw [h']; rfl
    · exact absurd hc h

/-- The two-state flip-flop machine which tracks the bit "the state of `M` is `p`": it copies its
input and appends the value of that bit *before* the current position. -/
noncomputable def bitMachine (M : Mealy A B Q) (p : Q) :
    Mealy (A × (Q → Bool)) (A × (Q → Bool)) Bool :=
  ⟨decide (M.init = p),
    fun s ab => ((match ffConst M ab.1 with | none => s | some q₀ => decide (q₀ = p)),
      (ab.1, Function.update ab.2 p s))⟩

lemma bitMachine_flipFlop (M : Mealy A B Q) (p : Q) : (bitMachine M p).FlipFlop := by
  intro ab
  cases h : ffConst M ab.1 with
  | none =>
      left
      funext s
      show (match ffConst M ab.1 with | none => s | some q₀ => decide (q₀ = p)) = s
      rw [h]
  | some q₀ =>
      right
      refine ⟨decide (q₀ = p), fun s => ?_⟩
      show (match ffConst M ab.1 with | none => s | some q₀ => decide (q₀ = p)) = _
      rw [h]

lemma next_bit (M : Mealy A B Q) (hM : M.FlipFlop) (p : Q) (a : A) (q : Q) :
    (match ffConst M a with | none => decide (q = p) | some q₀ => decide (q₀ = p))
      = decide (M.letterTrans a q = p) := by
  rw [ffConst_spec M hM a q]
  cases h : ffConst M a <;> simp

lemma annot_cons (M : Mealy A B Q) (l : List Q) (q : Q) (a : A) (w : List A) :
    annot M l q (a :: w) =
      (a, fun p => decide (p ∈ l ∧ q = p)) :: annot M l (M.letterTrans a q) w := by
  simp [annot, statesBefore]

lemma annot_nil (M : Mealy A B Q) (q : Q) (w : List A) :
    annot M [] q w = w.map (fun a => (a, fun _ => false)) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => rw [annot_cons, ih]; simp

lemma bitMachine_run (M : Mealy A B Q) (hM : M.FlipFlop) (p : Q) (l : List Q) (q : Q)
    (w : List A) :
    (bitMachine M p).run (decide (q = p)) (annot M l q w) = annot M (p :: l) q w := by
  induction w generalizing q with
  | nil => simp [annot, statesBefore]
  | cons a w ih =>
      rw [annot_cons, annot_cons, Mealy.run_cons]
      show ((a, Function.update (fun r => decide (r ∈ l ∧ q = r)) p (decide (q = p))) ::
        (bitMachine M p).run
          (match ffConst M a with | none => decide (q = p) | some q₀ => decide (q₀ = p))
          (annot M l (M.letterTrans a q) w)) = _
      rw [next_bit M hM p a q, ih (M.letterTrans a q)]
      have hbits : Function.update (fun r => decide (r ∈ l ∧ q = r)) p (decide (q = p))
          = fun r => decide (r ∈ p :: l ∧ q = r) := by
        funext r
        by_cases hr : r = p
        · subst hr; simp
        · simp [hr]
      rw [hbits]

open Classical in
/-- The state of `M` recovered from its vector of bits. -/
noncomputable def decodeState (M : Mealy A B Q) (bits : Q → Bool) : Q :=
  if h : ∃ p, bits p = true then h.choose else M.init

lemma decodeState_annot (M : Mealy A B Q) {l : List Q} (hl : ∀ p : Q, p ∈ l) (q : Q) :
    decodeState M (fun p => decide (p ∈ l ∧ q = p)) = q := by
  classical
  have hex : ∃ p, (decide (p ∈ l ∧ q = p)) = true := ⟨q, by simp [hl q]⟩
  unfold decodeState
  rw [dif_pos hex]
  exact (of_decide_eq_true hex.choose_spec).2.symm

lemma map_annot (M : Mealy A B Q) {l : List Q} (hl : ∀ p : Q, p ∈ l) (q : Q) (w : List A) :
    (annot M l q w).map (fun ab => (M.step (decodeState M ab.2) ab.1).2) = M.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      rw [annot_cons, List.map_cons, ih, decodeState_annot M hl q]
      rfl

/-- The chain of two-state flip-flop machines that annotates each position with the bits, for the
states listed in `l`, of the state of `M` before that position. -/
lemma chain_annot [Finite A] [Finite Q] (M : Mealy A B Q) (hM : M.FlipFlop) (l : List Q) :
    ∃ F : List A → List (A × (Q → Bool)),
      CompClosure TwoStateFlipFlopFam A (A × (Q → Bool)) F ∧ ∀ w, F w = annot M l M.init w := by
  induction l with
  | nil =>
      refine ⟨List.map (fun a => (a, fun _ => false)), CompClosure.base ?_, fun w => ?_⟩
      · exact ⟨Unit, inferInstance, homMealy _, homMealy_eval _, homMealy_flipFlop _, by simp⟩
      · rw [annot_nil]
  | cons p l ih =>
      obtain ⟨F, hF, hFeq⟩ := ih
      haveI : Finite (A × (Q → Bool)) := inferInstance
      refine ⟨(bitMachine M p).eval ∘ F, CompClosure.comp hF (CompClosure.base ?_), fun w => ?_⟩
      · exact ⟨Bool, inferInstance, bitMachine M p, rfl, bitMachine_flipFlop M p, by simp⟩
      · rw [Function.comp_apply, hFeq]
        exact bitMachine_run M hM p l M.init w

end FlipFlopBits

/-- **Exercise `exer:flip-flop-from-sequential-composition`.**  Every flip-flop Mealy machine is a
sequential composition of flip-flop Mealy machines with two states.  The proof is the author's: one
machine per bit of an encoding of the state space, each one copying its input and appending the
value of its bit *before* the current position, followed by a letter-to-letter homomorphism.  The
encoding used here is the unary one `q ↦ (fun p => p = q)`, so that there is one machine per state
rather than one per bit of a binary encoding; the exercise does not ask for a logarithmic number of
machines. -/
theorem flipflop_twoState_decomposition {A B Q : Type} [Finite A] [Finite Q] (M : Mealy A B Q)
    (hM : M.FlipFlop) : CompClosure TwoStateFlipFlopFam A B M.eval := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  have hl : ∀ p : Q, p ∈ (Finset.univ : Finset Q).toList := by
    intro p
    simp
  obtain ⟨F, hF, hFeq⟩ := chain_annot M hM (Finset.univ : Finset Q).toList
  haveI : Finite (A × (Q → Bool)) := inferInstance
  have hM' : M.eval = (List.map (fun ab : A × (Q → Bool) =>
      (M.step (decodeState M ab.2) ab.1).2)) ∘ F := by
    funext w
    rw [Function.comp_apply, hFeq, map_annot M hl]
    rfl
  rw [hM']
  exact CompClosure.comp hF (CompClosure.base
    ⟨Unit, inferInstance, homMealy _, homMealy_eval _, homMealy_flipFlop _, by simp⟩)

/-! ### Exercise `exer:delay-not-flip-flop-composition` -/

/-- The delay function of Example `ex:delay`: the input letters are shifted by one position to the
right, and the first position carries the extra letter `none`. -/
def delay {A : Type} (w : List A) : List (Option A) := (none :: w.map some).dropLast

/-- The family of the functions computed by reversible Mealy machines. -/
def ReversibleFam : ∀ (A B : Type), (List A → List B) → Prop := fun _ _ f => IsReversibleMealy f

lemma Mealy.trans_replicate {A B Q : Type} (M : Mealy A B Q) (a : A) (k : ℕ) (q : Q) :
    M.trans (List.replicate k a) q = (M.letterTrans a)^[k] q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, Mealy.trans_cons, ih, Function.iterate_succ_apply]

/-- Lemma `lem:reversible-composition` of the book, in the form used by the exercise: a composition
of reversible Mealy machines is computed by a single reversible Mealy machine. -/
lemma isReversibleMealy_of_compClosure {A B : Type} {f : List A → List B}
    (h : CompClosure ReversibleFam A B f) : IsReversibleMealy f := by
  induction h with
  | base hf => exact hf
  | id A =>
      refine ⟨Unit, inferInstance, ⟨(), fun _ a => ((), a)⟩, ?_, ?_⟩
      · funext w
        show Mealy.run _ () w = w
        induction w with
        | nil => rfl
        | cons a w ih => simpa using ih
      · intro a
        exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨(), Subsingleton.elim _ _⟩⟩
  | comp _ _ ihf ihg => exact reversible_comp ihf ihg

lemma delay_concat {A : Type} (u : List A) (x : A) : delay (u ++ [x]) = none :: u.map some := by
  show ((none :: (u ++ [x]).map some).dropLast) = _
  rw [List.map_append, List.map_cons, List.map_nil,
    show (none :: (u.map some ++ [some x])) = (none :: u.map some) ++ [some x] from rfl]
  exact List.dropLast_concat

/-- **Exercise `exer:delay-not-flip-flop-composition`.**  The delay function of Example `ex:delay`
is not a composition of reversible Mealy machines.  (The label of the exercise mentions flip-flops,
but its statement, which is the one formalised here, is about reversible machines.)  A nonempty
input alphabet is needed: over the empty alphabet the delay function is the identity. -/
theorem delay_not_reversible_composition {A : Type} (a : A) :
    ¬ CompClosure ReversibleFam A (Option A) (delay : List A → List (Option A)) := by
  intro h
  obtain ⟨Q, hQ, M, hM, hrev⟩ := isReversibleMealy_of_compClosure h
  haveI := hQ
  obtain ⟨i, j, hij, hfe⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (M.letterTrans a)^[n] M.init)
  obtain ⟨i, j, hlt, hfe⟩ : ∃ i j : ℕ, i < j ∧
      (M.letterTrans a)^[i] M.init = (M.letterTrans a)^[j] M.init := by
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', hfe⟩
    · exact ⟨j, i, h', hfe.symm⟩
  obtain ⟨m, hiter⟩ : ∃ m : ℕ, (M.letterTrans a)^[m + 1] M.init = M.init := by
    refine ⟨j - i - 1, ?_⟩
    have hji : j = i + (j - i - 1 + 1) := by omega
    rw [hji, Function.iterate_add_apply] at hfe
    exact ((Function.Injective.iterate (hrev a).1 i) hfe).symm
  have htr : M.trans (List.replicate (m + 1) a) M.init = M.init := by
    rw [Mealy.trans_replicate, hiter]
  have e1 : (M.eval (List.replicate (m + 1) a ++ [a])).getLast? = some ((M.step M.init a).2) := by
    rw [M.eval_append, htr]
    simp [Mealy.run]
  have e2 : (M.eval [a]).getLast? = some ((M.step M.init a).2) := by
    simp [Mealy.eval, Mealy.run]
  rw [hM] at e1 e2
  have g1 : (delay (List.replicate (m + 1) a ++ [a])).getLast? = some (some a) := by
    rw [delay_concat, List.map_replicate, List.replicate_succ',
      show (none :: (List.replicate m (some a) ++ [some a]))
        = (none :: List.replicate m (some a)) ++ [some a] from rfl]
    exact List.getLast?_concat
  have g2 : (delay ([a] : List A)).getLast? = some none := by
    rw [show ([a] : List A) = [] ++ [a] from rfl, delay_concat]
    simp
  rw [g1] at e1
  rw [g2] at e2
  rw [← e2] at e1
  simp at e1

/-! ### Exercise `exer:alternating-not-flip-flop-composition` -/

/-- The function of Example `ex:alternating-a-b`: over a one-letter input alphabet, it outputs the
two letters in alternation, starting with `true`. -/
def alternating (w : List Unit) : List Bool :=
  (List.range w.length).map (fun i => decide (i % 2 = 0))

lemma alternating_getLast?_of_length {w : List Unit} {n : ℕ} (h : w.length = n + 1) :
    (alternating w).getLast? = some (decide (n % 2 = 0)) := by
  simp [alternating, h, List.range_succ]

/-- **Exercise `exer:alternating-not-flip-flop-composition`.**  The function of Example
`ex:alternating-a-b` is not a composition of flip-flop Mealy machines: by Theorem
`thm:aperiodic-mealy` such a composition is aperiodic, and this function is not, since the last
letter of its output on `aⁿ` depends on the parity of `n`. -/
theorem alternating_not_flipflop_composition :
    ¬ CompClosure FlipFlopFam Unit Bool alternating := by
  intro h
  obtain ⟨o, N, hN⟩ := flipflop_composition_aperiodic h [] [()] []
  have h1 := hN (2 * N + 1) (by omega)
  have h2 := hN (2 * N + 2) (by omega)
  rw [alternating_getLast?_of_length (n := 2 * N) (by simp [npow_length])] at h1
  rw [alternating_getLast?_of_length (n := 2 * N + 1) (by simp [npow_length])] at h2
  rw [← h2] at h1
  simp [Nat.mul_mod_right] at h1

/-! ### Exercise `exer:invertible-mealy-is-reversible` -/

/-- The machine of the author's solution: it stores the previous input letter and swaps the two
output letters when that letter was `true`.  It is invertible but not reversible. -/
def swapPrev : Mealy Bool Bool Bool := ⟨false, fun s x => (x, if s then !x else x)⟩

/-- The one-state machine with constant output: it is reversible but not invertible. -/
def constOut : Mealy Bool Bool Unit := ⟨(), fun _ _ => ((), false)⟩

/-- **Exercise `exer:invertible-mealy-is-reversible`.**  Neither of invertibility (Exercise
`exer:invertible`) and reversibility implies the other.  The two machines are those of the author's
solution: the machine that stores the previous input letter and swaps the output letters after a
`true`, which is invertible but not reversible, and the one-state machine with constant output,
which is reversible but not invertible. -/
theorem invertible_reversible_independent :
    (∃ (Q : Type) (_ : Finite Q) (M : Mealy Bool Bool Q), M.Invertible ∧ ¬ M.Reversible) ∧
      (∃ (Q : Type) (_ : Finite Q) (M : Mealy Bool Bool Q), M.Reversible ∧ ¬ M.Invertible) := by
  constructor
  · have hreach : swapPrev.AllReachable := by
      intro q
      cases q with
      | false => exact ⟨[], rfl⟩
      | true => exact ⟨[true], rfl⟩
    refine ⟨Bool, inferInstance, swapPrev,
      (mealy_invertible_iff swapPrev hreach).2 (by decide), ?_⟩
    intro h
    have hfalse : (false : Bool) = true :=
      (h true).1 (show swapPrev.letterTrans true false = swapPrev.letterTrans true true from rfl)
    exact Bool.noConfusion hfalse
  · refine ⟨Unit, inferInstance, constOut, fun a =>
      ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨(), Subsingleton.elim _ _⟩⟩, ?_⟩
    rintro ⟨P, hP, N, hN⟩
    have h1 := congrFun hN [true]
    have h2 := congrFun hN [false]
    simp [Mealy.eval, Mealy.run, constOut] at h1 h2
    exact absurd (h1.symm.trans h2) (by simp)

/-! ### Exercise `ex:map-lifting-continuous` -/

/-- **Exercise `ex:map-lifting-continuous`.**  The map lifting of a continuous function is
continuous.  This is the same statement as Lemma `lem:map-lifting-continuous` of the book, which is
already proved in `PartC/ContAux.lean`; the exercise is therefore an instance of that lemma and is
not proved again here. -/
theorem mapLift_continuous_of_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f) :=
  mapLift_continuous hf

end Transducers
