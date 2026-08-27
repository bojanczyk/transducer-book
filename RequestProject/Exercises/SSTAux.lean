/-
The auxiliary notions that the solutions to the exercises of the chapter *Streaming string
transducers* (`sst.tex`) of *Transducers* (M. Bojańczyk) take for granted: copyful streaming
string transducers, and polynomial automata.

Neither notion is a numbered result of the book: copyful ssts are introduced in Exercise
`exer:sst-copyful-sst` ("consider copyful ssts, i.e. ones where the copyless restriction is
lifted") and polynomial automata in Exercise `exer:sst-polynomial-automaton`.  They are defined
here, next to the exercises that use them, and the exercises themselves are in
`RequestProject/Exercises/SST.lean`.

The copyless ssts of Definition `def:sst` are `Transducers.SST`, in
`RequestProject/PartC/SSTDef.lean`; a copyful sst is the same structure without the field
`step_copyless`, and it reuses `Transducers.SST.subst` for the semantics.
-/
import RequestProject.PartC.SSTDef
import RequestProject.Common.Basic

namespace Transducers.Exercises

open Transducers

/-! ## Copyful streaming string transducers -/

/-- A **copyful sst**: a streaming string transducer in the sense of Definition `def:sst` from
which the copyless restriction has been dropped (Exercise `exer:sst-copyful-sst`). -/
structure CopyfulSST (A B Q X : Type) [Fintype X] where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a new state and a register update. -/
  step : Q → A → Q × (X → List (X ⊕ B))
  /-- The final output function. -/
  final : Q → List (X ⊕ B)

namespace CopyfulSST

variable {A B Q X : Type} [Fintype X]

/-- Reading one input letter. -/
def stepConfig (T : CopyfulSST A B Q X) (c : Q × (X → List B)) (a : A) : Q × (X → List B) :=
  ((T.step c.1 a).1, fun x => SST.subst c.2 ((T.step c.1 a).2 x))

/-- The configuration reached after reading an input string. -/
def runConfig (T : CopyfulSST A B Q X) (w : List A) : Q × (X → List B) :=
  w.foldl T.stepConfig (T.init, fun _ => [])

/-- The semantics of a copyful sst. -/
def eval (T : CopyfulSST A B Q X) (w : List A) : List B :=
  SST.subst (T.runConfig w).2 (T.final (T.runConfig w).1)

@[simp] lemma runConfig_nil (T : CopyfulSST A B Q X) :
    T.runConfig [] = (T.init, fun _ => []) := rfl

lemma runConfig_cons (T : CopyfulSST A B Q X) (a : A) (w : List A) :
    T.runConfig (a :: w) = w.foldl T.stepConfig (T.stepConfig (T.init, fun _ => []) a) := rfl

/-- Every (copyless) sst is in particular a copyful one. -/
def ofSST (T : SST A B Q X) : CopyfulSST A B Q X :=
  ⟨T.init, T.step, T.final⟩

@[simp] lemma ofSST_eval (T : SST A B Q X) : (ofSST T).eval = T.eval := rfl

end CopyfulSST

/-- A string-to-string function computed by a copyful sst. -/
def IsCopyfulSST {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q X : Type) (_ : Finite Q) (instX : Fintype X) (T : @CopyfulSST A B Q X instX), T.eval = f

/-- A register update in which each register name `x` occurs exactly once, inside the string
assigned to `x` itself, is copyless. -/
lemma copyless_of_self {X B : Type} [Fintype X] (u : X → List (X ⊕ B))
    (h : ∀ v, ∃ pre post : List B,
      u v = pre.map Sum.inr ++ Sum.inl v :: post.map Sum.inr) : Copyless u := by
  have hnone : ∀ l : List B, List.filterMap (fun _ : B => (none : Option X)) l = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih => simp [ih]
  have key : ∀ l : List X, ((l.map u).flatten.filterMap
      (fun z : X ⊕ B => match z with | Sum.inl x => some x | Sum.inr _ => none)) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons v l ih =>
        obtain ⟨pre, post, hv⟩ := h v
        rw [List.map_cons, List.flatten_cons, List.filterMap_append, ih, hv]
        simp [Function.comp_def, hnone]
  have hiff : Copyless u ↔ (((Finset.univ : Finset X).toList.map u).flatten.filterMap
      (fun z : X ⊕ B => match z with | Sum.inl x => some x | Sum.inr _ => none)).Nodup := Iff.rfl
  rw [hiff, key]
  exact Finset.nodup_toList _

/-! ### Substitution: lengths and the action on a dfa -/

namespace SST

variable {B X : Type}

@[simp] lemma subst_nil (η : X → List B) : SST.subst η ([] : List (X ⊕ B)) = [] := rfl

lemma subst_cons (η : X → List B) (z : X ⊕ B) (s : List (X ⊕ B)) :
    SST.subst η (z :: s)
      = (match z with | Sum.inl x => η x | Sum.inr b => [b]) ++ SST.subst η s := by
  cases z <;> simp [SST.subst]

lemma subst_append (η : X → List B) (s t : List (X ⊕ B)) :
    SST.subst η (s ++ t) = SST.subst η s ++ SST.subst η t := by
  simp [SST.subst]

end SST

variable {A B Q X σ : Type}

/-- The total size of the registers. -/
def regSize [Fintype X] (η : X → List B) : ℕ := ∑ x : X, (η x).length

lemma length_le_regSize [Fintype X] (η : X → List B) (x : X) :
    (η x).length ≤ regSize η :=
  Finset.single_le_sum (f := fun y => (η y).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ x)

lemma length_subst_le [Fintype X] (η : X → List B) (s : List (X ⊕ B)) :
    (SST.subst η s).length ≤ s.length * (regSize η + 1) := by
  induction s with
  | nil => simp
  | cons z s ih =>
      simp only [List.length_cons]
      rcases z with x | b
      · have h0 : SST.subst η (Sum.inl x :: s) = η x ++ SST.subst η s := by simp [SST.subst]
        have h1 : (η x).length ≤ regSize η + 1 :=
          le_trans (length_le_regSize η x) (Nat.le_succ _)
        rw [h0, List.length_append]
        calc (η x).length + (SST.subst η s).length
            ≤ (regSize η + 1) + s.length * (regSize η + 1) := Nat.add_le_add h1 ih
          _ = (s.length + 1) * (regSize η + 1) := by ring
      · have h0 : SST.subst η (Sum.inr b :: s) = b :: SST.subst η s := by simp [SST.subst]
        rw [h0, List.length_cons]
        calc (SST.subst η s).length + 1
            ≤ s.length * (regSize η + 1) + (regSize η + 1) :=
              Nat.add_le_add ih (Nat.succ_le_succ (Nat.zero_le _))
          _ = (s.length + 1) * (regSize η + 1) := by ring

/-- The action on the states of a dfa of a string over `X + B`, when each register `x` acts by the
function `g x`. -/
def substTrans (D : DFA B σ) (g : X → σ → σ) (s : List (X ⊕ B)) : σ → σ := fun t =>
  s.foldl (fun t z => match z with | Sum.inl x => g x t | Sum.inr b => D.step t b) t

@[simp] lemma substTrans_nil (D : DFA B σ) (g : X → σ → σ) (t : σ) :
    substTrans D g ([] : List (X ⊕ B)) t = t := rfl

lemma substTrans_cons (D : DFA B σ) (g : X → σ → σ) (z : X ⊕ B) (s : List (X ⊕ B)) (t : σ) :
    substTrans D g (z :: s) t
      = substTrans D g s (match z with | Sum.inl x => g x t | Sum.inr b => D.step t b) := rfl

/-- Substituting the registers and then running the dfa is the same as letting each register act
by the transformation it induces on the states of the dfa. -/
lemma evalFrom_subst (D : DFA B σ) (η : X → List B) (s : List (X ⊕ B)) (t : σ) :
    D.evalFrom t (SST.subst η s) = substTrans D (fun x t => D.evalFrom t (η x)) s t := by
  induction s generalizing t with
  | nil => simp [DFA.evalFrom]
  | cons z s ih =>
      rw [SST.subst_cons, DFA.evalFrom_of_append, ih, substTrans_cons]
      cases z with
      | inl x => rfl
      | inr b => simp [DFA.evalFrom]

/-! ## Polynomial automata -/

/-- A **polynomial automaton** (Exercise `exer:sst-polynomial-automaton`): an automaton with
registers, like an sst, except that the registers hold rational numbers, and that the updates are
arbitrary polynomials in the registers -- so they need not be copyless, and they may use both
addition and multiplication.  A polynomial automaton computes a function from strings to rational
numbers. -/
structure PolyAut (A Q X : Type) where
  /-- The initial state. -/
  init : Q
  /-- The initial values of the registers. -/
  initVal : X → ℚ
  /-- The transition function: a new state and a polynomial update of the registers. -/
  step : Q → A → Q × (X → MvPolynomial X ℚ)
  /-- The final output: a polynomial in the registers. -/
  final : Q → MvPolynomial X ℚ

namespace PolyAut

variable {A Q X : Type}

/-- Reading one input letter. -/
def stepVal (P : PolyAut A Q X) (c : Q × (X → ℚ)) (a : A) : Q × (X → ℚ) :=
  ((P.step c.1 a).1, fun x => MvPolynomial.eval c.2 ((P.step c.1 a).2 x))

/-- The configuration reached after reading an input string. -/
def runConfig (P : PolyAut A Q X) (w : List A) : Q × (X → ℚ) :=
  w.foldl P.stepVal (P.init, P.initVal)

/-- The semantics of a polynomial automaton. -/
def eval (P : PolyAut A Q X) (w : List A) : ℚ :=
  MvPolynomial.eval (P.runConfig w).2 (P.final (P.runConfig w).1)

end PolyAut

/-- A string-to-rational-number function computed by a polynomial automaton. -/
def IsPolyAut {A : Type} (f : List A → ℚ) : Prop :=
  ∃ (Q X : Type) (_ : Finite Q) (_ : Finite X) (P : PolyAut A Q X), P.eval = f

end Transducers.Exercises
