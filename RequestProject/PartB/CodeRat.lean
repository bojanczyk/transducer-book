/-
The rational function described by a code, over the finite alphabets that the
code can see.

The decidability statements of Part B speak about codes, whose alphabet is the
infinite set `ℕ`, while the machine independent characterisations of Section B.4
are about functions over *finite* alphabets.  This file bridges the two.  A code
has finitely many transitions, so it reads only the letters of `codeAlphabet c`
and writes only the letters of `codeOutAlphabet c`; the corresponding subtypes
`InA c` and `OutA c` of `ℕ` are finite (a spurious letter `0` is added to the
output alphabet so that it is nonempty, which is convenient when a machine over
`ℕ` has to be turned into a machine over `OutA c`).  Under the promise that the
code describes a total function on the strings over its alphabet, that function
is `codeFun c : List (InA c) → List (OutA c)`; it is rational, and it is
computed by a Mealy machine exactly when the property appearing in Theorem B.4.2
holds.
-/
import RequestProject.PartB.PrefixCodes
import RequestProject.PartB.RationalStatements

namespace Transducers
namespace CodeRat

open LabAut

/-! ## The finite alphabets and the finite state space of a code -/

/-- The letters that the code can read. -/
def InA (c : RelCode) : Type := {x : ℕ // x ∈ codeAlphabet c}

/-- The letters that the code can write, together with the letter `0`. -/
def OutA (c : RelCode) : Type := {x : ℕ // x ∈ (0 : ℕ) :: codeOutAlphabet c}

/-- The states occurring in the code. -/
def stAll (c : RelCode) : List ℕ :=
  c.2.1 ++ c.2.2 ++ c.1.map (fun t => t.1) ++ c.1.map (fun t => t.2.2.2)

/-- The states of the code. -/
def StQ (c : RelCode) : Type := {q : ℕ // q ∈ stAll c}

instance instFiniteInA (c : RelCode) : Finite (InA c) := by
  sorry

instance instFiniteOutA (c : RelCode) : Finite (OutA c) := by
  sorry

instance instFiniteStQ (c : RelCode) : Finite (StQ c) := by
  sorry

/-! ## The automaton described by a code, over its own alphabets -/

/-- The nfa with output described by a code, over the finite alphabets and the
finite state space of the code. -/
def codeNFAO (c : RelCode) : NFAO (InA c) (OutA c) (StQ c) where
  init := {q | q.val ∈ c.2.1}
  final := {q | q.val ∈ c.2.2}
  δ := {t | (t.1.val, t.2.1.map Subtype.val, t.2.2.1.map Subtype.val, t.2.2.2.val) ∈ c.1}
  δ_finite := by sorry

/-- The relation described by the automaton over the finite alphabets is the
relation described by the code, read through the coercions. -/
theorem codeNFAO_rel (c : RelCode) (w : List (InA c)) (v : List (OutA c)) :
    (codeNFAO c).rel w v ↔ codeRel c (w.map Subtype.val) (v.map Subtype.val) := by
  sorry

/-! ## The function described by a code -/

/-- The function described by a code, over the finite alphabets of the code.
Outside the promise it is junk. -/
noncomputable def codeFun (c : RelCode) (w : List (InA c)) : List (OutA c) :=
  open Classical in
  if h : ∃ v : List (OutA c), codeRel c (w.map Subtype.val) (v.map Subtype.val)
    then h.choose else []

theorem codeFun_spec {c : RelCode} (hc : CodeFunctional c) (w : List (InA c)) :
    codeRel c (w.map Subtype.val) ((codeFun c w).map Subtype.val) := by
  sorry

theorem codeFun_eq {c : RelCode} (hc : CodeFunctional c) {w : List (InA c)} {v : List ℕ}
    (h : codeRel c (w.map Subtype.val) v) : v = (codeFun c w).map Subtype.val := by
  sorry

/-- Under the promise, the function described by a code is rational. -/
theorem isRationalFun_codeFun {c : RelCode} (hc : CodeFunctional c) :
    IsRationalFun (codeFun c) := by
  sorry

/-! ## The Mealy fragment -/

/-- Under the promise, the function described by a code is computed by a Mealy
machine exactly when it is length preserving and prefix preserving. -/
theorem isMealy_codeFun_iff {c : RelCode} (hc : CodeFunctional c) :
    IsMealy (codeFun c) ↔
      ((∀ w v, codeRel c w v → v.length = w.length) ∧ PrefixCodes.PrefixCrit c) := by
  sorry

/-- Under the promise, the property of Theorem B.4.2 -- that the relation
described by the code agrees on the strings over its alphabet with a function
computed by a Mealy machine over `ℕ` -- is equivalent to the function described
by the code over its own alphabets being computed by a Mealy machine. -/
theorem mealyProperty_iff {c : RelCode} (hc : CodeFunctional c) :
    (∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f)
      ↔ IsMealy (codeFun c) := by
  sorry

end CodeRat
end Transducers
