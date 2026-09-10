/-
Part D, Section *A functional programming language*: the string representation of the
higher-order terms of Definition `def:higher-order-terms`.

The book writes a closed term as a string over an alphabet `F` which consists of the eight letters
used for the elements of a type in Section *Combinators* (`Transducers.Sym8`), the letter `λ:`, the
letter `↑` used for the De Bruijn indices, and the four letters `+ × * →` needed to write the
types; it is these fifteen letters that give the alphabet its name.  Two deviations were necessary.

* **The atomic functions need letters too.**  The book's list of fifteen letters has no letter for
  `fst`, `snd`, `uncons`, `concat`, `split`, `mult`, `map` or `either`, and a term cannot be written
  without naming the atomic function it uses.  The alphabet `Transducers.HSym` below therefore has
  one letter for each of the eighteen atomic functions of `Transducers.HAtom`.  It is still finite,
  which is all that Lemma `claim:parsing-is-regular-with-resource-bounds` needs.

  A letter names the atomic function only, not the types it is instantiated at: those are
  determined by the type of the term, which the string does not carry.  So the representation is
  not injective across types -- `fst` at `A × B → A` and at `A' × B' → A'` are written the same
  way -- and, for the same reason, the two atomic functions that carry a group structure are
  written without it.  This costs nothing here, because the lemma is about the *set* of strings
  that represent a term consistent with a resource bound.

* **Application, and the list terms.**  The book writes an application by juxtaposition and a list
  term as `[a₁,…,aₙ]`.  The syntax formalised in `RequestProject/PartD/HOSyntax.lean` builds a list
  term one entry at a time, by `nil` and `cons`, and `cons` may be applied to a term of list type
  that is not itself a list term.  Application, `nil` and `cons` are therefore each written with a
  letter of their own, in prefix position: the cons-chain `cons a₁ (⋯ (cons aₙ nil))`, which is the
  book's list term `[a₁,…,aₙ]`, is written `⟨cons⟩ a₁ ⋯ ⟨cons⟩ aₙ ⟨nil⟩`.  Pairs and the unit term
  are written as in the book, `(a,b)` and `1`, and so are the types, always with parentheses.
-/
import RequestProject.PartD.HOBound

namespace Transducers

/-! ## The alphabet -/

/-- The alphabet in which a higher-order term is written.  The first four letters and the two
letters `lam` and `up` are the book's; `plus`, `times`, `star` and `to` write the types; `nil`,
`cons` and `app` write the term constructors that the book writes by juxtaposition or by brackets;
and the remaining eighteen letters name the atomic functions. -/
inductive HSym : Type
  | lpar | rpar | comma | one
  | lam | up
  | plus | times | star | to
  | nil | cons | app
  | atomId | atomFst | atomSnd | atomInl | atomInr | atomDiag | atomCodiag | atomDistr
  | atomConsA | atomUncons | atomReverse | atomConcat | atomBlockSplit | atomPref | atomMult
  | atomSplits | atomMap | atomEither
  deriving DecidableEq, Fintype

/-! ## The string representation of a type -/

/-- The string representation of a higher-order type, always with parentheses, so that it is
unique. -/
def HTy.reprTy : HTy → List HSym
  | .one => [HSym.one]
  | .prod A B => HSym.lpar :: (A.reprTy ++ HSym.times :: (B.reprTy ++ [HSym.rpar]))
  | .sum A B => HSym.lpar :: (A.reprTy ++ HSym.plus :: (B.reprTy ++ [HSym.rpar]))
  | .list A => HSym.lpar :: (A.reprTy ++ [HSym.star, HSym.rpar])
  | .arrow A B => HSym.lpar :: (A.reprTy ++ HSym.to :: (B.reprTy ++ [HSym.rpar]))

/-! ## The string representation of a term -/

/-- The De Bruijn index of a variable: the number of steps up in the syntax tree. -/
def HVar.idx : {Γ : List HTy} → {A : HTy} → HVar Γ A → ℕ
  | _, _, .zero => 0
  | _, _, .succ v => v.idx + 1

lemma HVar.idx_lt {Γ : List HTy} {A : HTy} : ∀ v : HVar Γ A, v.idx < Γ.length
  | .zero => Nat.succ_pos _
  | .succ v => Nat.succ_lt_succ v.idx_lt

/-- The letter that names an atomic function. -/
def HAtom.sym : {H : HTy} → HAtom H → HSym
  | _, .idA _ => .atomId
  | _, .fst _ _ => .atomFst
  | _, .snd _ _ => .atomSnd
  | _, .inl _ _ => .atomInl
  | _, .inr _ _ => .atomInr
  | _, .diag _ => .atomDiag
  | _, .codiag _ => .atomCodiag
  | _, .distr _ _ _ => .atomDistr
  | _, .consA _ => .atomConsA
  | _, .uncons _ => .atomUncons
  | _, .reverse _ => .atomReverse
  | _, .concat _ => .atomConcat
  | _, .blockSplit _ _ => .atomBlockSplit
  | _, .pref _ _ _ => .atomPref
  | _, .mult _ _ _ => .atomMult
  | _, .splits _ => .atomSplits
  | _, .map _ _ => .atomMap
  | _, .either _ _ _ => .atomEither

/-- **The string representation of a term.**  A variable is `↑ⁿ⁺¹`, an atomic function is the
letter that names it, an application is `⟨app⟩ f a`, an abstraction is `λ: A b`, the unit term is
`1`, a pair is `(a,b)`, and the two list constructors are `⟨nil⟩` and `⟨cons⟩ a l`. -/
def HTerm.repr : {Γ : List HTy} → {H : HTy} → HTerm Γ H → List HSym
  | _, _, .var v => List.replicate (v.idx + 1) HSym.up
  | _, _, .atom a => [a.sym]
  | _, _, .app f a => HSym.app :: (f.repr ++ a.repr)
  | _, _, .lam (A := A) b => HSym.lam :: (A.reprTy ++ b.repr)
  | _, _, .unit => [HSym.one]
  | _, _, .pair a b => HSym.lpar :: (a.repr ++ HSym.comma :: (b.repr ++ [HSym.rpar]))
  | _, _, .nil => [HSym.nil]
  | _, _, .cons a l => HSym.cons :: (a.repr ++ l.repr)

@[simp] lemma HTerm.repr_var {Γ : List HTy} {A : HTy} (v : HVar Γ A) :
    (HTerm.var v).repr = List.replicate (v.idx + 1) HSym.up := rfl

@[simp] lemma HTerm.repr_atom {Γ : List HTy} {H : HTy} (a : HAtom H) :
    (HTerm.atom (Γ := Γ) a).repr = [a.sym] := rfl

@[simp] lemma HTerm.repr_app {Γ : List HTy} {A B : HTy} (f : HTerm Γ (.arrow A B))
    (a : HTerm Γ A) : (f.app a).repr = HSym.app :: (f.repr ++ a.repr) := rfl

@[simp] lemma HTerm.repr_lam {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) :
    (HTerm.lam b).repr = HSym.lam :: (A.reprTy ++ b.repr) := rfl

@[simp] lemma HTerm.repr_unit {Γ : List HTy} :
    (HTerm.unit (Γ := Γ)).repr = [HSym.one] := rfl

@[simp] lemma HTerm.repr_pair {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) (b : HTerm Γ B) :
    (a.pair b).repr = HSym.lpar :: (a.repr ++ HSym.comma :: (b.repr ++ [HSym.rpar])) := rfl

@[simp] lemma HTerm.repr_nil {Γ : List HTy} {A : HTy} :
    (HTerm.nil (Γ := Γ) (A := A)).repr = [HSym.nil] := rfl

@[simp] lemma HTerm.repr_cons {Γ : List HTy} {A : HTy} (a : HTerm Γ A) (l : HTerm Γ (.list A)) :
    (a.cons l).repr = HSym.cons :: (a.repr ++ l.repr) := rfl

end Transducers
