/-
Part D, Section *Evaluation*, subsection *Simon trees*: Lemma `lem:factorisation-forest-rational`
(Simon trees of bounded height can be produced by a rational function).

## The output type

The book's lemma produces Simon trees as elements of a polynomial type `facttype{h,k}`, built by
induction on `k` with a sum over the labels, one co-ordinate for every child, and a list type for
the children of a node with three or more children.  A rational function, in this project
(`Transducers.IsRationalFun`), is a string-to-string function, so a value of such a type has to be
written as a string.  We use the standard **bracket encoding** (`Transducers.FactTree.enc`) over the
finite alphabet `Transducers.TreeSym A` = `A + {open, close}`: a leaf with letter `a` is written
`a`, and an inner node with children `t₁, …, tₙ` is written `open t₁ ⋯ tₙ close`.  This is an
injective encoding of factorisation trees, and the labels of the book's representation are
recomputed from the tree (`Transducers.FactTree.label`); erasing the brackets gives back the
underlying string (`Transducers.FactTree.erase_enc`).

## The proof

The book's second proof is the one formalised.  For each `k` and each `m ∈ M` the set
`TL h k m` of encodings of Simon trees of height at most `k` and label `m` is a regular language
(`Transducers.FactTree.isRegular_TL`): this is the fact that `facttype{h,k}` is a polynomial
type, proved by the same induction on `k` as the book's definition of `facttype{h,k,m}`.  Hence the
relation "`v` is the encoding of a Simon tree of height `≤ k` whose underlying string is `w`" is a
rational relation (guess the tree, check it with an automaton:
`Transducers.isRationalRel_of_regular_proj`); by the Factorisation Forest Theorem
(`Transducers.factorisation_forest`) it is total for a suitable `k`, and uniformisation
(`Transducers.exists_rationalFun_of_total_rel`, Lemma `lem:uniformisation`) extracts a rational
function from it.
-/
import RequestProject.PartD.FactForest
import RequestProject.PartD.SimonEval
import RequestProject.PartB.GuessCheck
import RequestProject.PartB.UniformFun
import RequestProject.Common.RegLangClosure

namespace Transducers

open Computability

/-- The alphabet of the bracket encoding of factorisation trees: the letters of `A`, an opening
bracket and a closing bracket. -/
inductive TreeSym (A : Type) : Type
  | letter : A → TreeSym A
  | op : TreeSym A
  | cl : TreeSym A

namespace TreeSym

variable {A : Type}

/-- The bracket alphabet embeds into `Option (Option A)`. -/
def toOpt : TreeSym A → Option (Option A)
  | letter a => some (some a)
  | op => some none
  | cl => none

lemma toOpt_injective : Function.Injective (toOpt (A := A)) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [toOpt]

instance [Finite A] : Finite (TreeSym A) := Finite.of_injective _ toOpt_injective

/-- Erasing the brackets. -/
def erase : TreeSym A → List A
  | letter a => [a]
  | op => []
  | cl => []

end TreeSym

open TreeSym

namespace FactTree

variable {A : Type}

/-- The **bracket encoding** of a factorisation tree: a leaf `a` is written `a`, and an inner node
with children `t₁, …, tₙ` is written `open t₁ ⋯ tₙ close`. -/
def enc : FactTree A → List (TreeSym A)
  | leaf a => [TreeSym.letter a]
  | node cs => [TreeSym.op] ++ (cs.map enc).flatten ++ [TreeSym.cl]

@[simp] lemma enc_leaf (a : A) : (leaf a).enc = [TreeSym.letter a] := by rw [enc]

lemma enc_node (cs : List (FactTree A)) :
    (node cs).enc = [TreeSym.op] ++ (cs.map enc).flatten ++ [TreeSym.cl] := by
  rw [enc]

lemma homOf_append {B C : Type} (g : B → List C) (u v : List B) :
    homOf g (u ++ v) = homOf g u ++ homOf g v := by
  simp [homOf]

lemma homOf_flatten {B C : Type} (g : B → List C) (us : List (List B)) :
    homOf g us.flatten = (us.map (homOf g)).flatten := by
  induction us with
  | nil => rfl
  | cons u us ih => rw [List.flatten_cons, homOf_append, ih, List.map_cons, List.flatten_cons]

/-- Erasing the brackets from the encoding of a tree gives its underlying string. -/
theorem erase_enc : ∀ t : FactTree A, homOf erase t.enc = t.yield
  | leaf a => by simp [homOf, erase]
  | node cs => by
    rw [enc_node, homOf_append, homOf_append, homOf_flatten, yield_node, List.map_map]
    have : ∀ c ∈ cs, (homOf erase ∘ enc) c = c.yield := fun c hc => by
      have := List.sizeOf_lt_of_mem hc
      exact erase_enc c
    rw [List.map_congr_left this]
    simp [homOf, erase]

variable {M : Type} [Monoid M] (h : FreeMonoid A →* M)

/-- The possible contents, between the brackets, of the encoding of a node of a Simon tree with
label `m`, given the languages `L m'` of encodings of the candidate children with label `m'`: no
child (then `m = 1`), one child, two children, or at least three children with the same idempotent
label `m`.  This mirrors the book's definition of `facttype{h,k+1,m}`. -/
def innerOf (L : M → Language (TreeSym A)) (m : M) : Language (TreeSym A) :=
  {x | (m = 1 ∧ x = []) ∨ x ∈ L m ∨
    (∃ m₁ m₂ : M, m₁ * m₂ = m ∧ ∃ x₁ ∈ L m₁, ∃ x₂ ∈ L m₂, x = x₁ ++ x₂) ∨
    (IsIdempotentElem m ∧ ∃ x₁ ∈ L m, ∃ x₂ ∈ L m, ∃ x₃ ∈ L m, ∃ y ∈ (L m)∗,
      x = x₁ ++ x₂ ++ x₃ ++ y)}

/-- `TL h k m`: the encodings of the Simon trees of height at most `k` with label `m` (see
`Transducers.FactTree.mem_TL_iff`). -/
def TL : ℕ → M → Language (TreeSym A)
  | 0, m => {w | ∃ a : A, h (FreeMonoid.of a) = m ∧ w = [TreeSym.letter a]}
  | k + 1, m => {w | w ∈ TL k m ∨ ∃ x ∈ innerOf (TL k) m, w = [TreeSym.op] ++ x ++ [TreeSym.cl]}

lemma isRegular_concat3 {L : Language (TreeSym A)} (hL : L.IsRegular) :
    Language.IsRegular {x | ∃ x₁ ∈ L, ∃ x₂ ∈ L, ∃ x₃ ∈ L, ∃ y ∈ L∗,
      x = x₁ ++ x₂ ++ x₃ ++ y} := by
  have h := isRegular_concat (isRegular_concat (isRegular_concat hL hL) hL) (isRegular_kstar hL)
  refine isRegular_of_eq ?_ h
  ext x
  constructor
  · rintro ⟨u, ⟨u', ⟨x₁, h₁, x₂, h₂, rfl⟩, x₃, h₃, rfl⟩, y, hy, rfl⟩
    exact ⟨x₁, h₁, x₂, h₂, x₃, h₃, y, hy, rfl⟩
  · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, y, hy, rfl⟩
    exact ⟨_, ⟨_, ⟨x₁, h₁, x₂, h₂, rfl⟩, x₃, h₃, rfl⟩, y, hy, rfl⟩

lemma isRegular_innerOf [Finite M] {L : M → Language (TreeSym A)} (hL : ∀ m, (L m).IsRegular)
    (m : M) : (innerOf L m).IsRegular := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have h0 : Language.IsRegular {x : List (TreeSym A) | m = 1 ∧ x = []} := by
    refine isRegular_of_eq ?_ (isRegular_prop_and (m = 1) (isRegular_singleton []))
    ext x; rfl
  have h2 : Language.IsRegular {x | ∃ m₁ m₂ : M, m₁ * m₂ = m ∧
      ∃ x₁ ∈ L m₁, ∃ x₂ ∈ L m₂, x = x₁ ++ x₂} := by
    refine isRegular_of_eq ?_ (isRegular_biUnion_finset (Finset.univ : Finset (M × M))
      (fun p => {x | p.1 * p.2 = m ∧ x ∈ {w | ∃ u ∈ L p.1, ∃ v ∈ L p.2, w = u ++ v}})
      (fun p _ => isRegular_prop_and _ (isRegular_concat (hL p.1) (hL p.2))))
    ext x
    constructor
    · rintro ⟨p, -, hp, hx⟩
      exact ⟨p.1, p.2, hp, hx⟩
    · rintro ⟨m₁, m₂, hp, hx⟩
      exact ⟨(m₁, m₂), Finset.mem_univ _, hp, hx⟩
  have h3 := isRegular_prop_and (IsIdempotentElem m) (isRegular_concat3 (hL m))
  exact isRegular_union h0 (isRegular_union (hL m) (isRegular_union h2 h3))

/-- The languages `TL h k m` are regular: `facttype{h,k}` is a polynomial type. -/
theorem isRegular_TL [Finite A] [Finite M] : ∀ (k : ℕ) (m : M), (TL h k m).IsRegular
  | 0, m => by
    classical
    haveI : Fintype A := Fintype.ofFinite A
    refine isRegular_of_subset_finite (F := Finset.univ.image fun a : A => [TreeSym.letter a]) ?_
    rintro w ⟨a, -, rfl⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  | k + 1, m => by
    have hI := isRegular_innerOf (fun m' => isRegular_TL k m') m
    have hb : Language.IsRegular {w | ∃ x ∈ innerOf (TL h k) m,
        w = [TreeSym.op] ++ x ++ [TreeSym.cl]} := by
      refine isRegular_of_eq ?_
        (isRegular_concat (isRegular_concat (isRegular_singleton [TreeSym.op]) hI)
          (isRegular_singleton [TreeSym.cl]))
      ext w
      constructor
      · rintro ⟨u, ⟨o, ho, x, hx, rfl⟩, c, hc, rfl⟩
        rw [show o = [TreeSym.op] from ho, show c = [TreeSym.cl] from hc]
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨[TreeSym.op], rfl, x, hx, rfl⟩, [TreeSym.cl], rfl, rfl⟩
    exact isRegular_union (isRegular_TL k m) hb

lemma label_node (cs : List (FactTree A)) :
    label h (node cs) = (cs.map (label h)).prod := by
  rw [prod_labels, label, yield_node]

lemma label_leaf (a : A) : label h (leaf a) = h (FreeMonoid.of a) := by
  simp [label]

/-- The forests whose encodings are given by a list of words of `TL h k m`. -/
lemma forest_of_kstar {k : ℕ} {m : M}
    (ih : ∀ w ∈ TL h k m, ∃ t : FactTree A, t.enc = w ∧ t.IsSimon h ∧ t.height ≤ k ∧
      label h t = m) :
    ∀ ws : List (List (TreeSym A)), (∀ w ∈ ws, w ∈ TL h k m) →
      ∃ cs : List (FactTree A), (cs.map enc).flatten = ws.flatten ∧
        ∀ c ∈ cs, c.IsSimon h ∧ c.height ≤ k ∧ label h c = m
  | [], _ => ⟨[], rfl, by simp⟩
  | w :: ws, hws => by
    obtain ⟨t, rfl, ht⟩ := ih w (hws w (by simp))
    obtain ⟨cs, hcs, hc⟩ := forest_of_kstar ih ws (fun w hw => hws w (by simp [hw]))
    refine ⟨t :: cs, by simp [hcs], ?_⟩
    intro c hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ht
    · exact hc c hc'

/-- Every word of `TL h k m` encodes a Simon tree of height at most `k` and label `m`. -/
theorem TL_sound : ∀ (k : ℕ) (m : M) (w : List (TreeSym A)), w ∈ TL h k m →
    ∃ t : FactTree A, t.enc = w ∧ t.IsSimon h ∧ t.height ≤ k ∧ label h t = m
  | 0, m, w, ⟨a, ha, hw⟩ => ⟨leaf a, by simp [hw], .leaf a, by simp, by rw [label_leaf, ha]⟩
  | k + 1, m, w, hw => by
    have ih := TL_sound k
    rcases hw with hw | ⟨x, hx, rfl⟩
    · obtain ⟨t, h₁, h₂, h₃, h₄⟩ := ih m w hw
      exact ⟨t, h₁, h₂, by omega, h₄⟩
    rcases hx with ⟨rfl, rfl⟩ | hx | ⟨m₁, m₂, rfl, x₁, h₁, x₂, h₂, rfl⟩ |
        ⟨he, x₁, h₁, x₂, h₂, x₃, h₃, y, hy, rfl⟩
    · refine ⟨node [], by simp [enc_node], .node [] (by simp) (by simp), ?_, by simp [label_node]⟩
      exact height_node_le (n := k) (by simp)
    · obtain ⟨t, rfl, ht, hk, hl⟩ := ih m x hx
      refine ⟨node [t], by simp [enc_node], .node [t] (by simpa using ht) (by simp), ?_,
        by simp [label_node, hl]⟩
      exact height_node_le (by simpa using hk)
    · obtain ⟨t₁, rfl, ht₁, hk₁, rfl⟩ := ih _ x₁ h₁
      obtain ⟨t₂, rfl, ht₂, hk₂, rfl⟩ := ih _ x₂ h₂
      refine ⟨node [t₁, t₂], by simp [enc_node], .node _ ?_ (by simp), ?_, by simp [label_node]⟩
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> assumption
      · refine height_node_le fun c hc => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> assumption
    · obtain ⟨t₁, rfl, ht₁, hk₁, hl₁⟩ := ih _ x₁ h₁
      obtain ⟨t₂, rfl, ht₂, hk₂, hl₂⟩ := ih _ x₂ h₂
      obtain ⟨t₃, rfl, ht₃, hk₃, hl₃⟩ := ih _ x₃ h₃
      obtain ⟨ws, rfl, hws⟩ := Language.mem_kstar.mp hy
      obtain ⟨cs, hcs, hc⟩ := forest_of_kstar h (ih m) ws hws
      have hall : ∀ c ∈ t₁ :: t₂ :: t₃ :: cs, c.IsSimon h ∧ c.height ≤ k ∧ label h c = m := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | rfl | rfl | hc'
        · exact ⟨ht₁, hk₁, hl₁⟩
        · exact ⟨ht₂, hk₂, hl₂⟩
        · exact ⟨ht₃, hk₃, hl₃⟩
        · exact hc c hc'
      refine ⟨node (t₁ :: t₂ :: t₃ :: cs), ?_, .node _ (fun c hc' => (hall c hc').1)
        (fun _ => ⟨m, he, fun c hc' => (hall c hc').2.2⟩),
        height_node_le fun c hc' => (hall c hc').2.1, ?_⟩
      · rw [enc_node, ← hcs]
        simp
      · rw [label_node, List.map_cons, hl₁]
        refine prod_cons_idem he _ ?_
        intro z hz
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hz
        exact (hall c (List.mem_cons_of_mem _ hc')).2.2

lemma TL_mono (k : ℕ) (m : M) {w : List (TreeSym A)} (hw : w ∈ TL h k m) :
    w ∈ TL h (k + 1) m := Or.inl hw

lemma TL_mono' {k k' : ℕ} (hkk : k ≤ k') (m : M) {w : List (TreeSym A)} (hw : w ∈ TL h k m) :
    w ∈ TL h k' m := by
  induction hkk with
  | refl => exact hw
  | step _ ih => exact TL_mono h _ m ih

/-- The encoding of every Simon tree of height at most `k` lies in `TL h k (label h t)`. -/
theorem TL_complete {t : FactTree A} (ht : t.IsSimon h) :
    ∀ k : ℕ, t.height ≤ k → t.enc ∈ TL h k (label h t) := by
  induction ht with
  | leaf a =>
    intro k _
    exact TL_mono' h (Nat.zero_le k) _ ⟨a, by rw [label_leaf], by simp⟩
  | node cs hcs hidem ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by rw [height_node] at hk; omega⟩
    have hck : ∀ c ∈ cs, c.height ≤ k := fun c hc => by
      have := height_le_of_mem hc; omega
    have hmem : ∀ c ∈ cs, c.enc ∈ TL h k (label h c) := fun c hc => ih c hc k (hck c hc)
    refine Or.inr ⟨(cs.map enc).flatten, ?_, enc_node cs⟩
    rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
    · exact Or.inl ⟨by simp [label_node], rfl⟩
    · exact Or.inr (Or.inl (by simpa [label_node] using hmem c₁ (by simp)))
    · refine Or.inr (Or.inr (Or.inl ⟨label h c₁, label h c₂, by simp [label_node], c₁.enc,
        hmem c₁ (by simp), c₂.enc, hmem c₂ (by simp), by simp⟩))
    · obtain ⟨e, he, hl⟩ := hidem (by simp)
      have hnode : label h (node (c₁ :: c₂ :: c₃ :: cs)) = e := by
        rw [label_node, List.map_cons, hl c₁ (by simp)]
        refine prod_cons_idem he _ ?_
        intro z hz
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hz
        exact hl c (List.mem_cons_of_mem _ hc')
      have hm : ∀ c ∈ c₁ :: c₂ :: c₃ :: cs, c.enc ∈ TL h k e := fun c hc => by
        rw [← hl c hc]; exact hmem c hc
      rw [hnode]
      refine Or.inr (Or.inr (Or.inr ⟨he, c₁.enc, hm c₁ (by simp), c₂.enc, hm c₂ (by simp),
        c₃.enc, hm c₃ (by simp), (cs.map enc).flatten, ?_, by simp⟩))
      refine Language.join_mem_kstar fun y hy => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      exact hm c (by simp [hc])

end FactTree

open FactTree

/-- **Lemma `lem:factorisation-forest-rational`.**  For every monoid homomorphism `h : A* → M`
into a finite monoid (over a finite alphabet `A`) there is a constant `k` and a rational function
`f`, from strings over `A` to strings over the bracket alphabet `TreeSym A`, which maps every
string `w` to (the bracket encoding `FactTree.enc` of) a Simon tree of height at most `k` whose
underlying string is `w`.

The book's codomain is the polynomial type `facttype{h,k}`; since a rational function in this
project is string-to-string, a Simon tree is output through its bracket encoding (see the module
docstring).  The alphabet `A` is required to be finite, as rational functions are defined over
finite alphabets throughout the book. -/
theorem factorisation_forest_rational {A M : Type} [Finite A] [Monoid M] [Finite M]
    (h : FreeMonoid A →* M) :
    ∃ (k : ℕ) (f : List A → List (TreeSym A)), IsRationalFun f ∧
      ∀ w : List A, ∃ t : FactTree A, f w = t.enc ∧ t.yield = w ∧ t.IsSimon h ∧ t.height ≤ k := by
  obtain ⟨k, -, hk⟩ := factorisation_forest h
  let L : Language (TreeSym A) := {v | ∃ m : M, v ∈ TL h k m}
  have hL : L.IsRegular := by
    classical
    haveI : Fintype M := Fintype.ofFinite M
    refine isRegular_of_eq ?_ (isRegular_biUnion_finset (Finset.univ : Finset M) (TL h k)
      (fun m _ => isRegular_TL h k m))
    ext v
    simp [L]
  have hR := isRationalRel_of_regular_proj TreeSym.erase hL
  obtain ⟨f, hf, hfR⟩ := exists_rationalFun_of_total_rel hR (fun w => by
    obtain ⟨t, hy, ht, hh⟩ := hk w
    exact ⟨t.enc, ⟨label h t, TL_complete h ht k hh⟩, by rw [erase_enc, hy]⟩)
  refine ⟨k, f, hf, fun w => ?_⟩
  obtain ⟨⟨m, hm⟩, hw⟩ := hfR w
  obtain ⟨t, he, ht, hh, -⟩ := TL_sound h k m _ hm
  exact ⟨t, he.symm, by rw [← erase_enc, he, hw], ht, hh⟩

end Transducers
