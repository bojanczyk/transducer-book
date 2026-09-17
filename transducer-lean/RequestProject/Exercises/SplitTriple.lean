/-
Exercise `exer:split-triple` of Section *A functional programming language* (`higher-order.tex`) of
*Transducers* (M. Bojańczyk).

The exercise asks for a polyregular term (Definition `def:polyregular-terms`) defining the variant
of the split function

    A* → (A* × A × A*)*
    [a₁,…,aₙ] ↦ [t₁,…,tₙ]  where  tᵢ = ([a₁,…,aᵢ₋₁], aᵢ, [aᵢ₊₁,…,aₙ]).

The author's solution is the composition taken here: the atomic function `split` of Definition
`def:polyregular-terms` produces all the cuts of the input into a prefix and a suffix; a term
applied to every cut turns `(w, a :: r)` into the one-entry list `[(w, a, r)]` and `(w, [])` into
the empty list — this is the list deconstructor, distributivity and a case distinction; the results
are concatenated; and the outcome is reversed at the end, because `split` enumerates the cuts with
the prefix getting shorter, so that without the reversal the triples would come out in the order
`tₙ,…,t₁`.

The building blocks `Transducers.Exercises.polyNil` and `Transducers.Exercises.polyPure`, the
recursion `Transducers.flatten_map_splitsRev_cons` over the cuts of a list and the lemma
`Transducers.flatten_reverse_of_length_le_one` are the ones of Exercise `exer:reverse-from-split`,
in `RequestProject/Exercises/HOAtomsFromSplit.lean` and `RequestProject/PartD/HOFewerAux.lean`.

The book writes the codomain as `(A* × A × A*)*` without saying how the product is bracketed; it is
read here as `A* × (A × A*)`.
-/
import RequestProject.Exercises.HOAtomsFromSplit

namespace Transducers

variable {X : Type}

/-! ## The function of the exercise -/

/-- **The function of Exercise `exer:split-triple`.**  Every entry of the list, together with the
prefix before it and the suffix after it, in the order of the input. -/
def splitTriples : List X → List (List X × X × List X)
  | [] => []
  | a :: l => ([], a, l) :: (splitTriples l).map (fun t => (a :: t.1, t.2))

@[simp] lemma splitTriples_nil : splitTriples ([] : List X) = [] := rfl

lemma splitTriples_cons (a : X) (l : List X) :
    splitTriples (a :: l) = ([], a, l) :: (splitTriples l).map (fun t => (a :: t.1, t.2)) := rfl

/-- What the term does to one cut of the input: a cut with a nonempty suffix gives the triple that
cuts out the first entry of that suffix, and the cut with the empty suffix gives nothing. -/
def cutTriple (z : List X × List X) : List (List X × X × List X) :=
  match z.2 with
  | [] => []
  | a :: r => [(z.1, a, r)]

@[simp] lemma cutTriple_nil (w : List X) : cutTriple (w, ([] : List X)) = [] := rfl

@[simp] lemma cutTriple_cons (w : List X) (a : X) (r : List X) :
    cutTriple (w, a :: r) = [(w, a, r)] := rfl

lemma cutTriple_cons_prefix (a : X) (z : List X × List X) :
    cutTriple (a :: z.1, z.2) = (cutTriple z).map (fun t => (a :: t.1, t.2)) := by
  obtain ⟨w, v⟩ := z
  cases v with
  | nil => rfl
  | cons b r => rfl

/-! ## The combinatorial identity -/

/-- Mapping a function over the pieces before flattening is mapping it over the flattening. -/
lemma flatten_map_map {α β γ : Type} (g : β → γ) (h : α → List β) :
    ∀ L : List α, (L.map (fun x => (h x).map g)).flatten = ((L.map h).flatten).map g
  | [] => rfl
  | x :: L => by
      simp only [List.map_cons, List.flatten_cons, List.map_append, flatten_map_map g h L]

/-- Running over the cuts of a list from the empty prefix to the whole list, and cutting out the
first entry of every nonempty suffix, gives the triples of the exercise. -/
theorem flatten_cutTriple_splitsRev (l : List X) :
    (((splitsList l).reverse).map cutTriple).flatten = splitTriples l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [flatten_map_splitsRev_cons cutTriple a l, splitTriples_cons, ← ih]
      have hmap : ∀ z : List X × List X,
          cutTriple (a :: z.1, z.2) = (cutTriple z).map (fun t => (a :: t.1, t.2)) :=
        fun z => cutTriple_cons_prefix a z
      simp only [hmap]
      rw [flatten_map_map (fun t : List X × X × List X => (a :: t.1, t.2)) cutTriple]
      rfl

/-- The same in the order in which the atomic function `split` produces the cuts: the triples come
out reversed, which is why the term of the exercise ends with a reversal. -/
theorem flatten_cutTriple_splits (l : List X) :
    (((splitsList l).map cutTriple).flatten) = (splitTriples l).reverse := by
  have hlen : ∀ u ∈ ((splitsList l).reverse).map (cutTriple (X := X)), u.length ≤ 1 := by
    intro u hu
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hu
    obtain ⟨w, v⟩ := z
    cases v <;> simp
  have h := flatten_reverse_of_length_le_one
    (((splitsList l).reverse).map (cutTriple (X := X))) hlen
  rw [← List.map_reverse, List.reverse_reverse] at h
  rw [h, flatten_cutTriple_splitsRev]

namespace Exercises

/-! ## The term -/

/-- The type `A* × (A × A*)` of the triples of the exercise. -/
abbrev tripleTy (A : Ty) : Ty := .prod (.list A) (.prod A (.list A))

/-- The term applied to every cut: the list deconstructor on the suffix, distributivity, and the
case distinction that returns the empty list on an empty suffix and the one-entry list holding the
triple otherwise. -/
def polyCutTriple (A : Ty) :
    PolyTerm (.prod (.list A) (.list A)) (.list (tripleTy A)) :=
  ((PolyTerm.prodMap (.id (.list A)) (PolyTerm.uncons A)).comp
      (PolyTerm.distr (.list A) .one (.prod A (.list A)))).comp
    ((PolyTerm.sumMap (polyNil (.prod (.list A) .one) (tripleTy A))
        (polyPure (tripleTy A))).comp (PolyTerm.codiag (.list (tripleTy A))))

@[simp] lemma polyCutTriple_eval (A : Ty) (z : (Ty.prod (.list A) (.list A)).Elt) :
    (polyCutTriple A).eval z = cutTriple z := by
  obtain ⟨w, v⟩ := z
  cases v with
  | nil => rfl
  | cons a r => rfl

/-- **The term of Exercise `exer:split-triple`**: the atomic function `split`, the term above
applied to every cut, concatenation, and a reversal. -/
def polySplitTriple (A : Ty) : PolyTerm (.list A) (.list (tripleTy A)) :=
  (((PolyTerm.splits A).comp (PolyTerm.map (polyCutTriple A))).comp
    (PolyTerm.concat (tripleTy A))).comp (PolyTerm.reverse (tripleTy A))

@[simp] lemma polySplitTriple_eval (A : Ty) (l : List A.Elt) :
    (polySplitTriple A).eval l = splitTriples l := by
  show (((splitsList l).map (polyCutTriple A).eval).flatten).reverse = splitTriples l
  have hmap : (splitsList l).map (polyCutTriple A).eval
      = (splitsList l).map (cutTriple (X := A.Elt)) :=
    List.map_congr_left (fun z _ => polyCutTriple_eval A z)
  rw [hmap, flatten_cutTriple_splits, List.reverse_reverse]

/-- **Exercise `exer:split-triple`.**  The variant of the split function that lists every entry of
the input together with the prefix before it and the suffix after it is defined by a polyregular
term. -/
theorem split_triple (A : Ty) :
    ∃ t : PolyTerm (.list A) (Ty.list (tripleTy A)),
      ∀ l : List A.Elt, t.eval l = splitTriples l :=
  ⟨polySplitTriple A, polySplitTriple_eval A⟩

end Exercises
end Transducers
