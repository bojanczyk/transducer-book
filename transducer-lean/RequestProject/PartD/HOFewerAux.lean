/-
Part D, Section *A functional programming language*: the combinatorial identities behind Lemma
`lem:fewer-atomic`.

Lemma `lem:fewer-atomic` says that the atomic functions `id`, `diag`, `codiag`, `distr`, `cons`,
`reverse`, the block split of Example `ex:block` and group prefix multiplication are redundant in
the presence of the higher-order features.  For the first five the book gives the defining terms,
and they are immediate; the last three are Example `ex:reverse-from-split` and the two exercises
the book refers to -- eliminating the block split, and replacing group prefix multiplication by the
product of a list -- whose labels the sources of this copy of the book do not define; each of them
computes its output by running over all the ways of cutting the input list into a prefix and a
suffix.  This file proves the three identities that those computations rest on, as statements
about lists:

* `Transducers.flatten_headAsList_splits` -- reversing a list;
* `Transducers.twiFun_eq` and `Transducers.bsFun_eq` -- the two components of the block split, the
  first one being the longest prefix of entries from `A`, which is found by keeping the cuts whose
  prefix contains no entry from `B`;
* `Transducers.prefFun_eq` -- the prefix products, which are the products of the non-empty
  prefixes.
-/
import RequestProject.PartD.HOSyntax

namespace Transducers

variable {X Y : Type}

/-! ## Recursion over the cuts of a list -/

/-- The cuts of `x :: l`, from the empty prefix to the whole list: the empty cut, and the cuts of
`l` with `x` put in front of the prefix. -/
theorem splitsList_reverse_cons (x : X) (l : List X) :
    (splitsList (x :: l)).reverse
      = ([], x :: l) :: ((splitsList l).reverse.map (fun z => (x :: z.1, z.2))) := by
  rw [splitsList_reverse, splitsList_reverse, List.length_cons, List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def]

/-- The recursion that the three identities of this file use. -/
theorem flatten_map_splitsRev_cons (f : List X × List X → List Y) (x : X) (l : List X) :
    (((splitsList (x :: l)).reverse).map f).flatten
      = f ([], x :: l) ++ (((splitsList l).reverse).map (fun z => f (x :: z.1, z.2))).flatten := by
  rw [splitsList_reverse_cons]
  simp [List.map_map, Function.comp_def]

/-- A list of empty lists flattens to the empty list. -/
theorem flatten_map_nil (L : List X) : ((L.map (fun _ => ([] : List Y))).flatten) = [] := by
  simp

/-- Reversing a list of lists of at most one entry reverses their concatenation. -/
theorem flatten_reverse_of_length_le_one : ∀ (L : List (List Y)), (∀ u ∈ L, u.length ≤ 1) →
    (L.reverse).flatten = L.flatten.reverse
  | [], _ => rfl
  | u :: L, h => by
      have hu : u.reverse = u := by
        match u, h u (by simp) with
        | [], _ => rfl
        | [a], _ => rfl
      have ih := flatten_reverse_of_length_le_one L (fun v hv => h v (by simp [hv]))
      simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.reverse_append,
        List.flatten_nil, List.append_nil, hu]
      rw [ih]

/-! ## Reversing a list -/

/-- The head of a list, as a list of at most one entry. -/
def headAsList (l : List X) : List X :=
  match l with
  | [] => []
  | a :: _ => [a]

@[simp] lemma headAsList_nil : headAsList ([] : List X) = [] := rfl

@[simp] lemma headAsList_cons (a : X) (l : List X) : headAsList (a :: l) = [a] := rfl

/-- Running over the cuts of a list, from the empty prefix to the whole list, and keeping the first
entry of every suffix, gives the list back. -/
theorem flatten_headAsList_splitsRev (l : List X) :
    ((((splitsList l).reverse).map (fun z => headAsList z.2)).flatten) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [flatten_map_splitsRev_cons (fun z => headAsList z.2) a l]
      simpa using ih

/-- **Example `ex:reverse-from-split`.**  Running over the cuts of a list in the order of the
atomic function `split` -- the prefix getting shorter -- and keeping the first entry of every
suffix, gives the reverse of the list. -/
theorem flatten_headAsList_splits (l : List X) :
    (((splitsList l).map (fun z => headAsList z.2)).flatten) = l.reverse := by
  have hlen : ∀ u ∈ ((splitsList l).reverse).map (fun z => headAsList z.2), u.length ≤ 1 := by
    intro u hu
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hu
    cases z.2 <;> simp
  have h := flatten_reverse_of_length_le_one
    (((splitsList l).reverse).map (fun z => headAsList z.2)) hlen
  rw [← List.map_reverse, List.reverse_reverse] at h
  rw [h, flatten_headAsList_splitsRev]

/-! ## The block split -/

section Block

variable {A B : Type}

/-- The entries of a list over `A + B` that come from `B`. -/
def inrPart (u : List (A ⊕ B)) : List B :=
  (u.map (fun x => match x with | Sum.inl _ => ([] : List B) | Sum.inr b => [b])).flatten

@[simp] lemma inrPart_nil : inrPart ([] : List (A ⊕ B)) = [] := rfl

@[simp] lemma inrPart_inl (a : A) (u : List (A ⊕ B)) : inrPart (Sum.inl a :: u) = inrPart u := by
  simp [inrPart]

@[simp] lemma inrPart_inr (b : B) (u : List (A ⊕ B)) :
    inrPart (Sum.inr b :: u) = b :: inrPart u := by
  simp [inrPart]

/-- The first entry of a list over `A + B`, if it comes from `A`. -/
def headInl (v : List (A ⊕ B)) : List A :=
  match v with
  | Sum.inl a :: _ => [a]
  | _ => []

/-- The longest prefix of entries from `A`, computed by running over the cuts of the list: a cut
whose prefix contains no entry from `B` contributes the first entry of its suffix, if that entry
comes from `A`. -/
def twiFun (m : List (A ⊕ B)) : List A :=
  ((((splitsList m).reverse).map
    (fun z => match inrPart z.1 with | [] => headInl z.2 | _ => [])).flatten)

/-- The computation above gives the first component of the block split. -/
theorem twiFun_eq (m : List (A ⊕ B)) : twiFun m = (splitList m).1 := by
  induction m with
  | nil => rfl
  | cons x m ih =>
      rw [twiFun, flatten_map_splitsRev_cons
        (fun z => match inrPart z.1 with | [] => headInl z.2 | _ => []) x m]
      cases x with
      | inl a =>
          have hstep : ∀ z : List (A ⊕ B) × List (A ⊕ B),
              (match inrPart (Sum.inl a :: z.1) with | [] => headInl z.2 | _ => [])
                = (match inrPart z.1 with | [] => headInl z.2 | _ => []) := by
            intro z; rw [inrPart_inl]
          simp only [hstep]
          rw [show ((match inrPart ([] : List (A ⊕ B)) with
              | [] => headInl (Sum.inl a :: m) | _ => []) : List A) = [a] from rfl]
          rw [← twiFun, ih]
          simp
      | inr b =>
          have hstep : ∀ z : List (A ⊕ B) × List (A ⊕ B),
              (match inrPart (Sum.inr b :: z.1) with | [] => headInl z.2 | _ => [])
                = ([] : List A) := by
            intro z; rw [inrPart_inr]
          simp only [hstep]
          rw [flatten_map_nil]
          simp [headInl]

/-- The second component of the block split, computed by running over the cuts of the list: a cut
whose suffix begins with an entry `b` from `B` contributes `b`, together with the block of entries
from `A` that follows it. -/
def bsFun (l : List (A ⊕ B)) : List (B × List A) :=
  ((((splitsList l).reverse).map
    (fun z => match z.2 with | Sum.inr b :: rest => [(b, twiFun rest)] | _ => [])).flatten)

/-- The computation above gives the second component of the block split. -/
theorem bsFun_eq (l : List (A ⊕ B)) : bsFun l = (splitList l).2 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [bsFun, flatten_map_splitsRev_cons
        (fun z => match z.2 with | Sum.inr b :: rest => [(b, twiFun rest)] | _ => []) x l]
      cases x with
      | inl a =>
          rw [show ((match (Sum.inl a :: l) with
            | Sum.inr b :: rest => [(b, twiFun rest)] | _ => []) : List (B × List A)) = [] from rfl]
          rw [← bsFun, ih]
          simp
      | inr b =>
          rw [show ((match (Sum.inr b :: l) with
              | Sum.inr b :: rest => [(b, twiFun rest)] | _ => []) : List (B × List A))
            = [(b, twiFun l)] from rfl]
          rw [← bsFun, ih, twiFun_eq]
          simp

end Block

/-! ## The prefix products -/

section Pref

variable {M : Type} [Monoid M]

lemma prefixProd_nil : prefixProd ([] : List M) = [] := rfl

/-- Shifting the starting point of the running products. -/
lemma scanl_mul_left (h : M) : ∀ (l : List M) (k : M),
    l.scanl (· * ·) (h * k) = (l.scanl (· * ·) k).map (fun g => h * g)
  | [], k => rfl
  | a :: l, k => by
      have h1 : ((a :: l).scanl (· * ·) (h * k)) = (h * k) :: (l.scanl (· * ·) (h * k * a)) := by
        simp [List.scanl]
      have h2 : ((a :: l).scanl (· * ·) k) = k :: (l.scanl (· * ·) (k * a)) := by
        simp [List.scanl]
      rw [h1, h2, mul_assoc, scanl_mul_left h l (k * a)]
      simp

lemma prefixProd_eq_scanl (a : M) (l : List M) : prefixProd (a :: l) = l.scanl (· * ·) a := by
  show ((a :: l).scanl (· * ·) 1).tail = _
  have h1 : ((a :: l).scanl (· * ·) 1) = 1 :: (l.scanl (· * ·) (1 * a)) := by
    simp [List.scanl]
  rw [h1, one_mul]
  rfl

lemma prefixProd_cons (a : M) (l : List M) :
    prefixProd (a :: l) = a :: (prefixProd l).map (fun g => a * g) := by
  rw [prefixProd_eq_scanl]
  cases l with
  | nil => rfl
  | cons b l =>
      have h2 : ((b :: l).scanl (· * ·) a) = a :: (l.scanl (· * ·) (a * b)) := by
        simp [List.scanl]
      rw [h2, prefixProd_eq_scanl, scanl_mul_left a l b]

/-- The products of the prefixes of a list, from the empty prefix to the whole list. -/
theorem map_prod_splitsRev : ∀ l : List M,
    (((splitsList l).reverse).map (fun z => z.1.prod)) = 1 :: prefixProd l
  | [] => rfl
  | x :: l => by
      rw [splitsList_reverse_cons]
      simp only [List.map_cons, List.map_map, Function.comp_def, List.prod_nil]
      rw [show (fun z : List M × List M => (x :: z.1).prod)
        = (fun z : List M × List M => x * z.1.prod) from funext (fun z => by simp)]
      rw [show (fun z : List M × List M => x * z.1.prod)
        = ((fun g => x * g) ∘ (fun z : List M × List M => z.1.prod)) from rfl]
      rw [← List.map_map, map_prod_splitsRev l, prefixProd_cons]
      simp

/-- The contribution of one cut to the prefix products: a non-empty prefix contributes its
product, and the empty prefix contributes nothing. -/
def prefStep (u : List M) : List M :=
  match u with | [] => [] | _ => [u.prod]

@[simp] lemma prefStep_nil : prefStep ([] : List M) = [] := rfl

@[simp] lemma prefStep_cons (a : M) (u : List M) : prefStep (a :: u) = [a * u.prod] := by
  simp [prefStep]

/-- The prefix products of a list, computed by running over the cuts of the list: every non-empty
prefix contributes its product. -/
def prefFun (l : List M) : List M :=
  ((((splitsList l).reverse).map (fun z => prefStep z.1)).flatten)

/-- The computation above gives the prefix products. -/
theorem prefFun_eq : ∀ l : List M, prefFun l = prefixProd l
  | [] => rfl
  | x :: l => by
      rw [prefFun, flatten_map_splitsRev_cons (fun z : List M × List M => prefStep z.1) x l]
      have hstep : ∀ z : List M × List M, prefStep (x :: z.1) = [x * z.1.prod] := by
        intro z; simp
      simp only [hstep, prefStep_nil, List.nil_append]
      rw [show (fun z : List M × List M => [x * z.1.prod])
        = (fun u : List M => [x * u.prod]) ∘ (fun z : List M × List M => z.1) from rfl]
      have : ∀ (L : List (List M × List M)),
          ((L.map (fun z => [x * z.1.prod])).flatten) = L.map (fun z => x * z.1.prod) := by
        intro L
        induction L with
        | nil => rfl
        | cons z L ih => simpa using ih
      rw [show ((((splitsList l).reverse).map
          ((fun u : List M => [x * u.prod]) ∘ (fun z : List M × List M => z.1))).flatten)
        = ((((splitsList l).reverse).map (fun z => [x * z.1.prod])).flatten) from rfl]
      rw [this]
      rw [show (fun z : List M × List M => x * z.1.prod)
        = ((fun g => x * g) ∘ (fun z : List M × List M => z.1.prod)) from rfl]
      rw [← List.map_map, map_prod_splitsRev l, prefixProd_cons]
      simp

end Pref

/-! ## The prefix products of a list over an arrow-free group type -/

section GroupPref

variable {G : Ty} [inst : Group G.Elt]

/-- Group prefix multiplication, computed by running over the cuts of the list: every non-empty
prefix contributes its product. -/
theorem groupPrefixProd_eq (l : List (HTy.ofTy G).Sem) :
    ((((splitsList l).reverse).map
        (fun z => (prefStep (z.1.map (HTy.toElt G))).map (HTy.ofElt G))).flatten)
      = groupPrefixProd G inst l := by
  rw [groupPrefixProd, ← prefFun_eq, prefFun, splitsList_map, List.map_reverse]
  simp [List.map_map, Function.comp_def, List.map_flatten]

end GroupPref

end Transducers
