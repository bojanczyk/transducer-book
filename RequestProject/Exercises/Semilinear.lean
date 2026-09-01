/-
Semilinear sets of pairs of natural numbers, and the algebra they need.

A *linear* set of pairs is `b + ℕ·P` for a base point `b` and a finite list of periods `P`; a
*semilinear* set is a finite union of linear ones, and is described by a `List LinPair`.  This
file gives the description, its semantics, and the three operations that the classical proof of
Parikh's theorem for regular languages needs: union, Minkowski sum, and the submonoid generated
by a set.  Semilinear sets are closed under all three, by explicit operations on descriptions.

Nothing here is about transducers.  The file is used by
`RequestProject/Exercises/Parikh.lean`, which proves that the set of weights of the accepting
paths of a finite graph with weights in `ℕ × ℕ` is semilinear, and by
`RequestProject/Exercises/LengthCollision.lean`, which is item (b) of Exercise
`exer:decide-rational-colision`.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Transducers
namespace Exercises

/-! ## Linear and semilinear sets -/

/-- A linear set of pairs, given by a base point and a finite list of periods. -/
abbrev LinPair : Type := (ℕ × ℕ) × List (ℕ × ℕ)

/-- The value `Σ nᵢ pᵢ` of the coefficients `ns` against the periods `ps`.  Missing coefficients
count as zero. -/
def pairCombVal : List (ℕ × ℕ) → List ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | _, [] => (0, 0)
  | p :: ps, n :: ns => (n * p.1 + (pairCombVal ps ns).1, n * p.2 + (pairCombVal ps ns).2)

@[simp] lemma pairCombVal_nil_left (ns : List ℕ) : pairCombVal [] ns = (0, 0) := by
  cases ns <;> rfl

@[simp] lemma pairCombVal_nil_right (ps : List (ℕ × ℕ)) : pairCombVal ps [] = (0, 0) := by
  cases ps <;> rfl

@[simp] lemma pairCombVal_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) (n : ℕ) (ns : List ℕ) :
    pairCombVal (p :: ps) (n :: ns)
      = (n * p.1 + (pairCombVal ps ns).1, n * p.2 + (pairCombVal ps ns).2) := rfl

lemma pairCombVal_cons_eq (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) (n : ℕ) (ns : List ℕ) :
    pairCombVal (p :: ps) (n :: ns) = (n * p.1, n * p.2) + pairCombVal ps ns := by
  simp [Prod.ext_iff]

lemma sum_replicate_pair (k : ℕ) (b : ℕ × ℕ) :
    (List.replicate k b).sum = (k * b.1, k * b.2) := by
  induction k with
  | zero => simp [Prod.ext_iff]
  | succ k ih =>
      rw [List.replicate_succ, List.sum_cons, ih]
      simp [Prod.ext_iff]
      constructor <;> ring

/-- The linear set with base `l.1` and periods `l.2`. -/
def linPairSet (l : LinPair) : Set (ℕ × ℕ) :=
  {x | ∃ ns : List ℕ, x = (l.1.1 + (pairCombVal l.2 ns).1, l.1.2 + (pairCombVal l.2 ns).2)}

/-- A semilinear set of pairs: a finite union of linear sets. -/
def semiPairSet (S : List LinPair) : Set (ℕ × ℕ) := {x | ∃ l ∈ S, x ∈ linPairSet l}

lemma mem_linPairSet {l : LinPair} {x : ℕ × ℕ} :
    x ∈ linPairSet l ↔ ∃ ns : List ℕ, x = l.1 + pairCombVal l.2 ns := by
  constructor
  · rintro ⟨ns, h⟩; exact ⟨ns, by rw [h]; rfl⟩
  · rintro ⟨ns, h⟩; exact ⟨ns, by rw [h]; rfl⟩

lemma mem_semiPairSet {S : List LinPair} {x : ℕ × ℕ} :
    x ∈ semiPairSet S ↔ ∃ l ∈ S, x ∈ linPairSet l := Iff.rfl

@[simp] lemma semiPairSet_nil : semiPairSet [] = ∅ := by
  ext x; simp [semiPairSet]

lemma semiPairSet_cons (l : LinPair) (S : List LinPair) :
    semiPairSet (l :: S) = linPairSet l ∪ semiPairSet S := by
  ext x
  simp only [semiPairSet, Set.mem_setOf_eq, List.mem_cons, Set.mem_union]
  constructor
  · rintro ⟨m, rfl | hm, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨m, hm, hx⟩
  · rintro (hx | ⟨m, hm, hx⟩)
    · exact ⟨l, Or.inl rfl, hx⟩
    · exact ⟨m, Or.inr hm, hx⟩

/-! ## Union -/

lemma semiPairSet_append (S T : List LinPair) :
    semiPairSet (S ++ T) = semiPairSet S ∪ semiPairSet T := by
  ext x
  simp only [semiPairSet, Set.mem_setOf_eq, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨l, hl | hl, hx⟩
    · exact Or.inl ⟨l, hl, hx⟩
    · exact Or.inr ⟨l, hl, hx⟩
  · rintro (⟨l, hl, hx⟩ | ⟨l, hl, hx⟩)
    · exact ⟨l, Or.inl hl, hx⟩
    · exact ⟨l, Or.inr hl, hx⟩

/-! ## Arithmetic of the coefficients -/

lemma pairCombVal_replicate_zero : ∀ (P : List (ℕ × ℕ)) (k : ℕ),
    pairCombVal P (List.replicate k 0) = (0, 0) := by
  intro P
  induction P with
  | nil => intro k; simp
  | cons p P ih =>
      intro k
      cases k with
      | zero => simp
      | succ k => rw [List.replicate_succ, pairCombVal_cons, ih k]; simp

lemma pairCombVal_append_zeros : ∀ (P : List (ℕ × ℕ)) (ns : List ℕ) (k : ℕ),
    pairCombVal P (ns ++ List.replicate k 0) = pairCombVal P ns := by
  intro P
  induction P with
  | nil => intro ns k; simp
  | cons p P ih =>
      intro ns k
      cases ns with
      | nil => simpa using pairCombVal_replicate_zero (p :: P) k
      | cons n ns => rw [List.cons_append, pairCombVal_cons, pairCombVal_cons, ih ns k]

lemma pairCombVal_take : ∀ (P : List (ℕ × ℕ)) (ns : List ℕ),
    pairCombVal P (ns.take P.length) = pairCombVal P ns := by
  intro P
  induction P with
  | nil => intro ns; simp
  | cons p P ih =>
      intro ns
      cases ns with
      | nil => simp
      | cons n ns => rw [List.length_cons, List.take_succ_cons, pairCombVal_cons,
          pairCombVal_cons, ih ns]

/-- The coefficient list `ns`, cut or padded with zeros to have exactly `n` entries. -/
def padCoef (ns : List ℕ) (n : ℕ) : List ℕ := ns.take n ++ List.replicate (n - ns.length) 0

lemma length_padCoef (ns : List ℕ) (n : ℕ) : (padCoef ns n).length = n := by
  simp only [padCoef, List.length_append, List.length_take, List.length_replicate]
  omega

lemma pairCombVal_padCoef (P : List (ℕ × ℕ)) (ns : List ℕ) :
    pairCombVal P (padCoef ns P.length) = pairCombVal P ns := by
  rw [padCoef, pairCombVal_append_zeros, pairCombVal_take]

lemma pairCombVal_append (P₁ P₂ : List (ℕ × ℕ)) (ns : List ℕ) :
    pairCombVal (P₁ ++ P₂) ns
      = pairCombVal P₁ (ns.take P₁.length) + pairCombVal P₂ (ns.drop P₁.length) := by
  induction P₁ generalizing ns with
  | nil => simp
  | cons p P₁ ih =>
      cases ns with
      | nil => simp
      | cons n ns =>
          rw [List.cons_append, pairCombVal_cons, List.length_cons, List.take_succ_cons,
            List.drop_succ_cons, pairCombVal_cons, ih ns]
          simp [Prod.ext_iff]
          omega

/-- Componentwise addition of coefficient lists, padding the shorter one with zeros. -/
def addCoef : List ℕ → List ℕ → List ℕ
  | [], ms => ms
  | ns, [] => ns
  | n :: ns, m :: ms => (n + m) :: addCoef ns ms

lemma pairCombVal_addCoef : ∀ (P : List (ℕ × ℕ)) (ns ms : List ℕ),
    pairCombVal P (addCoef ns ms) = pairCombVal P ns + pairCombVal P ms := by
  intro P
  induction P with
  | nil => intro ns ms; simp
  | cons p P ih =>
      intro ns ms
      cases ns with
      | nil => cases ms <;> simp [addCoef]
      | cons n ns =>
          cases ms with
          | nil => simp [addCoef]
          | cons m ms =>
              rw [addCoef, pairCombVal_cons, pairCombVal_cons, pairCombVal_cons, ih ns ms]
              simp [Prod.ext_iff]
              constructor <;> ring

/-! ## Sum -/

/-- The Minkowski sum of two sets of pairs. -/
def sumSet (A B : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}

lemma sumSet_union_left (A B C : Set (ℕ × ℕ)) :
    sumSet (A ∪ B) C = sumSet A C ∪ sumSet B C := by
  ext x
  simp only [sumSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨a, ha | ha, b, hb, rfl⟩
    · exact Or.inl ⟨a, ha, b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact ⟨a, Or.inl ha, b, hb, rfl⟩
    · exact ⟨a, Or.inr ha, b, hb, rfl⟩

lemma sumSet_union_right (A B C : Set (ℕ × ℕ)) :
    sumSet A (B ∪ C) = sumSet A B ∪ sumSet A C := by
  ext x
  simp only [sumSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨a, ha, b, hb | hb, rfl⟩
    · exact Or.inl ⟨a, ha, b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact ⟨a, ha, b, Or.inl hb, rfl⟩
    · exact ⟨a, ha, b, Or.inr hb, rfl⟩

@[simp] lemma sumSet_empty_left (A : Set (ℕ × ℕ)) : sumSet ∅ A = ∅ := by
  ext x; simp [sumSet]

@[simp] lemma sumSet_empty_right (A : Set (ℕ × ℕ)) : sumSet A ∅ = ∅ := by
  ext x; simp [sumSet]

lemma linPairSet_sum (l m : LinPair) :
    linPairSet ((l.1 + m.1, l.2 ++ m.2) : LinPair)
      = sumSet (linPairSet l) (linPairSet m) := by
  ext x
  simp only [mem_linPairSet, sumSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ns, rfl⟩
    refine ⟨l.1 + pairCombVal l.2 (ns.take l.2.length), ⟨_, rfl⟩,
      m.1 + pairCombVal m.2 (ns.drop l.2.length), ⟨_, rfl⟩, ?_⟩
    rw [pairCombVal_append]
    abel
  · rintro ⟨a, ⟨ns, rfl⟩, b, ⟨ms, rfl⟩, rfl⟩
    refine ⟨padCoef ns l.2.length ++ ms, ?_⟩
    have hlen : (padCoef ns l.2.length).length = l.2.length := length_padCoef _ _
    rw [pairCombVal_append, List.take_left' hlen, List.drop_left' hlen,
      pairCombVal_padCoef]
    abel

/-- The Minkowski sum of two semilinear descriptions. -/
def slSum (S T : List LinPair) : List LinPair :=
  S.flatMap (fun l => T.map (fun m => ((l.1 + m.1, l.2 ++ m.2) : LinPair)))

lemma semiPairSet_slSum (S T : List LinPair) :
    semiPairSet (slSum S T) = sumSet (semiPairSet S) (semiPairSet T) := by
  induction S with
  | nil => simp [slSum]
  | cons l S ih =>
      rw [slSum, List.flatMap_cons, semiPairSet_append, semiPairSet_cons, sumSet_union_left,
        ← ih, ← slSum]
      congr 1
      -- the singleton case
      clear ih
      induction T with
      | nil => simp
      | cons m T ihT =>
          rw [List.map_cons, semiPairSet_cons, semiPairSet_cons, sumSet_union_right, ihT,
            linPairSet_sum]

/-! ## The submonoid generated by a set -/

/-- All the finite sums of elements of `A`. -/
def starSet (A : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {x | ∃ L : List (ℕ × ℕ), (∀ y ∈ L, y ∈ A) ∧ x = L.sum}

lemma zero_mem_starSet (A : Set (ℕ × ℕ)) : (0 : ℕ × ℕ) ∈ starSet A := ⟨[], by simp, by simp⟩

@[simp] lemma starSet_empty : starSet (∅ : Set (ℕ × ℕ)) = {0} := by
  ext x
  simp only [starSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨L, hL, rfl⟩
    cases L with
    | nil => simp
    | cons y L => exact absurd (hL y (by simp)) (by simp)
  · rintro rfl; exact ⟨[], by simp, by simp⟩

lemma starSet_union (A B : Set (ℕ × ℕ)) :
    starSet (A ∪ B) = sumSet (starSet A) (starSet B) := by
  ext x
  constructor
  · rintro ⟨L, hL, rfl⟩
    induction L with
    | nil => exact ⟨0, zero_mem_starSet A, 0, zero_mem_starSet B, by simp⟩
    | cons y L ih =>
        obtain ⟨a, ⟨LA, hLA, rfl⟩, b, ⟨LB, hLB, rfl⟩, hsum⟩ :=
          ih (fun z hz => hL z (List.mem_cons_of_mem y hz))
        rcases hL y (by simp) with hy | hy
        · exact ⟨(y :: LA).sum, ⟨y :: LA, by
              rintro z hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact hy
              · exact hLA z hz, rfl⟩,
            LB.sum, ⟨LB, hLB, rfl⟩, by rw [List.sum_cons, List.sum_cons, hsum]; abel⟩
        · exact ⟨LA.sum, ⟨LA, hLA, rfl⟩, (y :: LB).sum, ⟨y :: LB, by
              rintro z hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact hy
              · exact hLB z hz, rfl⟩, by rw [List.sum_cons, List.sum_cons, hsum]; abel⟩
  · rintro ⟨a, ⟨LA, hLA, rfl⟩, b, ⟨LB, hLB, rfl⟩, rfl⟩
    refine ⟨LA ++ LB, ?_, by rw [List.sum_append]⟩
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact Or.inl (hLA y hy)
    · exact Or.inr (hLB y hy)

/-- The submonoid generated by one linear set is linear, together with the origin. -/
def linStar (l : LinPair) : List LinPair := [((0, 0), []), (l.1, l.1 :: l.2)]

lemma semiPairSet_linStar (l : LinPair) : semiPairSet (linStar l) = starSet (linPairSet l) := by
  ext x
  constructor
  · rintro ⟨m, hm, hxm⟩
    have hm' : m = ((0, 0), []) ∨ m = (l.1, l.1 :: l.2) := by
      simpa [linStar] using hm
    rcases hm' with rfl | rfl
    · obtain ⟨ns, hns⟩ := hxm
      refine ⟨[], by simp, ?_⟩
      simp only [pairCombVal_nil_left] at hns
      simpa [Prod.ext_iff] using hns
    · obtain ⟨ns, hns⟩ := mem_linPairSet.1 hxm
      simp only at hns
      cases ns with
      | nil =>
          refine ⟨[l.1], ?_, ?_⟩
          · intro y hy
            rw [List.mem_singleton.1 hy]
            exact ⟨[], by simp⟩
          · simpa using hns
      | cons k ns =>
          refine ⟨(l.1 + pairCombVal l.2 ns) :: List.replicate k l.1, ?_, ?_⟩
          · intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact ⟨ns, rfl⟩
            · rw [List.eq_of_mem_replicate hy]
              exact ⟨[], by simp⟩
          · rw [List.sum_cons, sum_replicate_pair, hns, pairCombVal_cons_eq]
            abel
  · rintro ⟨L, hL, rfl⟩
    induction L with
    | nil => exact ⟨((0, 0), []), by simp [linStar], ⟨[], by simp [Prod.ext_iff]⟩⟩
    | cons y L ih =>
        obtain ⟨ns, hns⟩ := mem_linPairSet.1 (hL y (by simp))
        obtain ⟨m, hm, hxm⟩ := ih (fun z hz => hL z (List.mem_cons_of_mem y hz))
        have hm' : m = ((0, 0), []) ∨ m = (l.1, l.1 :: l.2) := by
          simpa [linStar] using hm
        refine ⟨(l.1, l.1 :: l.2), by simp [linStar], ?_⟩
        rcases hm' with rfl | rfl
        · obtain ⟨ms, hms⟩ := hxm
          simp only [pairCombVal_nil_left] at hms
          have hz : L.sum = 0 := by
            rw [Prod.ext_iff]
            exact ⟨by simpa using congrArg Prod.fst hms, by simpa using congrArg Prod.snd hms⟩
          refine mem_linPairSet.2 ⟨0 :: ns, ?_⟩
          rw [List.sum_cons, hz, hns, pairCombVal_cons_eq]
          simp
        · obtain ⟨ms, hms⟩ := mem_linPairSet.1 hxm
          simp only at hms
          cases ms with
          | nil =>
              refine mem_linPairSet.2 ⟨1 :: ns, ?_⟩
              rw [List.sum_cons, hms, hns, pairCombVal_cons_eq]
              simp only [pairCombVal_nil_right, one_mul]
              abel
          | cons k ms =>
              refine mem_linPairSet.2 ⟨(k + 1) :: addCoef ns ms, ?_⟩
              rw [List.sum_cons, hms, hns, pairCombVal_cons_eq, pairCombVal_cons_eq,
                pairCombVal_addCoef]
              rw [Prod.ext_iff]
              simp only [Prod.fst_add, Prod.snd_add]
              constructor <;> ring

/-- The submonoid generated by a semilinear set, as a semilinear description. -/
def slStar (S : List LinPair) : List LinPair :=
  S.foldr (fun l acc => slSum (linStar l) acc) [((0, 0), [])]

lemma semiPairSet_slStar (S : List LinPair) :
    semiPairSet (slStar S) = starSet (semiPairSet S) := by
  induction S with
  | nil =>
      rw [slStar, List.foldr_nil, semiPairSet_nil, starSet_empty]
      ext x
      simp only [semiPairSet, Set.mem_setOf_eq, List.mem_singleton, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, rfl, ns, hns⟩
        simpa [Prod.ext_iff] using hns
      · rintro rfl
        exact ⟨((0, 0), []), rfl, ⟨[], by simp [Prod.ext_iff]⟩⟩
  | cons l S ih =>
      rw [slStar, List.foldr_cons, ← slStar, semiPairSet_slSum, ih, semiPairSet_linStar,
        semiPairSet_cons, starSet_union]

end Exercises
end Transducers
