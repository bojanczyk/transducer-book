/-
Codes of *letter automata with terminal output*: the intermediate machine model used by the
effective form of the Uniformisation Lemma `lem:uniformisation` of *Transducers*
(M. Bojańczyk), which discharges the effectivity hypothesis of Exercise
`exer:rational-injectivity-decidable`.

A letter automaton reads exactly one input letter per transition, writes an output string on
each transition, and writes one last output string when it stops, in a state where it is allowed
to stop.  Reading one letter per transition is what makes the runs over a fixed input word
*aligned*: they all use the same number of transitions, so they can be compared position by
position, which is what the selection of a canonical run in
`RequestProject/Exercises/LAutUnif.lean` needs.

Everything here is deliberately concrete: a run is a list of *indices* into the transition list
of the code, and the semantics of a run is computed by a total function into `Option`.  This
makes both the canonical (lexicographically least) run and the computability of the
constructions easy to handle.
-/
import RequestProject.Common.PrimrecList

namespace Transducers.Exercises

/-- A finite description of a *letter automaton with terminal output*: a list of transitions
`(q, a, y, q')` (from the state `q`, reading the letter `a`, writing the string `y`, to the state
`q'`), a list of initial states, and a list of pairs `(q, e)` saying that the automaton may stop
in the state `q`, writing the string `e`. -/
abbrev LCode : Type := List (ℕ × ℕ × List ℕ × ℕ) × List ℕ × List (ℕ × List ℕ)

namespace LAut

/-! ## Semantics -/

/-- The step made by the transition with index `i`, from the state `q`, reading the letter `a`:
the target state and the output string, if that transition applies. -/
def step (L : LCode) (q a i : ℕ) : Option (ℕ × List ℕ) :=
  (L.1[i]?).bind fun t => if t.1 = q ∧ t.2.1 = a then some (t.2.2.2, t.2.2.1) else none

/-- The output written when stopping in the state `q` by the terminal entry with index `k`, if
that entry applies. -/
def term (L : LCode) (q k : ℕ) : Option (List ℕ) :=
  (L.2.2[k]?).bind fun t => if t.1 = q then some t.2 else none

/-- The end state and the output of the path from the state `q` over the input `v` that uses the
transitions with indices `is`; `none` if there is no such path. -/
def pathFrom (L : LCode) : ℕ → List ℕ → List ℕ → Option (ℕ × List ℕ)
  | q, [], [] => some (q, [])
  | q, a :: v, i :: is =>
      (step L q a i).bind fun r => (pathFrom L r.1 v is).map fun z => (z.1, r.2 ++ z.2)
  | _, _, _ => none

/-- The output of the accepting run from the state `q` over `v` that uses the transitions with
indices `is` and stops with the terminal entry of index `k`. -/
def accFrom (L : LCode) (q : ℕ) (v : List ℕ) (is : List ℕ) (k : ℕ) : Option (List ℕ) :=
  (pathFrom L q v is).bind fun z => (term L z.1 k).map fun e => z.2 ++ e

/-- The relation computed by a letter automaton. -/
def rel (L : LCode) (v u : List ℕ) : Prop :=
  ∃ (j q k : ℕ) (is : List ℕ), L.2.1[j]? = some q ∧ accFrom L q v is k = some u

/-- The domain of the relation computed by a letter automaton. -/
def dom (L : LCode) (v : List ℕ) : Prop := ∃ u, rel L v u

@[simp] lemma pathFrom_nil_nil (L : LCode) (q : ℕ) : pathFrom L q [] [] = some (q, []) := rfl

@[simp] lemma pathFrom_nil_cons (L : LCode) (q i : ℕ) (is : List ℕ) :
    pathFrom L q [] (i :: is) = none := rfl

@[simp] lemma pathFrom_cons_nil (L : LCode) (q a : ℕ) (v : List ℕ) :
    pathFrom L q (a :: v) [] = none := rfl

@[simp] lemma pathFrom_cons_cons (L : LCode) (q a i : ℕ) (v is : List ℕ) :
    pathFrom L q (a :: v) (i :: is) =
      (step L q a i).bind fun r => (pathFrom L r.1 v is).map fun z => (z.1, r.2 ++ z.2) := rfl

@[simp] lemma accFrom_nil_nil (L : LCode) (q k : ℕ) : accFrom L q [] [] k = term L q k := by
  simp [accFrom]

@[simp] lemma accFrom_nil_cons (L : LCode) (q i k : ℕ) (is : List ℕ) :
    accFrom L q [] (i :: is) k = none := by
  simp [accFrom]

@[simp] lemma accFrom_cons_nil (L : LCode) (q a k : ℕ) (v : List ℕ) :
    accFrom L q (a :: v) [] k = none := by
  simp [accFrom]

lemma accFrom_cons (L : LCode) (q a i k : ℕ) (v is : List ℕ) :
    accFrom L q (a :: v) (i :: is) k =
      (step L q a i).bind fun r => (accFrom L r.1 v is k).map fun u => r.2 ++ u := by
  simp only [accFrom, pathFrom_cons_cons]
  cases step L q a i with
  | none => simp
  | some r =>
      simp only [Option.bind_some]
      cases pathFrom L r.1 v is with
      | none => simp
      | some z =>
          simp only [Option.map_some, Option.bind_some]
          cases term L z.1 k with
          | none => simp
          | some e => simp

/-- A path over `v` uses exactly `v.length` transitions. -/
lemma length_of_pathFrom (L : LCode) :
    ∀ {q : ℕ} {v is : List ℕ} {z : ℕ × List ℕ}, pathFrom L q v is = some z →
      is.length = v.length := by
  intro q v
  induction v generalizing q with
  | nil =>
      intro is z h
      match is with
      | [] => simp
      | _ :: _ => simp at h
  | cons a v ih =>
      intro is z h
      match is with
      | [] => simp at h
      | i :: is =>
          simp only [pathFrom_cons_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨r, -, z', hz', -⟩ := h
          simp [ih hz']

/-! ## Completability and the canonical run

The canonical run over an input word is the lexicographically least accepting one; it is
defined greedily, which is possible because "an accepting run can be completed from here" is
decidable.
-/

/-- Whether some accepting run from the state `q` over the input `v` exists. -/
def compFrom (L : LCode) : ℕ → List ℕ → Bool
  | q, [] => (List.range L.2.2.length).any fun k => (term L q k).isSome
  | q, a :: v => (List.range L.1.length).any fun i =>
      match step L q a i with
      | some r => compFrom L r.1 v
      | none => false
  termination_by _ v => v.length

/-- The index of the first transition from `q` reading `a` after which an accepting run over `v`
can still be completed. -/
def leastIdx (L : LCode) (q a : ℕ) (v : List ℕ) : Option ℕ :=
  (List.range L.1.length).find? fun i =>
    match step L q a i with
    | some r => compFrom L r.1 v
    | none => false

/-- The index of the first terminal entry that applies in the state `q`. -/
def leastTerm (L : LCode) (q : ℕ) : Option ℕ :=
  (List.range L.2.2.length).find? fun k => (term L q k).isSome

/-- The greedily chosen — that is, the lexicographically least — accepting path from `q` over
`v`.  Its value is meaningless if there is no accepting run. -/
def leastPathFrom (L : LCode) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | q, a :: v => match leastIdx L q a v with
      | some i => match step L q a i with
          | some r => i :: leastPathFrom L r.1 v
          | none => []
      | none => []
  termination_by _ v => v.length

/-! ### Basic facts about `List.find?` over a range -/

lemma find?_range_none {n : ℕ} {p : ℕ → Bool} (h : (List.range n).find? p = none) :
    ∀ j < n, p j = false := by
  intro j hj
  have := List.find?_eq_none.1 h j (by simpa using hj)
  simpa using this

lemma find?_range_spec : ∀ {n : ℕ} {p : ℕ → Bool} {i : ℕ},
    (List.range n).find? p = some i → i < n ∧ p i = true ∧ ∀ j < i, p j = false := by
  intro n
  induction n with
  | zero => intro p i h; simp at h
  | succ m ih =>
      intro p i h
      rw [List.range_succ, List.find?_append] at h
      cases hm : (List.range m).find? p with
      | some i' =>
          rw [hm, Option.some_or] at h
          have hii : i' = i := Option.some.inj h
          subst hii
          obtain ⟨h1, h2, h3⟩ := ih hm
          exact ⟨by omega, h2, h3⟩
      | none =>
          rw [hm] at h
          simp only [Option.none_or, List.find?_cons, List.find?_nil] at h
          have hall : ∀ j < m, p j = false := find?_range_none hm
          cases hpm : p m with
          | false => rw [hpm] at h; simp at h
          | true =>
              rw [hpm] at h
              simp only [Option.some.injEq] at h
              subst h
              exact ⟨by omega, hpm, hall⟩

/-! ### Completability -/

lemma term_isSome_lt {L : LCode} {q k : ℕ} (h : (term L q k).isSome = true) :
    k < L.2.2.length := by
  by_contra hk
  rw [term, List.getElem?_eq_none (by omega)] at h
  simp at h

lemma step_isSome_lt {L : LCode} {q a i : ℕ} (h : (step L q a i).isSome = true) :
    i < L.1.length := by
  by_contra hk
  rw [step, List.getElem?_eq_none (by omega)] at h
  simp at h

lemma compFrom_iff (L : LCode) : ∀ (v : List ℕ) (q : ℕ),
    compFrom L q v = true ↔ ∃ is k u, accFrom L q v is k = some u := by
  intro v
  induction v with
  | nil =>
      intro q
      rw [compFrom]
      simp only [List.any_eq_true, List.mem_range]
      constructor
      · rintro ⟨k, -, hk⟩
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hk
        exact ⟨[], k, e, by simpa using he⟩
      · rintro ⟨is, k, u, hk⟩
        match is with
        | [] =>
            have hk' : term L q k = some u := by simpa using hk
            exact ⟨k, term_isSome_lt (by rw [hk']; simp), by rw [hk']; simp⟩
        | _ :: _ => simp at hk
  | cons a v ih =>
      intro q
      rw [compFrom]
      simp only [List.any_eq_true, List.mem_range]
      constructor
      · rintro ⟨i, -, hi⟩
        cases hstep : step L q a i with
        | none => rw [hstep] at hi; simp at hi
        | some r =>
            rw [hstep] at hi
            obtain ⟨is, k, u, hk⟩ := (ih r.1).1 hi
            exact ⟨i :: is, k, r.2 ++ u, by rw [accFrom_cons, hstep, Option.bind_some, hk]; simp⟩
      · rintro ⟨is, k, u, hk⟩
        match is with
        | [] => simp at hk
        | i :: is =>
            rw [accFrom_cons] at hk
            cases hstep : step L q a i with
            | none => rw [hstep] at hk; simp at hk
            | some r =>
                rw [hstep, Option.bind_some, Option.map_eq_some_iff] at hk
                obtain ⟨u', hu', -⟩ := hk
                refine ⟨i, step_isSome_lt (by rw [hstep]; simp), ?_⟩
                rw [hstep]
                exact (ih r.1).2 ⟨is, k, u', hu'⟩

/-- An accepting run is a path followed by a terminal entry. -/
lemma compFrom_of_pathFrom {L : LCode} {q r : ℕ} {v : List ℕ} {is : List ℕ} {u : List ℕ}
    (hp : pathFrom L q v is = some (r, u)) (hr : compFrom L r [] = true) :
    compFrom L q v = true := by
  obtain ⟨is', k, e, hk⟩ := (compFrom_iff L [] r).1 hr
  match is' with
  | _ :: _ => simp at hk
  | [] =>
      have ht : term L r k = some e := by simpa using hk
      exact (compFrom_iff L v q).2 ⟨is, k, u ++ e, by simp [accFrom, hp, ht]⟩

/-! ### The canonical path -/

lemma leastTerm_spec {L : LCode} {q k : ℕ} (h : leastTerm L q = some k) :
    (term L q k).isSome = true ∧ ∀ j < k, term L q j = none := by
  obtain ⟨-, h2, h3⟩ := find?_range_spec h
  refine ⟨h2, fun j hj => ?_⟩
  have := h3 j hj
  simpa using this

lemma leastIdx_spec {L : LCode} {q a i : ℕ} {v : List ℕ} (h : leastIdx L q a v = some i) :
    (∃ r, step L q a i = some r ∧ compFrom L r.1 v = true) ∧
      ∀ j < i, ∀ r, step L q a j = some r → compFrom L r.1 v = false := by
  obtain ⟨-, h2, h3⟩ := find?_range_spec h
  constructor
  · cases hstep : step L q a i with
    | none => rw [hstep] at h2; simp at h2
    | some r => exact ⟨r, rfl, by rw [hstep] at h2; exact h2⟩
  · intro j hj r hr
    have := h3 j hj
    rw [hr] at this
    exact this

lemma leastTerm_isSome {L : LCode} {q : ℕ} (h : compFrom L q [] = true) :
    (leastTerm L q).isSome = true := by
  rw [compFrom] at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, hk'⟩ := h
  cases hfind : leastTerm L q with
  | some _ => simp
  | none =>
      have := find?_range_none hfind k hk
      rw [this] at hk'
      simp at hk'

lemma compFrom_nil_of_leastTerm {L : LCode} {q k : ℕ} (h : leastTerm L q = some k) :
    compFrom L q [] = true := by
  rw [compFrom]
  simp only [List.any_eq_true, List.mem_range]
  obtain ⟨h1, -⟩ := leastTerm_spec h
  exact ⟨k, term_isSome_lt h1, h1⟩

lemma leastIdx_isSome {L : LCode} {q a : ℕ} {v : List ℕ} (h : compFrom L q (a :: v) = true) :
    (leastIdx L q a v).isSome = true := by
  rw [compFrom] at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hi'⟩ := h
  cases hfind : leastIdx L q a v with
  | some _ => simp
  | none =>
      have := find?_range_none hfind i hi
      rw [this] at hi'
      simp at hi'

/-- The canonical path really is a path, and it ends in a state where the automaton may stop. -/
lemma pathFrom_leastPathFrom (L : LCode) : ∀ (v : List ℕ) (q : ℕ), compFrom L q v = true →
    ∃ r u, pathFrom L q v (leastPathFrom L q v) = some (r, u) ∧ compFrom L r [] = true := by
  intro v
  induction v with
  | nil => intro q h; exact ⟨q, [], by simp [leastPathFrom], h⟩
  | cons a v ih =>
      intro q h
      have hi := leastIdx_isSome h
      cases hfind : leastIdx L q a v with
      | none => rw [hfind] at hi; simp at hi
      | some i =>
          obtain ⟨⟨r, hstep, hcomp⟩, -⟩ := leastIdx_spec hfind
          obtain ⟨r', u', hp, hr'⟩ := ih r.1 hcomp
          have hrun : leastPathFrom L q (a :: v) = i :: leastPathFrom L r.1 v := by
            simp only [leastPathFrom, hfind, hstep]
          refine ⟨r', r.2 ++ u', ?_, hr'⟩
          simp only [hrun, pathFrom_cons_cons, hstep, Option.bind_some, hp, Option.map_some]

/-! ### Lexicographic comparison of paths -/

/-- `LexLt ks is` holds if the index list `ks` is smaller than `is` at the first position where
they differ.  Only lists of equal length are compared. -/
inductive LexLt : List ℕ → List ℕ → Prop
  | head {a b : ℕ} {l l' : List ℕ} (h : a < b) : LexLt (a :: l) (b :: l')
  | tail {a : ℕ} {l l' : List ℕ} (h : LexLt l l') : LexLt (a :: l) (a :: l')

/-- **Minimality of the canonical path**: no path that is lexicographically smaller than the
canonical one ends in a state where the automaton may stop. -/
lemma not_compFrom_of_lexLt (L : LCode) : ∀ (v : List ℕ) (q : ℕ), compFrom L q v = true →
    ∀ ks, LexLt ks (leastPathFrom L q v) → ∀ r u, pathFrom L q v ks = some (r, u) →
      compFrom L r [] = false := by
  intro v
  induction v with
  | nil =>
      intro q _ ks hks r u hp
      match ks with
      | [] => cases hks
      | _ :: _ => simp at hp
  | cons a v ih =>
      intro q h ks hks r u hp
      have hi := leastIdx_isSome h
      cases hfind : leastIdx L q a v with
      | none => rw [hfind] at hi; simp at hi
      | some i =>
          obtain ⟨⟨r₀, hstep, hcomp⟩, hmin⟩ := leastIdx_spec hfind
          have hrun : leastPathFrom L q (a :: v) = i :: leastPathFrom L r₀.1 v := by
            simp only [leastPathFrom, hfind, hstep]
          rw [hrun] at hks
          match ks with
          | [] => simp at hp
          | k :: ks =>
              simp only [pathFrom_cons_cons] at hp
              cases hstepk : step L q a k with
              | none => rw [hstepk] at hp; simp at hp
              | some rk =>
                  rw [hstepk] at hp
                  simp only [Option.bind_some, Option.map_eq_some_iff] at hp
                  obtain ⟨z, hz, hzeq⟩ := hp
                  obtain ⟨z1, z2⟩ := z
                  simp only [Prod.mk.injEq] at hzeq
                  obtain ⟨hz1, -⟩ := hzeq
                  subst hz1
                  cases hks with
                  | head hlt =>
                      by_contra hcon
                      have hcon : compFrom L z1 [] = true := by simpa using hcon
                      have hcomp' : compFrom L rk.1 v = true := compFrom_of_pathFrom hz hcon
                      have := hmin k hlt rk hstepk
                      rw [hcomp'] at this
                      exact absurd this (by simp)
                  | tail hks' =>
                      have hrk : rk = r₀ := by
                        rw [hstep] at hstepk
                        exact (Option.some.inj hstepk).symm
                      have hcomp' : compFrom L rk.1 v = true := by rw [hrk]; exact hcomp
                      have hlex : LexLt ks (leastPathFrom L rk.1 v) := by rw [hrk]; exact hks'
                      exact ih rk.1 hcomp' ks hlex z1 z2 hz

end LAut

end Transducers.Exercises
