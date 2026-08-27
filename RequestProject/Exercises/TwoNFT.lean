/-
The exercise `exer:2nft` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk), on the two nondeterministic variants of a two-way
transducer.

The two models of the exercise are:

1. a two-way transducer in which several transitions are available in a
   configuration, one of which is chosen nondeterministically;
2. a deterministic two-way transducer applied to the input string labelled
   nondeterministically by an auxiliary alphabet, the labelling being subject to
   a regular condition — as the solution says, the regular condition is what
   makes it possible for the model to produce no output at all.

This file has the first half of the exercise, namely that the first model is not
contained in the second one: the first model can have infinitely many output
strings for one input string, and the second one cannot.  The other half — that
the relation `{(aⁿ, v v) : |v| = n}` is in the second model and not in the first
— is in `RequestProject/Exercises/TwoNFT2.lean`.
-/
import RequestProject.PartC.RegCodeBound

namespace Transducers
namespace Exercises

/-! ## The first model: nondeterministic transitions -/

/-- A *nondeterministic* two-way transducer: in a configuration, any of the
available transitions may be taken. -/
structure TwoWayN (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transitions available for the letters adjacent to the head and the
  current state. -/
  step : Option A → Q → Option A → Set (List B ⊕ (Q × List B × Bool))

namespace TwoWayN

variable {A B Q : Type}

/-- One step of a run: the produced output and the next configuration. -/
inductive StepN (M : TwoWayN A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  /-- Halting. -/
  | halt {u v : List A} {q : Q} {o : List B} :
      (Sum.inl o ∈ M.step u.getLast? q v.head?) → StepN M (Cfg.conf u q v) o Cfg.halt
  /-- Moving right. -/
  | right {u v : List A} {a : A} {q q' : Q} {o : List B} :
      v.head? = some a →
      (Sum.inr (q', o, true) ∈ M.step u.getLast? q (some a)) →
        StepN M (Cfg.conf u q v) o (Cfg.conf (u ++ [a]) q' v.tail)
  /-- Moving left. -/
  | left {u v : List A} {a : A} {q q' : Q} {o : List B} :
      u.getLast? = some a →
      (Sum.inr (q', o, false) ∈ M.step (some a) q v.head?) →
        StepN M (Cfg.conf u q v) o (Cfg.conf u.dropLast q' (a :: v))

/-- Reachability along a run, recording the produced output. -/
inductive ReachesN (M : TwoWayN A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : ReachesN M c [] c
  | step {c c' c'' : Cfg A Q} {o o' : List B} :
      StepN M c o c' → ReachesN M c' o' c'' → ReachesN M c (o ++ o') c''

/-- The relation computed by a nondeterministic two-way transducer. -/
def RelOf (M : TwoWayN A B Q) (w : List A) (v : List B) : Prop :=
  ReachesN M (Cfg.conf [] M.init w) v Cfg.halt

lemma reachesN_halt {M : TwoWayN A B Q} {o : List B} {c : Cfg A Q}
    (h : ReachesN M Cfg.halt o c) : o = [] ∧ c = Cfg.halt := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => cases hs

end TwoWayN

/-- A relation computed by the first model.  The transition table is required to
be finite, as it is in the book. -/
def IsTwoNFT₁ {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : TwoWayN A B Q),
    (∀ l q r, (M.step l q r).Finite) ∧ ∀ w v, R w v ↔ M.RelOf w v

/-! ## The second model: a nondeterministic labelling of the input -/

/-- A relation computed by the second model: the input is labelled by an
auxiliary alphabet, the labelling must belong to a regular language, and a
deterministic two-way transducer is applied to the labelled input. -/
def IsTwoNFT₂ {A B : Type} (R : List A → List B → Prop) : Prop :=
  ∃ (C : Type) (_ : Finite C) (Q : Type) (_ : Finite Q) (M : TwoWay (A × C) B Q)
    (L : Language (A × C)), L.IsRegular ∧
    ∀ w v, R w v ↔ ∃ z : List (A × C), z.map Prod.fst = w ∧ z ∈ L ∧ M.Computes z v

/-- A string has finitely many labellings by a finite alphabet. -/
lemma finite_labellings {A C : Type} [Finite C] (w : List A) :
    {z : List (A × C) | z.map Prod.fst = w}.Finite := by
  induction w with
  | nil =>
    have h : {z : List (A × C) | z.map Prod.fst = []} = {[]} := by
      ext z; simp
    rw [h]
    exact Set.finite_singleton _
  | cons a w ih =>
    have hsub : {z : List (A × C) | z.map Prod.fst = a :: w} ⊆
        (fun p : C × List (A × C) => (a, p.1) :: p.2) ''
          ((Set.univ : Set C) ×ˢ {z : List (A × C) | z.map Prod.fst = w}) := by
      intro z hz
      cases z with
      | nil => simp at hz
      | cons x z' =>
        simp only [Set.mem_setOf_eq, List.map_cons, List.cons.injEq] at hz
        refine ⟨(x.2, z'), ⟨Set.mem_univ _, hz.2⟩, ?_⟩
        simp only
        rw [← hz.1]
    exact Set.Finite.subset (Set.Finite.image _ (Set.Finite.prod Set.finite_univ ih)) hsub

/-- The second model has only finitely many outputs for a given input. -/
theorem finite_outputs_of_isTwoNFT₂ {A B : Type} {R : List A → List B → Prop}
    (h : IsTwoNFT₂ R) (w : List A) : {v | R w v}.Finite := by
  classical
  obtain ⟨C, hC, Q, _, M, L, _, hR⟩ := h
  have hsub : {v | R w v} ⊆ ⋃ z ∈ {z : List (A × C) | z.map Prod.fst = w},
      {v | M.Computes z v} := by
    intro v hv
    obtain ⟨z, hz, _, hcomp⟩ := (hR w v).1 hv
    exact Set.mem_biUnion hz hcomp
  refine Set.Finite.subset (Set.Finite.biUnion (finite_labellings w) ?_) hsub
  intro z _
  refine Set.Finite.subset
    (Set.finite_singleton (if h : ∃ v, M.Computes z v then h.choose else [])) ?_
  intro v hv
  have hex : ∃ v, M.Computes z v := ⟨v, hv⟩
  simp only [Set.mem_singleton_iff, dif_pos hex]
  exact TwoWay.computes_unique hv hex.choose_spec

/-! ### Exercise `exer:2nft`, first half -/

/-- The nondeterministic two-way transducer of the counterexample: in the state
`false` it either halts or moves right producing one letter, and in the state
`true` it moves back to the left producing nothing.  On a nonempty input it
bounces between the first two positions for as long as it likes, so it produces
every string over the one-letter output alphabet. -/
def bounce : TwoWayN Unit Unit Bool where
  init := false
  step := fun _ q _ =>
    if q then {Sum.inr (false, [], false)} else {Sum.inl [], Sum.inr (true, [()], true)}

/-- The relation computed by `bounce`: on a nonempty input every output string
is produced, and on the empty input only the empty one. -/
def bounceRel (w v : List Unit) : Prop := w ≠ [] ∨ v = []

lemma bounce_reaches_replicate (a : Unit) (w : List Unit) (k : ℕ) :
    TwoWayN.ReachesN bounce (Cfg.conf [] false (a :: w)) (List.replicate k ()) Cfg.halt := by
  induction k with
  | zero =>
    have h : TwoWayN.StepN bounce (Cfg.conf [] false (a :: w)) [] Cfg.halt :=
      TwoWayN.StepN.halt (by simp [bounce])
    simpa using TwoWayN.ReachesN.step h (TwoWayN.ReachesN.refl _)
  | succ k ih =>
    have h1 : TwoWayN.StepN bounce (Cfg.conf [] false (a :: w)) [()]
        (Cfg.conf ([] ++ [a]) true (a :: w).tail) :=
      TwoWayN.StepN.right (by simp) (by simp [bounce])
    have h2 : TwoWayN.StepN bounce (Cfg.conf [a] true w) [] (Cfg.conf [] false (a :: w)) := by
      have h := TwoWayN.StepN.left (M := bounce) (u := [a]) (v := w) (q := true) (q' := false)
        (o := []) (a := a) (by simp) (by simp [bounce])
      simpa using h
    simp only [List.nil_append, List.tail_cons] at h1
    have := TwoWayN.ReachesN.step h1 (TwoWayN.ReachesN.step h2 ih)
    simpa [List.replicate_succ] using this

lemma bounce_nil (v : List Unit) (h : bounce.RelOf [] v) : v = [] := by
  rw [TwoWayN.RelOf] at h
  cases h with
  | @step c c' c'' o o' hs hr =>
    have hstep : o = [] ∧ c' = Cfg.halt := by
      cases hs with
      | @halt u v q o hmem =>
        refine ⟨?_, rfl⟩
        simp only [bounce, Bool.false_eq_true, if_false, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · exact (Sum.inl.injEq _ _ ▸ h : o = [])
        · exact absurd h (by simp)
      | @right u v a q q' o hh _ => simp at hh
      | @left u v a q q' o hh _ => simp at hh
    obtain ⟨ho, hc⟩ := hstep
    subst ho; subst hc
    simpa using (TwoWayN.reachesN_halt hr).1

theorem bounce_relOf (w v : List Unit) : bounceRel w v ↔ bounce.RelOf w v := by
  constructor
  · rintro (hw | rfl)
    · obtain ⟨a, w', rfl⟩ : ∃ a w', w = a :: w' := by
        cases w with
        | nil => exact absurd rfl hw
        | cons a w' => exact ⟨a, w', rfl⟩
      have hv : v = List.replicate v.length () := by
        induction v with
        | nil => rfl
        | cons b v ih => cases b; simpa [List.replicate_succ] using ih
      rw [TwoWayN.RelOf, hv]
      exact bounce_reaches_replicate a w' v.length
    · rw [TwoWayN.RelOf]
      cases w with
      | nil =>
        have h : TwoWayN.StepN bounce (Cfg.conf [] false ([] : List Unit)) [] Cfg.halt :=
          TwoWayN.StepN.halt (by simp [bounce])
        simpa using TwoWayN.ReachesN.step h (TwoWayN.ReachesN.refl _)
      | cons a w' => simpa using bounce_reaches_replicate a w' 0
  · intro h
    by_cases hw : w = []
    · subst hw
      exact Or.inr (bounce_nil v h)
    · exact Or.inl hw

/-- **Exercise `exer:2nft`, first half.**  The first nondeterministic model of a
two-way transducer is not contained in the second one: it can produce infinitely
many output strings for one input string, while the second model produces only
finitely many. -/
theorem exists_isTwoNFT₁_not_isTwoNFT₂ :
    ∃ R : List Unit → List Unit → Prop, IsTwoNFT₁ R ∧ ¬ IsTwoNFT₂ R := by
  refine ⟨bounceRel, ⟨Bool, inferInstance, bounce, ?_, bounce_relOf⟩, ?_⟩
  · intro l q r
    rcases q with _ | _ <;> simp [bounce]
  intro h
  have hfin := finite_outputs_of_isTwoNFT₂ h [()]
  have huniv : {v : List Unit | bounceRel [()] v} = Set.univ := by
    ext v; simp [bounceRel]
  rw [huniv] at hfin
  have hinf : Set.Infinite (Set.univ : Set (List Unit)) := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => List.replicate n ()) ?_ (fun _ => Set.mem_univ _)
    intro m n hmn
    have := congrArg List.length hmn
    simpa using this
  exact hinf hfin

end Exercises
end Transducers
