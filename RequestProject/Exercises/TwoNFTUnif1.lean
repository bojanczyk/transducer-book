/-
Exercise `exer:2nft-uniformise` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk), first model.

See `RequestProject/Exercises/TwoNFTUnif.lean` for the second model.
-/
import RequestProject.Exercises.TwoNFT
import RequestProject.Exercises.TwoDFALoop
import RequestProject.PartD.TwoWayTotal
import RequestProject.PartB.GuessCheck
import RequestProject.PartB.UniformFun

namespace Transducers.Exercises

open Transducers

variable {A B Q : Type}

/-! ## Transitions as data -/

/-- A transition of a two-way transducer: halt with an output, or produce an output, change state
and move. -/
abbrev Trn (B Q : Type) := List B ⊕ (Q × List B × Bool)

/-- The effect of a transition in a configuration, if it is defined there. -/
def applyTr (u v : List A) (t : Trn B Q) : Option (List B × Cfg A Q) :=
  match t with
  | Sum.inl o => some (o, Cfg.halt)
  | Sum.inr (q', o, true) =>
      match v with
      | [] => none
      | a :: v' => some (o, Cfg.conf (u ++ [a]) q' v')
  | Sum.inr (q', o, false) =>
      match u.getLast? with
      | none => none
      | some a => some (o, Cfg.conf u.dropLast q' (a :: v))

/-- A step of the nondeterministic transducer is the application of an available transition. -/
lemma stepN_iff (M : TwoWayN A B Q) (u v : List A) (q : Q) (o : List B) (c' : Cfg A Q) :
    M.StepN (Cfg.conf u q v) o c' ↔
      ∃ t ∈ M.step u.getLast? q v.head?, applyTr u v t = some (o, c') := by
  constructor
  · intro h
    cases h with
    | @halt u v q o hm => exact ⟨Sum.inl o, hm, rfl⟩
    | @right u v a q q' o hv hm =>
        refine ⟨Sum.inr (q', o, true), by rw [hv]; exact hm, ?_⟩
        cases v with
        | nil => exact absurd hv (by simp)
        | cons b v' =>
            have : b = a := by simpa using hv
            subst this
            rfl
    | @left u v a q q' o hu hm =>
        refine ⟨Sum.inr (q', o, false), by rw [hu]; exact hm, ?_⟩
        simp only [applyTr, hu]
  · rintro ⟨t, hm, ht⟩
    cases t with
    | inl o' =>
        simp only [applyTr, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact TwoWayN.StepN.halt hm
    | inr t =>
        obtain ⟨q', o', d⟩ := t
        cases d with
        | true =>
            cases v with
            | nil => simp [applyTr] at ht
            | cons a v' =>
                simp only [applyTr, Option.some.injEq, Prod.mk.injEq] at ht
                obtain ⟨rfl, rfl⟩ := ht
                exact TwoWayN.StepN.right rfl (by simpa using hm)
        | false =>
            cases hu : u.getLast? with
            | none => rw [applyTr, hu] at ht; exact absurd ht (by simp)
            | some a =>
                rw [applyTr, hu] at ht
                simp only [Option.some.injEq, Prod.mk.injEq] at ht
                obtain ⟨rfl, rfl⟩ := ht
                exact TwoWayN.StepN.left hu (by rw [← hu]; exact hm)

/-! ## Runs of a given length -/

/-- Reachability in a fixed number of steps. -/
inductive ReachesNn (M : TwoWayN A B Q) : ℕ → Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : ReachesNn M 0 c [] c
  | step {n : ℕ} {c c' c'' : Cfg A Q} {o o' : List B} :
      M.StepN c o c' → ReachesNn M n c' o' c'' → ReachesNn M (n + 1) c (o ++ o') c''

lemma reachesN_iff_exists_len (M : TwoWayN A B Q) (c : Cfg A Q) (o : List B) (c' : Cfg A Q) :
    M.ReachesN c o c' ↔ ∃ n, ReachesNn M n c o c' := by
  constructor
  · intro h
    induction h with
    | refl c => exact ⟨0, ReachesNn.refl c⟩
    | step hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, ReachesNn.step hs hn⟩
  · rintro ⟨n, hn⟩
    induction hn with
    | refl c => exact TwoWayN.ReachesN.refl c
    | step hs _ ih => exact TwoWayN.ReachesN.step hs ih

/-- The transducer can halt from the configuration `c` in `n` steps. -/
def HaltsInN (M : TwoWayN A B Q) (n : ℕ) (c : Cfg A Q) : Prop :=
  ∃ o, ReachesNn M n c o Cfg.halt

/-- The transducer can halt from the configuration `c`. -/
def CanHalt (M : TwoWayN A B Q) (c : Cfg A Q) : Prop := ∃ n, HaltsInN M n c

open scoped Classical in
/-- The least number of steps in which the transducer can halt from `c`. -/
noncomputable def dst (M : TwoWayN A B Q) (c : Cfg A Q) : ℕ :=
  if h : CanHalt M c then Nat.find h else 0

open scoped Classical in
lemma haltsInN_dst {M : TwoWayN A B Q} {c : Cfg A Q} (h : CanHalt M c) :
    HaltsInN M (dst M c) c := by
  rw [dst, dif_pos h]
  exact Nat.find_spec h

open scoped Classical in
lemma dst_le {M : TwoWayN A B Q} {c : Cfg A Q} (h : CanHalt M c) {n : ℕ}
    (hn : HaltsInN M n c) : dst M c ≤ n := by
  rw [dst, dif_pos h]
  exact Nat.find_le hn

/-- From a configuration that is not halting, halting takes at least one step. -/
lemma dst_pos {M : TwoWayN A B Q} {u v : List A} {q : Q} (h : CanHalt M (Cfg.conf u q v)) :
    0 < dst M (Cfg.conf u q v) := by
  rcases Nat.eq_zero_or_pos (dst M (Cfg.conf u q v)) with hz | hp
  · exfalso
    obtain ⟨o, ho⟩ := haltsInN_dst h
    rw [hz] at ho
    cases ho
  · exact hp

/-- A configuration from which the transducer can halt has a transition that gets strictly
closer to halting. -/
lemma exists_good_step {M : TwoWayN A B Q} {u v : List A} {q : Q}
    (h : CanHalt M (Cfg.conf u q v)) :
    ∃ t ∈ M.step u.getLast? q v.head?, ∃ o c', applyTr u v t = some (o, c') ∧
      CanHalt M c' ∧ dst M c' < dst M (Cfg.conf u q v) := by
  obtain ⟨o, ho⟩ := haltsInN_dst h
  obtain ⟨n, hn⟩ : ∃ n, dst M (Cfg.conf u q v) = n + 1 :=
    ⟨dst M (Cfg.conf u q v) - 1, by have := dst_pos h; omega⟩
  rw [hn] at ho
  cases ho with
  | @step _ _ c' _ o₁ o₂ hs hr =>
      obtain ⟨t, hmem, ht⟩ := (stepN_iff M u v q o₁ c').1 hs
      have hch : CanHalt M c' := ⟨n, ⟨o₂, hr⟩⟩
      exact ⟨t, hmem, o₁, c', ht, hch, by have := dst_le hch ⟨o₂, hr⟩; omega⟩

/-! ## The auxiliary alphabet of choices -/

/-- The transitions that occur in the transition table. -/
def usedTr (M : TwoWayN A B Q) : Set (Trn B Q) := {t | ∃ l q r, t ∈ M.step l q r}

lemma usedTr_finite [Finite A] [Finite Q] (M : TwoWayN A B Q)
    (hfin : ∀ l q r, (M.step l q r).Finite) : (usedTr M).Finite := by
  have h : usedTr M = ⋃ x : Option A × Q × Option A, M.step x.1 x.2.1 x.2.2 := by
    ext t
    simp only [usedTr, Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [h]
  exact Set.finite_iUnion (fun x => hfin x.1 x.2.1 x.2.2)

/-- A transition of the table.  This is a finite type when the table is finite. -/
abbrev Tr (M : TwoWayN A B Q) : Type := ↑(usedTr M)

/-- **The auxiliary alphabet.**  A letter records, for each state, the transition to be taken at
the cut to its left (first component) and — for the last letter only — at the cut to its right
(second component).  Along a run in which no configuration repeats, the transition taken depends
only on the cut and on the state, which is why one letter per input position is enough. -/
abbrev CAlph (M : TwoWayN A B Q) : Type := (Q → Option (Tr M)) × (Q → Option (Tr M))

/-- A transition of `M`, read as a transition of the deterministic transducer. -/
def liftTr : Trn B Q → List B ⊕ ((Q ⊕ Unit) × List B × Bool)
  | Sum.inl o => Sum.inl o
  | Sum.inr (q, o, d) => Sum.inr (Sum.inl q, o, d)

/-- The transition taken when the annotation is unusable: walk to the left for ever, and get
stuck at the left end.  The run then never halts. -/
def badTr (B Q : Type) : List B ⊕ ((Q ⊕ Unit) × List B × Bool) := Sum.inr (Sum.inr (), [], false)

open scoped Classical in
/-- The annotation is used only if it names a transition that `M` really has. -/
noncomputable def useTr (M : TwoWayN A B Q) (l : Option A) (q : Q) (r : Option A)
    (t : Option (Tr M)) : List B ⊕ ((Q ⊕ Unit) × List B × Bool) :=
  match t with
  | none => badTr B Q
  | some t => if (t : Trn B Q) ∈ M.step l q r then liftTr (t : Trn B Q) else badTr B Q

open scoped Classical in
/-- On the empty input there is no letter to carry an annotation, so a halting transition is
chosen once and for all. -/
noncomputable def emptyStep (M : TwoWayN A B Q) (q : Q) :
    List B ⊕ ((Q ⊕ Unit) × List B × Bool) :=
  if h : ∃ o, (Sum.inl o : Trn B Q) ∈ M.step none q none then Sum.inl h.choose else badTr B Q

open scoped Classical in
/-- **The deterministic transducer guided by the annotation.** -/
noncomputable def detOf (M : TwoWayN A B Q) : TwoWay (A × CAlph M) B (Q ⊕ Unit) where
  init := Sum.inl M.init
  step := fun l st r =>
    match st with
    | Sum.inr _ => badTr B Q
    | Sum.inl q =>
        match r with
        | some x => useTr M (l.map Prod.fst) q (some x.1) (x.2.1 q)
        | none =>
            match l with
            | some x => useTr M (some x.1) q none (x.2.2 q)
            | none => emptyStep M q

/-! ## Steps of the deterministic transducer -/

private lemma stepCfg_conf {A' R : Type} (N : TwoWay A' B R) (u v : List A') (r : R) :
    N.stepCfg (Cfg.conf u r v) =
      match N.step u.getLast? r v.head? with
      | Sum.inl o => some (o, Cfg.halt)
      | Sum.inr (r', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (o, Cfg.conf (u ++ [a]) r' v')
      | Sum.inr (r', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (o, Cfg.conf u.dropLast r' (a :: v)) := rfl

private lemma reaches_halt_eq {A' R : Type} {N : TwoWay A' B R} {o : List B} {c : Cfg A' R}
    (h : N.Reaches Cfg.halt o c) : o = [] ∧ c = Cfg.halt := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hs _ => exact absurd hs (by simp [TwoWay.stepCfg])

variable (M : TwoWayN A B Q)

private lemma detOf_step_badState (l r : Option (A × CAlph M)) :
    (detOf M).step l (Sum.inr () : Q ⊕ Unit) r = badTr B Q := rfl

private lemma stepCfg_badState (U V : List (A × CAlph M)) :
    (detOf M).stepCfg (Cfg.conf U (Sum.inr ()) V)
      = match U.getLast? with
        | none => none
        | some a => some ([], Cfg.conf U.dropLast (Sum.inr ()) (a :: V)) := by
  rw [stepCfg_conf, detOf_step_badState, badTr]
  cases U.getLast? with
  | none => rfl
  | some a => rfl

/-- Once the deterministic transducer has decided that the annotation is unusable, it never
halts. -/
lemma bad_never' {c c'' : Cfg (A × CAlph M) (Q ⊕ Unit)} {o : List B}
    (h : (detOf M).Reaches c o c'') :
    ∀ U V, c = Cfg.conf U (Sum.inr ()) V → c'' ≠ Cfg.halt := by
  induction h with
  | refl c => intro U V hc; rw [hc]; simp
  | @step c c' c'' o o' hs _ ih =>
      intro U V hc
      subst hc
      rw [stepCfg_badState] at hs
      cases hU : U.getLast? with
      | none => rw [hU] at hs; exact absurd hs (by simp)
      | some a =>
          rw [hU] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          exact ih U.dropLast (a :: V) hs.2.symm

lemma bad_never {c : Cfg (A × CAlph M) (Q ⊕ Unit)} {o : List B}
    (h : (detOf M).Reaches c o Cfg.halt) : ∀ U V, c ≠ Cfg.conf U (Sum.inr ()) V :=
  fun U V hc => bad_never' M h U V hc rfl

/-- A configuration of the deterministic transducer, read as one of `M`. -/
def prjCfg : Cfg (A × CAlph M) (Q ⊕ Unit) → Cfg A Q
  | Cfg.halt => Cfg.halt
  | Cfg.conf U (Sum.inl q) V => Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)
  | Cfg.conf _ (Sum.inr _) _ => Cfg.halt

private lemma detOf_step_r (l : Option (A × CAlph M)) (q : Q) (x : A × CAlph M) :
    (detOf M).step l (Sum.inl q) (some x) = useTr M (l.map Prod.fst) q (some x.1) (x.2.1 q) := rfl

private lemma detOf_step_l (x : A × CAlph M) (q : Q) :
    (detOf M).step (some x) (Sum.inl q) none = useTr M (some x.1) q none (x.2.2 q) := rfl

private lemma detOf_step_e (q : Q) :
    (detOf M).step (none : Option (A × CAlph M)) (Sum.inl q) none = emptyStep M q := rfl

/-- In a state of `M`, the deterministic transducer either takes a transition that `M` has, or
gives up. -/
lemma detOf_step_cases (U V : List (A × CAlph M)) (q : Q) :
    (∃ tv, tv ∈ M.step (U.map Prod.fst).getLast? q (V.map Prod.fst).head? ∧
        (detOf M).step U.getLast? (Sum.inl q) V.head? = liftTr tv)
      ∨ (detOf M).step U.getLast? (Sum.inl q) V.head? = badTr B Q := by
  classical
  have hmapl : (U.map Prod.fst).getLast? = U.getLast?.map Prod.fst := List.getLast?_map
  rw [hmapl]
  cases hV : V with
  | cons x V' =>
      simp only [List.head?_cons, List.map_cons, detOf_step_r]
      cases ht : x.2.1 q with
      | none => exact Or.inr rfl
      | some t =>
          by_cases hmem : (t : Trn B Q) ∈ M.step (U.getLast?.map Prod.fst) q (some x.1)
          · exact Or.inl ⟨t, hmem, by rw [useTr, if_pos hmem]⟩
          · exact Or.inr (by rw [useTr, if_neg hmem])
  | nil =>
      simp only [List.head?_nil, List.map_nil]
      cases hU : U.getLast? with
      | none =>
          simp only [Option.map_none, detOf_step_e]
          by_cases hex : ∃ o, (Sum.inl o : Trn B Q) ∈ M.step none q none
          · refine Or.inl ⟨Sum.inl hex.choose, hex.choose_spec, ?_⟩
            rw [emptyStep, dif_pos hex]
            rfl
          · exact Or.inr (by rw [emptyStep, dif_neg hex])
      | some x =>
          simp only [Option.map_some, detOf_step_l]
          cases ht : x.2.2 q with
          | none => exact Or.inr rfl
          | some t =>
              by_cases hmem : (t : Trn B Q) ∈ M.step (some x.1) q none
              · exact Or.inl ⟨t, hmem, by rw [useTr, if_pos hmem]⟩
              · exact Or.inr (by rw [useTr, if_neg hmem])

/-- A step of the deterministic transducer, when it takes a transition of `M`, is that transition
applied in the projected configuration. -/
lemma stepCfg_apply {U V : List (A × CAlph M)} {q : Q} {tv : Trn B Q} {o : List B}
    {c₁ : Cfg (A × CAlph M) (Q ⊕ Unit)}
    (hstep : (detOf M).step U.getLast? (Sum.inl q) V.head? = liftTr tv)
    (h : (detOf M).stepCfg (Cfg.conf U (Sum.inl q) V) = some (o, c₁)) :
    applyTr (U.map Prod.fst) (V.map Prod.fst) tv = some (o, prjCfg M c₁) := by
  rw [stepCfg_conf, hstep] at h
  cases tv with
  | inl o' =>
      rw [liftTr] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | inr t =>
      obtain ⟨q', o', d⟩ := t
      cases d with
      | true =>
          cases hV : V with
          | nil => rw [hV] at h; exact absurd h (by simp [liftTr])
          | cons x V' =>
              subst hV
              rw [liftTr] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [applyTr, List.map_cons, prjCfg, List.map_append, List.map_cons,
                List.map_nil]
      | false =>
          have hmapl : (U.map Prod.fst).getLast? = U.getLast?.map Prod.fst := List.getLast?_map
          cases hU : U.getLast? with
          | none =>
              rw [liftTr, hU] at h
              exact absurd h (by simp)
          | some x =>
              rw [liftTr, hU] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [applyTr, hmapl, hU, Option.map_some, prjCfg, List.map_cons,
                ← List.map_dropLast]

/-- **Soundness.**  Every output of the deterministic transducer is an output of `M` on the
projected input. -/
lemma sound' {c c'' : Cfg (A × CAlph M) (Q ⊕ Unit)} {o : List B}
    (h : (detOf M).Reaches c o c'') :
    ∀ U q V, c = Cfg.conf U (Sum.inl q) V → c'' = Cfg.halt →
      M.ReachesN (Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)) o Cfg.halt := by
  induction h with
  | refl c => intro U q V hc hh; rw [hc] at hh; exact absurd hh (by simp)
  | @step c c' c'' o o' hs hr ih =>
      intro U q V hc hh
      subst hc
      rcases detOf_step_cases M U V q with ⟨tv, hmem, hstep⟩ | hbad
      · have happ := stepCfg_apply M hstep hs
        have hstepN : M.StepN (Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)) o (prjCfg M c') :=
          (stepN_iff M _ _ q o _).2 ⟨tv, hmem, happ⟩
        refine TwoWayN.ReachesN.step hstepN ?_
        cases hc' : c' with
        | halt =>
            subst hc'
            obtain ⟨rfl, -⟩ := reaches_halt_eq hr
            exact TwoWayN.ReachesN.refl _
        | conf U' st V' =>
            cases st with
            | inl q' =>
                subst hc'
                exact ih U' q' V' rfl hh
            | inr u =>
                subst hc'
                exact absurd hh (bad_never' M hr U' V' rfl)
      · exfalso
        rw [stepCfg_conf, hbad, badTr] at hs
        cases hU : U.getLast? with
        | none => rw [hU] at hs; exact absurd hs (by simp)
        | some a =>
            rw [hU] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            exact absurd hh (bad_never' M hr U.dropLast (a :: V) hs.2.symm)

/-- **Soundness.**  Every output of the deterministic transducer is an output of `M` on the
projected input. -/
lemma sound {U V : List (A × CAlph M)} {q : Q} {o : List B}
    (h : (detOf M).Reaches (Cfg.conf U (Sum.inl q) V) o Cfg.halt) :
    M.ReachesN (Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)) o Cfg.halt :=
  sound' M h U q V rfl rfl

/-! ## The annotation of an input -/

open scoped Classical in
/-- The transition chosen at the cut between `u` and `v` in the state `q`: one that gets strictly
closer to halting, if there is one.  Because the choice depends only on the cut and on the state,
it can be recorded in a labelling of the input by a finite alphabet. -/
noncomputable def chooseTr (u : List A) (q : Q) (v : List A) : Option (Tr M) :=
  if h : ∃ t : Tr M, (t : Trn B Q) ∈ M.step u.getLast? q v.head? ∧
      ∃ o c', applyTr u v (t : Trn B Q) = some (o, c') ∧ CanHalt M c' ∧
        dst M c' < dst M (Cfg.conf u q v)
    then some h.choose else none

open scoped Classical in
lemma chooseTr_eq_some {u v : List A} {q : Q} (h : CanHalt M (Cfg.conf u q v)) :
    ∃ t : Tr M, chooseTr M u q v = some t ∧ (t : Trn B Q) ∈ M.step u.getLast? q v.head? ∧
      ∃ o c', applyTr u v (t : Trn B Q) = some (o, c') ∧ CanHalt M c' ∧
        dst M c' < dst M (Cfg.conf u q v) := by
  obtain ⟨t, hmem, o, c', happ, hch, hlt⟩ := exists_good_step h
  have hex : ∃ t : Tr M, (t : Trn B Q) ∈ M.step u.getLast? q v.head? ∧
      ∃ o c', applyTr u v (t : Trn B Q) = some (o, c') ∧ CanHalt M c' ∧
        dst M c' < dst M (Cfg.conf u q v) :=
    ⟨⟨t, ⟨u.getLast?, q, v.head?, hmem⟩⟩, hmem, o, c', happ, hch, hlt⟩
  exact ⟨hex.choose, by rw [chooseTr, dif_pos hex], hex.choose_spec.1, hex.choose_spec.2⟩

/-- The letter that annotates position `p` of the input `w`. -/
noncomputable def annLetter (w : List A) (p : ℕ) : CAlph M :=
  (fun q => chooseTr M (w.take p) q (w.drop p), fun q => chooseTr M w q [])

/-- **The annotated input.**  Position `p` records the choices made at the cut to its left, and
the last position also records the choices made at the right end. -/
noncomputable def annot (w : List A) : List (A × CAlph M) :=
  List.ofFn (fun i : Fin w.length => (w[i], annLetter M w i))

@[simp] lemma annot_length (w : List A) : (annot M w).length = w.length := by
  simp [annot]

lemma annot_getElem (w : List A) (p : ℕ) (h : p < (annot M w).length) :
    (annot M w)[p] = (w[p]'(by rwa [annot_length] at h), annLetter M w p) :=
  List.getElem_ofFn h

@[simp] lemma annot_map_fst (w : List A) : (annot M w).map Prod.fst = w := by
  refine List.ext_getElem (by simp) (fun p h h' => ?_)
  rw [List.getElem_map, annot_getElem]

/-! ## The deterministic transducer follows the annotation -/

/-- The converse of `stepCfg_apply`: a transition of `M` that the deterministic transducer takes
is applied by it. -/
lemma stepCfg_forward {U V : List (A × CAlph M)} {q : Q} {tv : Trn B Q} {o : List B}
    {c' : Cfg A Q}
    (hstep : (detOf M).step U.getLast? (Sum.inl q) V.head? = liftTr tv)
    (happ : applyTr (U.map Prod.fst) (V.map Prod.fst) tv = some (o, c')) :
    (c' = Cfg.halt ∧ (detOf M).stepCfg (Cfg.conf U (Sum.inl q) V) = some (o, Cfg.halt)) ∨
      ∃ U' V' q', (detOf M).stepCfg (Cfg.conf U (Sum.inl q) V)
          = some (o, Cfg.conf U' (Sum.inl q') V') ∧ U' ++ V' = U ++ V ∧
        c' = Cfg.conf (U'.map Prod.fst) q' (V'.map Prod.fst) := by
  have hmapl : (U.map Prod.fst).getLast? = U.getLast?.map Prod.fst := List.getLast?_map
  cases tv with
  | inl o' =>
      simp only [applyTr, Option.some.injEq, Prod.mk.injEq] at happ
      obtain ⟨rfl, rfl⟩ := happ
      exact Or.inl ⟨rfl, by rw [stepCfg_conf, hstep, liftTr]⟩
  | inr t =>
      obtain ⟨q', o', d⟩ := t
      cases d with
      | true =>
          cases hV : V with
          | nil => rw [hV] at happ; simp [applyTr] at happ
          | cons x V' =>
              subst hV
              simp only [applyTr, List.map_cons, Option.some.injEq, Prod.mk.injEq] at happ
              obtain ⟨rfl, rfl⟩ := happ
              refine Or.inr ⟨U ++ [x], V', q', ?_, by simp, ?_⟩
              · rw [stepCfg_conf, hstep, liftTr]
              · simp
      | false =>
          cases hU : U.getLast? with
          | none =>
              rw [applyTr, hmapl, hU] at happ
              exact absurd happ (by simp)
          | some y =>
              rw [applyTr, hmapl, hU] at happ
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at happ
              obtain ⟨rfl, rfl⟩ := happ
              refine Or.inr ⟨U.dropLast, y :: V, q', ?_, ?_, ?_⟩
              · rw [stepCfg_conf, hstep, liftTr, hU]
              · obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hU
                simp
              · simp [← List.map_dropLast]

/-- **Completeness.**  If `M` can halt from a configuration, then the deterministic transducer
halts from the corresponding configuration over the annotated input. -/
lemma detOf_complete (w : List A) : ∀ n (U V : List (A × CAlph M)) (q : Q),
    U ++ V = annot M w → dst M (Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)) = n →
    CanHalt M (Cfg.conf (U.map Prod.fst) q (V.map Prod.fst)) →
    ∃ o, (detOf M).Reaches (Cfg.conf U (Sum.inl q) V) o Cfg.halt := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro U V q hUV hdst hcan
      classical
      set p := U.length with hp
      have hU : U = (annot M w).take p := by rw [← hUV, List.take_left]
      have hV : V = (annot M w).drop p := by rw [← hUV, List.drop_left]
      have hu : U.map Prod.fst = w.take p := by
        rw [hU, List.map_take, annot_map_fst]
      have hv : V.map Prod.fst = w.drop p := by
        rw [hV, List.map_drop, annot_map_fst]
      rw [hu, hv] at hcan hdst
      have hmapl : (U.map Prod.fst).getLast? = U.getLast?.map Prod.fst := List.getLast?_map
      obtain ⟨t, hch, hmem, o₀, c₀, happ, hcan₀, hlt₀⟩ := chooseTr_eq_some M hcan
      by_cases hnil : U = [] ∧ V = []
      · -- The empty input: there is no letter to carry an annotation, and the only transitions
        -- that apply are the halting ones.
        obtain ⟨hU0, hV0⟩ := hnil
        have hw : w = [] := by
          have h0 : (annot M w).length = 0 := by rw [← hUV, hU0, hV0]; rfl
          rw [annot_length] at h0
          exact List.eq_nil_of_length_eq_zero h0
        rw [hw] at hmem happ
        simp only [List.take_nil, List.drop_nil, List.getLast?_nil, List.head?_nil] at hmem happ
        obtain ⟨tv, htv⟩ := t
        have hex : ∃ o : List B, (Sum.inl o : Trn B Q) ∈ M.step none q none := by
          cases tv with
          | inl o' => exact ⟨o', hmem⟩
          | inr r =>
              obtain ⟨q', o', d⟩ := r
              cases d with
              | true => rw [applyTr] at happ; exact absurd happ (by simp)
              | false => rw [applyTr] at happ; exact absurd happ (by simp)
        have hstep : (detOf M).step (none : Option (A × CAlph M)) (Sum.inl q) none
            = Sum.inl hex.choose := by rw [detOf_step_e, emptyStep, dif_pos hex]
        have hsc : (detOf M).stepCfg (Cfg.conf ([] : List (A × CAlph M)) (Sum.inl q) [])
            = some (hex.choose, Cfg.halt) := by
          rw [stepCfg_conf]
          simp only [List.getLast?_nil, List.head?_nil, hstep]
        rw [hU0, hV0]
        exact ⟨_, TwoWay.Reaches.step hsc (TwoWay.Reaches.refl _)⟩
      · -- Otherwise the annotation names the chosen transition, and the deterministic
        -- transducer takes it.
        have hstep : (detOf M).step U.getLast? (Sum.inl q) V.head? = liftTr (t : Trn B Q) := by
          cases hVc : V with
          | cons x V' =>
              have hlt : p < (annot M w).length := by
                rw [← hUV, hp]; simp [hVc]
              have hx : x = (w[p]'(by rwa [annot_length] at hlt), annLetter M w p) := by
                have hhd : (annot M w)[p]? = some x := by
                  rw [← List.head?_drop, ← hV, hVc]; rfl
                rw [List.getElem?_eq_getElem hlt, annot_getElem] at hhd
                exact (Option.some_inj.mp hhd).symm
              have hstep1 : (detOf M).step U.getLast? (Sum.inl q) (x :: V').head?
                  = useTr M (U.getLast?.map Prod.fst) q (some x.1) (x.2.1 q) := rfl
              rw [hstep1, hx]
              have hann : (annLetter M w p).1 q = chooseTr M (w.take p) q (w.drop p) := rfl
              rw [hann, hch]
              have hr : (some (w[p]'(by rwa [annot_length] at hlt)) : Option A)
                  = (w.drop p).head? := by
                rw [List.head?_drop, List.getElem?_eq_getElem (by rwa [annot_length] at hlt)]
              rw [← hmapl, hu, hr, useTr, if_pos hmem]
          | nil =>
              have hUa : U = annot M w := by rw [← hUV, hVc, List.append_nil]
              have hUne : U ≠ [] := fun h => hnil ⟨h, hVc⟩
              obtain ⟨y, hUl⟩ : ∃ y, U.getLast? = some y := by
                refine Option.ne_none_iff_exists'.mp ?_
                simpa [List.getLast?_eq_none_iff] using hUne
              have hpw : p = w.length := by rw [hp, hUa, annot_length]
              have hwpos : 0 < w.length := by
                rcases Nat.eq_zero_or_pos w.length with h0 | h0
                · exact absurd (by
                    have : (annot M w).length = 0 := by rw [annot_length, h0]
                    exact List.eq_nil_of_length_eq_zero (hUa ▸ this)) hUne
                · exact h0
              have htake : w.take p = w := by rw [hpw]; exact List.take_length
              have hdrop : w.drop p = [] := by rw [hpw]; exact List.drop_length
              have hy : y = (w[w.length - 1]'(by omega), annLetter M w (w.length - 1)) := by
                have h1 : (annot M w)[w.length - 1]? = some y := by
                  rw [← annot_length M w, ← List.getLast?_eq_getElem?, ← hUa]; exact hUl
                have hlt2 : w.length - 1 < (annot M w).length := by rw [annot_length]; omega
                rw [List.getElem?_eq_getElem hlt2, annot_getElem] at h1
                exact (Option.some_inj.mp h1).symm
              rw [htake, hdrop] at hch hmem
              rw [htake] at hu
              simp only [List.head?_nil] at hmem
              rw [hu, hUl] at hmapl
              simp only [Option.map_some] at hmapl
              rw [hmapl] at hmem
              have hy2 : y.2.2 q = some t := by rw [hy]; exact hch
              rw [hUl]
              show useTr M (some y.1) q none (y.2.2 q) = liftTr (t : Trn B Q)
              rw [hy2, useTr, if_pos hmem]
        rw [← hu, ← hv] at happ
        rcases stepCfg_forward M hstep happ with ⟨-, hsc⟩ | ⟨U', V', q', hsc, hUV', hc₀⟩
        · exact ⟨_, TwoWay.Reaches.step hsc (TwoWay.Reaches.refl _)⟩
        · have hltn : dst M c₀ < n := hdst ▸ hlt₀
          rw [hc₀] at hltn hcan₀
          obtain ⟨o', hr⟩ := ih _ hltn U' V' q' (by rw [hUV']; exact hUV) rfl hcan₀
          exact ⟨_, TwoWay.Reaches.step hsc hr⟩

/-- The deterministic transducer halts on the annotation of every input from which `M` can
halt. -/
lemma detOf_halts_annot {w : List A} (h : CanHalt M (Cfg.conf [] M.init w)) :
    ∃ o, (detOf M).Reaches (Cfg.conf [] (Sum.inl M.init) (annot M w)) o Cfg.halt := by
  refine detOf_complete M w _ [] (annot M w) M.init (by simp) rfl ?_
  simpa using h

/-! ## Uniformisation -/

/-- Reading the first component of each letter is the homomorphism `homOf` of the map that sends
a letter to the one-letter string of its first component. -/
private lemma homOf_fst_ann {A C : Type} (z : List (A × C)) :
    homOf (fun p : A × C => [p.1]) z = z.map Prod.fst := by
  induction z with
  | nil => rfl
  | cons p z ih =>
      rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, List.singleton_append,
        List.map_cons]

/-- **Exercise `exer:2nft-uniformise`, first model.**  A total relation recognised by the first
nondeterministic model -- a two-way transducer with a nondeterministic transition relation --
contains the graph of a regular function, that is of a function computed by a deterministic
two-way transducer.

The run is determinised by the auxiliary alphabet `CAlph M`: a letter records, for each state, the
transition that is to be taken at the cut to its left, and the last letter also records the ones
taken at the right end.  The deterministic transducer `detOf M` follows the annotation and checks
it, giving up -- and then never halting -- if the annotation names a transition that `M` does not
have.  So the annotations on which `detOf M` halts are exactly the usable ones, and they form a
regular language by Exercise `exer:2dfa-loop-elimination`; the rest of the argument is as for the
second model. -/
theorem exists_isRegularFun_uniformising_isTwoNFT₁ {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsTwoNFT₁ R) (htot : ∀ w, ∃ v, R w v) :
    ∃ f : List A → List B, IsRegularFun f ∧ ∀ w, R w (f w) := by
  classical
  obtain ⟨Q, hQ, M, hfin, hRM⟩ := hR
  haveI : Finite Q := hQ
  haveI : Finite (Tr M) := (usedTr_finite M hfin).to_subtype
  have hL : Language.IsRegular {z : List (A × CAlph M) | Halts (detOf M) z} :=
    halts_isRegular (detOf M)
  have hrat : IsRationalRel (fun (w : List A) (z : List (A × CAlph M)) =>
      z ∈ {z : List (A × CAlph M) | Halts (detOf M) z} ∧
        homOf (fun p : A × CAlph M => [p.1]) z = w) :=
    isRationalRel_of_regular_proj _ hL
  have htotal : ∀ w : List A, ∃ z : List (A × CAlph M),
      z ∈ {z : List (A × CAlph M) | Halts (detOf M) z} ∧
        homOf (fun p : A × CAlph M => [p.1]) z = w := by
    intro w
    obtain ⟨v, hv⟩ := htot w
    obtain ⟨n, hn⟩ := (reachesN_iff_exists_len M _ v _).1 ((hRM w v).1 hv)
    obtain ⟨o, hreach⟩ := detOf_halts_annot M ⟨n, v, hn⟩
    exact ⟨annot M w, ⟨o, hreach⟩, by rw [homOf_fst_ann, annot_map_fst]⟩
  obtain ⟨g, hgrat, hg⟩ := exists_rationalFun_of_total_rel hrat htotal
  obtain ⟨F, hFreg, hF⟩ := TwoWay.exists_regularFun_of_twoWay (detOf M)
  refine ⟨fun w => F (g w), (IsRegularFun.of_rational hgrat).comp hFreg, fun w => ?_⟩
  obtain ⟨⟨o, ho⟩, hgw⟩ := hg w
  have hsound := sound M ho
  rw [homOf_fst_ann] at hgw
  rw [List.map_nil, hgw] at hsound
  show R w (F (g w))
  rw [hF _ _ ho]
  exact (hRM w o).2 hsound

end Transducers.Exercises
