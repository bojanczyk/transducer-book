/-
The one-step transducer of the enumeration is a **rational** function in the first-to-last
direction.

This is one of the three ingredients of the solution of Exercise `exer:forward-for-transducer`
of *Transducers* (M. Bojańczyk).  The project already proves that
`Transducers.PolyEnum.stepFun d A k` -- the function that turns the marked square of the
enumeration of `k` variables into the enumeration of `k + 1` variables, the new (innermost) loop
running in the direction `d` -- is computed by a streaming string transducer, hence is regular
(`Transducers.PolyEnum.isRegularFun_stepFun`).  The exercise needs more: for `d = true` the
function must be *rational*.

The transducer `Transducers.PolyEnum.stepSST true A k` has three registers, `res`, `grp` and
`cur`, so it is not append-only in the sense of
`Transducers.Exercises.isRationalFun_of_appendOnlySST`; but for `d = true` every one of its
updates concatenates the registers in the fixed order `res`, `grp`, `cur`, and only ever appends
new letters at the end of the register they go to.  In other words the transducer never moves
anything backwards: it is *order preserving*, and the only thing that is not decided when a
letter is read is whether the piece of output it produces will survive to the end -- the content
of `cur` is thrown away when the block being read turns out not to be the one that is kept.

That is exactly a bimachine (Definition `def:bimachine`).  The prefix automaton is the state
space `BS` of the transducer itself.  The suffix automaton remembers the first letter of the
suffix together with the function

  `phi : BS → Reg → Bool`,

which says, for each state `q` and each register `x`, whether the content of `x` at the current
gap, the machine being in the state `q`, still occurs in the output at the end of the run.  Since
`phi` is computed right-to-left by a finite recursion, this is a finite amount of information.
Functions computed by bimachines are rational by Theorem `thm:bimachines`
(`Transducers.isRationalFun_of_bimachine`), so `stepFun true A k` is rational.

This discharges the hypothesis `Transducers.Exercises.ForwardStepRational`.
-/
import RequestProject.PartD.PolyStep
import RequestProject.PartC.RatBuild

namespace Transducers
namespace Exercises

open Transducers.PolyEnum

variable {A : Type} {k : ℕ}

/-! ## Keeping or discarding a piece of output -/

/-- `keepIf b l` is `l` when `b` is true and the empty string otherwise. -/
def keepIf {B : Type} (b : Bool) (l : List B) : List B := if b then l else []

@[simp] lemma keepIf_true {B : Type} (l : List B) : keepIf true l = l := rfl

@[simp] lemma keepIf_false {B : Type} (l : List B) : keepIf false l = [] := rfl

@[simp] lemma keepIf_nil {B : Type} (b : Bool) : keepIf b ([] : List B) = [] := by
  cases b <;> rfl

lemma keepIf_append {B : Type} (b : Bool) (l₁ l₂ : List B) :
    keepIf b (l₁ ++ l₂) = keepIf b l₁ ++ keepIf b l₂ := by
  cases b <;> simp [keepIf]

/-! ## The states of the transducer form a finite type -/

instance : Fintype BS :=
  ⟨{BS.empty, BS.allL, BS.trans, BS.allR}, by intro q; cases q <;> decide⟩

/-! ## Where the content of a register goes, and what is appended to it -/

/-- The register into which the content of the register `x` is moved when the transducer, in the
state `q`, reads the letter `z`; `none` when that content is thrown away.  This is the
"order preserving" shape of `Transducers.PolyEnum.stepUpd true`. -/
def stepMove (q : BS) : Ann A k ⊕ Ann A k → Reg → Option Reg
  | Sum.inl (Ann.letter _ _) => fun x => some x
  | Sum.inr (Ann.letter _ _) => fun x => some x
  | Sum.inr Ann.sep =>
      match q with
      | BS.trans => fun x =>
          match x with
          | Reg.res => some Reg.res
          | Reg.grp => some Reg.grp
          | Reg.cur => some Reg.grp
      | BS.allL => fun _ => some Reg.res
      | BS.empty => fun x =>
          match x with
          | Reg.res => some Reg.res
          | Reg.grp => some Reg.grp
          | Reg.cur => none
      | BS.allR => fun x =>
          match x with
          | Reg.res => some Reg.res
          | Reg.grp => some Reg.grp
          | Reg.cur => none
  | Sum.inl Ann.sep => fun x =>
      match x with
      | Reg.res => some Reg.res
      | Reg.grp => some Reg.grp
      | Reg.cur => none
  | Sum.inl Ann.eos => fun x =>
      match x with
      | Reg.res => some Reg.res
      | Reg.grp => some Reg.grp
      | Reg.cur => none
  | Sum.inr Ann.eos => fun x =>
      match x with
      | Reg.res => some Reg.res
      | Reg.grp => some Reg.grp
      | Reg.cur => none

/-- The letters that the transducer appends when, in the state `q`, it reads the letter `z`,
together with the register at the end of which they are appended. -/
def stepOut (q : BS) : Ann A k ⊕ Ann A k → List (Ann A (k + 1)) × Option Reg
  | Sum.inl (Ann.letter a m) => ([Ann.letter a (Fin.snoc m true)], some Reg.cur)
  | Sum.inr (Ann.letter a m) => ([Ann.letter a (Fin.snoc m false)], some Reg.cur)
  | Sum.inr Ann.sep =>
      match q with
      | BS.trans => ([Ann.sep], some Reg.grp)
      | BS.allL => ([Ann.sep], some Reg.res)
      | BS.empty => ([], none)
      | BS.allR => ([], none)
  | Sum.inl Ann.sep => ([], none)
  | Sum.inl Ann.eos => ([], none)
  | Sum.inr Ann.eos => ([], none)

/-! ## The suffix information -/

/-- At the last gap, only the content of `res` survives. -/
def phiNil : BS → Reg → Bool := fun _ x => decide (x = Reg.res)

/-- One step, right-to-left, of the computation of the surviving registers. -/
def phiStep (z : Ann A k ⊕ Ann A k) (psi : BS → Reg → Bool) : BS → Reg → Bool :=
  fun q x =>
    match stepMove q z x with
    | none => false
    | some y => psi (stepSt q z) y

/-- `phi v q x` is true when the content of the register `x`, the transducer being in the state
`q` at the current gap and `v` being the suffix that is still to be read, still occurs in the
output at the end of the run. -/
def phi : List (Ann A k ⊕ Ann A k) → BS → Reg → Bool
  | [] => phiNil
  | z :: t => phiStep z (phi t)

@[simp] lemma phi_nil : phi ([] : List (Ann A k ⊕ Ann A k)) = phiNil := rfl

@[simp] lemma phi_cons (z : Ann A k ⊕ Ann A k) (t : List (Ann A k ⊕ Ann A k)) :
    phi (z :: t) = phiStep z (phi t) := rfl

/-! ## The bimachine -/

/-- The output produced at a gap: the end marker at the last gap, and otherwise the letters
appended when the next letter is read, kept only if they survive. -/
def stepBimOut (q : BS)
    (s : Option (Ann A k ⊕ Ann A k) × (BS → Reg → Bool)) : List (Ann A (k + 1)) :=
  match s.1 with
  | none => [Ann.eos]
  | some z =>
      match (stepOut q z).2 with
      | none => []
      | some y => keepIf (s.2 (stepSt q z) y) (stepOut q z).1

/-- The bimachine computing `Transducers.PolyEnum.stepFun true A k`. -/
def stepBim (A : Type) (k : ℕ) :
    Bimachine (Ann A k ⊕ Ann A k) (Ann A (k + 1)) BS
      (Option (Ann A k ⊕ Ann A k) × (BS → Reg → Bool)) where
  prefixInit := BS.empty
  prefixStep := stepSt
  suffixInit := (none, phiNil)
  suffixStep := fun s z =>
    (some z, match s.1 with | none => s.2 | some c => phiStep c s.2)
  out := stepBimOut

lemma bmSfx_stepBim (A : Type) (k : ℕ) (v : List (Ann A k ⊕ Ann A k)) :
    bmSfx (stepBim A k) v = (v.head?, phi v.tail) := by
  induction v with
  | nil => rfl
  | cons z t ih =>
      rw [bmSfx_cons, ih]
      cases t with
      | nil => rfl
      | cons c t' => rfl

/-! ## The bimachine computes the same function as the transducer -/

/-- The invariant: at every gap, the output still to be produced is the surviving part of the
registers followed by the output of the bimachine on the rest of the input. -/
theorem stepSST_true_run (A : Type) (k : ℕ) :
    ∀ (v : List (Ann A k ⊕ Ann A k)) (q : BS) (r g c : List (Ann A (k + 1))),
      SST.subst (v.foldl (stepSST true A k).stepConfig (q, regs r g c)).2
          ((stepSST true A k).final (v.foldl (stepSST true A k).stepConfig (q, regs r g c)).1)
        = keepIf (phi v q Reg.res) r ++ keepIf (phi v q Reg.grp) g
            ++ keepIf (phi v q Reg.cur) c ++ (stepBim A k).evalFrom q v := by
  intro v
  induction v with
  | nil =>
      intro q r g c
      show SST.subst (regs r g c) [Sum.inl Reg.res, Sum.inr Ann.eos] = _
      rw [Bimachine.evalFrom_nil']
      simp [SST.subst, phiNil, stepBim, stepBimOut]
  | cons z t ih =>
      intro q r g c
      rw [List.foldl_cons, Bimachine.evalFrom_cons', bmSfx_stepBim]
      have hout : ∀ (y : BS) (s : Option (Ann A k ⊕ Ann A k) × (BS → Reg → Bool)),
          (stepBim A k).out y s = stepBimOut y s := fun _ _ => rfl
      have hpre : ∀ (y : BS) (u : Ann A k ⊕ Ann A k),
          (stepBim A k).prefixStep y u = stepSt y u := fun _ _ => rfl
      rw [hout]
      cases z with
      | inl z =>
          cases z with
          | letter a m =>
              rw [step_inl_letter, ih]
              simp only [hpre, List.head?_cons, List.tail_cons, phi_cons, phiStep, stepMove,
                stepSt, stepBimOut, stepOut, keepIf_append, List.append_assoc]
          | sep =>
              rw [step_inl_sep, ih]
              simp only [hpre, List.head?_cons, phi_cons, phiStep, stepMove,
                stepSt, stepBimOut, stepOut, keepIf_nil, keepIf_false, List.nil_append,
                List.append_assoc]
          | eos =>
              rw [step_inl_eos, ih]
              simp only [hpre, List.head?_cons, phi_cons, phiStep, stepMove,
                stepSt, stepBimOut, stepOut, keepIf_nil, keepIf_false, List.nil_append,
                List.append_assoc]
      | inr z =>
          cases z with
          | letter a m =>
              rw [step_inr_letter, ih]
              simp only [hpre, List.head?_cons, List.tail_cons, phi_cons, phiStep, stepMove,
                stepSt, stepBimOut, stepOut, keepIf_append, List.append_assoc]
          | sep =>
              cases q with
              | empty =>
                  rw [step_inr_sep_empty, ih]
                  simp only [hpre, List.head?_cons, phi_cons, phiStep, stepMove,
                    stepSt, stepBimOut, stepOut, keepIf_nil, keepIf_false, List.nil_append,
                    List.append_assoc]
              | allR =>
                  rw [step_inr_sep_allR, ih]
                  simp only [hpre, List.head?_cons, phi_cons, phiStep, stepMove,
                    stepSt, stepBimOut, stepOut, keepIf_nil, keepIf_false, List.nil_append,
                    List.append_assoc]
              | trans =>
                  rw [step_inr_sep_trans, ih]
                  simp only [hpre, List.head?_cons, List.tail_cons, phi_cons, phiStep, stepMove,
                    stepSt, stepBimOut, stepOut, pushList, if_true, keepIf_nil, keepIf_append,
                    List.nil_append, List.append_assoc]
              | allL =>
                  rw [step_inr_sep_allL, ih]
                  simp only [hpre, List.head?_cons, List.tail_cons, phi_cons, phiStep, stepMove,
                    stepSt, stepBimOut, stepOut, pushList, if_true, keepIf_nil, keepIf_append,
                    List.nil_append, List.append_assoc]
          | eos =>
              rw [step_inr_eos, ih]
              simp only [hpre, List.head?_cons, phi_cons, phiStep, stepMove,
                stepSt, stepBimOut, stepOut, keepIf_nil, keepIf_false, List.nil_append,
                List.append_assoc]

lemma stepBim_eval (A : Type) (k : ℕ) (w : List (Ann A k ⊕ Ann A k)) :
    (stepBim A k).eval w = stepFun true A k w := by
  have hregs : (fun _ => ([] : List (Ann A (k + 1)))) = regs ([] : List (Ann A (k + 1))) [] [] := by
    funext x; cases x <;> rfl
  rw [Bimachine.eval_eq_evalFrom, stepFun, SST.eval, SST.runConfig]
  show _ = SST.subst (w.foldl (stepSST true A k).stepConfig ((stepSST true A k).init, fun _ => [])).2
      ((stepSST true A k).final _)
  rw [show (stepSST true A k).init = BS.empty from rfl, hregs,
    stepSST_true_run A k w BS.empty [] [] []]
  simp [stepBim]

/-- **The one-step transducer of the enumeration is a rational function in the first-to-last
direction.**  This discharges the hypothesis `Transducers.Exercises.ForwardStepRational`. -/
theorem isRationalFun_stepFun_true (A : Type) [Finite A] (k : ℕ) :
    IsRationalFun (stepFun true A k) :=
  isRationalFun_of_bimachine (stepBim A k) (stepBim_eval A k)

end Exercises
end Transducers
