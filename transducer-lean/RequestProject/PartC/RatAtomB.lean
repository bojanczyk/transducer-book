/-
The list constructor and the two distributivities are rational under string representation.  Part
of the easy direction of Theorem `thm:rational-terms` of *Transducers* (M. Bojańczyk).

For these three atomic functions the regular development of `CombAtomCons.lean` and
`CombAtomDistr.lean` writes the output as the *pointwise concatenation* of two machines, and
pointwise concatenation does not preserve rationality -- it is exactly what would give string
duplication.  Each of the three is treated here by a single left-to-right pass instead.

* The list constructor turns `R (a,[a₂,…])` into `[a,a₂,…]`, and the difficulty is the comma after
  the representation of `a`, which is present exactly when the tail is not empty.  A machine that
  delays that comma by one letter -- it writes nothing at the opening bracket of the tail, and at
  the letter after it either the closing bracket (if the tail was empty) or the comma followed by
  that letter -- computes the whole function in one pass.

* Left distributivity, which is one of the atomic functions added by Theorem `thm:rational-terms`,
  turns `(L a, c)` into `L (a,c)`: the letter that decides between the two cases is the *second*
  letter of the input, so one pass suffices.

* Distributivity turns `(a, L b)` into `L (a,b)`, and here the deciding letter sits in the middle
  of the input, after the representation of `a`.  A machine writes `(a,b)` and remembers the
  deciding letter in its mode, emitting it as its final output; the letter is then moved from the
  end of the string to its front by `Transducers.RatComb.rotLast`, which is a bilateral rewriting
  (`Transducers.biEval`) whose right-to-left automaton remembers the last letter of the suffix.
-/
import RequestProject.PartC.RatAtomA
import RequestProject.PartC.RatBi

namespace Transducers
namespace RatComb

open Comb

/-! ## Moving the last letter of a string to its front -/

/-- The last letter of a string, moved to its front. -/
def rotLast {A : Type} (w : List A) : List A :=
  match w.getLast? with
  | none => []
  | some c => c :: w.dropLast

@[simp] lemma rotLast_append_singleton {A : Type} (u : List A) (c : A) :
    rotLast (u ++ [c]) = c :: u := by
  unfold rotLast
  rw [List.getLast?_concat, List.dropLast_concat]

section Rot

variable {A : Type}

/-- The right-to-left automaton of `rotLast`: it remembers the last letter of the suffix. -/
private def rotNu (s : Option A) (a : A) : Option A :=
  match s with
  | none => some a
  | some b => some b

/-- The output function of `rotLast`: at the first letter, the last letter of the string is
written first. -/
private def rotPsi (p : Bool) (a : A) (s : Option A) : List A :=
  match p, s with
  | false, none => [a]
  | false, some z => [z, a]
  | true, none => []
  | true, some _ => [a]

private lemma revTrans_rotNu (u : List A) (c : A) :
    revTrans rotNu (u ++ [c]) (none : Option A) = some c := by
  induction u with
  | nil => rfl
  | cons a u ih => rw [List.cons_append, revTrans_cons, ih]; rfl

private lemma rot_aux (c : A) :
    ∀ (u : List A) (p : Bool),
      biEvalT (fun (_ : Bool) (_ : A) => true) rotNu rotPsi p (u ++ [c]) none
        = (if p then [] else [c]) ++ u := by
  intro u
  induction u with
  | nil =>
      intro p
      cases p <;> rfl
  | cons a u ih =>
      intro p
      rw [List.cons_append, biEvalT_cons, revTrans_rotNu u c, ih true]
      cases p <;> simp [rotPsi]

/-- **Moving the last letter to the front is a rational function.** -/
theorem isRationalFun_rotLast [Finite A] : IsRationalFun (rotLast : List A → List A) := by
  refine (isRationalFun_biEval (fun (_ : Bool) (_ : A) => true) false rotNu none rotPsi).congr
    (fun w v => ?_)
  rcases List.eq_nil_or_concat w with rfl | ⟨u, c, rfl⟩
  · rfl
  · rw [List.concat_eq_append, show biEval (fun (_ : Bool) (_ : A) => true) false rotNu none rotPsi (u ++ [c])
        = biEvalT (fun (_ : Bool) (_ : A) => true) rotNu rotPsi false (u ++ [c]) none from rfl,
      rot_aux c u false, rotLast_append_singleton]
    simp

end Rot

/-! ## The list constructor -/

/-- The modes of the one-pass machine of the list constructor. -/
inductive RConsMode | s0 | sOpen | sA | sBrack | sPend | tBody | dead
  deriving DecidableEq, Fintype

/-- The one-pass machine of the list constructor: it writes the opening bracket, the head, and
then the tail, delaying by one letter the comma that separates the head from the tail. -/
def rconsMach : Mach RConsMode Sym8 where
  step := fun m e c => match m with
    | .s0 => if c = Sym8.left then .dead else .sOpen
    | .sOpen => .sA
    | .sA => if e = 1 ∧ c = Sym8.comma then .sBrack else .sA
    | .sBrack => .sPend
    | .sPend => if c = Sym8.rbrack then .dead else .tBody
    | .tBody => if e = 2 ∧ c = Sym8.rbrack then .dead else .tBody
    | .dead => .dead
  out := fun m e c => match m with
    | .s0 => if c = Sym8.left then [Sym8.lbrack, Sym8.rbrack] else [Sym8.lbrack]
    | .sOpen => []
    | .sA => if e = 1 ∧ c = Sym8.comma then [] else [c]
    | .sBrack => []
    | .sPend => if c = Sym8.rbrack then [Sym8.rbrack] else [Sym8.comma, c]
    | .tBody => if e = 2 ∧ c = Sym8.rbrack then [Sym8.rbrack] else [c]
    | .dead => []
  fin := fun _ _ => []

@[simp] lemma rconsMach_step_dead (e : ℕ) (c : Sym8) : rconsMach.step .dead e c = .dead := rfl
@[simp] lemma rconsMach_out_dead (e : ℕ) (c : Sym8) : rconsMach.out .dead e c = [] := rfl
@[simp] lemma rconsMach_fin (m : RConsMode) (e : ℕ) : rconsMach.fin m e = [] := rfl
@[simp] lemma rconsMach_out_s0_left (e : ℕ) :
    rconsMach.out .s0 e Sym8.left = [Sym8.lbrack, Sym8.rbrack] := rfl
@[simp] lemma rconsMach_step_s0_left (e : ℕ) : rconsMach.step .s0 e Sym8.left = .dead := rfl
@[simp] lemma rconsMach_out_s0_right (e : ℕ) : rconsMach.out .s0 e Sym8.right = [Sym8.lbrack] :=
  rfl
@[simp] lemma rconsMach_step_s0_right (e : ℕ) : rconsMach.step .s0 e Sym8.right = .sOpen := rfl
@[simp] lemma rconsMach_out_sOpen (e : ℕ) (c : Sym8) : rconsMach.out .sOpen e c = [] := rfl
@[simp] lemma rconsMach_step_sOpen (e : ℕ) (c : Sym8) : rconsMach.step .sOpen e c = .sA := rfl
@[simp] lemma rconsMach_out_sA_comma : rconsMach.out .sA 1 Sym8.comma = [] := rfl
@[simp] lemma rconsMach_step_sA_comma : rconsMach.step .sA 1 Sym8.comma = .sBrack := rfl
@[simp] lemma rconsMach_out_sBrack (e : ℕ) (c : Sym8) : rconsMach.out .sBrack e c = [] := rfl
@[simp] lemma rconsMach_step_sBrack (e : ℕ) (c : Sym8) : rconsMach.step .sBrack e c = .sPend :=
  rfl
@[simp] lemma rconsMach_out_sPend_rbrack (e : ℕ) :
    rconsMach.out .sPend e Sym8.rbrack = [Sym8.rbrack] := rfl
@[simp] lemma rconsMach_step_sPend_rbrack (e : ℕ) :
    rconsMach.step .sPend e Sym8.rbrack = .dead := rfl
@[simp] lemma rconsMach_out_tBody_rbrack : rconsMach.out .tBody 2 Sym8.rbrack = [Sym8.rbrack] :=
  rfl
@[simp] lemma rconsMach_step_tBody_rbrack : rconsMach.step .tBody 2 Sym8.rbrack = .dead := rfl

section RCons

variable (A : Ty)

private lemma rcons_copies_sA : rconsMach.Copies .sA (c1 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [rconsMach, hne, if_false], by simp only [rconsMach, hne, if_false]⟩

private lemma rcons_copies_tBody : rconsMach.Copies .tBody (c2 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 2 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [rconsMach, hne, if_false], by simp only [rconsMach, hne, if_false]⟩

private lemma rcons_comma_tBody : rconsMach.CopiesComma .tBody (c2 A).1 (fun c => [c]) :=
  ⟨rfl, rfl⟩

/-- The run of the machine on the input `L 1`. -/
theorem rconsMach_run_left (u : Ty.one.Elt) :
    rconsMach.run ((consDom A).height) .s0 ((consDom A).repr (Sum.inl u))
      = (Ty.list A).repr [] := by
  show rconsMach.runFrom ((consDom A).height) (RConsMode.s0, 0) (Sym8.left :: [Sym8.one]) = _
  rw [Mach.runFrom_cons]
  simp only [rconsMach_out_s0_left, rconsMach_step_s0_left]
  rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  simp [Ty.repr]

/-- The run of the machine on the input `R (a,l)`. -/
theorem rconsMach_run_right (a : A.Elt) (l : List A.Elt) :
    rconsMach.run ((consDom A).height) .s0 ((consDom A).repr (Sum.inr (a, l)))
      = (Ty.list A).repr (a :: l) := by
  show rconsMach.runFrom ((consDom A).height) (RConsMode.s0, 0)
      (Sym8.right :: (Sym8.lpar :: (A.repr a ++ Sym8.comma ::
        ((Ty.list A).repr l ++ [Sym8.rpar])))) = _
  rw [Mach.runFrom_cons]
  simp only [rconsMach_out_s0_right, rconsMach_step_s0_right,
    dstep_neutral (by simp : wt Sym8.right = 0)]
  rw [Mach.runFrom_cons]
  simp only [rconsMach_out_sOpen, rconsMach_step_sOpen, dstep_c0_lpar, List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (c1 A) _ (consCapA A) (rcons_copies_sA A),
    flatten_map_single, Mach.runFrom_cons]
  simp only [c1_val, rconsMach_out_sA_comma, rconsMach_step_sA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  have hlist : (Ty.list A).repr l ++ [Sym8.rpar]
      = Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack] ++ [Sym8.rpar]) := by
    simp [Ty.repr]
  rw [hlist, Mach.runFrom_cons]
  simp only [c1_val, rconsMach_out_sBrack, rconsMach_step_sBrack, dstep_c1_lbrack,
    List.nil_append]
  cases l with
  | nil =>
      simp only [List.map_nil, joinSep_nil, List.nil_append, List.cons_append]
      rw [Mach.runFrom_cons]
      simp only [c2_val, rconsMach_out_sPend_rbrack, rconsMach_step_sPend_rbrack]
      rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
      simp [Ty.repr]
  | cons a2 l2 =>
      obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a2
      have hcne : c ≠ Sym8.rbrack := by rintro rfl; simp [transparent] at hc
      have hbody : joinSep ((a2 :: l2).map A.repr) ++ [Sym8.rbrack] ++ [Sym8.rpar]
          = A.repr a2 ++ (joinSepTail A l2 ++ [Sym8.rbrack] ++ [Sym8.rpar]) := by
        rw [joinSep_cons]
        simp
      rw [hbody]
      rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) A a2 c w hcw (c2 A) _ (consCapA2 A)
        (by simp only [c2_val]; simp only [rconsMach, hcne, if_false])
        (rcons_copies_tBody A)]
      simp only [c2_val, flatten_map_single]
      rw [show rconsMach.out .sPend 2 c = [Sym8.comma, c] from by
        simp only [rconsMach, hcne, if_false]]
      rw [show joinSepTail A l2 ++ [Sym8.rbrack] ++ [Sym8.rpar]
          = joinSepTail A l2 ++ ([Sym8.rbrack] ++ [Sym8.rpar]) from by simp]
      rw [Mach.runFrom_joinSepTail _ _ _ (fun c => [c]) A (c2 A) (consCapA2 A)
        (rcons_copies_tBody A) (rcons_comma_tBody A) l2 _, flatten_map_single]
      rw [show ([Sym8.rbrack] ++ [Sym8.rpar]) = Sym8.rbrack :: [Sym8.rpar] from rfl,
        Mach.runFrom_cons]
      simp only [c2_val, rconsMach_out_tBody_rbrack, rconsMach_step_tBody_rbrack]
      rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
      rw [Ty.repr_list, joinSep_cons, joinSepTail_cons, joinSep_cons, hcw]
      simp

/-- **The list constructor is rational under string representation.** -/
theorem isRationalUnderRepr_cons :
    IsRationalUnderRepr (A := consDom A) (B := Ty.list A)
      (fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) := by
  refine ⟨rconsMach.run ((consDom A).height) .s0, rconsMach.isRationalFun_run _ _, ?_⟩
  rintro (u | ⟨a, l⟩)
  · exact rconsMach_run_left A u
  · exact rconsMach_run_right A a l

end RCons

/-! ## Left distributivity -/

/-- The modes of the machine of left distributivity. -/
inductive DistlMode | start | tag | inA | inC | stop
  deriving DecidableEq, Fintype

/-- The machine of left distributivity: it moves the tag `L` or `R`, which is the second letter of
the input, to the front. -/
def distlMach : Mach DistlMode Sym8 where
  step := fun m e c => match m with
    | .start => .tag
    | .tag => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .inC else .inA
    | .inC => if e = 1 ∧ c = Sym8.rpar then .stop else .inC
    | .stop => .stop
  out := fun m e c => match m with
    | .start => []
    | .tag => [c, Sym8.lpar]
    | .inA => if e = 1 ∧ c = Sym8.comma then [Sym8.comma] else [c]
    | .inC => if e = 1 ∧ c = Sym8.rpar then [Sym8.rpar] else [c]
    | .stop => []
  fin := fun _ _ => []

@[simp] lemma distlMach_out_start (e : ℕ) (c : Sym8) : distlMach.out .start e c = [] := rfl
@[simp] lemma distlMach_step_start (e : ℕ) (c : Sym8) : distlMach.step .start e c = .tag := rfl
@[simp] lemma distlMach_out_tag (e : ℕ) (c : Sym8) :
    distlMach.out .tag e c = [c, Sym8.lpar] := rfl
@[simp] lemma distlMach_step_tag (e : ℕ) (c : Sym8) : distlMach.step .tag e c = .inA := rfl
@[simp] lemma distlMach_out_inA_comma : distlMach.out .inA 1 Sym8.comma = [Sym8.comma] := rfl
@[simp] lemma distlMach_step_inA_comma : distlMach.step .inA 1 Sym8.comma = .inC := rfl
@[simp] lemma distlMach_out_inC_rpar : distlMach.out .inC 1 Sym8.rpar = [Sym8.rpar] := rfl
@[simp] lemma distlMach_step_inC_rpar : distlMach.step .inC 1 Sym8.rpar = .stop := rfl
@[simp] lemma distlMach_fin (m : DistlMode) (e : ℕ) : distlMach.fin m e = [] := rfl

section Distl

variable (A B C : Ty)

/-- The domain of left distributivity. -/
def distlDom : Ty := Ty.prod (Ty.sum A B) C

private lemma distlDom_height_pos : 1 ≤ (distlDom A B C).height := by
  rw [distlDom, Ty.height]; omega

/-- The counter at depth `1`. -/
private def l1 : Fin ((distlDom A B C).height + 1) :=
  ⟨1, by have := distlDom_height_pos A B C; omega⟩

@[simp] private lemma l1_val : (l1 A B C).1 = 1 := rfl

private lemma dstep_l0_lpar :
    dstep (0 : Fin ((distlDom A B C).height + 1)) Sym8.lpar = l1 A B C := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by have := distlDom_height_pos A B C; simpa using this)]
  rfl

private lemma distlCapS : (1 : ℤ) + ((Ty.sum A B).height : ℤ) ≤ ((distlDom A B C).height : ℤ) := by
  have : (Ty.sum A B).height ≤ max (Ty.sum A B).height C.height := Nat.le_max_left _ _
  rw [distlDom, Ty.height]
  push_cast
  omega

private lemma distlCapC : (1 : ℤ) + (C.height : ℤ) ≤ ((distlDom A B C).height : ℤ) := by
  have : C.height ≤ max (Ty.sum A B).height C.height := Nat.le_max_right _ _
  rw [distlDom, Ty.height]
  push_cast
  omega

private lemma distl_copies_inA : distlMach.Copies .inA (l1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [distlMach, hne, if_false], by simp only [distlMach, hne, if_false]⟩

private lemma distl_copies_inC : distlMach.Copies .inC (l1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [distlMach, hne, if_false], by simp only [distlMach, hne, if_false]⟩

private lemma distlMach_run_aux (x : (Ty.sum A B).Elt) (tag : Sym8) (v : List Sym8)
    (hx : (Ty.sum A B).repr x = tag :: v) (c : C.Elt) :
    distlMach.run ((distlDom A B C).height) .start ((distlDom A B C).repr (x, c))
      = tag :: (Sym8.lpar :: (v ++ Sym8.comma :: (C.repr c ++ [Sym8.rpar]))) := by
  show distlMach.runFrom ((distlDom A B C).height) (DistlMode.start, 0)
      (Sym8.lpar :: ((Ty.sum A B).repr x ++ Sym8.comma :: (C.repr c ++ [Sym8.rpar]))) = _
  rw [Mach.runFrom_cons]
  simp only [distlMach_out_start, distlMach_step_start, dstep_l0_lpar, List.nil_append]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) (Ty.sum A B) x tag v hx (l1 A B C) _
    (distlCapS A B C) rfl (distl_copies_inA A B C)]
  simp only [l1_val, flatten_map_single, distlMach_out_tag, distlMach_step_tag]
  rw [Mach.runFrom_cons]
  simp only [l1_val, distlMach_out_inA_comma, distlMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) C c (l1 A B C) _ (distlCapC A B C)
    (distl_copies_inC A B C), flatten_map_single, Mach.runFrom_cons]
  simp only [l1_val, distlMach_out_inC_rpar, distlMach_step_inC_rpar]
  rw [Mach.runFrom_nil]
  simp only [distlMach_fin]
  simp

/-- **Left distributivity is rational under string representation.** -/
theorem isRationalUnderRepr_distl :
    IsRationalUnderRepr (A := distlDom A B C)
      (B := Ty.sum (Ty.prod A C) (Ty.prod B C))
      (fun p => Sum.elim (fun a => Sum.inl (a, p.2)) (fun b => Sum.inr (b, p.2)) p.1) := by
  refine ⟨distlMach.run ((distlDom A B C).height) .start,
    distlMach.isRationalFun_run _ _, ?_⟩
  rintro ⟨a | b, c⟩
  · rw [distlMach_run_aux A B C (Sum.inl a) Sym8.left (A.repr a) rfl c]
    rfl
  · rw [distlMach_run_aux A B C (Sum.inr b) Sym8.right (B.repr b) rfl c]
    rfl

end Distl

/-! ## Distributivity -/

/-- The modes of the machine of distributivity. -/
inductive RDistrMode | start | inA | skip | inBL | inBR | stopL | stopR
  deriving DecidableEq, Fintype

/-- The machine of distributivity: it writes the pair and remembers the tag `L` or `R`, which it
emits as its final output. -/
def rdistrMach : Mach RDistrMode Sym8 where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .skip else .inA
    | .skip => if c = Sym8.left then .inBL else .inBR
    | .inBL => if e = 1 ∧ c = Sym8.rpar then .stopL else .inBL
    | .inBR => if e = 1 ∧ c = Sym8.rpar then .stopR else .inBR
    | .stopL => .stopL
    | .stopR => .stopR
  out := fun m e c => match m with
    | .start => [Sym8.lpar]
    | .inA => if e = 1 ∧ c = Sym8.comma then [Sym8.comma] else [c]
    | .skip => []
    | .inBL => if e = 1 ∧ c = Sym8.rpar then [Sym8.rpar] else [c]
    | .inBR => if e = 1 ∧ c = Sym8.rpar then [Sym8.rpar] else [c]
    | .stopL => []
    | .stopR => []
  fin := fun m _ => match m with
    | .stopL => [Sym8.left]
    | .stopR => [Sym8.right]
    | _ => []

@[simp] lemma rdistrMach_out_start (e : ℕ) (c : Sym8) :
    rdistrMach.out .start e c = [Sym8.lpar] := rfl
@[simp] lemma rdistrMach_step_start (e : ℕ) (c : Sym8) : rdistrMach.step .start e c = .inA := rfl
@[simp] lemma rdistrMach_out_inA_comma : rdistrMach.out .inA 1 Sym8.comma = [Sym8.comma] := rfl
@[simp] lemma rdistrMach_step_inA_comma : rdistrMach.step .inA 1 Sym8.comma = .skip := rfl
@[simp] lemma rdistrMach_out_skip (e : ℕ) (c : Sym8) : rdistrMach.out .skip e c = [] := rfl
@[simp] lemma rdistrMach_step_skip_left (e : ℕ) :
    rdistrMach.step .skip e Sym8.left = .inBL := rfl
@[simp] lemma rdistrMach_step_skip_right (e : ℕ) :
    rdistrMach.step .skip e Sym8.right = .inBR := rfl
@[simp] lemma rdistrMach_out_inBL_rpar : rdistrMach.out .inBL 1 Sym8.rpar = [Sym8.rpar] := rfl
@[simp] lemma rdistrMach_step_inBL_rpar : rdistrMach.step .inBL 1 Sym8.rpar = .stopL := rfl
@[simp] lemma rdistrMach_out_inBR_rpar : rdistrMach.out .inBR 1 Sym8.rpar = [Sym8.rpar] := rfl
@[simp] lemma rdistrMach_step_inBR_rpar : rdistrMach.step .inBR 1 Sym8.rpar = .stopR := rfl
@[simp] lemma rdistrMach_fin_stopL (e : ℕ) : rdistrMach.fin .stopL e = [Sym8.left] := rfl
@[simp] lemma rdistrMach_fin_stopR (e : ℕ) : rdistrMach.fin .stopR e = [Sym8.right] := rfl

section Distr

variable (A B C : Ty)

/-- The domain of distributivity. -/
def rdistrDom : Ty := Ty.prod A (Ty.sum B C)

private lemma rdistrDom_height_pos : 1 ≤ (rdistrDom A B C).height := by
  rw [rdistrDom, Ty.height]; omega

/-- The counter at depth `1`. -/
private def r1 : Fin ((rdistrDom A B C).height + 1) :=
  ⟨1, by have := rdistrDom_height_pos A B C; omega⟩

@[simp] private lemma r1_val : (r1 A B C).1 = 1 := rfl

private lemma dstep_r0_lpar :
    dstep (0 : Fin ((rdistrDom A B C).height + 1)) Sym8.lpar = r1 A B C := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by have := rdistrDom_height_pos A B C; simpa using this)]
  rfl

private lemma rdistrCapA : (1 : ℤ) + (A.height : ℤ) ≤ ((rdistrDom A B C).height : ℤ) := by
  have : A.height ≤ max A.height (Ty.sum B C).height := Nat.le_max_left _ _
  rw [rdistrDom, Ty.height]
  push_cast
  omega

private lemma rdistrCapS :
    (1 : ℤ) + ((Ty.sum B C).height : ℤ) ≤ ((rdistrDom A B C).height : ℤ) := by
  have : (Ty.sum B C).height ≤ max A.height (Ty.sum B C).height := Nat.le_max_right _ _
  rw [rdistrDom, Ty.height]
  push_cast
  omega

private lemma rdistr_copies_inA : rdistrMach.Copies .inA (r1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [rdistrMach, hne, if_false], by simp only [rdistrMach, hne, if_false]⟩

private lemma rdistr_copies_inBL : rdistrMach.Copies .inBL (r1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [rdistrMach, hne, if_false], by simp only [rdistrMach, hne, if_false]⟩

private lemma rdistr_copies_inBR : rdistrMach.Copies .inBR (r1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [rdistrMach, hne, if_false], by simp only [rdistrMach, hne, if_false]⟩

private lemma rdistrMach_run_inl (a : A.Elt) (b : B.Elt) :
    rdistrMach.run ((rdistrDom A B C).height) .start ((rdistrDom A B C).repr (a, Sum.inl b))
      = (Ty.prod A B).repr (a, b) ++ [Sym8.left] := by
  show rdistrMach.runFrom ((rdistrDom A B C).height) (RDistrMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma ::
        ((Ty.sum B C).repr (Sum.inl b) ++ [Sym8.rpar]))) = _
  rw [Mach.runFrom_cons]
  simp only [rdistrMach_out_start, rdistrMach_step_start, dstep_r0_lpar]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (r1 A B C) _ (rdistrCapA A B C)
    (rdistr_copies_inA A B C), flatten_map_single, Mach.runFrom_cons]
  simp only [r1_val, rdistrMach_out_inA_comma, rdistrMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) (Ty.sum B C) (Sum.inl b) Sym8.left (B.repr b)
    rfl (r1 A B C) _ (rdistrCapS A B C) rfl (rdistr_copies_inBL A B C)]
  simp only [r1_val, rdistrMach_out_skip, flatten_map_single, List.nil_append]
  rw [Mach.runFrom_cons]
  rw [Mach.runFrom_nil]
  simp [Ty.repr, rdistrMach]

private lemma rdistrMach_run_inr (a : A.Elt) (c : C.Elt) :
    rdistrMach.run ((rdistrDom A B C).height) .start ((rdistrDom A B C).repr (a, Sum.inr c))
      = (Ty.prod A C).repr (a, c) ++ [Sym8.right] := by
  show rdistrMach.runFrom ((rdistrDom A B C).height) (RDistrMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma ::
        ((Ty.sum B C).repr (Sum.inr c) ++ [Sym8.rpar]))) = _
  rw [Mach.runFrom_cons]
  simp only [rdistrMach_out_start, rdistrMach_step_start, dstep_r0_lpar]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (r1 A B C) _ (rdistrCapA A B C)
    (rdistr_copies_inA A B C), flatten_map_single, Mach.runFrom_cons]
  simp only [r1_val, rdistrMach_out_inA_comma, rdistrMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) (Ty.sum B C) (Sum.inr c) Sym8.right (C.repr c)
    rfl (r1 A B C) _ (rdistrCapS A B C) rfl (rdistr_copies_inBR A B C)]
  simp only [r1_val, rdistrMach_out_skip, flatten_map_single, List.nil_append]
  rw [Mach.runFrom_cons]
  rw [Mach.runFrom_nil]
  simp [Ty.repr, rdistrMach]

/-- **Distributivity is rational under string representation.** -/
theorem isRationalUnderRepr_distr :
    IsRationalUnderRepr (A := rdistrDom A B C)
      (B := Ty.sum (Ty.prod A B) (Ty.prod A C))
      (fun x => Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) := by
  refine ⟨fun w => rotLast (rdistrMach.run ((rdistrDom A B C).height) .start w),
    isRationalFun_comp' (rdistrMach.isRationalFun_run _ _) isRationalFun_rotLast
      (fun _ => rfl), ?_⟩
  rintro ⟨a, b | c⟩
  · show rotLast (rdistrMach.run _ _ ((rdistrDom A B C).repr (a, Sum.inl b))) = _
    rw [rdistrMach_run_inl, rotLast_append_singleton]
    rfl
  · show rotLast (rdistrMach.run _ _ ((rdistrDom A B C).repr (a, Sum.inr c))) = _
    rw [rdistrMach_run_inr, rotLast_append_singleton]
    rfl

end Distr

end RatComb
end Transducers
