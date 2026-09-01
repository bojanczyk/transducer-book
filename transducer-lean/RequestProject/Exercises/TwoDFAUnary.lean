/-
Exercise `exer:2dfa-unary-output` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): over a one-letter output alphabet, the regular functions are exactly
the rational functions.

The solution of the book is the one that is followed here.  One inclusion is immediate, since a
rational function is regular.  For the other one, a regular function is computed by a two-way
transducer `M` (Corollary `cor:2dfa-computes-all-regular-functions`), and the function which maps
an input string to the string representation of its reachable configuration graph is rational
(Lemma `lem:compute-configuration-graph`, `Transducers.TwoWay.isRationalFun_enc`).  In that
representation each input position carries one slice of the graph, and the slice determines the
output strings of the transitions performed while the head is at that position; so it is enough to
post-compose the encoding with the map which sends a slice to the concatenation of the output
strings of its edges.  Over a one-letter output alphabet the resulting string is the output of `M`,
because the two differ only in the order of their letters.

Two points that the book passes over have to be dealt with.

* A slice records the outgoing edge of a vertex on *both* of the cuts it is adjacent to: an edge
  that moves right is recorded on the left copy of the slice of the letter it crosses, an edge that
  moves left on the right copy, and a *halting* edge on both copies of its cut.  Counting the label
  of every edge of every slice would therefore count the halting transition twice.  The map applied
  to a slice counts, on the left copy, all the edges, and on the right copy only the edges that
  move left; this counts each edge exactly once, *except* for a halting transition at the very last
  cut, which is then recorded nowhere.  The map is therefore not a homomorphism but a bimachine:
  at the last letter it counts the halting edges of the right copy as well.  Bimachines compute
  rational functions (Theorem `thm:bimachines`), so this costs nothing.
* That the count is right rests on the run of `M` visiting each configuration at most once, which
  holds because the run halts (`Transducers.TwoWay.run_inj`), and on a visited configuration never
  being stuck, for the same reason.

The exercise says *unary* output alphabet.  The statement below asks only for the output alphabet
to be a subsingleton, which is the property the proof uses; a one-letter alphabet is a subsingleton,
and the empty alphabet is covered as well.
-/
import RequestProject.PartC.ConfGraphReg
import RequestProject.PartC.ConfGraphRun
import RequestProject.PartC.Statements

namespace Transducers
namespace Exercises

open Transducers TwoWay

variable {A B Q : Type}

/-! ## Counting the output letters recorded by a slice -/

/-- The length of the output string labelling the outgoing edge of a vertex, whether the edge is a
move or a halting edge. -/
def voutEdgeLen {L : Type} (len : L → ℕ) : VOut Q L → ℕ
  | VOut.nil => 0
  | VOut.move _ l => len l
  | VOut.halt l => len l

/-- The length of the output string labelling the outgoing edge of a vertex, counting only edges
that move. -/
def voutMoveLen {L : Type} (len : L → ℕ) : VOut Q L → ℕ
  | VOut.nil => 0
  | VOut.move _ l => len l
  | VOut.halt _ => 0

/-- The length of the output string labelling the outgoing edge of a vertex, counting only halting
edges. -/
def voutHaltLen {L : Type} (len : L → ℕ) : VOut Q L → ℕ
  | VOut.nil => 0
  | VOut.move _ _ => 0
  | VOut.halt l => len l

/-- The length of the output string of an edge label. -/
def labLen (M : TwoWay A B Q) (l : M.Lab) : ℕ := l.val.length

section Fintype

variable [Fintype Q]

/-- The number of output letters that a letter of the alphabet `C` records.  On the left copy of a
slice every edge is counted, on the right copy only the edges that move -- and, if the letter is
the last one of the input (`last`), the halting edges of the right copy as well, since a halting
transition at the last cut is recorded on no left copy. -/
def sliceCount (M : TwoWay A B Q) (last : Bool) : CLet Q M.Lab → ℕ
  | Sum.inl s =>
      (∑ q : Q, voutEdgeLen (labLen M) (s (false, q)))
        + (∑ q : Q, voutMoveLen (labLen M) (s (true, q)))
        + (if last then ∑ q : Q, voutHaltLen (labLen M) (s (true, q)) else 0)
  | Sum.inr o => o.elim 0 (fun l => l.val.length)

/-- The total number of output letters recorded by a string over the alphabet `C`. -/
def countList (M : TwoWay A B Q) : List (CLet Q M.Lab) → ℕ
  | [] => 0
  | c :: u => sliceCount M u.isEmpty c + countList M u

/-- The bimachine of the solution, as a function: at each letter of the encoded configuration graph
it prints as many copies of the output letter `b` as the letter records. -/
def unaryOut (M : TwoWay A B Q) (b : B) : List (CLet Q M.Lab) → List B :=
  biEval (fun (_ : Unit) (_ : CLet Q M.Lab) => ()) ()
    (fun (_ : Bool) (_ : CLet Q M.Lab) => false) true
    (fun _ c s => List.replicate (sliceCount M s c) b)

lemma revTrans_const_false {Γ : Type} (u : List Γ) (t : Bool) :
    revTrans (fun (_ : Bool) (_ : Γ) => false) u t = if u.isEmpty then t else false := by
  cases u with
  | nil => simp
  | cons a u => simp

lemma unaryOut_length (M : TwoWay A B Q) (b : B) (u : List (CLet Q M.Lab)) :
    (unaryOut M b u).length = countList M u := by
  show (biEvalT _ _ _ () u true).length = countList M u
  induction u with
  | nil => simp [countList]
  | cons c u ih =>
      rw [biEvalT_cons, countList, List.length_append, ih, revTrans_const_false]
      have hb : (if u.isEmpty then (true : Bool) else false) = u.isEmpty := by
        cases hu : u.isEmpty <;> simp
      rw [hb, List.length_replicate]

/-- The count of a string that is a list of consecutive slices. -/
lemma countList_map_range' (M : TwoWay A B Q) (F : ℕ → CLet Q M.Lab) :
    ∀ (n k : ℕ), countList M ((List.range' k n).map F)
      = ∑ i ∈ Finset.range n, sliceCount M (decide (i + 1 = n)) (F (k + i)) := by
  intro n
  induction n with
  | zero => intro k; simp [countList]
  | succ m ih =>
      intro k
      have hL : ∀ i ∈ Finset.range m, sliceCount M (decide (i + 1 = m)) (F (k + 1 + i))
          = sliceCount M (decide (i + 1 + 1 = m + 1)) (F (k + (i + 1))) := by
        intro i _
        have e1 : (decide (i + 1 = m)) = decide (i + 1 + 1 = m + 1) := by simp
        have e2 : k + 1 + i = k + (i + 1) := by omega
        rw [e1, e2]
      have h1 : ((List.range' (k + 1) m).map F).isEmpty = decide (0 + 1 = m + 1) := by
        cases m <;> simp
      rw [List.range'_succ, List.map_cons, countList, ih (k + 1), Finset.sum_range_succ',
        h1, Finset.sum_congr rfl hL]
      simp only [Nat.add_zero]
      omega

lemma countList_enc_of_ne_nil {M : TwoWay A B Q} {w : List A} (hw : w ≠ []) :
    countList M (enc M w)
      = ∑ i ∈ Finset.range w.length,
          sliceCount M (decide (i + 1 = w.length)) (Sum.inl (encSlice M w i)) := by
  rw [enc_of_ne_nil hw, List.range_eq_range']
  rw [countList_map_range' M (fun i => (Sum.inl (encSlice M w i) : CLet Q M.Lab)) w.length 0]
  exact Finset.sum_congr rfl (fun i _ => by simp)

end Fintype

/-! ## The output letters produced at a vertex of the configuration graph -/

open scoped Classical in
/-- The number of output letters produced by the transition out of the vertex given by the state
`q` at the cut `j`, or `0` if that vertex is not visited. -/
noncomputable def vertexOut (M : TwoWay A B Q) (w : List A) (j : ℕ) (q : Q) : ℕ :=
  if Visits M w (Cfg.conf (w.take j) q (w.drop j)) then
    (M.transOut (prevAt w j) q w[j]?).length
  else 0

/-! ### Reading off the transition at a cut -/

lemma getLast?_take_of_le {w : List A} {j : ℕ} (hj : j ≤ w.length) :
    (w.take j).getLast? = prevAt w j := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp [prevAt]
  · rw [List.getLast?_eq_getElem?]
    have hlen : (w.take j).length = j := by rw [List.length_take]; omega
    rw [hlen, prevAt, if_neg (by omega), List.getElem?_take]
    rw [if_pos (by omega)]

lemma head?_drop_eq {w : List A} {j : ℕ} : (w.drop j).head? = w[j]? := List.head?_drop

/-- The transition taken at the vertex given by the state `q` at the cut `j`. -/
lemma step_conf_eq {M : TwoWay A B Q} {w : List A} {j : ℕ} (hj : j ≤ w.length) (q : Q) :
    M.step (w.take j).getLast? q (w.drop j).head? = M.step (prevAt w j) q w[j]? := by
  rw [getLast?_take_of_le hj, head?_drop_eq]

/-- A right move at the right end of the input gets stuck. -/
lemma stepCfg_right_end {M : TwoWay A B Q} {w : List A} {q q' : Q} {o : List B}
    (h : M.step (prevAt w w.length) q w[w.length]? = Sum.inr (q', o, true)) :
    M.stepCfg (Cfg.conf (w.take w.length) q (w.drop w.length)) = none := by
  have hd : w.drop w.length = [] := by simp
  rw [TwoWay.stepCfg, step_conf_eq (le_refl _) q, h]
  simp [hd]

/-- A left move at the left end of the input gets stuck. -/
lemma stepCfg_left_end {M : TwoWay A B Q} {w : List A} {q q' : Q} {o : List B}
    (h : M.step (prevAt w 0) q w[0]? = Sum.inr (q', o, false)) :
    M.stepCfg (Cfg.conf (w.take 0) q (w.drop 0)) = none := by
  rw [TwoWay.stepCfg, step_conf_eq (Nat.zero_le _) q, h]
  simp

/-- A configuration on a halting run is never stuck. -/
lemma stepCfg_isSome_of_visits {M : TwoWay A B Q} {w : List A} {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) {c : Cfg A Q} (hv : Visits M w c) (hc : c ≠ Cfg.halt) :
    (M.stepCfg c).isSome := by
  obtain ⟨t, ht⟩ := hv
  rcases hs : M.stepCfg c with _ | p
  · exfalso
    have hnext : cfgAt M w (t + 1) = none := by
      rw [cfgAt_succ, ht]; simp [hs]
    have hle : T ≤ t := by
      by_contra hcon
      have : cfgAt M w T = none := cfgAt_none_mono M w (by omega) hnext
      rw [hT] at this; simp at this
    rcases Nat.lt_or_ge T t with hlt | hge
    · have : cfgAt M w t = none := cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
      rw [ht] at this; simp at this
    · have : T = t := by omega
      subst this
      rw [hT] at ht
      exact hc (Option.some_injective _ ht).symm
  · simp

/-! ### One vertex contributes its output exactly once -/

lemma slice_term_eq {M : TwoWay A B Q} {w : List A} {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    {j : ℕ} (hj : j ≤ w.length) (q : Q) :
    (if j = w.length then voutHaltLen (labLen M) (cutV M w j q false)
      else voutEdgeLen (labLen M) (cutV M w j q true))
      + voutMoveLen (labLen M) (cutV M w j q false) = vertexOut M w j q := by
  classical
  by_cases hvis : Visits M w (Cfg.conf (w.take j) q (w.drop j))
  · have hcut : ∀ d : Bool, cutV M w j q d = edgeOf M (prevAt w j) q w[j]? d := by
      intro d; rw [cutV, if_pos hvis]
    have hvo : vertexOut M w j q = (M.transOut (prevAt w j) q w[j]?).length := by
      rw [vertexOut, if_pos hvis]
    rcases hstep : M.step (prevAt w j) q w[j]? with o | ⟨q', o, dir⟩
    · simp only [hcut, edgeOf_halt hstep, hvo]
      rcases eq_or_ne j w.length with hjn | hjn
      · rw [if_pos hjn]
        simp [voutHaltLen, voutMoveLen, labLen, labOf, transOut, hstep]
      · rw [if_neg hjn]
        simp [voutEdgeLen, voutMoveLen, labLen, labOf, transOut, hstep]
    · have hne : j ≠ w.length ∨ dir = false := by
        by_cases hjn : j = w.length
        · right
          rcases hdir : dir with _ | _
          · rfl
          · exfalso
            subst hjn
            have := stepCfg_right_end (M := M) (w := w) (q := q) (q' := q') (o := o)
              (by rw [hstep, hdir])
            have hsome := stepCfg_isSome_of_visits hT hvis (by simp)
            rw [this] at hsome; simp at hsome
        · left; exact hjn
      have hj0 : dir = false → j ≠ 0 := by
        intro hdir hj0
        subst hj0
        have := stepCfg_left_end (M := M) (w := w) (q := q) (q' := q') (o := o)
          (by rw [hstep, hdir])
        have hsome := stepCfg_isSome_of_visits hT hvis (by simp)
        rw [this] at hsome; simp at hsome
      rw [hvo]
      rcases hdir : dir with _ | _
      · -- moving left
        subst hdir
        simp only [hcut, edgeOf_move hstep, edgeOf_move_ne hstep (by simp : (false : Bool) ≠ true)]
        rcases eq_or_ne j w.length with hjn | hjn
        · rw [if_pos hjn]
          simp [voutHaltLen, voutMoveLen, labLen, labOf, transOut, hstep]
        · rw [if_neg hjn]
          simp [voutEdgeLen, voutMoveLen, labLen, labOf, transOut, hstep]
      · -- moving right
        subst hdir
        have hjn : j ≠ w.length := by
          rcases hne with h | h
          · exact h
          · simp at h
        simp only [hcut, edgeOf_move hstep, edgeOf_move_ne hstep (by simp : (true : Bool) ≠ false)]
        rw [if_neg hjn]
        simp [voutEdgeLen, voutMoveLen, labLen, labOf, transOut, hstep]
  · have hcut : ∀ d : Bool, cutV M w j q d = VOut.nil := by
      intro d; rw [cutV, if_neg hvis]
    simp only [hcut]
    rw [vertexOut, if_neg hvis]
    rcases eq_or_ne j w.length with hjn | hjn
    · rw [if_pos hjn]; simp [voutHaltLen, voutMoveLen]
    · rw [if_neg hjn]; simp [voutEdgeLen, voutMoveLen]

/-- On a halting run there is no left move at the left end of the input. -/
lemma moveLen_cut_zero {M : TwoWay A B Q} {w : List A} {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (q : Q) :
    voutMoveLen (labLen M) (cutV M w 0 q false) = 0 := by
  classical
  by_cases hvis : Visits M w (Cfg.conf (w.take 0) q (w.drop 0))
  · rw [cutV, if_pos hvis]
    rcases hstep : M.step (prevAt w 0) q w[0]? with o | ⟨q', o, dir⟩
    · rw [edgeOf_halt hstep]; rfl
    · rcases hdir : dir with _ | _
      · exfalso
        subst hdir
        have hstuck := stepCfg_left_end (M := M) (w := w) (q := q) (q' := q') (o := o) hstep
        have hsome := stepCfg_isSome_of_visits hT hvis (by simp)
        rw [hstuck] at hsome; simp at hsome
      · subst hdir
        rw [edgeOf_move_ne hstep (by simp : (true : Bool) ≠ false)]; rfl
  · rw [cutV, if_neg hvis]; rfl

/-! ### Claim A: the encoded graph records exactly the output letters -/

section Fintype2

variable [Fintype Q]

lemma sum_sliceCount_eq_sum_vertexOut {M : TwoWay A B Q} {w : List A} {T : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (hw : w ≠ []) :
    ∑ i ∈ Finset.range w.length,
        sliceCount M (decide (i + 1 = w.length)) (Sum.inl (encSlice M w i))
      = ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q, vertexOut M w j q := by
  classical
  have hpos : 0 < w.length := by
    rcases w with _ | ⟨a, t⟩
    · exact absurd rfl hw
    · simp
  have hslice : ∀ i, sliceCount M (decide (i + 1 = w.length)) (Sum.inl (encSlice M w i))
      = ((∑ q : Q, voutEdgeLen (labLen M) (cutV M w i q true))
          + (∑ q : Q, voutMoveLen (labLen M) (cutV M w (i + 1) q false)))
        + (if i + 1 = w.length then ∑ q : Q, voutHaltLen (labLen M) (cutV M w (i + 1) q false)
            else 0) := by
    intro i
    simp only [sliceCount, encSlice, decide_eq_true_eq, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true]
  rw [Finset.sum_congr rfl (fun i _ => hslice i), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hS3 : ∑ i ∈ Finset.range w.length,
      (if i + 1 = w.length then ∑ q : Q, voutHaltLen (labLen M) (cutV M w (i + 1) q false)
        else 0)
      = ∑ q : Q, voutHaltLen (labLen M) (cutV M w w.length q false) := by
    rw [Finset.sum_eq_single (w.length - 1)]
    · have he : w.length - 1 + 1 = w.length := by omega
      rw [if_pos he, he]
    · intro i hi hne
      rw [if_neg (by simp only [Finset.mem_range] at hi; omega)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  have hRHS : ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q, vertexOut M w j q
      = (∑ j ∈ Finset.range (w.length + 1), ∑ q : Q,
            (if j = w.length then voutHaltLen (labLen M) (cutV M w j q false)
              else voutEdgeLen (labLen M) (cutV M w j q true)))
        + ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q,
            voutMoveLen (labLen M) (cutV M w j q false) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    exact (slice_term_eq hT (by simp only [Finset.mem_range] at hj; omega) q).symm
  have hA : ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q,
      (if j = w.length then voutHaltLen (labLen M) (cutV M w j q false)
        else voutEdgeLen (labLen M) (cutV M w j q true))
      = (∑ i ∈ Finset.range w.length, ∑ q : Q, voutEdgeLen (labLen M) (cutV M w i q true))
        + ∑ q : Q, voutHaltLen (labLen M) (cutV M w w.length q false) := by
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [if_neg (by simp only [Finset.mem_range] at hi; omega)]
    · refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [if_pos rfl]
  have hB : ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q,
      voutMoveLen (labLen M) (cutV M w j q false)
      = ∑ i ∈ Finset.range w.length, ∑ q : Q,
          voutMoveLen (labLen M) (cutV M w (i + 1) q false) := by
    rw [Finset.sum_range_succ']
    have hz : ∑ q : Q, voutMoveLen (labLen M) (cutV M w 0 q false) = 0 :=
      Finset.sum_eq_zero (fun q _ => moveLen_cut_zero hT q)
    rw [hz, Nat.add_zero]
  rw [hRHS, hA, hB, hS3]
  omega

end Fintype2

/-! ### Claim B: the run produces exactly those output letters -/

open scoped Classical in
/-- The cut and the state of the configuration of the run of `M` on `w` at time `t`. -/
noncomputable def runPos (M : TwoWay A B Q) (w : List A) (t : ℕ) : ℕ × Q :=
  match cfgAt M w t with
  | some (Cfg.conf u q _) => (u.length, q)
  | _ => (0, M.init)

lemma runPos_of_conf {M : TwoWay A B Q} {w u v' : List A} {q : Q} {t : ℕ}
    (h : cfgAt M w t = some (Cfg.conf u q v')) : runPos M w t = (u.length, q) := by
  rw [runPos, h]

lemma time_le_halt {M : TwoWay A B Q} {w : List A} {T t : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (h : (cfgAt M w t).isSome) : t ≤ T := by
  by_contra hcon
  have hnone : cfgAt M w t = none := cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
  rw [hnone] at h; simp at h

/-- The output of a step is the output string of the transition it takes. -/
lemma stepCfg_out {M : TwoWay A B Q} {u v' : List A} {q : Q} {o : List B} {c' : Cfg A Q}
    (h : M.stepCfg (Cfg.conf u q v') = some (o, c')) :
    o = M.transOut u.getLast? q v'.head? := by
  rw [TwoWay.stepCfg] at h
  rcases hs : M.step u.getLast? q v'.head? with o' | ⟨q', o', dir⟩
  · rw [hs] at h
    rw [transOut_halt hs]
    exact (congrArg Prod.fst (Option.some.inj h)).symm
  · rw [hs] at h
    rw [transOut_move hs]
    cases dir
    · rcases hu : u.getLast? with _ | a
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h; exact (congrArg Prod.fst (Option.some.inj h)).symm
    · rcases hv : v' with _ | ⟨a, tl⟩
      · rw [hv] at h; exact absurd h (by simp)
      · rw [hv] at h; exact (congrArg Prod.fst (Option.some.inj h)).symm

/-- The configuration of the run at a time before it halts, written with the cut it is at. -/
lemma cfgAt_take_drop {M : TwoWay A B Q} {w : List A} {T t : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (htT : t < T) :
    cfgAt M w t = some (Cfg.conf (w.take (runPos M w t).1) (runPos M w t).2
        (w.drop (runPos M w t).1))
      ∧ (runPos M w t).1 ≤ w.length := by
  have hsome : (cfgAt M w t).isSome :=
    cfgAt_isSome_of_le M w (le_of_lt htT) (by rw [hT]; simp)
  rcases hc : cfgAt M w t with _ | c
  · rw [hc] at hsome; simp at hsome
  · cases c with
    | halt =>
        exact absurd (halt_time_unique M w hc hT) (by omega)
    | conf u q v' =>
        have hap : u ++ v' = w := cfgAt_append M w t hc
        have h1 : w.take u.length = u := by rw [← hap]; exact List.take_left
        have h2 : w.drop u.length = v' := by rw [← hap]; exact List.drop_left
        have hr : runPos M w t = (u.length, q) := runPos_of_conf hc
        rw [hr]
        refine ⟨?_, ?_⟩
        · simp only [h1, h2]
        · rw [← hap]; simp

/-- Each step of the run produces the output recorded at the vertex it leaves. -/
lemma vertexOut_runPos {M : TwoWay A B Q} {w : List A} {T t : ℕ}
    (hT : cfgAt M w T = some Cfg.halt) (htT : t < T) :
    vertexOut M w (runPos M w t).1 (runPos M w t).2 = (outAt M w t).length := by
  classical
  obtain ⟨hc, hle⟩ := cfgAt_take_drop hT htT
  have hsucc : (cfgAt M w (t + 1)).isSome :=
    cfgAt_isSome_of_le M w (n := T) (by omega) (by rw [hT]; simp)
  rcases hn : cfgAt M w (t + 1) with _ | c₁
  · rw [hn] at hsucc; simp at hsucc
  · obtain ⟨c', hc', hstep⟩ := exists_pred M w hn
    rw [hc] at hc'
    have hc'eq : c' = Cfg.conf (w.take (runPos M w t).1) (runPos M w t).2
        (w.drop (runPos M w t).1) := (Option.some.inj hc').symm
    subst hc'eq
    have hvis : Visits M w (Cfg.conf (w.take (runPos M w t).1) (runPos M w t).2
        (w.drop (runPos M w t).1)) := ⟨t, hc⟩
    rw [vertexOut, if_pos hvis]
    rw [stepCfg_out hstep, getLast?_take_of_le hle, head?_drop_eq]

section Fintype3

variable [Fintype Q]

lemma sum_vertexOut_eq_length {M : TwoWay A B Q} {w : List A} {v : List B}
    (h : M.Computes w v) :
    ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q, vertexOut M w j q = v.length := by
  classical
  obtain ⟨T, hT, hout⟩ := exists_halt_time M w h
  have hvlen : v.length = ∑ t ∈ Finset.range T, (outAt M w t).length := by
    rw [← hout, outRange, Nat.sub_zero, List.length_flatten, List.map_map,
      ← List.range_eq_range']
    rfl
  have hprod : ∑ j ∈ Finset.range (w.length + 1), ∑ q : Q, vertexOut M w j q
      = ∑ x ∈ (Finset.range (w.length + 1) ×ˢ (Finset.univ : Finset Q)),
          vertexOut M w x.1 x.2 :=
    (Finset.sum_product _ _ (fun x => vertexOut M w x.1 x.2)).symm
  rw [hprod, hvlen]
  set S : Finset (ℕ × Q) := (Finset.range (w.length + 1) ×ˢ (Finset.univ : Finset Q)).filter
      (fun x => Visits M w (Cfg.conf (w.take x.1) x.2 (w.drop x.1))) with hSdef
  have hsub : S ⊆ Finset.range (w.length + 1) ×ˢ (Finset.univ : Finset Q) :=
    Finset.filter_subset _ _
  have hzero : ∀ x ∈ Finset.range (w.length + 1) ×ˢ (Finset.univ : Finset Q), x ∉ S →
      vertexOut M w x.1 x.2 = 0 := by
    intro x hx hxS
    rw [vertexOut, if_neg]
    intro hvis
    exact hxS (Finset.mem_filter.mpr ⟨hx, hvis⟩)
  rw [← Finset.sum_subset hsub hzero]
  refine (Finset.sum_nbij (runPos M w) ?_ ?_ ?_ ?_).symm
  · intro t ht
    rw [Finset.mem_range] at ht
    obtain ⟨hc, hle⟩ := cfgAt_take_drop hT ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ⟨t, hc⟩⟩
    exact Finset.mem_range.mpr (by omega)
  · intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at ht₁ ht₂
    obtain ⟨hc₁, -⟩ := cfgAt_take_drop hT ht₁
    obtain ⟨hc₂, -⟩ := cfgAt_take_drop hT ht₂
    rw [heq] at hc₁
    exact run_inj M w hT hc₁ hc₂
  · intro x hx
    simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq] at hx
    obtain ⟨hxmem, hvis⟩ := hx
    have hxle : x.1 ≤ w.length := by
      have := Finset.mem_product.mp hxmem
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this.1)
    obtain ⟨t, ht⟩ := hvis
    have hne : Cfg.conf (w.take x.1) x.2 (w.drop x.1) ≠ Cfg.halt := by simp
    have htT : t < T := by
      have hle := time_le_halt hT (by rw [ht]; simp)
      rcases Nat.lt_or_ge t T with hlt | hge
      · exact hlt
      · exfalso
        have : t = T := by omega
        subst this
        rw [hT] at ht
        exact hne (Option.some.inj ht).symm
    refine ⟨t, by simpa using htT, ?_⟩
    rw [runPos_of_conf ht]
    have : (w.take x.1).length = x.1 := by rw [List.length_take]; omega
    rw [this]
  · intro t ht
    rw [Finset.mem_range] at ht
    exact (vertexOut_runPos hT ht).symm

end Fintype3

/-! ## The count of the encoded configuration graph is the output length -/

section Main

variable [Fintype Q]

/-- On the empty input the special letter of the alphabet `C` records the output. -/
lemma countList_enc_nil {M : TwoWay A B Q} {v : List B} (h : M.Computes [] v) :
    countList M (enc M ([] : List A)) = v.length := by
  rw [enc_nil, countList, countList]
  cases h with
  | @step c c' c'' o o' hstep hrest =>
      rcases hs : M.step (none : Option A) M.init none with o₁ | ⟨q', o₁, dir⟩
      · have hstep' : M.stepCfg (Cfg.conf ([] : List A) M.init []) = some (o₁, Cfg.halt) := by
          rw [TwoWay.stepCfg]; simp only [List.getLast?_nil, List.head?_nil, hs]
        rw [hstep'] at hstep
        obtain ⟨ho, hc⟩ := Prod.mk.injEq .. ▸ Option.some.inj hstep
        subst hc
        obtain ⟨rfl, -⟩ := TwoWay.reaches_halt hrest
        simp only [emptyOut, hs, Option.elim, sliceCount, labOf_val, transOut_halt hs,
          Nat.add_zero, ← ho, List.append_nil]
      · exfalso
        have hstuck : M.stepCfg (Cfg.conf ([] : List A) M.init []) = none := by
          rw [TwoWay.stepCfg]
          simp only [List.getLast?_nil, List.head?_nil, hs]
          cases dir <;> rfl
        rw [hstuck] at hstep
        exact absurd hstep (by simp)

lemma countList_enc_eq_length {M : TwoWay A B Q} {w : List A} {v : List B}
    (h : M.Computes w v) : countList M (enc M w) = v.length := by
  classical
  by_cases hne : w = []
  · subst hne; exact countList_enc_nil h
  · obtain ⟨T, hT, -⟩ := exists_halt_time M w h
    rw [countList_enc_of_ne_nil hne, sum_sliceCount_eq_sum_vertexOut hT hne,
      sum_vertexOut_eq_length h]

end Main

/-! ## The exercise -/

/-- Two strings over a subsingleton alphabet with the same length are equal. -/
lemma List.eq_of_length_eq_of_subsingleton {Γ : Type} [Subsingleton Γ] :
    ∀ (u v : List Γ), u.length = v.length → u = v := by
  intro u
  induction u with
  | nil => intro v hv; exact (List.length_eq_zero_iff.mp hv.symm).symm
  | cons a u ih =>
      intro v hv
      cases v with
      | nil => simp at hv
      | cons b v =>
          rw [Subsingleton.elim a b, ih v (by simpa using hv)]

/-- The hard half of Exercise `exer:2dfa-unary-output`: over a subsingleton output alphabet, a
function computed by a two-way transducer is rational. -/
theorem isRationalFun_of_isTwoWay_subsingleton {A B : Type} [Finite A] [Finite B] [Subsingleton B]
    {f : List A → List B} (hf : IsTwoWay f) : IsRationalFun f := by
  classical
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI := hQ
  haveI : Fintype Q := Fintype.ofFinite Q
  rcases isEmpty_or_nonempty B with hB | hBne
  · have hnil : f = fun _ : List A => ([] : List B) := by
      funext w
      rcases hfw : f w with _ | ⟨x, xs⟩
      · rfl
      · exact (hB.false x).elim
    rw [hnil]
    exact isRationalFun_const []
  · obtain ⟨b⟩ := hBne
    have hrat : IsRationalFun (unaryOut M b) := isRationalFun_biEval _ _ _ _ _
    have hcomp : IsRationalFun (fun w => unaryOut M b (enc M w)) :=
      isRationalFun_comp (isRationalFun_enc M) hrat
    have heq : f = fun w => unaryOut M b (enc M w) := by
      funext w
      refine List.eq_of_length_eq_of_subsingleton _ _ ?_
      rw [unaryOut_length, countList_enc_eq_length (hM w)]
    rw [heq]
    exact hcomp

/-- **Exercise `exer:2dfa-unary-output`.**  If the output alphabet has one letter, then the regular
functions are exactly the rational functions.

The hypothesis on the output alphabet is that it is a subsingleton, which is what the proof uses
and which a one-letter alphabet satisfies. -/
theorem isRegularFun_iff_isRationalFun_of_unary_output {A B : Type} [Finite A] [Finite B]
    [Subsingleton B] (f : List A → List B) : IsRegularFun f ↔ IsRationalFun f := by
  constructor
  · intro hf
    exact isRationalFun_of_isTwoWay_subsingleton (regularFun_isTwoWay hf)
  · intro hf
    exact IsRegularFun.of_rational hf

end Exercises
end Transducers
