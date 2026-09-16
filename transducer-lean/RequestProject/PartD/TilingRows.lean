/-
Part D, Section *A functional programming language*: from a row of the grid to a rewriting.

This file proves the combinatorial heart of the reduction of Lemma `lem:tiling`: a row of cells
whose rôles fit together (`Transducers.TilingRed.horizB`) describes a sequence of rewritings of the
machine, so that the letters of the row below are reached from the letters of the row itself.

The proof reads the row from left to right.  A cell of rôle `0` carries its letter over unchanged;
a cell of rôle `1` is followed by one of rôle `2`, and the two of them apply a rule `q a ⟶ b r` of
the machine; a cell of rôle `3` is followed by ones of rôles `4` and `5`, and the three of them
apply a rule `c q a ⟶ r c b`.  The rôle of the first cell of the row is one that begins a
rewriting and that of the last one is one that ends a rewriting, so no rewriting is left
unfinished.
-/
import RequestProject.PartD.TilingCells
import RequestProject.PartD.TilingSRS

namespace Transducers
namespace TilingRed

open PCP

variable {M : TM} {w : List ℕ} {x y z : Cell}

/-! ## Reading the conditions on a cell -/

lemma validB_tape (h : validB M w x = true) (hk : x.k = 0) : x.v ∈ M.tapeSyms w := by
  simp only [validB, hk, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role0 (h : validB M w x = true) (hr : x.role = 0) : x.nk = x.k ∧ x.nv = x.v := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role1 (h : validB M w x = true) (hr : x.role = 1) : x.k = 1 ∧ x.nk = 0 := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role2 (h : validB M w x = true) (hr : x.role = 2) : x.k = 0 ∧ x.nk = 1 := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role3 (h : validB M w x = true) (hr : x.role = 3) : x.k = 0 ∧ x.nk = 1 := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role4 (h : validB M w x = true) (hr : x.role = 4) : x.k = 1 ∧ x.nk = 0 := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role5 (h : validB M w x = true) (hr : x.role = 5) : x.k = 0 ∧ x.nk = 0 := by
  simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto

/-! ## Reading the conditions on two horizontally adjacent cells -/

lemma horizB_role0 (h : horizB M w x y = true) (hr : x.role = 0) :
    y.role = 0 ∨ y.role = 1 ∨ y.role = 3 := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_role1 (h : horizB M w x y = true) (hr : x.role = 1) :
    y.role = 2 ∧ (x.v, y.v, y.nv, x.nv, true) ∈ M.trans := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_role2 (h : horizB M w x y = true) (hr : x.role = 2) : y.role = 0 := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_role3 (h : horizB M w x y = true) (hr : x.role = 3) :
    y.role = 4 ∧ x.nv = y.aux ∧ y.nv = x.v := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_role4 (h : horizB M w x y = true) (hr : x.role = 4) :
    y.role = 5 ∧ (x.v, y.v, x.aux, y.nv, false) ∈ M.trans := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_role5 (h : horizB M w x y = true) (hr : x.role = 5) : y.role = 0 := by
  simp only [horizB, hr, Bool.and_eq_true] at h; simp at h; tauto

/-! ## The rules of the machine -/

lemma mem_rightRules_of_trans {q a r b : ℕ} (h : (q, a, r, b, true) ∈ M.trans) :
    ([Sym.state q, Sym.tape a], [Sym.tape b, Sym.state r]) ∈ M.rightRules := by
  simp only [TM.rightRules, List.mem_filterMap]
  exact ⟨(q, a, r, b, true), h, by simp⟩

lemma mem_leftRules_of_trans {q a r b c : ℕ} (h : (q, a, r, b, false) ∈ M.trans)
    (hc : c ∈ M.tapeSyms w) :
    ([Sym.tape c, Sym.state q, Sym.tape a], [Sym.state r, Sym.tape c, Sym.tape b]) ∈
      M.leftRules w := by
  simp only [TM.leftRules, List.mem_flatMap, List.mem_filterMap]
  exact ⟨c, hc, (q, a, r, b, false), h, by simp⟩

lemma mem_transRules_right {q a r b : ℕ} (h : (q, a, r, b, true) ∈ M.trans) :
    ([Sym.state q, Sym.tape a], [Sym.tape b, Sym.state r]) ∈ M.transRules w :=
  List.mem_append_left _ (mem_rightRules_of_trans h)

lemma mem_transRules_left {q a r b c : ℕ} (h : (q, a, r, b, false) ∈ M.trans)
    (hc : c ∈ M.tapeSyms w) :
    ([Sym.tape c, Sym.state q, Sym.tape a], [Sym.state r, Sym.tape c, Sym.tape b]) ∈
      M.transRules w :=
  List.mem_append_right _ (mem_leftRules_of_trans h hc)

/-! ## A row of the grid describes a rewriting -/

private lemma getLast?_cons_ne {α : Type*} (a : α) {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t => simp [List.getLast?_cons_cons]

/-- **A row of the grid describes a sequence of rewritings.**  If the cells of a row are cells of
the machine, if consecutive cells satisfy the horizontal conditions, and if the rôle of the first
cell begins a rewriting and that of the last cell ends one, then the letters of the row below are
obtained from the letters of the row by rewriting rules of the machine. -/
lemma reachesR_of_row (u : List Cell)
    (hv : ∀ x ∈ u, validB M w x = true)
    (hch : List.IsChain (fun x y => horizB M w x y = true) u)
    (hhead : ∀ x ∈ u.head?, x.role = 0 ∨ x.role = 1 ∨ x.role = 3)
    (hlast : ∀ x ∈ u.getLast?, x.role = 0 ∨ x.role = 2 ∨ x.role = 5) :
    ReachesR (M.transRules w) (u.map Cell.sym) (u.map Cell.nsym) := by
  induction hn : u.length using Nat.strong_induction_on generalizing u with
  | _ N ih =>
  subst hn
  match u with
  | [] => simpa using ReachesR.refl (M.transRules w) []
  | x :: t =>
    have hx : validB M w x = true := hv x List.mem_cons_self
    have hxrole : x.role = 0 ∨ x.role = 1 ∨ x.role = 3 := hhead x (by simp)
    rcases hxrole with hr | hr | hr
    · -- the letter is carried over unchanged
      obtain ⟨hk, hvv⟩ := validB_role0 hx hr
      have hs : x.nsym = x.sym := by simp [Cell.sym, Cell.nsym, hk, hvv]
      have hrest : ReachesR (M.transRules w) (t.map Cell.sym) (t.map Cell.nsym) := by
        refine ih t.length (by simp) t (fun y hy => hv y (List.mem_cons_of_mem _ hy))
          (List.IsChain.tail hch) ?_ ?_ rfl
        · intro y hy
          have hxy : horizB M w x y = true := by
            cases t with
            | nil => simp at hy
            | cons b t' =>
                have : y = b := by simpa using hy.symm
                subst this
                exact (List.isChain_cons_cons.mp hch).1
          exact horizB_role0 hxy hr
        · intro y hy
          refine hlast y ?_
          have ht : t ≠ [] := by
            rintro rfl; simp at hy
          rw [getLast?_cons_ne x ht]; exact hy
      simpa [hs] using hrest.append_left [x.sym]
    · -- a rewriting `q a ⟶ b r`
      match t with
      | [] =>
          exact absurd (hlast x (by simp)) (by simp [hr])
      | y :: t' =>
        have hy : validB M w y = true := hv y (by simp)
        have hxy : horizB M w x y = true := (List.isChain_cons_cons.mp hch).1
        obtain ⟨hyr, hrule⟩ := horizB_role1 hxy hr
        obtain ⟨hxk, hxnk⟩ := validB_role1 hx hr
        obtain ⟨hyk, hynk⟩ := validB_role2 hy hyr
        have hstep : StepRule (M.transRules w)
            (x.sym :: y.sym :: t'.map Cell.sym) (x.nsym :: y.nsym :: t'.map Cell.sym) := by
          have h0 := StepRule.mk (rules := M.transRules w) []
            [Sym.state x.v, Sym.tape y.v] [Sym.tape x.nv, Sym.state y.nv]
            (t'.map Cell.sym) (mem_transRules_right hrule)
          simpa [Cell.sym, Cell.nsym, hxk, hxnk, hyk, hynk] using h0
        have hrest : ReachesR (M.transRules w) (t'.map Cell.sym) (t'.map Cell.nsym) := by
          refine ih t'.length (by simp only [List.length_cons]; omega) t'
            (fun a ha => hv a (by simp [ha])) (List.IsChain.tail (List.IsChain.tail hch)) ?_ ?_ rfl
          · intro a ha
            have hya : horizB M w y a = true := by
              cases t' with
              | nil => simp at ha
              | cons b t'' =>
                  have : a = b := by simpa using ha.symm
                  subst this
                  exact (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hch).2).1
            exact Or.inl (horizB_role2 hya hyr)
          · intro a ha
            refine hlast a ?_
            have ht : t' ≠ [] := by rintro rfl; simp at ha
            rw [getLast?_cons_ne x (by simp), getLast?_cons_ne y ht]; exact ha
        refine (ReachesR.single hstep).trans ?_
        have := hrest.append_left [x.nsym, y.nsym]
        simpa using this
    · -- a rewriting `c q a ⟶ r c b`
      match t with
      | [] => exact absurd (hlast x (by simp)) (by simp [hr])
      | [y] =>
          have hxy : horizB M w x y = true := (List.isChain_cons_cons.mp hch).1
          obtain ⟨hyr, -, -⟩ := horizB_role3 hxy hr
          exact absurd (hlast y (by simp)) (by simp [hyr])
      | y :: z :: t' =>
        have hy : validB M w y = true := hv y (by simp)
        have hz : validB M w z = true := hv z (by simp)
        have hxy : horizB M w x y = true := (List.isChain_cons_cons.mp hch).1
        have hyz : horizB M w y z = true := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hch).2).1
        obtain ⟨hyr, haux, hyv⟩ := horizB_role3 hxy hr
        obtain ⟨hzr, hrule⟩ := horizB_role4 hyz hyr
        obtain ⟨hxk, hxnk⟩ := validB_role3 hx hr
        obtain ⟨hyk, hynk⟩ := validB_role4 hy hyr
        obtain ⟨hzk, hznk⟩ := validB_role5 hz hzr
        have hc : x.v ∈ M.tapeSyms w := validB_tape hx hxk
        have hstep : StepRule (M.transRules w)
            (x.sym :: y.sym :: z.sym :: t'.map Cell.sym)
            (x.nsym :: y.nsym :: z.nsym :: t'.map Cell.sym) := by
          have h0 := StepRule.mk (rules := M.transRules w) []
            [Sym.tape x.v, Sym.state y.v, Sym.tape z.v]
            [Sym.state y.aux, Sym.tape x.v, Sym.tape z.nv]
            (t'.map Cell.sym) (mem_transRules_left hrule hc)
          simpa [Cell.sym, Cell.nsym, hxk, hxnk, hyk, hynk, hzk, hznk, haux, hyv] using h0
        have hrest : ReachesR (M.transRules w) (t'.map Cell.sym) (t'.map Cell.nsym) := by
          refine ih t'.length (by simp only [List.length_cons]; omega) t'
            (fun a ha => hv a (by simp [ha])) (List.IsChain.tail (List.IsChain.tail
              (List.IsChain.tail hch))) ?_ ?_ rfl
          · intro a ha
            have hza : horizB M w z a = true := by
              cases t' with
              | nil => simp at ha
              | cons b t'' =>
                  have : a = b := by simpa using ha.symm
                  subst this
                  exact (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp
                    (List.isChain_cons_cons.mp hch).2).2).1
            exact Or.inl (horizB_role5 hza hzr)
          · intro a ha
            refine hlast a ?_
            have ht : t' ≠ [] := by rintro rfl; simp at ha
            rw [getLast?_cons_ne x (by simp), getLast?_cons_ne y (by simp),
              getLast?_cons_ne z ht]
            exact ha
        refine (ReachesR.single hstep).trans ?_
        have := hrest.append_left [x.nsym, y.nsym, z.nsym]
        simpa using this

/-! ## Further readings of the conditions -/

lemma validB_lb_role (h : validB M w x = true) (hlb : x.lb = true) :
    x.role = 0 ∨ x.role = 1 ∨ x.role = 3 := by
  simp only [validB, hlb, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_rb_role (h : validB M w x = true) (hrb : x.rb = true) :
    x.role = 0 ∨ x.role = 2 ∨ x.role = 5 := by
  simp only [validB, hrb, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_lb_acc (h : validB M w x = true) (hlb : x.lb = true) :
    x.acc = (decide (x.k = 1) && decide (x.v = M.qacc)) := by
  simp only [validB, hlb, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_cnt (h : validB M w x = true) (ht : x.top = true) : x.cnt ≤ w.length + 1 := by
  simp only [validB, ht, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_role (h : validB M w x = true) (ht : x.top = true) : x.role = 0 := by
  simp only [validB, ht, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_notfin (h : validB M w x = true) (ht : x.top = true) : x.fin = false := by
  simp only [validB, ht, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_rb (h : validB M w x = true) (ht : x.top = true) (hrb : x.rb = true) :
    x.cnt = w.length + 1 := by
  simp only [validB, ht, hrb, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_zero (h : validB M w x = true) (ht : x.top = true) (h0 : x.cnt = 0) :
    x.k = 1 ∧ x.v = M.q0 := by
  simp only [validB, ht, h0, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_top_succ (h : validB M w x = true) (ht : x.top = true) (h0 : x.cnt ≠ 0) :
    x.k = 0 ∧ x.v = w.getD (x.cnt - 1) 0 := by
  simp only [validB, ht, h0, Bool.and_eq_true] at h; simp [h0] at h; tauto

lemma horizB_lb (h : horizB M w x y = true) : y.lb = false := by
  simp only [horizB, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_rb (h : horizB M w x y = true) : x.rb = false := by
  simp only [horizB, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_top (h : horizB M w x y = true) : x.top = y.top := by
  simp only [horizB, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_fin (h : horizB M w x y = true) : x.fin = y.fin := by
  simp only [horizB, Bool.and_eq_true] at h; simp at h; tauto

lemma horizB_cnt (h : horizB M w x y = true) (ht : x.top = true) :
    y.cnt = min x.cnt w.length + 1 := by
  simp only [horizB, ht, Bool.and_eq_true] at h; simp [ht] at h; tauto

lemma horizB_acc (h : horizB M w x y = true) :
    y.acc = (x.acc || decide (y.k = 1) && decide (y.v = M.qacc)) := by
  simp only [horizB, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_notfin (h : vertB x y = true) : x.fin = false := by
  simp only [vertB, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_lb (h : vertB x y = true) : x.lb = y.lb := by
  simp only [vertB, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_rb (h : vertB x y = true) : x.rb = y.rb := by
  simp only [vertB, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_nottop (h : vertB x y = true) : y.top = false := by
  simp only [vertB, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_content (h : vertB x y = true) (hy : y.fin = false) : y.k = x.nk ∧ y.v = x.nv := by
  simp only [vertB, hy, Bool.and_eq_true] at h; simp at h; tauto

lemma vertB_acc (h : vertB x y = true) (hy : y.fin = true) (hrb : y.rb = true) :
    x.acc = true := by
  simp only [vertB, hy, hrb, Bool.and_eq_true] at h; simp at h; tauto

lemma windowB_valid₁ {a b c d : Cell} (h : windowB M w a b c d = true) : validB M w a = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_valid₂ {a b c d : Cell} (h : windowB M w a b c d = true) : validB M w b = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_valid₃ {a b c d : Cell} (h : windowB M w a b c d = true) : validB M w c = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_valid₄ {a b c d : Cell} (h : windowB M w a b c d = true) : validB M w d = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_horiz₁ {a b c d : Cell} (h : windowB M w a b c d = true) :
    horizB M w a b = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_horiz₂ {a b c d : Cell} (h : windowB M w a b c d = true) :
    horizB M w c d = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_vert₁ {a b c d : Cell} (h : windowB M w a b c d = true) : vertB a c = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

lemma windowB_vert₂ {a b c d : Cell} (h : windowB M w a b c d = true) : vertB b d = true := by
  simp only [windowB, Bool.and_eq_true] at h; tauto

end TilingRed
end Transducers
