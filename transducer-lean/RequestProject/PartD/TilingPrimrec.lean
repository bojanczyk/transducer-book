/-
Part D, Section *A functional programming language*: the instance of the tiling problem built from
a machine and an input word is a primitive recursive function of the two.

`RequestProject/PartD/TilingComputable.lean` proves that the fields of a cell are primitive
recursive functions of the cell.  This file continues from there: the conditions on a cell, on two
adjacent cells and on a `2 × 2` window, the enumeration of the cells, and finally the instance
`Transducers.TilingRed.inst` itself.  The effectiveness of the reduction is what lets a decision
procedure for the tiling problem be turned into one for the acceptance problem, which is how Lemma
`lem:tiling` is proved in `RequestProject/PartD/TilingUndec.lean`.
-/
import RequestProject.PartD.TilingComputable
import RequestProject.PCP.Computable

namespace Transducers
namespace TilingRed

open PCP

/-! ## More Boolean combinators -/

namespace PrimAux

variable {α : Type} [Primcodable α]

/-- Deciding a conjunction. -/
theorem decAnd {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Primrec fun a => decide (p a)) (hq : Primrec fun a => decide (q a)) :
    Primrec fun a => decide (p a ∧ q a) :=
  (band hp hq).of_eq fun a => by simp

/-- Deciding a disjunction. -/
theorem decOr {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Primrec fun a => decide (p a)) (hq : Primrec fun a => decide (q a)) :
    Primrec fun a => decide (p a ∨ q a) :=
  (bor hp hq).of_eq fun a => by simp

/-- Deciding membership in a list, over any type with a decidable equality. -/
theorem decMemG {β : Type} [Primcodable β] [DecidableEq β] {f : α → β} {g : α → List β}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a ∈ g a) := by
  obtain ⟨_, h⟩ : PrimrecPred fun a => f a ∈ g a := Primrec.list_mem.comp hf hg
  exact h.of_eq fun a => by simp

/-- Deciding an equality, over any type with a decidable equality. -/
theorem decEqG {β : Type} [Primcodable β] [DecidableEq β] {f g : α → β}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a = g a) := by
  obtain ⟨_, h⟩ : PrimrecPred fun a => f a = g a := Primrec.eq.comp hf hg
  exact h.of_eq fun a => by simp

/-- The Boolean equality test. -/
theorem beqB {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) :=
  (Primrec.dom_bool₂ (fun x y => x == y)).comp hf hg

/-- The equality test on natural numbers. -/
theorem beqNat {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) :=
  (decEq hf hg).of_eq fun a => Bool.eq_iff_iff.2 (by simp)

/-- A Boolean, read as a decidable proposition. -/
theorem decBool {f : α → Bool} (hf : Primrec f) : Primrec fun a => decide (f a = true) :=
  hf.of_eq fun a => by simp

/-- A conditional with Boolean branches. -/
theorem ifb {c : α → Prop} [DecidablePred c] {f g : α → Bool}
    (hc : Primrec fun a => decide (c a)) (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => if c a then f a else g a :=
  (Primrec.cond hc hf hg).of_eq fun a => by by_cases h : c a <;> simp [h]

end PrimAux

/-! ## The conditions on cells -/


section Validity

private abbrev ArgC := _root_.PCP.Arg × Cell

private theorem harg : Primrec fun q : ArgC => q.1 := Primrec.fst
private theorem hcell : Primrec fun q : ArgC => q.2 := Primrec.snd

set_option maxHeartbeats 1000000 in
/-- **The conditions on a single cell are primitive recursive.** -/
theorem primrec_validB : Primrec fun q : ArgC => validB q.1.1 q.1.2 q.2 := by
  have hk := primrec_k.comp hcell
  have hv := primrec_v.comp hcell
  have hnk := primrec_nk.comp hcell
  have hnv := primrec_nv.comp hcell
  have hrole := primrec_role.comp hcell
  have haux := primrec_aux.comp hcell
  have hcnt := primrec_cnt.comp hcell
  have hlb := primrec_lb.comp hcell
  have hrb := primrec_rb.comp hcell
  have htop := primrec_top.comp hcell
  have hfin := primrec_fin.comp hcell
  have hacc := primrec_acc.comp hcell
  have hw : Primrec fun q : ArgC => q.1.2 := Primrec.snd.comp harg
  have htape : Primrec fun q : ArgC => q.1.1.tapeSyms q.1.2 := _root_.PCP.primrec_tapeSyms.comp harg
  have hstates : Primrec fun q : ArgC => q.1.1.states := _root_.PCP.primrec_states.comp harg
  have hq0 : Primrec fun q : ArgC => q.1.1.q0 := _root_.PCP.primrec_q0.comp (Primrec.fst.comp harg)
  have hqacc : Primrec fun q : ArgC => q.1.1.qacc := _root_.PCP.primrec_qacc.comp (Primrec.fst.comp harg)
  have hlen : Primrec fun q : ArgC => q.1.2.length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hw)
  have c1 := PrimAux.decLe hk (Primrec.const 1)
  have c2 := PrimAux.decLe hnk (Primrec.const 1)
  have c3 := PrimAux.decLe hrole (Primrec.const 5)
  have c4 := PrimAux.ifb (PrimAux.decEq hk (Primrec.const 0)) (PrimAux.decMemG hv htape) (PrimAux.decMemG hv hstates)
  have c5 := PrimAux.ifb (PrimAux.decEq hnk (Primrec.const 0)) (PrimAux.decMemG hnv htape) (PrimAux.decMemG hnv hstates)
  have c6 := PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 4)) (PrimAux.decMemG haux hstates)
    (PrimAux.decEq haux (Primrec.const 0))
  have c7 := PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 0)) (PrimAux.decAnd (PrimAux.decEq hnk hk) (PrimAux.decEq hnv hv))
    (PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 1))
      (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 1)) (PrimAux.decEq hnk (Primrec.const 0)))
      (PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 2))
        (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 0)) (PrimAux.decEq hnk (Primrec.const 1)))
        (PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 3))
          (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 0)) (PrimAux.decEq hnk (Primrec.const 1)))
          (PrimAux.ifb (PrimAux.decEq hrole (Primrec.const 4))
            (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 1)) (PrimAux.decEq hnk (Primrec.const 0)))
            (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 0)) (PrimAux.decEq hnk (Primrec.const 0)))))))
  have c8 := PrimAux.bor (PrimAux.bnot hlb) (PrimAux.decOr (PrimAux.decEq hrole (Primrec.const 0))
    (PrimAux.decOr (PrimAux.decEq hrole (Primrec.const 1)) (PrimAux.decEq hrole (Primrec.const 3))))
  have c9 := PrimAux.bor (PrimAux.bnot hrb) (PrimAux.decOr (PrimAux.decEq hrole (Primrec.const 0))
    (PrimAux.decOr (PrimAux.decEq hrole (Primrec.const 2)) (PrimAux.decEq hrole (Primrec.const 5))))
  have c10 := PrimAux.bor (PrimAux.bnot hlb)
    (PrimAux.beqB hacc (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 1)) (PrimAux.decEq hv hqacc)))
  have c11 := PrimAux.ifb (PrimAux.decBool htop)
    (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.decLe hcnt hlen) (PrimAux.decEq hrole (Primrec.const 0)))
      (PrimAux.ifb (PrimAux.decEq hcnt (Primrec.const 0))
        (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 1)) (PrimAux.decEq hv hq0))
        (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 0))
          (PrimAux.decEq hv ((Primrec.list_getD 0).comp hw
            (Primrec.nat_sub.comp hcnt (Primrec.const 1)))))))
      (PrimAux.bor (PrimAux.bnot hrb) (PrimAux.decEq hcnt hlen))) (PrimAux.bnot hfin))
    (PrimAux.decEq hcnt (Primrec.const 0))
  have c12 := PrimAux.bor (PrimAux.bnot hfin)
    (PrimAux.band (PrimAux.decAnd (PrimAux.decEq hk (Primrec.const 0))
      (PrimAux.decAnd (PrimAux.decEq hv (Primrec.const 0))
        (PrimAux.decAnd (PrimAux.decEq hnk (Primrec.const 0))
          (PrimAux.decAnd (PrimAux.decEq hnv (Primrec.const 0))
            (PrimAux.decAnd (PrimAux.decEq hrole (Primrec.const 0)) (PrimAux.decEq haux (Primrec.const 0)))))))
      (PrimAux.bnot hacc))
  exact PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band c1 c2) c3) c4) c5) c6)
    c7) c8) c9) c10) c11) c12

/-- Deciding membership in a list, for whatever decidability instance the goal carries: the
membership tests of `Transducers.TilingRed.horizB` are at a product type, where the instance
Lean synthesises is not the one that comes from the decidable equality. -/
private theorem decMemI {α β : Type} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f : α → β} {g : α → List β} {inst : ∀ a, Decidable (f a ∈ g a)}
    (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => @decide (f a ∈ g a) (inst a) := by
  obtain ⟨_, h⟩ : PrimrecPred fun a => f a ∈ g a := Primrec.list_mem.comp hf hg
  exact h.of_eq fun a => by simp

set_option maxHeartbeats 1000000 in
/-- **The conditions on two horizontally adjacent cells are primitive recursive.** -/
theorem primrec_horizB :
    Primrec fun q : _root_.PCP.Arg × Cell × Cell => horizB q.1.1 q.1.2 q.2.1 q.2.2 := by
  have harg : Primrec fun q : _root_.PCP.Arg × Cell × Cell => q.1 := Primrec.fst
  have hx : Primrec fun q : _root_.PCP.Arg × Cell × Cell => q.2.1 := Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : _root_.PCP.Arg × Cell × Cell => q.2.2 := Primrec.snd.comp Primrec.snd
  have hw : Primrec fun q : _root_.PCP.Arg × Cell × Cell => q.1.2 := Primrec.snd.comp harg
  have hqacc := _root_.PCP.primrec_qacc.comp (Primrec.fst.comp harg)
  have htrans := _root_.PCP.primrec_trans.comp (Primrec.fst.comp harg)
  have hxv := primrec_v.comp hx
  have hxnv := primrec_nv.comp hx
  have hxaux := primrec_aux.comp hx
  have hxcnt := primrec_cnt.comp hx
  have hxrb := primrec_rb.comp hx
  have hxtop := primrec_top.comp hx
  have hxfin := primrec_fin.comp hx
  have hxacc := primrec_acc.comp hx
  have hxrole := primrec_role.comp hx
  have hyk := primrec_k.comp hy
  have hyv := primrec_v.comp hy
  have hynv := primrec_nv.comp hy
  have hyaux := primrec_aux.comp hy
  have hycnt := primrec_cnt.comp hy
  have hylb := primrec_lb.comp hy
  have hytop := primrec_top.comp hy
  have hyfin := primrec_fin.comp hy
  have hyacc := primrec_acc.comp hy
  have hyrole := primrec_role.comp hy
  have hlen : Primrec fun q : _root_.PCP.Arg × Cell × Cell => q.1.2.length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hw)
  have hmin : Primrec fun q : _root_.PCP.Arg × Cell × Cell =>
      min (q.2.1.cnt + 1) (q.1.2.length + 1) :=
    Primrec.nat_min.comp (Primrec.succ.comp hxcnt) hlen
  have hrule1 : Primrec fun q : _root_.PCP.Arg × Cell × Cell =>
      ((q.2.1.v, q.2.2.v, q.2.2.nv, q.2.1.nv, true) : ℕ × ℕ × ℕ × ℕ × Bool) :=
    Primrec.pair hxv (Primrec.pair hyv (Primrec.pair hynv (Primrec.pair hxnv
      (Primrec.const true))))
  have hrule2 : Primrec fun q : _root_.PCP.Arg × Cell × Cell =>
      ((q.2.1.v, q.2.2.v, q.2.1.aux, q.2.2.nv, false) : ℕ × ℕ × ℕ × ℕ × Bool) :=
    Primrec.pair hxv (Primrec.pair hyv (Primrec.pair hxaux (Primrec.pair hynv
      (Primrec.const false))))
  have c1 := PrimAux.bnot hylb
  have c2 := PrimAux.bnot hxrb
  have c3 := PrimAux.beqB hxtop hytop
  have c4 := PrimAux.beqB hxfin hyfin
  have c5 := PrimAux.bor (PrimAux.bnot hxtop) (PrimAux.decEq hycnt hmin)
  have c6 := PrimAux.beqB hyacc (PrimAux.bor hxacc (PrimAux.decAnd (PrimAux.decEq hyk (Primrec.const 1)) (PrimAux.decEq hyv hqacc)))
  exact PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band c1 c2) c3) c4) c5) c6)
    (PrimAux.ifb (PrimAux.decEq hxrole (Primrec.const 0))
      (PrimAux.decOr (PrimAux.decEq hyrole (Primrec.const 0))
        (PrimAux.decOr (PrimAux.decEq hyrole (Primrec.const 1)) (PrimAux.decEq hyrole (Primrec.const 3))))
      (PrimAux.ifb (PrimAux.decEq hxrole (Primrec.const 1))
        (PrimAux.band (PrimAux.decEq hyrole (Primrec.const 2)) (decMemI hrule1 htrans))
        (PrimAux.ifb (PrimAux.decEq hxrole (Primrec.const 2)) (PrimAux.decEq hyrole (Primrec.const 0))
          (PrimAux.ifb (PrimAux.decEq hxrole (Primrec.const 3))
            (PrimAux.band (PrimAux.decEq hyrole (Primrec.const 4)) (PrimAux.decAnd (PrimAux.decEq hxnv hyaux) (PrimAux.decEq hynv hxv)))
            (PrimAux.ifb (PrimAux.decEq hxrole (Primrec.const 4))
              (PrimAux.band (PrimAux.decEq hyrole (Primrec.const 5)) (decMemI hrule2 htrans))
              (PrimAux.decEq hyrole (Primrec.const 0)))))))

/-- **The conditions on two vertically adjacent cells are primitive recursive.** -/
theorem primrec_vertB : Primrec fun q : Cell × Cell => vertB q.1 q.2 := by
  have hx : Primrec fun q : Cell × Cell => q.1 := Primrec.fst
  have hy : Primrec fun q : Cell × Cell => q.2 := Primrec.snd
  have c1 := PrimAux.bnot (primrec_fin.comp hx)
  have c2 := PrimAux.beqB (primrec_lb.comp hx) (primrec_lb.comp hy)
  have c3 := PrimAux.beqB (primrec_rb.comp hx) (primrec_rb.comp hy)
  have c4 := PrimAux.bnot (primrec_top.comp hy)
  have c5 := PrimAux.decEq (primrec_cnt.comp hy) (Primrec.const 0)
  have c6 := PrimAux.ifb (PrimAux.decBool (primrec_fin.comp hy))
    (PrimAux.bor (PrimAux.bnot (primrec_rb.comp hy)) (primrec_acc.comp hx))
    (PrimAux.decAnd (PrimAux.decEq (primrec_k.comp hy) (primrec_nk.comp hx))
      (PrimAux.decEq (primrec_v.comp hy) (primrec_nv.comp hx)))
  exact PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band c1 c2) c3) c4) c5) c6

set_option maxHeartbeats 1000000 in
/-- **The conditions on a `2 × 2` window are primitive recursive.** -/
theorem primrec_windowB :
    Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell =>
      windowB q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have harg : Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell => q.1 := Primrec.fst
  have ha : Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hb : Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec fun q : _root_.PCP.Arg × Cell × Cell × Cell × Cell => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have va := primrec_validB.comp (Primrec.pair harg ha)
  have vb := primrec_validB.comp (Primrec.pair harg hb)
  have vc := primrec_validB.comp (Primrec.pair harg hc)
  have vd := primrec_validB.comp (Primrec.pair harg hd)
  have hab := primrec_horizB.comp (Primrec.pair harg (Primrec.pair ha hb))
  have hcd := primrec_horizB.comp (Primrec.pair harg (Primrec.pair hc hd))
  have vac := primrec_vertB.comp (Primrec.pair ha hc)
  have vbd := primrec_vertB.comp (Primrec.pair hb hd)
  exact PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band (PrimAux.band va vb) vc) vd) hab) hcd) vac) vbd

end Validity

/-! ## The enumeration of the cells -/

private lemma tupleList_eq_foldr (ls : List (List ℕ)) :
    tupleList ls = ls.foldr (fun l acc => l.flatMap fun a => acc.map fun t => a :: t) [[]] := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [tupleList, ih, List.foldr_cons]

/-- Enumerating the tuples with prescribed entries is primitive recursive. -/
theorem primrec_tupleList : Primrec tupleList := by
  have h : Primrec fun ls : List (List ℕ) =>
      ls.foldr (fun l acc => l.flatMap fun a => acc.map fun t => a :: t) [[]] := by
    refine Primrec.list_foldr (h := fun (_ : List (List ℕ)) (x : List ℕ × List (List ℕ)) =>
        x.1.flatMap fun a => x.2.map fun t => a :: t)
      (Primrec.id (α := List (List ℕ))) (Primrec.const ([[]] : List (List ℕ)))
      (Primrec₂.mk ?_)
    refine Primrec.list_flatMap (Primrec.fst.comp Primrec.snd) (Primrec₂.mk ?_)
    exact Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec₂.mk (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact h.of_eq fun ls => (tupleList_eq_foldr ls).symm

/-- Reading a cell off a list of twelve natural numbers is primitive recursive. -/
theorem primrec_cellOfList : Primrec cellOfList := by
  have hid : Primrec fun t : List ℕ => t := Primrec.id
  have hg : ∀ i : ℕ, Primrec fun t : List ℕ => t.getD i 0 := fun i =>
    (Primrec.list_getD (0 : ℕ)).comp hid (Primrec.const i)
  have hb : ∀ i : ℕ, Primrec fun t : List ℕ => (t.getD i 0 == 1) := fun i =>
    PrimAux.beqNat (hg i) (Primrec.const 1)
  have h : Primrec fun t : List ℕ =>
      Cell.equivProd.symm ((t.getD 0 0, t.getD 1 0, t.getD 2 0, t.getD 3 0, t.getD 4 0,
        t.getD 5 0, t.getD 11 0),
        ((t.getD 6 0 == 1), (t.getD 7 0 == 1), (t.getD 8 0 == 1), (t.getD 9 0 == 1),
          (t.getD 10 0 == 1))) := by
    refine (Primrec.of_equiv_symm_iff Cell.equivProd).2 ?_
    exact Primrec.pair
      (Primrec.pair (hg 0) (Primrec.pair (hg 1) (Primrec.pair (hg 2) (Primrec.pair (hg 3)
        (Primrec.pair (hg 4) (Primrec.pair (hg 5) (hg 11)))))))
      (Primrec.pair (hb 6) (Primrec.pair (hb 7) (Primrec.pair (hb 8)
        (Primrec.pair (hb 9) (hb 10)))))
  exact h.of_eq fun t => rfl

/-- The lists of entries allowed in the fields of a cell are primitive recursive. -/
theorem primrec_fieldLists : Primrec fun p : _root_.PCP.Arg => fieldLists p.1 p.2 := by
  have hsyms : Primrec fun p : _root_.PCP.Arg => p.1.tapeSyms p.2 ++ p.1.states :=
    Primrec.list_append.comp _root_.PCP.primrec_tapeSyms _root_.PCP.primrec_states
  have hst : Primrec fun p : _root_.PCP.Arg => (0 : ℕ) :: p.1.states :=
    Primrec.list_cons.comp (Primrec.const 0) _root_.PCP.primrec_states
  have hrange : Primrec fun p : _root_.PCP.Arg => List.range (p.2.length + 2) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.succ.comp
      (Primrec.list_length.comp Primrec.snd)))
  have hz : Primrec fun _ : _root_.PCP.Arg => ([0, 1] : List ℕ) := Primrec.const _
  have e12 := Primrec.list_cons.comp hrange (Primrec.const ([] : List (List ℕ)))
  have e11 := Primrec.list_cons.comp hz e12
  have e10 := Primrec.list_cons.comp hz e11
  have e9 := Primrec.list_cons.comp hz e10
  have e8 := Primrec.list_cons.comp hz e9
  have e7 := Primrec.list_cons.comp hz e8
  have e6 := Primrec.list_cons.comp hst e7
  have e5 := Primrec.list_cons.comp (Primrec.const (List.range 6)) e6
  have e4 := Primrec.list_cons.comp hsyms e5
  have e3 := Primrec.list_cons.comp hz e4
  have e2 := Primrec.list_cons.comp hsyms e3
  exact (Primrec.list_cons.comp hz e2).of_eq fun p => rfl

/-- The enumeration of the cells of a machine is primitive recursive. -/
theorem primrec_allCells : Primrec fun p : _root_.PCP.Arg => allCells p.1 p.2 := by
  have hmap : Primrec fun p : _root_.PCP.Arg => (tupleList (fieldLists p.1 p.2)).map cellOfList :=
    Primrec.list_map (primrec_tupleList.comp primrec_fieldLists)
      (Primrec₂.mk (primrec_cellOfList.comp Primrec.snd))
  exact (Primrec.list_filter hmap (Primrec₂.mk primrec_validB)).of_eq fun p => rfl

/-- The largest code of a cell is a primitive recursive function of the machine. -/
theorem primrec_maxCode : Primrec fun p : _root_.PCP.Arg => maxCode p.1 p.2 := by
  refine Primrec.list_foldr (h := fun (_ : _root_.PCP.Arg) (x : Cell × ℕ) =>
    max (Encodable.encode x.1) x.2) primrec_allCells (Primrec.const 0) (Primrec₂.mk ?_)
  exact Primrec.nat_max.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

/-- The tile of the corner `(0,0)` is a primitive recursive function of the machine. -/
theorem primrec_startTile : Primrec fun p : _root_.PCP.Arg => startTile p.1 := by
  have hq0 : Primrec fun p : _root_.PCP.Arg => p.1.q0 := _root_.PCP.primrec_q0.comp Primrec.fst
  have hqacc : Primrec fun p : _root_.PCP.Arg => p.1.qacc :=
    _root_.PCP.primrec_qacc.comp Primrec.fst
  have h : Primrec fun p : _root_.PCP.Arg =>
      Cell.equivProd.symm ((1, p.1.q0, 1, p.1.q0, 0, 0, 0),
        (true, false, true, false, decide (p.1.q0 = p.1.qacc))) := by
    refine (Primrec.of_equiv_symm_iff Cell.equivProd).2 ?_
    exact Primrec.pair
      (Primrec.pair (Primrec.const 1) (Primrec.pair hq0 (Primrec.pair (Primrec.const 1)
        (Primrec.pair hq0 (Primrec.pair (Primrec.const 0)
          (Primrec.pair (Primrec.const 0) (Primrec.const 0)))))))
      (Primrec.pair (Primrec.const true) (Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.const true) (Primrec.pair (Primrec.const false)
          (PrimAux.decEq hq0 hqacc)))))
  exact h.of_eq fun p => rfl

/-! ## The instance -/

section Constraint

/-- The context in which the innermost list of the local constraint is built: an argument of the
reduction together with the three cells that the enumeration has already chosen. -/
private abbrev Ctx := ((_root_.PCP.Arg × Cell) × Cell) × Cell

private theorem primrec_winCtx : Primrec fun z : Ctx × Cell =>
    windowB z.1.1.1.1.1 z.1.1.1.1.2 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  have harg : Primrec fun q : Ctx => q.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec fun q : Ctx => q.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec fun q : Ctx => q.1.2 := Primrec.snd.comp Primrec.fst
  have hc : Primrec fun q : Ctx => q.2 := Primrec.snd
  exact (primrec_windowB.comp (Primrec.pair (harg.comp Primrec.fst)
    (Primrec.pair (ha.comp Primrec.fst) (Primrec.pair (hb.comp Primrec.fst)
      (Primrec.pair (hc.comp Primrec.fst) Primrec.snd))))).of_eq fun z => rfl

/-- The local constraint of the instance is a primitive recursive function of the machine and the
input word. -/
theorem primrec_constraint : Primrec fun p : _root_.PCP.Arg =>
    (allCells p.1 p.2).flatMap fun a => (allCells p.1 p.2).flatMap fun b =>
      (allCells p.1 p.2).flatMap fun c =>
        ((allCells p.1 p.2).filter (windowB p.1 p.2 a b c)).map fun d =>
          (Encodable.encode a, Encodable.encode b, Encodable.encode c, Encodable.encode d) := by
  have harg : Primrec fun q : Ctx => q.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec fun q : Ctx => q.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec fun q : Ctx => q.1.2 := Primrec.snd.comp Primrec.fst
  have hc : Primrec fun q : Ctx => q.2 := Primrec.snd
  have hfil : Primrec fun q : Ctx =>
      (allCells q.1.1.1.1 q.1.1.1.2).filter (windowB q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2) :=
    Primrec.list_filter (primrec_allCells.comp harg) (Primrec₂.mk primrec_winCtx)
  have h3 : Primrec fun q : Ctx =>
      ((allCells q.1.1.1.1 q.1.1.1.2).filter
          (windowB q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)).map fun d =>
        (Encodable.encode q.1.1.2, Encodable.encode q.1.2, Encodable.encode q.2,
          Encodable.encode d) :=
    Primrec.list_map hfil
      (Primrec₂.mk (Primrec.pair (Primrec.encode.comp (ha.comp Primrec.fst))
        (Primrec.pair (Primrec.encode.comp (hb.comp Primrec.fst))
          (Primrec.pair (Primrec.encode.comp (hc.comp Primrec.fst))
            (Primrec.encode.comp Primrec.snd)))))
  have h2 : Primrec fun q : (_root_.PCP.Arg × Cell) × Cell =>
      (allCells q.1.1.1 q.1.1.2).flatMap fun c =>
        ((allCells q.1.1.1 q.1.1.2).filter (windowB q.1.1.1 q.1.1.2 q.1.2 q.2 c)).map fun d =>
          (Encodable.encode q.1.2, Encodable.encode q.2, Encodable.encode c,
            Encodable.encode d) :=
    Primrec.list_flatMap (primrec_allCells.comp (Primrec.fst.comp Primrec.fst))
      (Primrec₂.mk h3)
  have h1 : Primrec fun q : _root_.PCP.Arg × Cell =>
      (allCells q.1.1 q.1.2).flatMap fun b => (allCells q.1.1 q.1.2).flatMap fun c =>
        ((allCells q.1.1 q.1.2).filter (windowB q.1.1 q.1.2 q.2 b c)).map fun d =>
          (Encodable.encode q.2, Encodable.encode b, Encodable.encode c, Encodable.encode d) :=
    Primrec.list_flatMap (primrec_allCells.comp Primrec.fst) (Primrec₂.mk h2)
  exact Primrec.list_flatMap primrec_allCells (Primrec₂.mk h1)

end Constraint

set_option maxHeartbeats 400000 in
/-- **The instance of the tiling problem built from a machine and an input word is a primitive
recursive function of the two.** -/
theorem primrec_inst : Primrec fun p : _root_.PCP.Arg => inst p.1 p.2 := by
  have h : Primrec fun p : _root_.PCP.Arg =>
      Tiling.Instance.equivProd.symm (maxCode p.1 p.2, Encodable.encode (startTile p.1),
        Encodable.encode finalTile,
        (allCells p.1 p.2).flatMap fun a => (allCells p.1 p.2).flatMap fun b =>
          (allCells p.1 p.2).flatMap fun c =>
            ((allCells p.1 p.2).filter (windowB p.1 p.2 a b c)).map fun d =>
              (Encodable.encode a, Encodable.encode b, Encodable.encode c,
                Encodable.encode d)) :=
    (Primrec.of_equiv_symm_iff Tiling.Instance.equivProd).2
      (Primrec.pair primrec_maxCode (Primrec.pair (Primrec.encode.comp primrec_startTile)
        (Primrec.pair (Primrec.const (Encodable.encode finalTile)) primrec_constraint)))
  exact h.of_eq fun p => by
    rw [inst]
    simp only [Tiling.Instance.equivProd, Equiv.coe_fn_symm_mk]

end TilingRed
end Transducers
