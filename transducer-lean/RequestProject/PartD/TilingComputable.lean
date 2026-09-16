/-
Part D, Section *A functional programming language*: the tiling instance of the reduction is
computed by a primitive recursive function of the input word.

This is the effectiveness half of Lemma `lem:tiling`: the reduction of
`RequestProject/PartD/TilingSound.lean` and `RequestProject/PartD/TilingComplete.lean` maps an
input word `w` of a fixed machine `M` to the instance `Transducers.TilingRed.inst M w` of the
tiling problem, and a decision procedure for the tiling problem is of use only if that map can be
computed.  The file proves that it is primitive recursive, field by field: the cells of the
machine, the conditions on a cell, on two adjacent cells and on a `2 × 2` window, the enumeration
of the cells, and finally the instance itself.
-/
import RequestProject.PartD.TilingCells
import RequestProject.Common.PrimrecList

namespace Transducers
namespace TilingRed

open PCP

/-! ## Boolean combinators -/

namespace PrimAux

variable {α : Type*} [Primcodable α]

theorem band {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a && g a :=
  (Primrec.dom_bool₂ (fun x y => x && y)).comp hf hg

theorem bor {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a || g a :=
  (Primrec.dom_bool₂ (fun x y => x || y)).comp hf hg

theorem bnot {f : α → Bool} (hf : Primrec f) : Primrec fun a => !f a :=
  (Primrec.dom_bool (fun x => !x)).comp hf

theorem decEq {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a = g a) := Primrec.eq.comp hf hg

theorem beqNat {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) := (decEq hf hg).of_eq fun a => by simp

theorem beqBool {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) := (Primrec.eq.comp hf hg).of_eq fun a => by simp

theorem decLe {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ≤ g a) := Primrec.nat_le.comp hf hg

theorem decMem {f : α → ℕ} {g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ∈ g a) := Primrec.list_mem.comp hf hg

end PrimAux

/-! ## The fields of a cell -/

theorem primrec_equivProd : Primrec Cell.equivProd := Primrec.of_equiv

private theorem pn1 : Primrec (fun x : Cell => (Cell.equivProd x).1) :=
  (Primrec.fst (α := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (β := Bool × Bool × Bool × Bool × Bool)).comp
    primrec_equivProd

private theorem pn2 : Primrec (fun x : Cell => (Cell.equivProd x).1.2) :=
  (Primrec.snd (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)).comp pn1

private theorem pn3 : Primrec (fun x : Cell => (Cell.equivProd x).1.2.2) :=
  (Primrec.snd (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ × ℕ)).comp pn2

private theorem pn4 : Primrec (fun x : Cell => (Cell.equivProd x).1.2.2.2) :=
  (Primrec.snd (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ)).comp pn3

private theorem pn5 : Primrec (fun x : Cell => (Cell.equivProd x).1.2.2.2.2) :=
  (Primrec.snd (α := ℕ) (β := ℕ × ℕ × ℕ)).comp pn4

private theorem pn6 : Primrec (fun x : Cell => (Cell.equivProd x).1.2.2.2.2.2) :=
  (Primrec.snd (α := ℕ) (β := ℕ × ℕ)).comp pn5

private theorem pb1 : Primrec (fun x : Cell => (Cell.equivProd x).2) :=
  (Primrec.snd (α := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (β := Bool × Bool × Bool × Bool × Bool)).comp
    primrec_equivProd

private theorem pb2 : Primrec (fun x : Cell => (Cell.equivProd x).2.2) :=
  (Primrec.snd (α := Bool) (β := Bool × Bool × Bool × Bool)).comp pb1

private theorem pb3 : Primrec (fun x : Cell => (Cell.equivProd x).2.2.2) :=
  (Primrec.snd (α := Bool) (β := Bool × Bool × Bool)).comp pb2

private theorem pb4 : Primrec (fun x : Cell => (Cell.equivProd x).2.2.2.2) :=
  (Primrec.snd (α := Bool) (β := Bool × Bool)).comp pb3

theorem primrec_k : Primrec (fun x : Cell => x.k) :=
  ((Primrec.fst (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)).comp pn1).of_eq fun _ => rfl

theorem primrec_v : Primrec (fun x : Cell => x.v) :=
  ((Primrec.fst (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ × ℕ)).comp pn2).of_eq fun _ => rfl

theorem primrec_nk : Primrec (fun x : Cell => x.nk) :=
  ((Primrec.fst (α := ℕ) (β := ℕ × ℕ × ℕ × ℕ)).comp pn3).of_eq fun _ => rfl

theorem primrec_nv : Primrec (fun x : Cell => x.nv) :=
  ((Primrec.fst (α := ℕ) (β := ℕ × ℕ × ℕ)).comp pn4).of_eq fun _ => rfl

theorem primrec_role : Primrec (fun x : Cell => x.role) :=
  ((Primrec.fst (α := ℕ) (β := ℕ × ℕ)).comp pn5).of_eq fun _ => rfl

theorem primrec_aux : Primrec (fun x : Cell => x.aux) :=
  ((Primrec.fst (α := ℕ) (β := ℕ)).comp pn6).of_eq fun _ => rfl

theorem primrec_cnt : Primrec (fun x : Cell => x.cnt) :=
  ((Primrec.snd (α := ℕ) (β := ℕ)).comp pn6).of_eq fun _ => rfl

theorem primrec_lb : Primrec (fun x : Cell => x.lb) :=
  ((Primrec.fst (α := Bool) (β := Bool × Bool × Bool × Bool)).comp pb1).of_eq fun _ => rfl

theorem primrec_rb : Primrec (fun x : Cell => x.rb) :=
  ((Primrec.fst (α := Bool) (β := Bool × Bool × Bool)).comp pb2).of_eq fun _ => rfl

theorem primrec_top : Primrec (fun x : Cell => x.top) :=
  ((Primrec.fst (α := Bool) (β := Bool × Bool)).comp pb3).of_eq fun _ => rfl

theorem primrec_fin : Primrec (fun x : Cell => x.fin) :=
  ((Primrec.fst (α := Bool) (β := Bool)).comp pb4).of_eq fun _ => rfl

theorem primrec_acc : Primrec (fun x : Cell => x.acc) :=
  ((Primrec.snd (α := Bool) (β := Bool)).comp pb4).of_eq fun _ => rfl

end TilingRed
end Transducers
