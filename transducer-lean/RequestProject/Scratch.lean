import RequestProject.Common.PrimrecList

variable {α : Type*} [Primcodable α]

example {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a = g a) := by
  obtain ⟨inst, h⟩ : PrimrecPred fun a => f a = g a := Primrec.eq.comp hf hg
  exact h.of_eq fun a => by simp

example {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) := by
  obtain ⟨inst, h⟩ : PrimrecPred fun a => f a = g a := Primrec.eq.comp hf hg
  exact h.of_eq fun a => by simp

example {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ≤ g a) := by
  obtain ⟨inst, h⟩ : PrimrecPred fun a => f a ≤ g a := Primrec.nat_le.comp hf hg
  exact h.of_eq fun a => by simp

example {f : α → ℕ} {g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ∈ g a) := by
  obtain ⟨inst, h⟩ : PrimrecPred fun a => f a ∈ g a := Primrec.list_mem.comp hf hg
  exact h.of_eq fun a => by simp

example {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => (f a == g a) := by
  obtain ⟨inst, h⟩ : PrimrecPred fun a => f a = g a := Primrec.eq.comp hf hg
  exact h.of_eq fun a => by simp

example {c : α → Prop} [DecidablePred c] {f g : α → Bool} (hc : Primrec fun a => decide (c a))
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  exact Primrec.ite ⟨_, hc⟩ hf hg
