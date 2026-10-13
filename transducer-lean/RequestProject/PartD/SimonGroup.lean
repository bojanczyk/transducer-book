/-
Part D, Section *Evaluation*: the group case of the Factorisation Forest Theorem
(Lemma `lem:factorisation-forest-group`), and the induction that proves the theorem.

## The group case

The book's argument is followed exactly.  For a string `w` let `σ(w)` be the set of values of its
prefixes that are neither empty nor full (`Transducers.Simon.sigma φ 1 w`).  Every string `w` has a
Simon tree of height at most `3·|σ(w)|`: choose `g ∈ σ(w)`, cut `w` at every gap whose prefix has
value `g`, obtaining `w = w₀ w₁ ⋯ wₙ`; every factor has a smaller `σ`, because `σ(w₀)` and the
translates `g·σ(wᵢ)` all lie in `σ(w) \ {g}`, and translating by `g` does not change the size of a
set; and the middle factors `w₁, …, wₙ₋₁` all have the value `e` with `g·e = g`, which is an
idempotent, so they go under one idempotent node.  Two more nodes add `w₀` and `wₙ`.

The only property of groups that this uses is that left multiplication by an element is injective,
so `Transducers.Simon.good_group` is stated for a finite subsemigroup `T` of a monoid in which left
multiplication by every element of `T` is injective on `T`.

The factorisation at the gaps is produced by `Transducers.Simon.exists_blocks`, which cuts the part
of the string after the first gap into its blocks, by repeatedly taking the shortest nonempty prefix
whose value, multiplied on the left by `g`, is `g`.
-/
import RequestProject.PartD.SimonFF

namespace Transducers

namespace Simon

open Finset

variable {M : Type} [Monoid M] [DecidableEq M] {X : Type}

/-- `sigma φ g r`: the values `g · val (prefix)` of the prefixes of `r` that are neither empty nor
full.  For `g = 1` this is the set `σ(r)` of the book. -/
def sigma (φ : X → M) (g : M) (r : List X) : Finset M :=
  ((range r.length).filter (fun j => 0 < j)).image (fun j => g * val φ (r.take j))

lemma mem_sigma {φ : X → M} {g : M} {r : List X} {m : M} :
    m ∈ sigma φ g r ↔ ∃ j, 0 < j ∧ j < r.length ∧ g * val φ (r.take j) = m := by
  simp only [sigma, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, h3⟩; exact ⟨j, h2, h1, h3⟩
  · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, ⟨h2, h1⟩, h3⟩

lemma take_length_add_append (l₁ l₂ : List X) (j : ℕ) :
    (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j := by
  simp [List.take_append]

/-- The blocks of the part of a string after a gap whose prefix has value `g`. -/
lemma exists_blocks (φ : X → M) (g : M) : ∀ (n : ℕ) (r : List X), r.length ≤ n → r ≠ [] →
    ∃ (bs : List (List X)) (last : List X), r = bs.flatten ++ last ∧ last ≠ [] ∧
      (∀ b ∈ bs, b ≠ [] ∧ g * val φ b = g) ∧
      (∀ b ∈ bs ++ [last], ∀ j, 0 < j → j < b.length →
        g * val φ (b.take j) ≠ g ∧ g * val φ (b.take j) ∈ sigma φ g r)
  | 0, r, hn, hr => absurd (List.length_eq_zero_iff.mp (by omega)) hr
  | n + 1, r, hn, hr => by
    classical
    by_cases hex : ∃ j, 0 < j ∧ j < r.length ∧ g * val φ (r.take j) = g
    · set j₀ := Nat.find hex with hj₀def
      obtain ⟨hj₀, hj₀r, hj₀g⟩ := Nat.find_spec hex
      have hmin : ∀ j, 0 < j → j < j₀ → g * val φ (r.take j) ≠ g := by
        intro j hj hjj heq
        exact Nat.find_min hex hjj ⟨hj, by omega, heq⟩
      set b := r.take j₀ with hb
      set r' := r.drop j₀ with hr'
      have hblen : b.length = j₀ := by rw [hb, List.length_take]; omega
      have hr'ne : r' ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [hr', List.length_drop] at this
        simp at this; omega
      have hr'len : r'.length ≤ n := by rw [hr', List.length_drop]; omega
      obtain ⟨bs, last, hdec, hlast, hbs, hpre⟩ := exists_blocks φ g n r' hr'len hr'ne
      have hrbr : r = b ++ r' := (List.take_append_drop _ _).symm
      have hsub : sigma φ g r' ⊆ sigma φ g r := by
        intro m hm
        obtain ⟨j, hj, hjr, rfl⟩ := mem_sigma.mp hm
        refine mem_sigma.mpr ⟨b.length + j, by omega, ?_, ?_⟩
        · rw [hrbr, List.length_append]; omega
        · rw [hrbr, take_length_add_append, val_append, ← mul_assoc, hj₀g]
      refine ⟨b :: bs, last, ?_, hlast, ?_, ?_⟩
      · rw [hrbr, hdec]; simp
      · intro b' hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · refine ⟨?_, hj₀g⟩
          intro h; rw [h] at hblen; simp at hblen; omega
        · exact hbs b' hb'
      · intro b' hb' j hj hjb
        simp only [List.cons_append, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · have htake : b.take j = r.take j := by
            rw [hb, List.take_take]; congr 1; omega
          rw [htake]
          refine ⟨hmin j hj (by omega), mem_sigma.mpr ⟨j, hj, by omega, rfl⟩⟩
        · obtain ⟨h1, h2⟩ := hpre b' hb' j hj hjb
          exact ⟨h1, hsub h2⟩
    · push_neg at hex
      refine ⟨[], r, by simp, hr, by simp, ?_⟩
      intro b hb j hj hjb
      simp only [List.nil_append, List.mem_singleton] at hb
      subst hb
      exact ⟨hex j hj hjb, mem_sigma.mpr ⟨j, hj, hjb, rfl⟩⟩

lemma sigma_subset {T : Finset M} (hT : Closed T) {φ : X → M} {w : List X}
    (hx : ∀ x ∈ w, φ x ∈ T) : sigma φ 1 w ⊆ T := by
  intro m hm
  obtain ⟨j, hj, hjw, rfl⟩ := mem_sigma.mp hm
  rw [one_mul]
  refine val_mem hT ?_ fun x hxw => hx x (List.mem_of_mem_take hxw)
  intro h
  rcases List.take_eq_nil_iff.mp h with h | h
  · omega
  · subst h; simp at hjw

/-- **The group case** (Lemma `lem:factorisation-forest-group`, in the form used by the induction).
If left multiplication by every element of the finite subsemigroup `T` is injective on `T`, then
every nonempty string with letter values in `T` has a Simon tree of height at most `3·|T|`. -/
theorem good_group {T : Finset M} (hT : Closed T) (hinj : ∀ g ∈ T, Set.InjOn (g * ·) T) :
    ∃ K, K = 3 * T.card ∧ ∀ (X : Type) (φ : X → M) (w : List X), w ≠ [] →
      (∀ x ∈ w, φ x ∈ T) → Bnd φ K w := by
  classical
  refine ⟨3 * T.card, rfl, fun X φ w hw hx => ?_⟩
  have key : ∀ n, ∀ w : List X, w ≠ [] → (∀ x ∈ w, φ x ∈ T) → (sigma φ 1 w).card ≤ n →
      Bnd φ (3 * n) w := by
    intro n
    induction n with
    | zero =>
      intro w hw _ hcard
      have hempty : sigma φ 1 w = ∅ := Finset.card_eq_zero.mp (by omega)
      match w, hw with
      | [x], _ => exact Bnd.leaf _ x
      | x :: y :: w, _ =>
        exfalso
        have : 1 * val φ ((x :: y :: w).take 1) ∈ sigma φ 1 (x :: y :: w) :=
          mem_sigma.mpr ⟨1, by omega, by simp, rfl⟩
        rw [hempty] at this; simp at this
    | succ n ih =>
      intro w hw hx hcard
      by_cases hempty : sigma φ 1 w = ∅
      · match w, hw with
        | [x], _ => exact Bnd.leaf _ x
        | x :: y :: w, _ =>
          exfalso
          have : 1 * val φ ((x :: y :: w).take 1) ∈ sigma φ 1 (x :: y :: w) :=
            mem_sigma.mpr ⟨1, by omega, by simp, rfl⟩
          rw [hempty] at this; simp at this
      obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hex : ∃ i, 0 < i ∧ i < w.length ∧ 1 * val φ (w.take i) = g := mem_sigma.mp hg
      set i₀ := Nat.find hex
      obtain ⟨hi₀, hi₀w, hi₀g⟩ := Nat.find_spec hex
      have hmin : ∀ j, 0 < j → j < i₀ → 1 * val φ (w.take j) ≠ g := by
        intro j hj hjj heq
        exact Nat.find_min hex hjj ⟨hj, by omega, heq⟩
      set w₀ := w.take i₀ with hw₀
      set r := w.drop i₀ with hr
      have hwr : w = w₀ ++ r := (List.take_append_drop _ _).symm
      have hw₀len : w₀.length = i₀ := by rw [hw₀, List.length_take]; omega
      have hw₀ne : w₀ ≠ [] := by intro h; rw [h] at hw₀len; simp at hw₀len; omega
      have hrne : r ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [hr, List.length_drop] at this; simp at this; omega
      have hxw₀ : ∀ x ∈ w₀, φ x ∈ T := fun x h => hx x (List.mem_of_mem_take h)
      have hxr : ∀ x ∈ r, φ x ∈ T := fun x h => hx x (List.mem_of_mem_drop h)
      have hvalw₀ : val φ w₀ = g := by rw [← hi₀g, one_mul]
      have hgT : g ∈ T := hvalw₀ ▸ val_mem hT hw₀ne hxw₀
      have hcard' : ((sigma φ 1 w).erase g).card ≤ n := by
        rw [Finset.card_erase_of_mem hg]; omega
      -- the first factor
      have hb₀ : Bnd φ (3 * n) w₀ := by
        refine ih w₀ hw₀ne hxw₀ (le_trans (Finset.card_le_card ?_) hcard')
        intro m hm
        obtain ⟨j, hj, hjw, rfl⟩ := mem_sigma.mp hm
        have htake : w₀.take j = w.take j := by rw [hw₀, List.take_take]; congr 1; omega
        rw [htake]
        exact Finset.mem_erase.mpr ⟨hmin j hj (by omega), mem_sigma.mpr ⟨j, hj, by omega, rfl⟩⟩
      -- the blocks after the first gap
      obtain ⟨bs, last, hdec, hlast, hbs, hpre⟩ := exists_blocks φ g r.length r le_rfl hrne
      have hsub : sigma φ g r ⊆ sigma φ 1 w := by
        intro m hm
        obtain ⟨j, hj, hjr, rfl⟩ := mem_sigma.mp hm
        refine mem_sigma.mpr ⟨w₀.length + j, by omega, ?_, ?_⟩
        · rw [hwr, List.length_append]; omega
        · rw [hwr, take_length_add_append, val_append, one_mul, hvalw₀]
      have hxb : ∀ b ∈ bs ++ [last], ∀ x ∈ b, φ x ∈ T := by
        intro b hb x hxb
        refine hxr x ?_
        rw [hdec]
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact List.mem_append_left _ (List.mem_flatten.mpr ⟨b, hb, hxb⟩)
        · exact List.mem_append_right _ hxb
      have hblock : ∀ b ∈ bs ++ [last], Bnd φ (3 * n) b := by
        intro b hb
        have hbne : b ≠ [] := by
          simp only [List.mem_append, List.mem_singleton] at hb
          rcases hb with hb | rfl
          · exact (hbs b hb).1
          · exact hlast
        refine ih b hbne (hxb b hb) ?_
        have himg : (sigma φ 1 b).image (g * ·) ⊆ (sigma φ 1 w).erase g := by
          intro m hm
          obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨j, hj, hjb, rfl⟩ := mem_sigma.mp hm'
          obtain ⟨h1, h2⟩ := hpre b hb j hj hjb
          rw [one_mul]
          exact Finset.mem_erase.mpr ⟨h1, hsub h2⟩
        have hinjb : Set.InjOn (g * ·) (sigma φ 1 b) :=
          (hinj g hgT).mono (fun m hm => sigma_subset hT (hxb b hb) hm)
        rw [← Finset.card_image_of_injOn hinjb]
        exact le_trans (Finset.card_le_card himg) hcard'
      have hlastb : Bnd φ (3 * n) last := hblock last (by simp)
      rw [hwr, hdec]
      rcases eq_or_ne bs [] with hbsnil | hbsne
      · rw [hbsnil]
        simpa using (hb₀.append hlastb).mono (by omega)
      · -- the middle blocks all have the same idempotent value
        obtain ⟨b₀, bs', hbs'⟩ := List.exists_cons_of_ne_nil hbsne
        set e := val φ b₀ with he
        have hvalT : ∀ b ∈ bs, val φ b ∈ T := fun b hb =>
          val_mem hT (hbs b hb).1 (hxb b (List.mem_append_left _ hb))
        have heT : e ∈ T := hvalT b₀ (by simp [hbs'])
        have hge : g * e = g := (hbs b₀ (by simp [hbs'])).2
        have hidem : IsIdempotentElem e := by
          show e * e = e
          refine hinj g hgT (hT _ heT _ heT) heT ?_
          show g * (e * e) = g * e
          rw [← mul_assoc, hge, hge]
        have hvals : ∀ b ∈ bs, val φ b = e := by
          intro b hb
          refine hinj g hgT (hvalT b hb) heT ?_
          show g * val φ b = g * e
          rw [(hbs b hb).2, hge]
        have hmid : Bnd φ (3 * n + 1) bs.flatten :=
          Bnd.group hbsne hidem (fun b hb => hblock b (List.mem_append_left _ hb)) hvals
        have := (hb₀.append hmid).append hlastb
        rw [← List.append_assoc]
        exact this.mono (by omega)
  exact key T.card w hw hx (Finset.card_le_card (sigma_subset hT hx))

end Simon

end Transducers
