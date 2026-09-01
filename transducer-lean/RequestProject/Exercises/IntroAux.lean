/-
Auxiliary facts used by the exercises of the introduction of
*Transducers* (M. Bojańczyk).

Nothing here is a result of the book: these are the elementary facts about
deterministic automata and regular languages that the solutions of the
exercises of `intro.tex` take for granted (transporting a dfa to the state set
`Fin n`, regularity of singletons, of subsingletons and of finite unions, the
run of a dfa on a power `wⁿ`, and the eventual stabilisation of the iterates of
a self-map of a finite set).
-/
import RequestProject.Common

namespace Transducers.Exercises

open scoped Nat

/-! ## Transporting a dfa along a bijection of its state set -/

/-- The dfa obtained from `M` by renaming its states along `e`. -/
def dfaTransport {A σ τ : Type} (M : DFA A σ) (e : σ ≃ τ) : DFA A τ where
  step := fun q a => e (M.step (e.symm q) a)
  start := e M.start
  accept := e.symm ⁻¹' M.accept

lemma evalFrom_dfaTransport {A σ τ : Type} (M : DFA A σ) (e : σ ≃ τ) (q : σ) (w : List A) :
    (dfaTransport M e).evalFrom (e q) w = e (M.evalFrom q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      rw [DFA.evalFrom_cons, DFA.evalFrom_cons]
      simpa [dfaTransport] using ih (M.step q a)

lemma accepts_dfaTransport {A σ τ : Type} (M : DFA A σ) (e : σ ≃ τ) :
    (dfaTransport M e).accepts = M.accepts := by
  ext w
  simp only [DFA.mem_accepts, DFA.eval]
  show (dfaTransport M e).evalFrom (e M.start) w ∈ _ ↔ _
  rw [evalFrom_dfaTransport]
  simp [dfaTransport]

/-- Every regular language is recognised by a dfa whose state set is `Fin n`
for some `n`. -/
lemma exists_fin_dfa {A : Type} {L : Language A} (h : L.IsRegular) :
    ∃ (n : ℕ) (M : DFA A (Fin n)), M.accepts = L := by
  classical
  obtain ⟨σ, hσ, M, rfl⟩ := h
  obtain ⟨e⟩ := Fintype.truncEquivFin σ
  exact ⟨Fintype.card σ, dfaTransport M e, accepts_dfaTransport M e⟩

/-- The complement of a dfa: the same automaton with the complemented set of
accepting states. -/
def dfaCompl {A σ : Type} (M : DFA A σ) : DFA A σ where
  step := M.step
  start := M.start
  accept := M.acceptᶜ

lemma mem_accepts_dfaCompl {A σ : Type} (M : DFA A σ) (w : List A) :
    w ∈ (dfaCompl M).accepts ↔ w ∉ M.accepts := Iff.rfl

/-- The dfa `M` with its acceptance condition shifted by a fixed suffix `v`:
it accepts `x` exactly when `M` accepts `x ++ v`. -/
def accDFA {A : Type} {j : ℕ} (M : DFA A (Fin j)) (v : List A) : DFA A (Fin j) where
  step := M.step
  start := M.start
  accept := {q | M.evalFrom q v ∈ M.accept}

lemma mem_accDFA {A : Type} {j : ℕ} (M : DFA A (Fin j)) (v x : List A) :
    x ∈ (accDFA M v).accepts ↔ x ++ v ∈ M.accepts := by
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  exact Iff.rfl

/-- Over a finite alphabet, there are finitely many dfas with a given finite
state set. -/
instance instFiniteDFA (A σ : Type) [Finite A] [Finite σ] : Finite (DFA A σ) := by
  classical
  refine Finite.of_injective (fun M : DFA A σ => (M.step, M.start, fun q => q ∈ M.accept)) ?_
  rintro ⟨s1, st1, ac1⟩ ⟨s2, st2, ac2⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1; subst h2
  congr 1

/-! ## Regularity of some small languages -/

/-- A singleton language is regular. -/
lemma isRegular_singleton {A : Type} (w : List A) : Language.IsRegular ({w} : Language A) := by
  classical
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  have hsub : Set.range (Language.leftQuotient ({w} : Language A)) ⊆
      (fun v : List A => ({v} : Language A)) '' {v | v ∈ w.tails} ∪ {(0 : Language A)} := by
    rintro _ ⟨u, rfl⟩
    by_cases h : u <+: w
    · obtain ⟨v, rfl⟩ := h
      refine Or.inl ⟨v, by simp [List.mem_tails], ?_⟩
      ext x
      simp only [Language.mem_leftQuotient]
      constructor
      · rintro rfl; rfl
      · intro hx; exact List.append_cancel_left hx
    · refine Or.inr ?_
      simp only [Set.mem_singleton_iff]
      ext x
      simp only [Language.mem_leftQuotient]
      exact ⟨fun hx => absurd ⟨x, hx⟩ h, fun hx => hx.elim⟩
  exact Set.Finite.subset
    (Set.Finite.union (Set.Finite.image _ (List.finite_toSet _)) (Set.finite_singleton _)) hsub

/-- The empty language is regular. -/
lemma isRegular_zero {A : Type} : Language.IsRegular (0 : Language A) := by
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  refine Set.Finite.subset (Set.finite_singleton (0 : Language A)) ?_
  rintro _ ⟨u, rfl⟩
  simp only [Set.mem_singleton_iff]
  ext x
  simp only [Language.mem_leftQuotient]
  exact ⟨fun hx => hx.elim, fun hx => hx.elim⟩

/-- A language with at most one word is regular. -/
lemma isRegular_of_subsingleton {A : Type} {L : Language A}
    (h : ∀ x ∈ L, ∀ y ∈ L, x = y) : L.IsRegular := by
  by_cases hne : ∃ w, w ∈ L
  · obtain ⟨w, hw⟩ := hne
    have hL : L = ({w} : Language A) := by
      ext x
      exact ⟨fun hx => h x hx w hw, fun hx => by cases hx; exact hw⟩
    rw [hL]; exact isRegular_singleton w
  · push_neg at hne
    have hL : L = (0 : Language A) := by
      ext x
      exact ⟨fun hx => (hne x hx).elim, fun hx => hx.elim⟩
    rw [hL]; exact isRegular_zero

/-- The union of the languages `P i` for `i` in a list. -/
def unionOf {A ι : Type} (P : ι → Language A) (l : List ι) : Language A :=
  List.foldr (fun i acc => P i + acc) 0 l

lemma mem_unionOf {A ι : Type} (P : ι → Language A) (l : List ι) (x : List A) :
    x ∈ unionOf P l ↔ ∃ i ∈ l, x ∈ P i := by
  induction l with
  | nil => exact ⟨fun hx => hx.elim, fun ⟨i, hi, _⟩ => absurd hi List.not_mem_nil⟩
  | cons i l ih =>
      show x ∈ P i + unionOf P l ↔ _
      rw [Language.add_def]
      constructor
      · rintro (hx | hx)
        · exact ⟨i, List.mem_cons_self, hx⟩
        · obtain ⟨j, hj, hx⟩ := ih.1 hx
          exact ⟨j, List.mem_cons_of_mem _ hj, hx⟩
      · rintro ⟨j, hj, hx⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact Or.inl hx
        · exact Or.inr (ih.2 ⟨j, hj, hx⟩)

/-- A finite union of regular languages is regular. -/
lemma isRegular_unionOf {A ι : Type} (P : ι → Language A) (l : List ι)
    (h : ∀ i ∈ l, (P i).IsRegular) : (unionOf P l).IsRegular := by
  induction l with
  | nil => exact isRegular_zero
  | cons i l ih =>
      exact Language.IsRegular.add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

/-! ## Runs on a power of a word -/

/-- Reading `wⁿ` iterates the state transformation of `w`. -/
lemma evalFrom_npow {A σ : Type} (M : DFA A σ) (w : List A) (n : ℕ) (q : σ) :
    M.evalFrom q (npow w n) = (fun p => M.evalFrom p w)^[n] q := by
  induction n generalizing q with
  | zero => simp [npow, DFA.evalFrom]
  | succ n ih =>
      show M.evalFrom q (w ++ npow w n) = _
      rw [DFA.evalFrom_of_append, ih, Function.iterate_succ_apply]

/-! ## Stabilisation of the iterates of a self-map of a finite set -/

/-- For a self-map `t` of a finite set there is a `D > 0` such that `t^[m]`
does not depend on `m` as long as `m` is a multiple of `D` that is at least
`D`. -/
lemma iterate_stable_single {S : Type} [Finite S] (t : S → S) :
    ∃ D, 0 < D ∧ ∀ m, D ≤ m → D ∣ m → t^[m] = t^[D] := by
  classical
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j, i < j ∧ t^[i] = t^[j] := by
    have hni : ¬ Function.Injective (fun n : ℕ => t^[n]) := fun h =>
      Set.infinite_range_of_injective h (Set.toFinite _)
    rw [Function.not_injective_iff] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, h, hab⟩
    · exact ⟨b, a, h, hab.symm⟩
  set k := i with hk
  set l := j - i with hl
  have hl0 : 0 < l := by omega
  have hper : ∀ n, k ≤ n → t^[n + l] = t^[n] := by
    intro n hn
    have h1 : t^[k + l] = t^[k] := by
      rw [hl, show k + (j - i) = j by omega]; exact hEq.symm
    calc t^[n + l] = t^[(n - k) + (k + l)] := by rw [show (n - k) + (k + l) = n + l by omega]
      _ = t^[n - k] ∘ t^[k + l] := by rw [Function.iterate_add]
      _ = t^[n - k] ∘ t^[k] := by rw [h1]
      _ = t^[(n - k) + k] := by rw [Function.iterate_add]
      _ = t^[n] := by rw [show (n - k) + k = n by omega]
  have hmul : ∀ n, k ≤ n → ∀ c, t^[n + c * l] = t^[n] := by
    intro n hn c
    induction c with
    | zero => simp
    | succ c ih =>
        have he : n + (c + 1) * l = (n + c * l) + l := by ring
        rw [he, hper _ (by omega), ih]
  refine ⟨(k + 1) * l, by positivity, ?_⟩
  intro m hm hdvd
  obtain ⟨c, rfl⟩ := hdvd
  have hc : c ≠ 0 := by rintro rfl; simp at hm; omega
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have he : (k + 1) * l * (d + 1) = (k + 1) * l + (d * (k + 1)) * l := by ring
  rw [he]
  exact hmul _ (by nlinarith) _

/-- The bound of `iterate_stable_single`, uniformly in the self-map. -/
lemma iterate_stable_uniform (S : Type) [Finite S] :
    ∃ D, 0 < D ∧ ∀ (t : S → S) (m : ℕ), D ≤ m → D ∣ m → t^[m] = t^[D] := by
  classical
  have := Fintype.ofFinite S
  choose Dt hDt hDtspec using fun t : S → S => iterate_stable_single t
  have hP : 0 < ∏ t : S → S, Dt t := Finset.prod_pos (fun t _ => hDt t)
  refine ⟨∏ t : S → S, Dt t, hP, ?_⟩
  intro t m hm hdvd
  have hdt : Dt t ∣ ∏ t : S → S, Dt t := Finset.dvd_prod_of_mem _ (Finset.mem_univ t)
  have hle : Dt t ≤ ∏ t : S → S, Dt t := Nat.le_of_dvd hP hdt
  rw [hDtspec t m (le_trans hle hm) (hdt.trans hdvd), hDtspec t _ hle hdt]

end Transducers.Exercises
