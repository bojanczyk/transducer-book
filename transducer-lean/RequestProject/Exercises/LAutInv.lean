/-
The inverse of a code, as a letter automaton.

This is the second step of the effective form of the Uniformisation Lemma `lem:uniformisation`
of *Transducers* (M. Bojańczyk), which discharges the effectivity hypothesis of Exercise
`exer:rational-injectivity-decidable`.

Let `d` be a code all of whose transitions write at most one letter (obtained from an arbitrary
code by `Transducers.Exercises.Split.splitCode`).  Exchanging the input and the output of every
transition of `d` gives an automaton for the inverse relation, but that automaton reads nothing
on the transitions of `d` that write nothing, so it is not a letter automaton.  Those
"ε-transitions" are removed here in the usual way: a transition of the letter automaton reads a
letter `b` and consists of an ε-path followed by one transition of `d` writing `b`, and the
automaton may stop wherever an ε-path leads to a final state of `d`.

Only *finitely many* ε-paths may be used, so the ε-paths are restricted to those of length at
most the number of transitions of `d`.  This loses some pairs of the inverse relation, but it
loses no *input*: an ε-path can always be shortened to one of that length with the same
endpoints (`Transducers.LabAut.Path.exists_short`).  Keeping the domain is all that the
Uniformisation Lemma needs, since it only asks for a function inside the relation with the same
domain.
-/
import RequestProject.Exercises.LAut
import RequestProject.Exercises.SplitCode

namespace Transducers.Exercises

open Transducers

namespace LAut

/-! ## ε-paths -/

/-- The transitions of `d` that write nothing. -/
def epsTrans (d : RelCode) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  d.1.filter (fun t => decide (t.2.2.1 = []))

lemma mem_epsTrans {d : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ epsTrans d ↔ t ∈ d.1 ∧ t.2.2.1 = [] := by
  simp [epsTrans]

/-- The automaton made of the transitions of `d` that write nothing. -/
def epsAut (d : RelCode) : NFAO ℕ ℕ ℕ where
  init := ∅
  final := ∅
  δ := {t | t ∈ epsTrans d}
  δ_finite := (epsTrans d).finite_toSet

lemma path_epsAut_of_path {d : RelCode} : ∀ {p : ℕ} {ts : List (ℕ × List ℕ × List ℕ × ℕ)} {q : ℕ},
    (codeAut d).Path p ts q → NFAO.outputOf ts = [] → (epsAut d).Path p ts q := by
  intro p ts q h
  induction h with
  | nil q => intro _; exact LabAut.Path.nil q
  | @cons q u l q' ts p ht _ ih =>
      intro hout
      rw [NFAO.outputOf_cons] at hout
      have h1 : l = [] := (List.append_eq_nil_iff.1 hout).1
      have h2 : NFAO.outputOf ts = [] := (List.append_eq_nil_iff.1 hout).2
      have hmem : (q, u, l, q') ∈ (epsAut d).δ := mem_epsTrans.2 ⟨ht, h1⟩
      exact LabAut.Path.cons hmem (ih h2)

lemma relFrom_of_path_epsAut {d : RelCode} : ∀ {p : ℕ}
    {ts : List (ℕ × List ℕ × List ℕ × ℕ)} {q : ℕ},
    (epsAut d).Path p ts q → (codeAut d).relFrom p (LabAut.inputOf ts) [] q := by
  intro p ts q h
  induction h with
  | nil q => exact (codeAut d).relFrom_nil q
  | @cons q u l q' ts p ht _ ih =>
      obtain ⟨ht1, ht2⟩ := mem_epsTrans.1 ht
      have hl : l = [] := ht2
      subst hl
      have hstep := NFAO.relFrom_step (M := codeAut d) ht1 ih
      simpa using hstep

/-- One round of the ε-closure: every ε-path found so far, and every one of its extensions by
one ε-transition. -/
def epsStep (d : RelCode) (acc : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  acc ++ acc.flatMap (fun z => (epsTrans d).filterMap (fun t =>
    if t.1 = z.1 then some (t.2.2.2, z.2 ++ t.2.1) else none))

/-- The ε-paths of length at most `k` starting in `p`: the list of pairs consisting of the state
reached and of the input string read along the way. -/
def epsPaths (d : RelCode) (k p : ℕ) : List (ℕ × List ℕ) :=
  Nat.rec [(p, ([] : List ℕ))] (fun _ acc => epsStep d acc) k

@[simp] lemma epsPaths_zero (d : RelCode) (p : ℕ) : epsPaths d 0 p = [(p, [])] := rfl

@[simp] lemma epsPaths_succ (d : RelCode) (k p : ℕ) :
    epsPaths d (k + 1) p = epsStep d (epsPaths d k p) := rfl

lemma mem_epsStep_of {d : RelCode} {acc : List (ℕ × List ℕ)} {z : ℕ × List ℕ} (h : z ∈ acc) :
    z ∈ epsStep d acc := List.mem_append_left _ h

lemma mem_epsStep_extend {d : RelCode} {acc : List (ℕ × List ℕ)} {q : ℕ} {w : List ℕ}
    (hz : (q, w) ∈ acc) {t : ℕ × List ℕ × List ℕ × ℕ} (ht : t ∈ epsTrans d) (hq : t.1 = q) :
    (t.2.2.2, w ++ t.2.1) ∈ epsStep d acc := by
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨(q, w), hz, ?_⟩)
  refine List.mem_filterMap.2 ⟨t, ht, ?_⟩
  simpa using hq

lemma self_mem_epsPaths (d : RelCode) (k p : ℕ) : (p, ([] : List ℕ)) ∈ epsPaths d k p := by
  induction k with
  | zero => simp
  | succ k ih => exact mem_epsStep_of ih

lemma epsPaths_mono {d : RelCode} {k k' p : ℕ} (hk : k ≤ k') {z : ℕ × List ℕ}
    (h : z ∈ epsPaths d k p) : z ∈ epsPaths d k' p := by
  induction k' with
  | zero => rwa [Nat.le_zero.1 hk] at h
  | succ k' ih =>
      rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
      · exact mem_epsStep_of (ih (Nat.lt_succ_iff.1 hlt))
      · have : k = k' + 1 := le_antisymm hk hge
        rwa [this] at h

lemma epsPaths_sound {d : RelCode} : ∀ (k p q : ℕ) (w : List ℕ), (q, w) ∈ epsPaths d k p →
    (codeAut d).relFrom p w [] q := by
  intro k
  induction k with
  | zero =>
      intro p q w h
      simp only [epsPaths_zero, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (codeAut d).relFrom_nil _
  | succ k ih =>
      intro p q w h
      rw [epsPaths_succ, epsStep, List.mem_append] at h
      rcases h with h | h
      · exact ih p q w h
      · rw [List.mem_flatMap] at h
        obtain ⟨z, hz, h⟩ := h
        rw [List.mem_filterMap] at h
        obtain ⟨t, ht, hcond⟩ := h
        by_cases hc : t.1 = z.1
        · rw [if_pos hc] at hcond
          have e1 : t.2.2.2 = q := congrArg Prod.fst (Option.some.inj hcond)
          have e2 : z.2 ++ t.2.1 = w := congrArg Prod.snd (Option.some.inj hcond)
          obtain ⟨ht1, ht2⟩ := mem_epsTrans.1 ht
          have hpz : (codeAut d).relFrom p z.2 [] z.1 := ih p z.1 z.2 (by simpa using hz)
          have hstep : (codeAut d).relFrom z.1 t.2.1 [] t.2.2.2 := by
            have hm : (t.1, t.2.1, t.2.2.1, t.2.2.2) ∈ (codeAut d).δ := ht1
            rw [hc, ht2] at hm
            exact NFAO.relFrom_single hm
          have hcomb := NFAO.relFrom_trans hpz hstep
          rw [e2, e1] at hcomb
          simpa using hcomb
        · rw [if_neg hc] at hcond; simp at hcond

lemma inputOf_append (ts ts' : List (ℕ × List ℕ × List ℕ × ℕ)) :
    LabAut.inputOf (ts ++ ts') = LabAut.inputOf ts ++ LabAut.inputOf ts' := by
  simp [LabAut.inputOf]

lemma mem_epsPaths_of_path {d : RelCode} : ∀ (k : ℕ) {p : ℕ}
    {ts : List (ℕ × List ℕ × List ℕ × ℕ)} {q : ℕ},
    (epsAut d).Path p ts q → ts.length ≤ k → (q, LabAut.inputOf ts) ∈ epsPaths d k p := by
  intro k
  induction k with
  | zero =>
      intro p ts q h hlen
      have hts : ts = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
      subst hts
      have hpq := LabAut.Path.eq_of_nil h
      subst hpq
      simp [LabAut.inputOf]
  | succ k ih =>
      intro p ts q h hlen
      by_cases hle : ts.length ≤ k
      · exact epsPaths_mono (Nat.le_succ k) (ih h hle)
      · rcases List.eq_nil_or_concat ts with rfl | ⟨ts', t, rfl⟩
        · simp at hle
        · simp only [List.concat_eq_append] at h hlen ⊢
          obtain ⟨m, hpath₁, hpath₂⟩ := LabAut.Path.split_append h
          obtain ⟨hsrc, ht, hpath₃⟩ := LabAut.Path.cons_inv hpath₂
          have htgt : t.2.2.2 = q := LabAut.Path.eq_of_nil hpath₃
          have hlen' : ts'.length ≤ k := by
            simp only [List.length_append, List.length_singleton] at hlen
            omega
          have hrec := ih hpath₁ hlen'
          have := mem_epsStep_extend (d := d) hrec ht hsrc
          rw [htgt] at this
          rw [epsPaths_succ, inputOf_append]
          simpa using this

/-- The bound on the length of the ε-paths that are used. -/
def epsBound (d : RelCode) : ℕ := d.1.length

/-- **Every ε-path can be replaced by one of the bounded length**, with the same endpoints. -/
lemma exists_mem_epsPaths {d : RelCode} {p q : ℕ} {w : List ℕ}
    (h : (codeAut d).relFrom p w [] q) : ∃ w', (q, w') ∈ epsPaths d (epsBound d) p := by
  obtain ⟨ts, hpath, -, hout⟩ := h
  have heps := path_epsAut_of_path hpath hout
  set S : List ℕ := p :: (epsTrans d).map (fun t => t.2.2.2) with hS
  have hSmem : ∀ t ∈ (epsAut d).δ, t.2.2.2 ∈ S := by
    intro t ht
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨t, ht, rfl⟩)
  obtain ⟨ts', hpath', hlen'⟩ := LabAut.Path.exists_short S hSmem heps (by simp [hS])
  have hSlen : S.length ≤ epsBound d + 1 := by
    have hfl : (epsTrans d).length ≤ d.1.length := List.length_filter_le _ _
    simp only [hS, List.length_cons, List.length_map, epsBound]
    omega
  exact ⟨LabAut.inputOf ts', mem_epsPaths_of_path (epsBound d) hpath' (by omega)⟩

/-! ## The inverse letter automaton -/

/-- The states of a code. -/
def sts (d : RelCode) : List ℕ := d.2.1 ++ d.1.map (fun t => t.1) ++ d.1.map (fun t => t.2.2.2)

lemma mem_sts_init {d : RelCode} {q : ℕ} (h : q ∈ d.2.1) : q ∈ sts d := by
  simp [sts, h]

lemma mem_sts_target {d : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ d.1) :
    t.2.2.2 ∈ sts d := by
  simp only [sts, List.mem_append, List.mem_map]
  exact Or.inr ⟨t, h, rfl⟩

/-- The transitions of the inverse letter automaton: an ε-path from `p` to the source of a
transition of `d` writing one letter, followed by that transition. -/
def invTrans (d : RelCode) : List (ℕ × ℕ × List ℕ × ℕ) :=
  (sts d).flatMap (fun p =>
    (epsPaths d (epsBound d) p).flatMap (fun z =>
      d.1.flatMap (fun t =>
        if t.1 = z.1 ∧ t.2.2.1.length = 1 then
          [(p, t.2.2.1.headD 0, z.2 ++ t.2.1, t.2.2.2)] else [])))

/-- The terminal entries of the inverse letter automaton: an ε-path from `p` to a final state
of `d`. -/
def invTerm (d : RelCode) : List (ℕ × List ℕ) :=
  (sts d).flatMap (fun p =>
    (epsPaths d (epsBound d) p).flatMap (fun z => if z.1 ∈ d.2.2 then [(p, z.2)] else []))

/-- **The inverse of a code, as a letter automaton.** -/
def invLCode (d : RelCode) : LCode := (invTrans d, d.2.1, invTerm d)

lemma mem_invTrans {d : RelCode} {tr : ℕ × ℕ × List ℕ × ℕ} (h : tr ∈ invTrans d) :
    ∃ (p q b : ℕ) (w₀ : List ℕ) (t : ℕ × List ℕ × List ℕ × ℕ),
      (q, w₀) ∈ epsPaths d (epsBound d) p ∧ t ∈ d.1 ∧ t.1 = q ∧ t.2.2.1 = [b] ∧
        tr = (p, b, w₀ ++ t.2.1, t.2.2.2) := by
  rw [invTrans, List.mem_flatMap] at h
  obtain ⟨p, -, h⟩ := h
  rw [List.mem_flatMap] at h
  obtain ⟨z, hz, h⟩ := h
  rw [List.mem_flatMap] at h
  obtain ⟨t, ht, h⟩ := h
  by_cases hc : t.1 = z.1 ∧ t.2.2.1.length = 1
  · rw [if_pos hc, List.mem_singleton] at h
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hc.2
    exact ⟨p, z.1, t.2.2.1.headD 0, z.2, t, by simpa using hz, ht, hc.1, by rw [hb]; simp, h⟩
  · rw [if_neg hc] at h; simp at h

lemma mem_invTrans_of {d : RelCode} {p q b : ℕ} {w₀ : List ℕ} {t : ℕ × List ℕ × List ℕ × ℕ}
    (hp : p ∈ sts d) (hz : (q, w₀) ∈ epsPaths d (epsBound d) p) (ht : t ∈ d.1) (h1 : t.1 = q)
    (h2 : t.2.2.1 = [b]) : (p, b, w₀ ++ t.2.1, t.2.2.2) ∈ invTrans d := by
  refine List.mem_flatMap.2 ⟨p, hp, List.mem_flatMap.2 ⟨(q, w₀), hz, ?_⟩⟩
  refine List.mem_flatMap.2 ⟨t, ht, ?_⟩
  have hcond : t.1 = ((q, w₀) : ℕ × List ℕ).1 ∧ t.2.2.1.length = 1 := ⟨h1, by rw [h2]; simp⟩
  rw [if_pos hcond, h2]
  simp

lemma mem_invTerm_of {d : RelCode} {p q : ℕ} {w₀ : List ℕ} (hp : p ∈ sts d)
    (hz : (q, w₀) ∈ epsPaths d (epsBound d) p) (hq : q ∈ d.2.2) : (p, w₀) ∈ invTerm d := by
  refine List.mem_flatMap.2 ⟨p, hp, List.mem_flatMap.2 ⟨(q, w₀), hz, ?_⟩⟩
  simpa using hq

lemma mem_invTerm {d : RelCode} {tr : ℕ × List ℕ} (h : tr ∈ invTerm d) :
    ∃ q ∈ d.2.2, (q, tr.2) ∈ epsPaths d (epsBound d) tr.1 := by
  rw [invTerm, List.mem_flatMap] at h
  obtain ⟨p, -, h⟩ := h
  rw [List.mem_flatMap] at h
  obtain ⟨z, hz, h⟩ := h
  by_cases hc : z.1 ∈ d.2.2
  · rw [if_pos hc, List.mem_singleton] at h
    subst h
    exact ⟨z.1, hc, by simpa using hz⟩
  · rw [if_neg hc] at h; simp at h

/-! ## Soundness -/

lemma exists_index {α : Type} {l : List α} {a : α} (h : a ∈ l) : ∃ i : ℕ, l[i]? = some a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, by rw [List.getElem?_eq_getElem hi]⟩

lemma pathFrom_invLCode_sound {d : RelCode} : ∀ (v is : List ℕ) (p r : ℕ) (u : List ℕ),
    pathFrom (invLCode d) p v is = some (r, u) → (codeAut d).relFrom p u v r := by
  intro v
  induction v with
  | nil =>
      intro is p r u h
      match is with
      | [] =>
          rw [pathFrom] at h
          have hr : p = r := congrArg Prod.fst (Option.some.inj h)
          have hu : ([] : List ℕ) = u := congrArg Prod.snd (Option.some.inj h)
          subst hr; subst hu
          exact (codeAut d).relFrom_nil _
      | _ :: _ => simp [pathFrom] at h
  | cons b v ih =>
      intro is p r u h
      match is with
      | [] => simp [pathFrom] at h
      | i :: is =>
          rw [pathFrom_cons_cons] at h
          cases hstep : step (invLCode d) p b i with
          | none => rw [hstep] at h; simp at h
          | some z =>
              rw [hstep, Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨z', hz', hzeq⟩ := h
              have hr : z'.1 = r := congrArg Prod.fst hzeq
              have hu : z.2 ++ z'.2 = u := congrArg Prod.snd hzeq
              rw [step, Option.bind_eq_some_iff] at hstep
              obtain ⟨tr, htr, hcond⟩ := hstep
              by_cases hc : tr.1 = p ∧ tr.2.1 = b
              · rw [if_pos hc] at hcond
                have hz1 : tr.2.2.2 = z.1 := congrArg Prod.fst (Option.some.inj hcond)
                have hz2 : tr.2.2.1 = z.2 := congrArg Prod.snd (Option.some.inj hcond)
                obtain ⟨p', q, b', w₀, t, hzs, ht, h1, h2, heq⟩ :=
                  mem_invTrans (List.mem_of_getElem? htr)
                subst heq
                obtain ⟨hp', hb'⟩ := hc
                simp only at hp' hb' hz1 hz2
                subst hp'; subst hb'
                have hpq : (codeAut d).relFrom p' w₀ [] q := epsPaths_sound _ _ _ _ hzs
                have htq : (codeAut d).relFrom q t.2.1 [b'] t.2.2.2 := by
                  have hm : (t.1, t.2.1, t.2.2.1, t.2.2.2) ∈ (codeAut d).δ := ht
                  rw [h1, h2] at hm
                  exact NFAO.relFrom_single hm
                have hrec : (codeAut d).relFrom z.1 z'.2 v r := by
                  have hh := ih is z.1 z'.1 z'.2 hz'
                  rw [hr] at hh
                  exact hh
                have hcomb := NFAO.relFrom_trans (NFAO.relFrom_trans hpq htq)
                  (show (codeAut d).relFrom t.2.2.2 z'.2 v r by rw [hz1]; exact hrec)
                rw [← hu, ← hz2]
                simpa using hcomb
              · rw [if_neg hc] at hcond; simp at hcond

/-- **The inverse letter automaton computes a subrelation of the inverse relation.** -/
theorem invLCode_sound {d : RelCode} {v u : List ℕ} (h : rel (invLCode d) v u) :
    codeRel d u v := by
  obtain ⟨j, p, k, is, hj, hacc⟩ := h
  rw [accFrom, Option.bind_eq_some_iff] at hacc
  obtain ⟨z, hz, he⟩ := hacc
  rw [Option.map_eq_some_iff] at he
  obtain ⟨e, he, hue⟩ := he
  have hpath : (codeAut d).relFrom p z.2 v z.1 := pathFrom_invLCode_sound v is p z.1 z.2 hz
  rw [term, Option.bind_eq_some_iff] at he
  obtain ⟨tr, htr, hcond⟩ := he
  by_cases hc : tr.1 = z.1
  · rw [if_pos hc] at hcond
    have hte : tr.2 = e := Option.some.inj hcond
    obtain ⟨q, hq, hzs⟩ := mem_invTerm (List.mem_of_getElem? htr)
    rw [hc, hte] at hzs
    have hend : (codeAut d).relFrom z.1 e [] q := epsPaths_sound _ _ _ _ hzs
    refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨p, List.mem_of_getElem? hj, q, hq, ?_⟩
    have hcomb := NFAO.relFrom_trans hpath hend
    rw [← hue]
    simpa using hcomb
  · rw [if_neg hc] at hcond; simp at hcond

/-! ## The domain is preserved -/

/-- **Decomposition of a run at its first transition that writes a letter.** -/
lemma relFrom_decompose {d : RelCode} (hd : ∀ tr ∈ d.1, tr.2.2.1.length ≤ 1) {f : ℕ}
    {s : ℕ} {u v : List ℕ} (h : (codeAut d).relFrom s u v f) :
    ∀ b v', v = b :: v' → ∃ (q : ℕ) (u₁ : List ℕ) (t : ℕ × List ℕ × List ℕ × ℕ) (u₃ : List ℕ),
      (codeAut d).relFrom s u₁ [] q ∧ t ∈ d.1 ∧ t.1 = q ∧ t.2.2.1 = [b] ∧
        (codeAut d).relFrom t.2.2.2 u₃ v' f ∧ u = u₁ ++ (t.2.1 ++ u₃) := by
  refine NFAO.relFrom_induction (M := codeAut d)
    (motive := fun s u v => ∀ b v', v = b :: v' →
      ∃ (q : ℕ) (u₁ : List ℕ) (t : ℕ × List ℕ × List ℕ × ℕ) (u₃ : List ℕ),
        (codeAut d).relFrom s u₁ [] q ∧ t ∈ d.1 ∧ t.1 = q ∧ t.2.2.1 = [b] ∧
          (codeAut d).relFrom t.2.2.2 u₃ v' f ∧ u = u₁ ++ (t.2.1 ++ u₃)) ?_ ?_ h
  · intro b v' hv; simp at hv
  · intro q q' u₀ x w v ht hrel ih b v' hv
    have hlen : x.length ≤ 1 := hd (q, u₀, x, q') ht
    match x with
    | [] =>
        rw [List.nil_append] at hv
        obtain ⟨q₂, u₁, t, u₃, hq₂, ht₂, h1, h2, h3, h4⟩ := ih b v' hv
        refine ⟨q₂, u₀ ++ u₁, t, u₃, ?_, ht₂, h1, h2, h3, by rw [h4]; simp⟩
        have hs := NFAO.relFrom_step (M := codeAut d) ht hq₂
        simpa using hs
    | [b₀] =>
        have hb : b₀ = b := by
          have hh := congrArg (fun l : List ℕ => l.head?) hv
          simpa using hh
        have hv' : v = v' := by
          have hh := congrArg (fun l : List ℕ => l.tail) hv
          simpa using hh
        subst hb; subst hv'
        exact ⟨q, [], (q, u₀, [b₀], q'), w, (codeAut d).relFrom_nil q, ht, rfl, rfl, hrel, by simp⟩
    | _ :: _ :: _ => simp at hlen

lemma dom_invLCode_from {d : RelCode} (hd : ∀ tr ∈ d.1, tr.2.2.1.length ≤ 1) {f : ℕ}
    (hf : f ∈ d.2.2) : ∀ (v : List ℕ) (p : ℕ) (u : List ℕ), p ∈ sts d →
      (codeAut d).relFrom p u v f → ∃ (is : List ℕ) (k : ℕ) (u' : List ℕ),
        accFrom (invLCode d) p v is k = some u' := by
  intro v
  induction v with
  | nil =>
      intro p u hp h
      obtain ⟨w', hw'⟩ := exists_mem_epsPaths h
      obtain ⟨k, hk⟩ := exists_index (mem_invTerm_of hp hw' hf)
      have hterm : term (invLCode d) p k = some w' := by simp [term, invLCode, hk]
      exact ⟨[], k, w', by simp [accFrom, pathFrom, hterm]⟩
  | cons b v ih =>
      intro p u hp h
      obtain ⟨q, u₁, t, u₃, hq, ht, h1, h2, h3, -⟩ := relFrom_decompose hd h b v rfl
      obtain ⟨w₀, hw₀⟩ := exists_mem_epsPaths hq
      obtain ⟨i, hi⟩ := exists_index (mem_invTrans_of hp hw₀ ht h1 h2)
      obtain ⟨is, k, u', hacc⟩ := ih t.2.2.2 u₃ (mem_sts_target ht) h3
      have hstep : step (invLCode d) p b i = some (t.2.2.2, w₀ ++ t.2.1) := by
        simp [step, invLCode, hi]
      rw [accFrom, Option.bind_eq_some_iff] at hacc
      obtain ⟨z, hz, he⟩ := hacc
      rw [Option.map_eq_some_iff] at he
      obtain ⟨e, he1, he2⟩ := he
      exact ⟨i :: is, k, (w₀ ++ t.2.1) ++ (z.2 ++ e),
        by simp [accFrom, pathFrom_cons_cons, hstep, hz, he1]⟩

/-- **The inverse letter automaton has the whole range of the code as its domain.** -/
theorem invLCode_dom {d : RelCode} (hd : ∀ tr ∈ d.1, tr.2.2.1.length ≤ 1) {u v : List ℕ}
    (h : codeRel d u v) : dom (invLCode d) v := by
  obtain ⟨p, hp, f, hf, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
  obtain ⟨j, hj⟩ := exists_index (l := d.2.1) hp
  obtain ⟨is, k, u', hacc⟩ := dom_invLCode_from hd hf v p u (mem_sts_init hp) hrel
  exact ⟨u', j, p, k, is, hj, hacc⟩

end LAut

end Transducers.Exercises
