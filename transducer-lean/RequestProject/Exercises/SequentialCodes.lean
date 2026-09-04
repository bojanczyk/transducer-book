/-
Sequential transducers as codes: the machinery needed to build instances of the promise
problem of Exercise `exer:rational-composition-finiteness-undecidable`.
-/
import RequestProject.Exercises.IterateFiniteness

/-!
# Deterministic letter-reading transducers as codes

A *sequential transducer* over the alphabet `{0, …, a-1}` with states `{0, …, m-1}` is given by a
transition function `f : ℕ → ℕ → ℕ × List ℕ`: reading the letter `x` in the state `q` moves the
automaton to the state `(f q x).1` and writes the string `(f q x).2`.  Such a transducer reads
every string over its alphabet, deterministically, so the relation it describes is a function.

This file turns that data into a `Transducers.RelCode` (`Transducers.Exercises.seqCode`),
identifies the relation it describes (`Transducers.Exercises.codeRel_seqCode`), and shows that the
code satisfies the promise `Transducers.Exercises.CodeSelfMap` of the exercise as soon as the
outputs of `f` are strings over the alphabet.  The induced map on the strings over the alphabet is
the obvious one, `Transducers.Exercises.seqMap`.

The point of the file is that it reduces the construction of an instance of the exercise to the
construction of a finite transition table: everything about codes, paths and promises is done
once and for all here.
-/

namespace Transducers.Exercises

open Transducers

/-! ## The transducer and the function it computes -/

/-- The function computed by a sequential transducer started in the state `q`: the resulting
state, together with the concatenation of the strings written along the way. -/
def seqRun (f : ℕ → ℕ → ℕ × List ℕ) : ℕ → List ℕ → ℕ × List ℕ
  | q, [] => (q, [])
  | q, x :: w => ((seqRun f (f q x).1 w).1, (f q x).2 ++ (seqRun f (f q x).1 w).2)

@[simp] lemma seqRun_nil (f : ℕ → ℕ → ℕ × List ℕ) (q : ℕ) : seqRun f q [] = (q, []) := rfl

@[simp] lemma seqRun_cons (f : ℕ → ℕ → ℕ × List ℕ) (q x : ℕ) (w : List ℕ) :
    seqRun f q (x :: w) =
      ((seqRun f (f q x).1 w).1, (f q x).2 ++ (seqRun f (f q x).1 w).2) := rfl

/-- The transitions of the code of a sequential transducer: one transition for each state below
`m` and each letter below `a`. -/
def seqTrans (m a : ℕ) (f : ℕ → ℕ → ℕ × List ℕ) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  (List.range m).flatMap fun q => (List.range a).map fun x => (q, [x], (f q x).2, (f q x).1)

/-- The code of a sequential transducer: the initial state is `0`, and every state below `m` is
final, so that every string over the alphabet is read. -/
def seqCode (m a : ℕ) (f : ℕ → ℕ → ℕ × List ℕ) : RelCode :=
  (seqTrans m a f, ([0], List.range m))

lemma mem_seqTrans {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ seqTrans m a f ↔ ∃ q < m, ∃ x < a, t = (q, [x], (f q x).2, (f q x).1) := by
  simp [seqTrans, eq_comm]

lemma mem_delta_seqTrans {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} {q x : ℕ}
    (hq : q < m) (hx : x < a) :
    (q, [x], (f q x).2, (f q x).1) ∈ (codeAut (seqCode m a f)).δ :=
  mem_seqTrans.2 ⟨q, hq, x, hx, rfl⟩

/-- The alphabet of the code of a sequential transducer is `{0, …, a-1}`. -/
lemma mem_codeAlphabet_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m) {y : ℕ} :
    y ∈ codeAlphabet (seqCode m a f) ↔ y < a := by
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := List.mem_flatMap.1 hy
    have ht' : t ∈ seqTrans m a f := ht
    obtain ⟨q, -, x, hx, rfl⟩ := mem_seqTrans.1 ht'
    simp only [List.mem_singleton] at hyt
    exact hyt ▸ hx
  · intro hy
    refine List.mem_flatMap.2 ⟨(0, [y], (f 0 y).2, (f 0 y).1), ?_, by simp⟩
    exact mem_seqTrans.2 ⟨0, hm, y, hy, rfl⟩

lemma codeWord_seqCode_iff {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m) {w : List ℕ} :
    CodeWord (seqCode m a f) w ↔ ∀ x ∈ w, x < a := by
  simp [CodeWord, mem_codeAlphabet_seqCode hm]

/-! ## The relation described by the code -/

/-- Every path of the code of a sequential transducer is a run of the transducer. -/
lemma seqRun_of_relFrom {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} {q p : ℕ} {w v : List ℕ}
    (h : (codeAut (seqCode m a f)).relFrom q w v p) : seqRun f q w = (p, v) := by
  refine NFAO.relFrom_induction (M := codeAut (seqCode m a f))
    (motive := fun q w v => seqRun f q w = (p, v)) rfl ?_ h
  rintro q q' u x w v ht - ih
  have ht' : (q, u, x, q') ∈ seqTrans m a f := ht
  obtain ⟨q₀, -, y, -, heq⟩ := mem_seqTrans.1 ht'
  obtain ⟨rfl, rfl, rfl, rfl⟩ : q₀ = q ∧ [y] = u ∧ (f q₀ y).2 = x ∧ (f q₀ y).1 = q' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Prod.ext_iff] at heq <;> tauto
  simp [ih]

/-- The runs of a sequential transducer are paths of its code. -/
lemma relFrom_seqRun {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ}
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) :
    ∀ {q : ℕ} {w : List ℕ}, q < m → (∀ x ∈ w, x < a) →
      (codeAut (seqCode m a f)).relFrom q w (seqRun f q w).2 (seqRun f q w).1 := by
  intro q w
  induction w generalizing q with
  | nil => intro _ _; simpa using NFAO.relFrom_nil _ q
  | cons x w ih =>
      intro hq hw
      have hx : x < a := hw x (by simp)
      have hw' : ∀ y ∈ w, y < a := fun y hy => hw y (by simp [hy])
      have := NFAO.relFrom_step (mem_delta_seqTrans (f := f) hq hx)
        (ih (hf q hq x hx) hw')
      simpa using this

/-- The states reached by a sequential transducer stay below `m`. -/
lemma seqRun_state_lt {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ}
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) :
    ∀ {q : ℕ} {w : List ℕ}, q < m → (∀ x ∈ w, x < a) → (seqRun f q w).1 < m := by
  intro q w
  induction w generalizing q with
  | nil => intro hq _; simpa using hq
  | cons x w ih =>
      intro hq hw
      have hx : x < a := hw x (by simp)
      exact ih (hf q hq x hx) (fun y hy => hw y (by simp [hy]))

/-- **The relation described by the code of a sequential transducer**: on the strings over its
alphabet it is the function computed by the transducer from its initial state. -/
lemma codeRel_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) {w v : List ℕ} (hw : ∀ x ∈ w, x < a) :
    codeRel (seqCode m a f) w v ↔ v = (seqRun f 0 w).2 := by
  constructor
  · rintro hrel
    rw [codeRel, NFAO.rel_iff_relFrom] at hrel
    obtain ⟨q, hq, p, -, hpath⟩ := hrel
    have hq0 : q = 0 := by simpa [codeAut, seqCode] using hq
    subst hq0
    have := seqRun_of_relFrom hpath
    simpa using congrArg Prod.snd this.symm
  · rintro rfl
    rw [codeRel, NFAO.rel_iff_relFrom]
    refine ⟨0, by simp [codeAut, seqCode], (seqRun f 0 w).1, ?_, relFrom_seqRun hf hm hw⟩
    simpa [codeAut, seqCode] using seqRun_state_lt hf hm hw

/-! ## The promise of the exercise -/

/-- The map on strings computed by a sequential transducer. -/
def seqMap (f : ℕ → ℕ → ℕ × List ℕ) (w : List ℕ) : List ℕ := (seqRun f 0 w).2

/-- The code of a sequential transducer describes a function on the strings over its alphabet. -/
lemma codeFunctional_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) : CodeFunctional (seqCode m a f) := by
  intro w hw
  rw [codeWord_seqCode_iff hm] at hw
  exact ⟨seqMap f w, (codeRel_seqCode hm hf hw).2 rfl, fun v hv => (codeRel_seqCode hm hf hw).1 hv⟩

/-- The output of a run is a string over the alphabet, as soon as the strings written by the
transducer are. -/
lemma seqRun_output_lt {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ}
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) (hout : ∀ q < m, ∀ x < a, ∀ y ∈ (f q x).2, y < a) :
    ∀ (w : List ℕ) (q : ℕ), q < m → (∀ x ∈ w, x < a) → ∀ y ∈ (seqRun f q w).2, y < a := by
  intro w
  induction w with
  | nil => intro q _ _ y hy; simp at hy
  | cons x w ih =>
      intro q hq hw y hy
      have hx : x < a := hw x (by simp)
      have hw' : ∀ z ∈ w, z < a := fun z hz => hw z (by simp [hz])
      rw [seqRun_cons] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hout q hq x hx y hy
      · exact ih (f q x).1 (hf q hq x hx) hw' y hy

/-- **The code of a sequential transducer can be iterated** as soon as the strings it writes are
strings over its alphabet. -/
theorem codeSelfMap_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) (hout : ∀ q < m, ∀ x < a, ∀ y ∈ (f q x).2, y < a) :
    CodeSelfMap (seqCode m a f) := by
  refine ⟨codeFunctional_seqCode hm hf, ?_⟩
  intro w v hw hrel
  rw [codeWord_seqCode_iff hm] at hw ⊢
  rw [codeRel_seqCode hm hf hw] at hrel
  subst hrel
  exact seqRun_output_lt hf hout w 0 hm hw

/-- The map that the code of a sequential transducer induces on the strings over its alphabet is
`seqMap`. -/
lemma codeSelfFun_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) (h : CodeSelfMap (seqCode m a f))
    (w : {w : List ℕ // CodeWord (seqCode m a f) w}) :
    (codeSelfFun h w).1 = seqMap f w.1 := by
  have hw : ∀ x ∈ w.1, x < a := (codeWord_seqCode_iff hm).1 w.2
  have := (h.1 w.1 w.2).choose_spec.1
  exact (codeRel_seqCode hm hf hw).1 this

/-! ## The problem of the exercise, on a sequential transducer -/

/-- Iterating the map induced by the code is iterating `seqMap`. -/
lemma iterate_codeSelfFun_seqCode {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) (h : CodeSelfMap (seqCode m a f)) :
    ∀ (n : ℕ) (w : {w : List ℕ // CodeWord (seqCode m a f) w}),
      ((codeSelfFun h)^[n] w).1 = (seqMap f)^[n] w.1 := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        codeSelfFun_seqCode hm hf h w]

/-- **The problem of the exercise for the code of a sequential transducer**: the set of iterates
is finite exactly when the map computed by the transducer is eventually periodic on all strings
over its alphabet at once. -/
theorem codeIteratesFinite_seqCode_iff {m a : ℕ} {f : ℕ → ℕ → ℕ × List ℕ} (hm : 0 < m)
    (hf : ∀ q < m, ∀ x < a, (f q x).1 < m) (hout : ∀ q < m, ∀ x < a, ∀ y ∈ (f q x).2, y < a) :
    CodeIteratesFinite (seqCode m a f) ↔ ∃ n k : ℕ, 1 ≤ k ∧ ∀ w : List ℕ, (∀ x ∈ w, x < a) →
      (seqMap f)^[n] w = (seqMap f)^[n + k] w := by
  have h : CodeSelfMap (seqCode m a f) := codeSelfMap_seqCode hm hf hout
  rw [codeIteratesFinite_iff_uniform h]
  constructor
  · rintro ⟨n, k, hk, hiter⟩
    refine ⟨n, k, hk, fun w hw => ?_⟩
    have hW : CodeWord (seqCode m a f) w := (codeWord_seqCode_iff hm).2 hw
    have := congrArg Subtype.val (hiter ⟨w, hW⟩)
    rwa [iterate_codeSelfFun_seqCode hm hf h, iterate_codeSelfFun_seqCode hm hf h] at this
  · rintro ⟨n, k, hk, hiter⟩
    refine ⟨n, k, hk, fun w => Subtype.ext ?_⟩
    rw [iterate_codeSelfFun_seqCode hm hf h, iterate_codeSelfFun_seqCode hm hf h]
    exact hiter w.1 ((codeWord_seqCode_iff hm).1 w.2)

/-! ## Computability of the code -/

/-- **The code of a sequential transducer is computable in the transducer.**  A family of
transition tables that is primitive recursive in a parameter therefore yields a computable family
of codes, which is what a reduction to the problem of the exercise has to produce. -/
theorem primrec_seqCode {α : Type} [Primcodable α] {m a : α → ℕ} {f : α → ℕ → ℕ → ℕ × List ℕ}
    (hm : Primrec m) (ha : Primrec a)
    (hf : Primrec fun p : (α × ℕ) × ℕ => f p.1.1 p.1.2 p.2) :
    Primrec fun e => seqCode (m e) (a e) (f e) := by
  have hbody : Primrec fun p : (α × ℕ) × ℕ =>
      (p.1.2, [p.2], (f p.1.1 p.1.2 p.2).2, (f p.1.1 p.1.2 p.2).1) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ)))
        (Primrec.pair (Primrec.snd.comp hf) (Primrec.fst.comp hf)))
  have hinner : Primrec fun p : α × ℕ =>
      (List.range (a p.1)).map fun x => (p.2, [x], (f p.1 p.2 x).2, (f p.1 p.2 x).1) :=
    Primrec.list_map (Primrec.list_range.comp (ha.comp Primrec.fst)) hbody
  have htrans : Primrec fun e => seqTrans (m e) (a e) (f e) :=
    Primrec.list_flatMap (Primrec.list_range.comp hm) hinner
  have hfinal : Primrec fun e => (([0] : List ℕ), List.range (m e)) :=
    Primrec.pair (Primrec.const ([0] : List ℕ)) (Primrec.list_range.comp hm)
  exact Primrec.pair htrans hfinal

/-! ## An example: deleting the first letter

The transducer with two states over the two-letter alphabet which skips the first letter of its
input and copies the rest.  Its `n`-th iterate deletes the first `n` letters, so no two iterates
agree: a string of length `n + k` is a witness.  This is the mechanism by which the set of
iterates of a code is infinite — arbitrarily long strings have arbitrarily long transients — and
it is the mechanism a reduction has to control; see the docstring of
`Transducers.Exercises.IteratesReduction`. -/

/-- The transition function of the transducer which deletes the first letter: in the state `0` it
writes nothing, in the state `1` it copies. -/
def tailFun (q x : ℕ) : ℕ × List ℕ := if q = 0 then (1, []) else (1, [x])

lemma seqRun_tailFun_one (w : List ℕ) : seqRun tailFun 1 w = (1, w) := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [seqRun_cons, tailFun, ih]

@[simp] lemma seqMap_tailFun (w : List ℕ) : seqMap tailFun w = w.tail := by
  cases w with
  | nil => rfl
  | cons x w => simp [seqMap, seqRun_cons, tailFun, seqRun_tailFun_one]

lemma iterate_seqMap_tailFun (n : ℕ) (w : List ℕ) : (seqMap tailFun)^[n] w = w.drop n := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, seqMap_tailFun, ih, ← List.drop_one, List.drop_drop]
      congr 1
      omega

lemma codeSelfMap_tailCode : CodeSelfMap (seqCode 2 2 tailFun) := by
  refine codeSelfMap_seqCode (by norm_num) (fun q _ x _ => ?_) (fun q _ x hx y hy => ?_)
  · by_cases h : q = 0 <;> simp [tailFun, h]
  · by_cases h : q = 0
    · simp [tailFun, h] at hy
    · simp only [tailFun, if_neg h, List.mem_singleton] at hy
      exact hy ▸ hx

/-- The set of iterates of the code that deletes the first letter is infinite. -/
theorem not_codeIteratesFinite_tailCode : ¬ CodeIteratesFinite (seqCode 2 2 tailFun) := by
  rw [codeIteratesFinite_seqCode_iff (by norm_num) (fun q _ x _ => by
      by_cases h : q = 0 <;> simp [tailFun, h])
    (fun q _ x hx y hy => by
      by_cases h : q = 0
      · simp [tailFun, h] at hy
      · simp only [tailFun, if_neg h, List.mem_singleton] at hy
        exact hy ▸ hx)]
  rintro ⟨n, k, hk, hiter⟩
  have hw : ∀ x ∈ List.replicate (n + k) (0 : ℕ), x < 2 := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    norm_num
  have := hiter (List.replicate (n + k) 0) hw
  rw [iterate_seqMap_tailFun, iterate_seqMap_tailFun, List.drop_replicate,
    List.drop_replicate] at this
  have hlen := congrArg List.length this
  simp only [List.length_replicate] at hlen
  omega

/-! ## What is left of the hypothesis of the exercise -/

/-- **The hypothesis `IteratesReduction` in elementary terms.**  A family of sequential
transducers, primitive recursive in the index `e`, whose states and outputs stay inside their
alphabets, and whose induced maps on strings are eventually periodic — uniformly in the string —
exactly for the indices in the acceptance problem `Acceptance.ATM`, gives the hypothesis of
Exercise `exer:rational-composition-finiteness-undecidable`.

So nothing about codes, paths, promises or computability is missing any more: what remains is a
finite transition table for each `e`, and the combinatorial statement `hred` about it. -/
theorem iteratesReduction_of_seq_family {m a : ℕ → ℕ} {f : ℕ → ℕ → ℕ → ℕ × List ℕ}
    (hm : Primrec m) (ha : Primrec a)
    (hf : Primrec fun p : (ℕ × ℕ) × ℕ => f p.1.1 p.1.2 p.2)
    (hpos : ∀ e, 0 < m e)
    (hstate : ∀ e, ∀ q < m e, ∀ x < a e, (f e q x).1 < m e)
    (hout : ∀ e, ∀ q < m e, ∀ x < a e, ∀ y ∈ (f e q x).2, y < a e)
    (hred : ∀ e, (∃ n k : ℕ, 1 ≤ k ∧ ∀ w : List ℕ, (∀ x ∈ w, x < a e) →
        (seqMap (f e))^[n] w = (seqMap (f e))^[n + k] w) ↔ e ∈ Acceptance.ATM) :
    IteratesReduction := by
  refine iteratesReduction_of_atm_reduction (fun e => seqCode (m e) (a e) (f e))
    (primrec_seqCode hm ha hf).to_comp fun e => ?_
  exact ⟨codeSelfMap_seqCode (hpos e) (hstate e) (hout e),
    (codeIteratesFinite_seqCode_iff (hpos e) (hstate e) (hout e)).trans (hred e)⟩

end Transducers.Exercises
