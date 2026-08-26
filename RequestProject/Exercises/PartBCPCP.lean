/-
The reduction from the Post correspondence problem used by the solution to Exercise
`exer:rational-relations-intersection-undecidable` of *Transducers* (M. Bojańczyk): it is
undecidable whether two rational relations have a nonempty intersection.

As in the main text (Theorem `thm:undecidable-equivalence-rational-relations`, whose reduction is in
`RequestProject/PartB/PCPRed.lean`), a decision problem about rational relations is a problem about
their finite descriptions, the codes `Transducers.RelCode` of `RequestProject/PartB/Codes.lean`, and
the undecidability of the Post correspondence problem itself is not proved but is taken as an
explicit hypothesis.

The same file also carries the reduction used by item (a) of Exercise
`exer:decide-rational-colision`: it is undecidable whether two rational *functions* have a common
output on a common input.  There the two homomorphisms must be made total, and must be made to
differ on the empty input, which is what the extra transition of `funCode` does.

The reduction is the author's.  A homomorphism `g : A* → B*`, viewed as the relation
`{(w, g w) | w ≠ ε}`, is computed by the two-state automaton that reads a letter `i` and writes
`g i` on every transition; the two states are used only to rule out the empty input.  The
intersection of the two relations obtained from the two homomorphisms of an instance of the Post
correspondence problem is nonempty exactly when the instance is solvable.
-/
import RequestProject.PartB.PCPRed

namespace Transducers
namespace Exercises

open PCP

/-! ## The automaton of a homomorphism -/

/-- The transitions of the automaton computing the graph of the homomorphism `i ↦ ws[i]` on
nonempty inputs: from the initial state `0` and from the final state `1`, reading the letter `i`
and writing `ws[i]` leads to `1`. -/
def homTrans (ws : List (List ℕ)) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  (List.range ws.length).flatMap fun i =>
    [(0, [i], ws.getD i [], 1), (1, [i], ws.getD i [], 1)]

/-- The code of the automaton computing the graph of the homomorphism `i ↦ ws[i]` on nonempty
inputs. -/
def homCode (ws : List (List ℕ)) : RelCode := (homTrans ws, ([0], [1]))

lemma mem_homTrans {ws : List (List ℕ)} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ homTrans ws ↔ ∃ i < ws.length,
      t = (0, [i], ws.getD i [], 1) ∨ t = (1, [i], ws.getD i [], 1) := by
  simp [homTrans]

/-- Every path of the automaton that ends in the final state reads a string of letters that are
indices of `ws`, writes its homomorphic image, and is nonempty when it starts in the initial
state. -/
lemma relFrom_homCode_to_one (ws : List (List ℕ)) {q : ℕ} {w v : List ℕ}
    (h : (codeAut (homCode ws)).relFrom q w v 1) :
    (∀ i ∈ w, i < ws.length) ∧ v = conc ws w ∧ (q = 0 → w ≠ []) := by
  refine NFAO.relFrom_induction (M := codeAut (homCode ws))
    (motive := fun q w v => (∀ i ∈ w, i < ws.length) ∧ v = conc ws w ∧ (q = 0 → w ≠ []))
    ⟨by simp, rfl, by simp⟩ ?_ h
  rintro q q' u x w v ht - ⟨hgood, hconc, -⟩
  have ht' : (q, u, x, q') ∈ homTrans ws := ht
  obtain ⟨i, hi, hcase⟩ := mem_homTrans.1 ht'
  have hu : u = [i] ∧ x = ws.getD i [] := by
    rcases hcase with h | h <;> exact ⟨congrArg (fun t => t.2.1) h, congrArg (fun t => t.2.2.1) h⟩
  obtain ⟨rfl, rfl⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rcases List.mem_cons.1 (by simpa using hj) with rfl | hj'
    · exact hi
    · exact hgood j hj'
  · show ws.getD i [] ++ v = conc ws (i :: w)
    rw [conc_cons, hconc]
  · intro _
    simp

/-- A string of indices of `ws` is read by a path from the final state to itself. -/
lemma relFrom_homCode_one_one (ws : List (List ℕ)) {w : List ℕ}
    (hw : ∀ i ∈ w, i < ws.length) : (codeAut (homCode ws)).relFrom 1 w (conc ws w) 1 := by
  induction w with
  | nil => exact (codeAut (homCode ws)).relFrom_nil 1
  | cons i w ih =>
      have hi : i < ws.length := hw i (by simp)
      have ht : ((1 : ℕ), [i], ws.getD i [], (1 : ℕ)) ∈ (codeAut (homCode ws)).δ :=
        mem_homTrans.2 ⟨i, hi, Or.inr rfl⟩
      have := NFAO.relFrom_step ht (ih fun j hj => hw j (by simp [hj]))
      simpa [conc_cons] using this

/-- **The relation described by `homCode ws`**: the pairs `(w, ws w)` for a nonempty string `w` of
indices of `ws`. -/
lemma codeRel_homCode (ws : List (List ℕ)) (w v : List ℕ) :
    codeRel (homCode ws) w v ↔ w ≠ [] ∧ (∀ i ∈ w, i < ws.length) ∧ v = conc ws w := by
  constructor
  · intro h
    obtain ⟨q, hq, p, hp, hrel⟩ := (NFAO.rel_iff_relFrom _ w v).1 h
    have hq0 : q = 0 := by simpa [codeAut, homCode] using hq
    have hp1 : p = 1 := by simpa [codeAut, homCode] using hp
    subst hq0; subst hp1
    obtain ⟨hgood, hconc, hne⟩ := relFrom_homCode_to_one ws hrel
    exact ⟨hne rfl, hgood, hconc⟩
  · rintro ⟨hne, hgood, rfl⟩
    obtain ⟨i, w, rfl⟩ : ∃ i w', w = i :: w' := by
      cases w with
      | nil => exact absurd rfl hne
      | cons i w' => exact ⟨i, w', rfl⟩
    have hi : i < ws.length := hgood i (by simp)
    have ht : ((0 : ℕ), [i], ws.getD i [], (1 : ℕ)) ∈ (codeAut (homCode ws)).δ :=
      mem_homTrans.2 ⟨i, hi, Or.inl rfl⟩
    have hpath := NFAO.relFrom_step ht
      (relFrom_homCode_one_one ws (fun j hj => hgood j (List.mem_cons_of_mem i hj)))
    refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨0, by simp [codeAut, homCode], 1,
      by simp [codeAut, homCode], ?_⟩
    simpa [conc_cons] using hpath

/-! ## The reduction -/

/-- The two codes produced by the reduction from an instance of the Post correspondence
problem. -/
def pcpPair (P : Instance) : RelCode × RelCode :=
  (homCode (P.map Prod.fst), homCode (P.map Prod.snd))

/-- **The reduction is correct**: the two relations meet exactly when the instance is solvable. -/
lemma exists_common_iff_solvable (P : Instance) :
    (∃ w v, codeRel (pcpPair P).1 w v ∧ codeRel (pcpPair P).2 w v) ↔ Solvable P := by
  constructor
  · rintro ⟨w, v, h1, h2⟩
    obtain ⟨hne, hgood, hv1⟩ := (codeRel_homCode _ w v).1 h1
    obtain ⟨-, -, hv2⟩ := (codeRel_homCode _ w v).1 h2
    exact ⟨w, hne, by simpa using hgood, by rw [← hv1, hv2]⟩
  · rintro ⟨idx, hne, hgood, heq⟩
    refine ⟨idx, conc (P.map Prod.fst) idx, ?_, ?_⟩
    · exact (codeRel_homCode _ _ _).2 ⟨hne, by simpa using hgood, rfl⟩
    · exact (codeRel_homCode _ _ _).2 ⟨hne, by simpa using hgood, heq⟩

/-- **The reduction is computable.** -/
lemma computable_pcpPair : Computable pcpPair := by
  have hfst : Primrec (fun P : Instance => P.map Prod.fst) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.1
    exact Primrec.fst.comp Primrec.snd
  have hsnd : Primrec (fun P : Instance => P.map Prod.snd) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.2
    exact Primrec.snd.comp Primrec.snd
  have hhom : Primrec homTrans := by
    have hbody : Primrec (fun q : List (List ℕ) × ℕ =>
        [((0 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ)),
          ((1 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))]) := by
      have hi : Primrec (fun q : List (List ℕ) × ℕ => q.2) := Primrec.snd
      have hword : Primrec (fun q : List (List ℕ) × ℕ => q.1.getD q.2 []) :=
        (Primrec.list_getD ([] : List ℕ)).comp Primrec.fst hi
      have hlet : Primrec (fun q : List (List ℕ) × ℕ => [q.2]) :=
        Primrec.list_cons.comp hi (Primrec.const ([] : List ℕ))
      have h0 : Primrec (fun q : List (List ℕ) × ℕ =>
          ((0 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))) :=
        Primrec.pair (Primrec.const 0)
          (Primrec.pair hlet (Primrec.pair hword (Primrec.const 1)))
      have h1 : Primrec (fun q : List (List ℕ) × ℕ =>
          ((1 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))) :=
        Primrec.pair (Primrec.const 1)
          (Primrec.pair hlet (Primrec.pair hword (Primrec.const 1)))
      exact Primrec.list_cons.comp h0 (Primrec.list_cons.comp h1
        (Primrec.const ([] : List (ℕ × List ℕ × List ℕ × ℕ))))
    exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) hbody
  have hcode : ∀ {f : Instance → List (List ℕ)}, Primrec f →
      Primrec (fun P : Instance => homCode (f P)) := by
    intro f hf
    exact Primrec.pair (hhom.comp hf) (Primrec.const (([0], [1]) : List ℕ × List ℕ))
  exact (Primrec.pair (hcode hfst) (hcode hsnd)).to_comp

/-- The undecidability of the nonemptiness of the intersection, from the undecidability of the Post
correspondence problem.  This is Exercise `exer:rational-relations-intersection-undecidable`, whose
statement is `Transducers.Exercises.rationalRel_intersection_undecidable` in
`RequestProject/Exercises/PartBC.lean`. -/
theorem intersection_undecidable_aux (hPCP : ¬ ComputablePred PCP.Solvable) :
    ¬ ComputablePred (fun p : RelCode × RelCode => ∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v) := by
  rintro ⟨hdec, hcomp⟩
  set F : RelCode × RelCode → Bool :=
    fun p => decide (∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v) with hF
  have hFspec : ∀ p, F p = true ↔ ∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v := by
    intro p; simp [hF]
  have hD : Computable (fun P : Instance => F (pcpPair P)) := hcomp.comp computable_pcpPair
  refine hPCP ⟨fun P => Classical.propDecidable _, hD.of_eq fun P => ?_⟩
  by_cases h : Solvable P
  · have : F (pcpPair P) = true := (hFspec _).2 ((exists_common_iff_solvable P).2 h)
    simp [this, h]
  · have : F (pcpPair P) = false := by
      by_contra hc
      exact h ((exists_common_iff_solvable P).1 ((hFspec _).1 (by simpa using hc)))
    simp [this, h]

/-! ## The automaton of a homomorphism with a separate output on the empty input -/

/-- The transitions of the automaton of `homTrans`, together with one extra transition which reads
the empty input, writes the letter `x` and leads to the sink state `2`.  This makes the relation a
total function on the strings over the alphabet of the code: the empty input, on which the
homomorphism automaton produced nothing, now has the single output `x`. -/
def funTrans (ws : List (List ℕ)) (x : ℕ) : List (ℕ × List ℕ × List ℕ × ℕ) :=
  homTrans ws ++ [(0, ([] : List ℕ), [x], 2)]

/-- The code of the automaton of `funTrans`: a rational function that maps the empty input to `x`
and a nonempty string of indices of `ws` to its homomorphic image. -/
def funCode (ws : List (List ℕ)) (x : ℕ) : RelCode := (funTrans ws x, ([0], [1, 2]))

lemma mem_funTrans {ws : List (List ℕ)} {x : ℕ} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ funTrans ws x ↔ t ∈ homTrans ws ∨ t = (0, ([] : List ℕ), [x], 2) := by
  simp [funTrans]

/-- The sink state `2` has no outgoing transition. -/
lemma funTrans_source_ne_two {ws : List (List ℕ)} {x : ℕ} {t : ℕ × List ℕ × List ℕ × ℕ}
    (ht : t ∈ funTrans ws x) : t.1 ≠ 2 := by
  rcases mem_funTrans.1 ht with h | h
  · obtain ⟨i, -, hcase⟩ := mem_homTrans.1 h
    rcases hcase with rfl | rfl <;> simp
  · subst h; simp

/-- A path that starts in the sink state `2` is empty. -/
lemma relFrom_funCode_from_two (ws : List (List ℕ)) (x : ℕ) {w v : List ℕ} {p : ℕ}
    (h : (codeAut (funCode ws x)).relFrom 2 w v p) : p = 2 ∧ w = [] ∧ v = [] := by
  have := NFAO.relFrom_induction (M := codeAut (funCode ws x))
    (motive := fun q w v => q = 2 → p = 2 ∧ w = [] ∧ v = [])
    (fun hp => ⟨hp, rfl, rfl⟩) ?_ h rfl
  · exact this
  · rintro q q' u y w v ht - - rfl
    exact absurd (congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) rfl) (funTrans_source_ne_two ht)

/-- Every path of the automaton that ends in the state `1` reads a nonempty string of indices of
`ws` and writes its homomorphic image, as in `relFrom_homCode_to_one`. -/
lemma relFrom_funCode_to_one (ws : List (List ℕ)) (x : ℕ) {q : ℕ} {w v : List ℕ}
    (h : (codeAut (funCode ws x)).relFrom q w v 1) :
    (∀ i ∈ w, i < ws.length) ∧ v = conc ws w ∧ (q = 0 → w ≠ []) := by
  refine NFAO.relFrom_induction (M := codeAut (funCode ws x))
    (motive := fun q w v => (∀ i ∈ w, i < ws.length) ∧ v = conc ws w ∧ (q = 0 → w ≠ []))
    ⟨by simp, rfl, by simp⟩ ?_ h
  rintro q q' u y w v ht hrel ⟨hgood, hconc, -⟩
  have ht' : (q, u, y, q') ∈ funTrans ws x := ht
  rcases mem_funTrans.1 ht' with hhom | hnew
  · obtain ⟨i, hi, hcase⟩ := mem_homTrans.1 hhom
    have hu : u = [i] ∧ y = ws.getD i [] := by
      rcases hcase with h | h <;> exact ⟨congrArg (fun t => t.2.1) h, congrArg (fun t => t.2.2.1) h⟩
    obtain ⟨rfl, rfl⟩ := hu
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.1 (by simpa using hj) with rfl | hj'
      · exact hi
      · exact hgood j hj'
    · show ws.getD i [] ++ v = conc ws (i :: w)
      rw [conc_cons, hconc]
    · intro _
      simp
  · have hq' : q' = 2 := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) hnew
    subst hq'
    exact absurd (relFrom_funCode_from_two ws x hrel).1 (by simp)

/-- **The relation described by `funCode ws x`**: the empty input has the single output `x`, and a
nonempty string of indices of `ws` has its homomorphic image as its single output. -/
lemma codeRel_funCode (ws : List (List ℕ)) (x : ℕ) (w v : List ℕ) :
    codeRel (funCode ws x) w v ↔
      (w = [] ∧ v = [x]) ∨ (w ≠ [] ∧ (∀ i ∈ w, i < ws.length) ∧ v = conc ws w) := by
  constructor
  · intro h
    obtain ⟨q, hq, p, hp, hrel⟩ := (NFAO.rel_iff_relFrom _ w v).1 h
    have hq0 : q = 0 := by simpa [codeAut, funCode] using hq
    subst hq0
    have hp' : p = 1 ∨ p = 2 := by simpa [codeAut, funCode] using hp
    rcases hp' with rfl | rfl
    · obtain ⟨hgood, hconc, hne⟩ := relFrom_funCode_to_one ws x hrel
      exact Or.inr ⟨hne rfl, hgood, hconc⟩
    · -- the only path from `0` to `2` is the extra transition
      refine Or.inl ?_
      have hmotive := NFAO.relFrom_induction (M := codeAut (funCode ws x))
        (motive := fun q w v => (q = 2 ∧ w = [] ∧ v = []) ∨ (q = 0 ∧ w = [] ∧ v = [x]))
        (Or.inl ⟨rfl, rfl, rfl⟩) ?_ hrel
      · rcases hmotive with ⟨h0, -, -⟩ | ⟨-, hw, hv⟩
        · exact absurd h0 (by simp)
        · exact ⟨hw, hv⟩
      · rintro q q' u y w v ht - hih
        have ht' : (q, u, y, q') ∈ funTrans ws x := ht
        rcases mem_funTrans.1 ht' with hhom | hnew
        · obtain ⟨i, -, hcase⟩ := mem_homTrans.1 hhom
          have hq'1 : q' = 1 := by
            rcases hcase with h | h <;>
              exact congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) h
          subst hq'1
          rcases hih with ⟨h2, -, -⟩ | ⟨h0, -, -⟩
          · exact absurd h2 (by simp)
          · exact absurd h0 (by simp)
        · have hq : q = 0 := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) hnew
          have hu : u = [] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.1) hnew
          have hy : y = [x] := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.1) hnew
          have hq' : q' = 2 := congrArg (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) hnew
          subst hq; subst hu; subst hy; subst hq'
          rcases hih with ⟨-, hw, hv⟩ | ⟨h0, -, -⟩
          · exact Or.inr ⟨rfl, by simp [hw], by simp [hv]⟩
          · exact absurd h0 (by simp)
  · rintro (⟨rfl, rfl⟩ | ⟨hne, hgood, rfl⟩)
    · have ht : ((0 : ℕ), ([] : List ℕ), [x], (2 : ℕ)) ∈ (codeAut (funCode ws x)).δ :=
        mem_funTrans.2 (Or.inr rfl)
      refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨0, by simp [codeAut, funCode], 2,
        by simp [codeAut, funCode], ?_⟩
      simpa using NFAO.relFrom_single ht
    · obtain ⟨i, w, rfl⟩ : ∃ i w', w = i :: w' := by
        cases w with
        | nil => exact absurd rfl hne
        | cons i w' => exact ⟨i, w', rfl⟩
      have hi : i < ws.length := hgood i (by simp)
      have ht : ((0 : ℕ), [i], ws.getD i [], (1 : ℕ)) ∈ (codeAut (funCode ws x)).δ :=
        mem_funTrans.2 (Or.inl (mem_homTrans.2 ⟨i, hi, Or.inl rfl⟩))
      have hloop : ∀ u : List ℕ, (∀ j ∈ u, j < ws.length) →
          (codeAut (funCode ws x)).relFrom 1 u (conc ws u) 1 := by
        intro u
        induction u with
        | nil => exact fun _ => (codeAut (funCode ws x)).relFrom_nil 1
        | cons j u ih =>
            intro hu
            have hj : j < ws.length := hu j (by simp)
            have htj : ((1 : ℕ), [j], ws.getD j [], (1 : ℕ)) ∈ (codeAut (funCode ws x)).δ :=
              mem_funTrans.2 (Or.inl (mem_homTrans.2 ⟨j, hj, Or.inr rfl⟩))
            have := NFAO.relFrom_step htj (ih fun k hk => hu k (by simp [hk]))
            simpa [conc_cons] using this
      have hpath := NFAO.relFrom_step ht
        (hloop w (fun j hj => hgood j (List.mem_cons_of_mem i hj)))
      refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨0, by simp [codeAut, funCode], 1,
        by simp [codeAut, funCode], ?_⟩
      simpa [conc_cons] using hpath

/-- The alphabet of the code `funCode ws x` consists of the indices of `ws`. -/
lemma mem_codeAlphabet_funCode {ws : List (List ℕ)} {x i : ℕ} :
    i ∈ codeAlphabet (funCode ws x) ↔ i < ws.length := by
  simp only [codeAlphabet, funCode, funTrans, homTrans, List.flatMap_append, List.mem_append,
    List.mem_flatMap, List.mem_range, List.flatMap_cons, List.flatMap_nil, List.mem_cons,
    List.not_mem_nil]
  constructor
  · rintro (⟨u, ⟨j, hj, hcase⟩, hmem⟩ | h | h)
    · have hu : u.2.1 = [j] := by
        rcases hcase with rfl | rfl | h
        · rfl
        · rfl
        · exact h.elim
      rw [hu] at hmem
      have : i = j := by simpa using hmem
      omega
    · exact h.elim
    · exact h.elim
  · intro hi
    exact Or.inl ⟨(0, [i], ws.getD i [], 1), ⟨i, hi, Or.inl rfl⟩, by simp⟩

/-- **`funCode ws x` describes a function**: every string over its alphabet has exactly one
output. -/
lemma codeFunctional_funCode (ws : List (List ℕ)) (x : ℕ) : CodeFunctional (funCode ws x) := by
  intro w hw
  have hgood : ∀ i ∈ w, i < ws.length := fun i hi => mem_codeAlphabet_funCode.1 (hw i hi)
  by_cases hne : w = []
  · subst hne
    refine ⟨[x], (codeRel_funCode ws x [] [x]).2 (Or.inl ⟨rfl, rfl⟩), fun v hv => ?_⟩
    rcases (codeRel_funCode ws x [] v).1 hv with ⟨-, hv⟩ | ⟨h0, -, -⟩
    · exact hv
    · exact absurd rfl h0
  · refine ⟨conc ws w, (codeRel_funCode ws x w _).2 (Or.inr ⟨hne, hgood, rfl⟩), fun v hv => ?_⟩
    rcases (codeRel_funCode ws x w v).1 hv with ⟨h0, -⟩ | ⟨-, -, hv⟩
    · exact absurd h0 hne
    · exact hv

/-! ## The reduction for the collision problem -/

/-- The two codes produced by the reduction from an instance of the Post correspondence problem to
the collision problem: the two homomorphisms of the instance, made total by outputting `0`,
respectively `1`, on the empty input, so that they do not collide there. -/
def pcpFunPair (P : Instance) : RelCode × RelCode :=
  (funCode (P.map Prod.fst) 0, funCode (P.map Prod.snd) 1)

/-- **The reduction is correct**: the two functions have a common output on a common input exactly
when the instance is solvable. -/
lemma exists_collision_iff_solvable (P : Instance) :
    (∃ w v, codeRel (pcpFunPair P).1 w v ∧ codeRel (pcpFunPair P).2 w v) ↔ Solvable P := by
  constructor
  · rintro ⟨w, v, h1, h2⟩
    rcases (codeRel_funCode _ _ w v).1 h1 with ⟨rfl, rfl⟩ | ⟨hne, hgood, hv1⟩
    · rcases (codeRel_funCode _ _ [] [0]).1 h2 with ⟨-, hv⟩ | ⟨h0, -, -⟩
      · exact absurd hv (by simp)
      · exact absurd rfl h0
    · rcases (codeRel_funCode _ _ w v).1 h2 with ⟨h0, -⟩ | ⟨-, -, hv2⟩
      · exact absurd h0 hne
      · exact ⟨w, hne, by simpa using hgood, by rw [← hv1, hv2]⟩
  · rintro ⟨idx, hne, hgood, heq⟩
    refine ⟨idx, conc (P.map Prod.fst) idx, ?_, ?_⟩
    · exact (codeRel_funCode _ _ _ _).2 (Or.inr ⟨hne, by simpa using hgood, rfl⟩)
    · exact (codeRel_funCode _ _ _ _).2 (Or.inr ⟨hne, by simpa using hgood, heq⟩)

/-- **The reduction is computable.** -/
lemma computable_pcpFunPair : Computable pcpFunPair := by
  have hfst : Primrec (fun P : Instance => P.map Prod.fst) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.1
    exact Primrec.fst.comp Primrec.snd
  have hsnd : Primrec (fun P : Instance => P.map Prod.snd) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.2
    exact Primrec.snd.comp Primrec.snd
  have hhom : Primrec homTrans := by
    have hbody : Primrec (fun q : List (List ℕ) × ℕ =>
        [((0 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ)),
          ((1 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))]) := by
      have hi : Primrec (fun q : List (List ℕ) × ℕ => q.2) := Primrec.snd
      have hword : Primrec (fun q : List (List ℕ) × ℕ => q.1.getD q.2 []) :=
        (Primrec.list_getD ([] : List ℕ)).comp Primrec.fst hi
      have hlet : Primrec (fun q : List (List ℕ) × ℕ => [q.2]) :=
        Primrec.list_cons.comp hi (Primrec.const ([] : List ℕ))
      have h0 : Primrec (fun q : List (List ℕ) × ℕ =>
          ((0 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))) :=
        Primrec.pair (Primrec.const 0)
          (Primrec.pair hlet (Primrec.pair hword (Primrec.const 1)))
      have h1 : Primrec (fun q : List (List ℕ) × ℕ =>
          ((1 : ℕ), [q.2], q.1.getD q.2 [], (1 : ℕ))) :=
        Primrec.pair (Primrec.const 1)
          (Primrec.pair hlet (Primrec.pair hword (Primrec.const 1)))
      exact Primrec.list_cons.comp h0 (Primrec.list_cons.comp h1
        (Primrec.const ([] : List (ℕ × List ℕ × List ℕ × ℕ))))
    exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length) hbody
  have hcode : ∀ {f : Instance → List (List ℕ)} (x : ℕ), Primrec f →
      Primrec (fun P : Instance => funCode (f P) x) := by
    intro f x hf
    have : Primrec (fun P : Instance => funTrans (f P) x) :=
      Primrec.list_append.comp (hhom.comp hf)
        (Primrec.const [((0 : ℕ), ([] : List ℕ), [x], (2 : ℕ))])
    exact Primrec.pair this (Primrec.const (([0], [1, 2]) : List ℕ × List ℕ))
  exact (Primrec.pair (hcode 0 hfst) (hcode 1 hsnd)).to_comp

/-- The undecidability of the collision problem for rational functions, from the undecidability of
the Post correspondence problem.  This is item (a) of Exercise `exer:decide-rational-colision`,
whose statement is `Transducers.Exercises.rationalFun_collision_undecidable` in
`RequestProject/Exercises/PartBC.lean`. -/
theorem collision_undecidable_aux (hPCP : ¬ ComputablePred PCP.Solvable) :
    ¬ DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => ∃ w v, codeRel p.1 w v ∧ codeRel p.2 w v) := by
  rintro ⟨D, hcomp, hspec⟩
  have hpromise : ∀ P : Instance,
      CodeFunctional (pcpFunPair P).1 ∧ CodeFunctional (pcpFunPair P).2 :=
    fun P => ⟨codeFunctional_funCode _ _, codeFunctional_funCode _ _⟩
  have hD : Computable (fun P : Instance => D (pcpFunPair P)) := hcomp.comp computable_pcpFunPair
  refine hPCP ⟨fun P => Classical.propDecidable _, hD.of_eq fun P => ?_⟩
  have hiff : D (pcpFunPair P) = true ↔ Solvable P :=
    (hspec _ (hpromise P)).trans (exists_collision_iff_solvable P)
  by_cases h : Solvable P
  · simp [hiff.2 h, h]
  · have : D (pcpFunPair P) = false := by
      by_contra hc
      exact h (hiff.1 (by simpa using hc))
    simp [this, h]

end Exercises
end Transducers
