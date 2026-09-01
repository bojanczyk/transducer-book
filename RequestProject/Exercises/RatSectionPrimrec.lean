/-
The construction of the effective Uniformisation Lemma is primitive recursive.

Every definition used by `Transducers.Exercises.LAut.invCode` — the splitting of the output
blocks, the ε-elimination that inverts a code, the uniformisation of a letter automaton, and the
product of a code with a letter automaton — is built from list operations only, with no
unbounded search.  This file records that, one definition at a time, so that
`RequestProject/Exercises/RatInjectiveDec.lean` can discharge the effectivity hypothesis of
Exercise `exer:rational-injectivity-decidable`.

Each statement is given in "composition" form: from primitive recursive arguments one gets a
primitive recursive result.  That is what makes the lemmas usable in the next one.
-/
import RequestProject.Exercises.RatSection
import RequestProject.Common.PrimrecList2

namespace Transducers.Exercises

open Transducers Primrec

variable {γ : Type} [Primcodable γ]

/-- The alphabet of a code is primitive recursive in the code. -/
theorem primrec_codeAlphabet : Primrec codeAlphabet := by
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun z : RelCode × (ℕ × List ℕ × List ℕ × ℕ) => z.2.2.1
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

namespace LAut

/-! ## The semantics of a letter automaton -/

theorem primrec_step {L : γ → LCode} {q a i : γ → ℕ}
    (hL : Primrec L) (hq : Primrec q) (ha : Primrec a) (hi : Primrec i) :
    Primrec fun x => step (L x) (q x) (a x) (i x) := by
  have h1 : Primrec fun x => (L x).1[i x]? :=
    Primrec.list_getElem?.comp (Primrec.fst.comp hL) hi
  refine Primrec.option_bind h1 ?_
  have he1 : PrimrecPred fun z : γ × (ℕ × ℕ × List ℕ × ℕ) => z.2.1 = q z.1 :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (hq.comp Primrec.fst)
  have he2 : PrimrecPred fun z : γ × (ℕ × ℕ × List ℕ × ℕ) => z.2.2.1 = a z.1 :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (ha.comp Primrec.fst)
  have hval : Primrec fun z : γ × (ℕ × ℕ × List ℕ × ℕ) =>
      some (z.2.2.2.2, z.2.2.2.1) :=
    Primrec.option_some.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.ite (he1.and he2) hval (Primrec.const none)).to₂

theorem primrec_term {L : γ → LCode} {q k : γ → ℕ}
    (hL : Primrec L) (hq : Primrec q) (hk : Primrec k) :
    Primrec fun x => term (L x) (q x) (k x) := by
  have h1 : Primrec fun x => (L x).2.2[k x]? :=
    Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.snd.comp hL)) hk
  refine Primrec.option_bind h1 ?_
  have he1 : PrimrecPred fun z : γ × (ℕ × List ℕ) => z.2.1 = q z.1 :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd) (hq.comp Primrec.fst)
  have hval : Primrec fun z : γ × (ℕ × List ℕ) => some z.2.2 :=
    Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.ite he1 hval (Primrec.const none)).to₂

theorem primrec_leastTerm {L : γ → LCode} {q : γ → ℕ} (hL : Primrec L) (hq : Primrec q) :
    Primrec fun x => leastTerm (L x) (q x) := by
  have hr : Primrec fun x => List.range (L x).2.2.length :=
    Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp hL)))
  refine Primrec.list_find? hr ?_
  have h : Primrec fun z : γ × ℕ => (term (L z.1) (q z.1) z.2).isSome :=
    Primrec.option_isSome.comp
      (primrec_term (hL.comp Primrec.fst) (hq.comp Primrec.fst) Primrec.snd)
  exact h.to₂

/-! ## The uniformisation of a letter automaton -/

theorem primrec_states {L : γ → LCode} (hL : Primrec L) : Primrec fun x => states (L x) := by
  have h1 : Primrec fun x => (L x).2.1 := Primrec.fst.comp (Primrec.snd.comp hL)
  have h2 : Primrec fun x => (L x).1.flatMap (fun t => [t.1, t.2.2.2]) := by
    refine Primrec.list_flatMap (Primrec.fst.comp hL) ?_
    have ha : Primrec fun z : γ × (ℕ × ℕ × List ℕ × ℕ) => z.2.1 := Primrec.fst.comp Primrec.snd
    have hb : Primrec fun z : γ × (ℕ × ℕ × List ℕ × ℕ) => z.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.list_cons.comp ha
      (Primrec.list_cons.comp hb (Primrec.const []))).to₂
  have h3 : Primrec fun x => (L x).2.2.map (Prod.fst : ℕ × List ℕ → ℕ) :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp hL)) (Primrec.fst.comp Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3

theorem primrec_canon {L : γ → LCode} {S : γ → List ℕ} (hL : Primrec L) (hS : Primrec S) :
    Primrec fun x => canon (L x) (S x) := by
  have h : Primrec fun z : γ × ℕ => decide (z.2 ∈ S z.1) :=
    (Primrec.list_mem.comp Primrec.snd (hS.comp Primrec.fst)).decide
  exact Primrec.list_filter (primrec_states hL) h.to₂

theorem primrec_enc {q : γ → ℕ} {S : γ → List ℕ} (hq : Primrec q) (hS : Primrec S) :
    Primrec fun x => enc (q x) (S x) :=
  Primrec.encode.comp (Primrec.pair hq hS)

theorem primrec_succSet {L : γ → LCode} {S : γ → List ℕ} {a : γ → ℕ}
    (hL : Primrec L) (hS : Primrec S) (ha : Primrec a) :
    Primrec fun x => succSet (L x) (S x) (a x) := by
  have hr : Primrec fun z : γ × ℕ => List.range (L z.1).1.length :=
    Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp (hL.comp Primrec.fst)))
  have h : Primrec fun w : (γ × ℕ) × ℕ =>
      (step (L w.1.1) w.1.2 (a w.1.1) w.2).map (Prod.fst : ℕ × List ℕ → ℕ) :=
    Primrec.option_map
      (primrec_step (hL.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) (ha.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (Primrec.fst.comp Primrec.snd).to₂
  have hinner : Primrec fun z : γ × ℕ => (List.range (L z.1).1.length).filterMap
      (fun i => (step (L z.1) z.2 (a z.1) i).map (Prod.fst : ℕ × List ℕ → ℕ)) :=
    Primrec.listFilterMap hr h.to₂
  exact Primrec.list_flatMap hS hinner.to₂

theorem primrec_smallerSet {L : γ → LCode} {q a i : γ → ℕ}
    (hL : Primrec L) (hq : Primrec q) (ha : Primrec a) (hi : Primrec i) :
    Primrec fun x => smallerSet (L x) (q x) (a x) (i x) := by
  refine Primrec.listFilterMap (Primrec.list_range.comp hi) ?_
  have h : Primrec fun z : γ × ℕ =>
      (step (L z.1) (q z.1) (a z.1) z.2).map (Prod.fst : ℕ × List ℕ → ℕ) :=
    Primrec.option_map
      (primrec_step (hL.comp Primrec.fst) (hq.comp Primrec.fst) (ha.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.snd).to₂
  exact h.to₂

theorem primrec_initsBefore {L : γ → LCode} {j : γ → ℕ} (hL : Primrec L) (hj : Primrec j) :
    Primrec fun x => initsBefore (L x) (j x) := by
  refine Primrec.listFilterMap (Primrec.list_range.comp hj) ?_
  have h : Primrec fun z : γ × ℕ => (L z.1).2.1[z.2]? :=
    Primrec.list_getElem?.comp (Primrec.fst.comp (Primrec.snd.comp (hL.comp Primrec.fst)))
      Primrec.snd
  exact h.to₂

theorem primrec_nextSet {L : γ → LCode} {q : γ → ℕ} {S : γ → List ℕ} {a i : γ → ℕ}
    (hL : Primrec L) (hq : Primrec q) (hS : Primrec S) (ha : Primrec a) (hi : Primrec i) :
    Primrec fun x => nextSet (L x) (q x) (S x) (a x) (i x) :=
  primrec_canon hL (Primrec.list_append.comp (primrec_succSet hL hS ha)
    (primrec_smallerSet hL hq ha hi))

theorem primrec_unifLCode {L : γ → LCode} (hL : Primrec L) :
    Primrec fun x => unifLCode (L x) := by
  -- the transitions
  have htr : Primrec fun x => (List.range (L x).1.length).flatMap (fun i =>
      (((states (L x)).sublists).filterMap (fun S =>
        ((L x).1[i]?).map (fun t =>
          (enc t.1 (canon (L x) S), t.2.1, t.2.2.1,
            enc t.2.2.2 (nextSet (L x) t.1 (canon (L x) S) t.2.1 i)))))) := by
    have hsub : Primrec fun z : γ × ℕ => ((states (L z.1)).sublists) :=
      Primrec.list_sublists.comp (primrec_states (hL.comp Primrec.fst))
    have hget : Primrec fun w : (γ × ℕ) × List ℕ => (L w.1.1).1[w.1.2]? :=
      Primrec.list_getElem?.comp (Primrec.fst.comp (hL.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)
    have hLv : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => L v.1.1.1 :=
      hL.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hiv : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hSv : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.1.2 :=
      Primrec.snd.comp Primrec.fst
    have ht1 : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.2.1 :=
      Primrec.fst.comp Primrec.snd
    have ht2 : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have ht3 : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have ht4 : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) => v.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hcan : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) =>
        canon (L v.1.1.1) v.1.2 := primrec_canon hLv hSv
    have hval : Primrec fun v : ((γ × ℕ) × List ℕ) × (ℕ × ℕ × List ℕ × ℕ) =>
        (enc v.2.1 (canon (L v.1.1.1) v.1.2), v.2.2.1, v.2.2.2.1,
          enc v.2.2.2.2 (nextSet (L v.1.1.1) v.2.1 (canon (L v.1.1.1) v.1.2) v.2.2.1 v.1.1.2)) :=
      Primrec.pair (primrec_enc ht1 hcan)
        (Primrec.pair ht2 (Primrec.pair ht3
          (primrec_enc ht4 (primrec_nextSet hLv ht1 hcan ht2 hiv))))
    have hmap : Primrec fun w : (γ × ℕ) × List ℕ =>
        ((L w.1.1).1[w.1.2]?).map (fun t =>
          (enc t.1 (canon (L w.1.1) w.2), t.2.1, t.2.2.1,
            enc t.2.2.2 (nextSet (L w.1.1) t.1 (canon (L w.1.1) w.2) t.2.1 w.1.2))) :=
      Primrec.option_map hget hval.to₂
    have hfm : Primrec fun z : γ × ℕ => ((states (L z.1)).sublists).filterMap (fun S =>
        ((L z.1).1[z.2]?).map (fun t =>
          (enc t.1 (canon (L z.1) S), t.2.1, t.2.2.1,
            enc t.2.2.2 (nextSet (L z.1) t.1 (canon (L z.1) S) t.2.1 z.2)))) :=
      Primrec.listFilterMap hsub hmap.to₂
    exact Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp hL))) hfm.to₂
  -- the initial states
  have hin : Primrec fun x => (List.range (L x).2.1.length).filterMap (fun j =>
      ((L x).2.1[j]?).map (fun q => enc q (canon (L x) (initsBefore (L x) j)))) := by
    have hget : Primrec fun z : γ × ℕ => (L z.1).2.1[z.2]? :=
      Primrec.list_getElem?.comp (Primrec.fst.comp (Primrec.snd.comp (hL.comp Primrec.fst)))
        Primrec.snd
    have hLv : Primrec fun v : (γ × ℕ) × ℕ => L v.1.1 := hL.comp (Primrec.fst.comp Primrec.fst)
    have hj : Primrec fun v : (γ × ℕ) × ℕ => v.1.2 := Primrec.snd.comp Primrec.fst
    have hval : Primrec fun v : (γ × ℕ) × ℕ =>
        enc v.2 (canon (L v.1.1) (initsBefore (L v.1.1) v.1.2)) :=
      primrec_enc Primrec.snd (primrec_canon hLv (primrec_initsBefore hLv hj))
    have hmap : Primrec fun z : γ × ℕ =>
        ((L z.1).2.1[z.2]?).map (fun q => enc q (canon (L z.1) (initsBefore (L z.1) z.2))) :=
      Primrec.option_map hget hval.to₂
    exact Primrec.listFilterMap (Primrec.list_range.comp
      (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp hL)))) hmap.to₂
  -- the terminal entries
  have hte : Primrec fun x => (states (L x)).flatMap (fun q =>
      (((states (L x)).sublists).filterMap (fun S =>
        if (canon (L x) S).all (fun p => (leastTerm (L x) p).isNone) then
          ((leastTerm (L x) q).bind (fun k => term (L x) q k)).map
            (fun e => (enc q (canon (L x) S), e))
        else none))) := by
    have hsub : Primrec fun z : γ × ℕ => ((states (L z.1)).sublists) :=
      Primrec.list_sublists.comp (primrec_states (hL.comp Primrec.fst))
    have hLv : Primrec fun v : (γ × ℕ) × List ℕ => L v.1.1 := hL.comp (Primrec.fst.comp Primrec.fst)
    have hq : Primrec fun v : (γ × ℕ) × List ℕ => v.1.2 := Primrec.snd.comp Primrec.fst
    have hcan : Primrec fun v : (γ × ℕ) × List ℕ => canon (L v.1.1) v.2 :=
      primrec_canon hLv Primrec.snd
    have hallb : Primrec fun v : (γ × ℕ) × List ℕ =>
        (canon (L v.1.1) v.2).all (fun p => (leastTerm (L v.1.1) p).isNone) := by
      have hh : Primrec fun w : ((γ × ℕ) × List ℕ) × ℕ =>
          (leastTerm (L w.1.1.1) w.2).isNone := by
        have h1 : Primrec fun w : ((γ × ℕ) × List ℕ) × ℕ =>
            !((leastTerm (L w.1.1.1) w.2).isSome) :=
          (Primrec.dom_bool not).comp (Primrec.option_isSome.comp
            (primrec_leastTerm (hL.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
              Primrec.snd))
        exact h1.of_eq fun w => by cases leastTerm (L w.1.1.1) w.2 <;> rfl
      exact Primrec.list_all hcan hh.to₂
    have hb : Primrec fun v : (γ × ℕ) × List ℕ =>
        (leastTerm (L v.1.1) v.1.2).bind (fun k => term (L v.1.1) v.1.2 k) := by
      have hin2 : Primrec fun w : ((γ × ℕ) × List ℕ) × ℕ => term (L w.1.1.1) w.1.1.2 w.2 :=
        primrec_term (hL.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      exact Primrec.option_bind (primrec_leastTerm hLv hq) hin2.to₂
    have hpv : Primrec fun w : ((γ × ℕ) × List ℕ) × List ℕ =>
        (enc w.1.1.2 (canon (L w.1.1.1) w.1.2), w.2) :=
      Primrec.pair
        (primrec_enc (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (primrec_canon (hL.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp Primrec.fst)))
        Primrec.snd
    have hthen : Primrec fun v : (γ × ℕ) × List ℕ =>
        ((leastTerm (L v.1.1) v.1.2).bind (fun k => term (L v.1.1) v.1.2 k)).map
          (fun e => (enc v.1.2 (canon (L v.1.1) v.2), e)) :=
      Primrec.option_map hb hpv.to₂
    have hite : Primrec fun v : (γ × ℕ) × List ℕ =>
        if (canon (L v.1.1) v.2).all (fun p => (leastTerm (L v.1.1) p).isNone) then
          ((leastTerm (L v.1.1) v.1.2).bind (fun k => term (L v.1.1) v.1.2 k)).map
            (fun e => (enc v.1.2 (canon (L v.1.1) v.2), e))
        else none := by
      have h := Primrec.cond hallb hthen
        (Primrec.const (α := (γ × ℕ) × List ℕ) (none : Option (ℕ × List ℕ)))
      exact h.of_eq fun v => by
        cases hc : (canon (L v.1.1) v.2).all (fun p => (leastTerm (L v.1.1) p).isNone) <;> simp
    have hfm : Primrec fun z : γ × ℕ => ((states (L z.1)).sublists).filterMap (fun S =>
        if (canon (L z.1) S).all (fun p => (leastTerm (L z.1) p).isNone) then
          ((leastTerm (L z.1) z.2).bind (fun k => term (L z.1) z.2 k)).map
            (fun e => (enc z.2 (canon (L z.1) S), e))
        else none) := Primrec.listFilterMap hsub hite.to₂
    exact Primrec.list_flatMap (primrec_states hL) hfm.to₂
  exact Primrec.pair htr (Primrec.pair hin hte)

end LAut

/-! ## Splitting the output blocks -/

namespace Split

/-- The part of `chain q' y s u` that does not depend on `s` and `u`: it is the tail of the
chain, which starts in the state that the first transition of the chain leads to. -/
def chainT (q' : ℕ) (y : List ℕ) : List (ℕ × List ℕ × List ℕ × ℕ) := chain q' y (nxt y q') []

lemma chainT_nil (q' : ℕ) : chainT q' [] = [(old q', [], [], old q')] := rfl

lemma chainT_cons (q' b : ℕ) (y : List ℕ) :
    chainT q' (b :: y) = (mid (b :: y) q', [], [b], nxt y q') :: chainT q' y := by
  simp [chainT, chain, nxt]

lemma chain_eq (q' : ℕ) (y : List ℕ) (s : ℕ) (u : List ℕ) :
    chain q' y s u = y.casesOn [(s, u, [], old q')]
      (fun b y' => (s, u, [b], nxt y' q') :: chainT q' y') := by
  cases y <;> rfl

theorem primrec_old {q : γ → ℕ} (hq : Primrec q) : Primrec fun x => old (q x) :=
  Primrec.encode.comp (Primrec.sumInl.comp hq)

theorem primrec_mid {z : γ → List ℕ} {q : γ → ℕ} (hz : Primrec z) (hq : Primrec q) :
    Primrec fun x => mid (z x) (q x) :=
  Primrec.encode.comp (Primrec.sumInr.comp (Primrec.pair hz hq))

theorem primrec_nxt {z : γ → List ℕ} {q : γ → ℕ} (hz : Primrec z) (hq : Primrec q) :
    Primrec fun x => nxt (z x) (q x) :=
  Primrec.ite (PrimrecRel.comp Primrec.eq hz (Primrec.const []))
    (primrec_old hq) (primrec_mid hz hq)

theorem primrec_chainT {q : γ → ℕ} {y : γ → List ℕ} (hq : Primrec q) (hy : Primrec y) :
    Primrec fun x => chainT (q x) (y x) := by
  have hg : Primrec fun x => [(old (q x), ([] : List ℕ), ([] : List ℕ), old (q x))] :=
    Primrec.list_cons.comp
      (Primrec.pair (primrec_old hq)
        (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const []) (primrec_old hq))))
      (Primrec.const [])
  have hh : Primrec fun w : γ × (ℕ × List ℕ × List (ℕ × List ℕ × List ℕ × ℕ)) =>
      (mid (w.2.1 :: w.2.2.1) (q w.1), ([] : List ℕ), [w.2.1], nxt w.2.2.1 (q w.1)) ::
        w.2.2.2 := by
    have hb : Primrec fun w : γ × (ℕ × List ℕ × List (ℕ × List ℕ × List ℕ × ℕ)) => w.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hl : Primrec fun w : γ × (ℕ × List ℕ × List (ℕ × List ℕ × List ℕ × ℕ)) => w.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hIH : Primrec fun w : γ × (ℕ × List ℕ × List (ℕ × List ℕ × List ℕ × ℕ)) => w.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hqw : Primrec fun w : γ × (ℕ × List ℕ × List (ℕ × List ℕ × List ℕ × ℕ)) => q w.1 :=
      hq.comp Primrec.fst
    exact Primrec.list_cons.comp
      (Primrec.pair (primrec_mid (Primrec.list_cons.comp hb hl) hqw)
        (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.list_cons.comp hb (Primrec.const []))
            (primrec_nxt hl hqw))))
      hIH
  have h := Primrec.list_rec hy hg hh.to₂
  refine h.of_eq fun x => ?_
  induction y x with
  | nil => rfl
  | cons b l ih => rw [chainT_cons, ← ih]

theorem primrec_chain {q : γ → ℕ} {y : γ → List ℕ} {s : γ → ℕ} {u : γ → List ℕ}
    (hq : Primrec q) (hy : Primrec y) (hs : Primrec s) (hu : Primrec u) :
    Primrec fun x => chain (q x) (y x) (s x) (u x) := by
  have hg : Primrec fun x => [(s x, u x, ([] : List ℕ), old (q x))] :=
    Primrec.list_cons.comp
      (Primrec.pair hs (Primrec.pair hu (Primrec.pair (Primrec.const []) (primrec_old hq))))
      (Primrec.const [])
  have hh : Primrec fun w : γ × (ℕ × List ℕ) =>
      (s w.1, u w.1, [w.2.1], nxt w.2.2 (q w.1)) :: chainT (q w.1) w.2.2 := by
    have hb : Primrec fun w : γ × (ℕ × List ℕ) => w.2.1 := Primrec.fst.comp Primrec.snd
    have hl : Primrec fun w : γ × (ℕ × List ℕ) => w.2.2 := Primrec.snd.comp Primrec.snd
    have hqw : Primrec fun w : γ × (ℕ × List ℕ) => q w.1 := hq.comp Primrec.fst
    exact Primrec.list_cons.comp
      (Primrec.pair (hs.comp Primrec.fst)
        (Primrec.pair (hu.comp Primrec.fst)
          (Primrec.pair (Primrec.list_cons.comp hb (Primrec.const []))
            (primrec_nxt hl hqw))))
      (primrec_chainT hqw hl)
  have h := Primrec.list_casesOn hy hg hh.to₂
  exact h.of_eq fun x => by rw [chain_eq]

theorem primrec_trans {c : γ → RelCode} (hc : Primrec c) : Primrec fun x => trans (c x) := by
  refine Primrec.list_flatMap (Primrec.fst.comp hc) ?_
  have h : Primrec fun w : γ × (ℕ × List ℕ × List ℕ × ℕ) =>
      chain w.2.2.2.2 w.2.2.2.1 (old w.2.1) w.2.2.1 :=
    primrec_chain (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_old (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact h.to₂

theorem primrec_splitCode {c : γ → RelCode} (hc : Primrec c) :
    Primrec fun x => splitCode (c x) := by
  have hm : Primrec fun x => (c x).2.1.map old :=
    Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp hc)) (primrec_old Primrec.snd).to₂
  have hf : Primrec fun x => (c x).2.2.map old :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp hc)) (primrec_old Primrec.snd).to₂
  exact Primrec.pair (primrec_trans hc) (Primrec.pair hm hf)

end Split

/-! ## The inverse of a code as a letter automaton -/

namespace LAut

theorem primrec_epsTrans {d : γ → RelCode} (hd : Primrec d) :
    Primrec fun x => epsTrans (d x) := by
  have hp : Primrec fun w : γ × (ℕ × List ℕ × List ℕ × ℕ) => decide (w.2.2.2.1 = []) :=
    (PrimrecRel.comp Primrec.eq
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const [])).decide
  exact Primrec.list_filter (Primrec.fst.comp hd) hp.to₂

theorem primrec_epsStep {d : γ → RelCode} {acc : γ → List (ℕ × List ℕ)}
    (hd : Primrec d) (hacc : Primrec acc) :
    Primrec fun x => epsStep (d x) (acc x) := by
  have hcond : PrimrecPred fun w : (γ × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      w.2.1 = w.1.2.1 :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hthen : Primrec fun w : (γ × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      some (w.2.2.2.2, w.1.2.2 ++ w.2.2.1) :=
    Primrec.option_some.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hif : Primrec fun w : (γ × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      if w.2.1 = w.1.2.1 then some (w.2.2.2.2, w.1.2.2 ++ w.2.2.1) else none :=
    Primrec.ite hcond hthen (Primrec.const none)
  have hfm : Primrec fun z : γ × (ℕ × List ℕ) => (epsTrans (d z.1)).filterMap (fun t =>
      if t.1 = z.2.1 then some (t.2.2.2, z.2.2 ++ t.2.1) else none) :=
    Primrec.listFilterMap (primrec_epsTrans (hd.comp Primrec.fst)) hif.to₂
  exact Primrec.list_append.comp hacc (Primrec.list_flatMap hacc hfm.to₂)

theorem primrec_epsPaths {d : γ → RelCode} {k p : γ → ℕ}
    (hd : Primrec d) (hk : Primrec k) (hp : Primrec p) :
    Primrec fun x => epsPaths (d x) (k x) (p x) := by
  have hg : Primrec fun x => [(p x, ([] : List ℕ))] :=
    Primrec.list_cons.comp (Primrec.pair hp (Primrec.const [])) (Primrec.const [])
  have hh : Primrec fun w : γ × (ℕ × List (ℕ × List ℕ)) => epsStep (d w.1) w.2.2 :=
    primrec_epsStep (hd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_rec' hk hg hh.to₂

theorem primrec_epsBound {d : γ → RelCode} (hd : Primrec d) :
    Primrec fun x => epsBound (d x) :=
  Primrec.list_length.comp (Primrec.fst.comp hd)

theorem primrec_sts {d : γ → RelCode} (hd : Primrec d) : Primrec fun x => sts (d x) := by
  have h1 : Primrec fun x => (d x).2.1 := Primrec.fst.comp (Primrec.snd.comp hd)
  have h2 : Primrec fun x => (d x).1.map (fun t : ℕ × List ℕ × List ℕ × ℕ => t.1) :=
    Primrec.list_map (Primrec.fst.comp hd) (Primrec.fst.comp Primrec.snd).to₂
  have h3 : Primrec fun x => (d x).1.map (fun t : ℕ × List ℕ × List ℕ × ℕ => t.2.2.2) :=
    Primrec.list_map (Primrec.fst.comp hd)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3

theorem primrec_invTrans {d : γ → RelCode} (hd : Primrec d) :
    Primrec fun x => invTrans (d x) := by
  -- innermost: `t` ranges over the transitions of the code
  have hcond : PrimrecPred fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      v.2.1 = v.1.2.1 ∧ v.2.2.2.1.length = 1 := by
    have h1 : PrimrecPred fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
        v.2.1 = v.1.2.1 :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have h2 : PrimrecPred fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
        v.2.2.2.1.length = 1 :=
      PrimrecRel.comp Primrec.eq
        (Primrec.list_length.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const 1)
    exact h1.and h2
  have hhd : Primrec fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      v.2.2.2.1.headD 0 := by
    have h1 : Primrec fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
        (v.2.2.2.1.head?).getD 0 :=
      Primrec.option_getD.comp
        (Primrec.list_head?.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const 0)
    exact h1.of_eq fun v => by cases v.2.2.2.1 <;> rfl
  have hthen : Primrec fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      [(v.1.1.2, v.2.2.2.1.headD 0, v.1.2.2 ++ v.2.2.1, v.2.2.2.2)] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair hhd
          (Primrec.pair
            (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
              (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
      (Primrec.const [])
  have hif : Primrec fun v : ((γ × ℕ) × (ℕ × List ℕ)) × (ℕ × List ℕ × List ℕ × ℕ) =>
      if v.2.1 = v.1.2.1 ∧ v.2.2.2.1.length = 1 then
        [(v.1.1.2, v.2.2.2.1.headD 0, v.1.2.2 ++ v.2.2.1, v.2.2.2.2)] else [] :=
    Primrec.ite hcond hthen (Primrec.const [])
  have hmid : Primrec fun w : (γ × ℕ) × (ℕ × List ℕ) => (d w.1.1).1.flatMap (fun t =>
      if t.1 = w.2.1 ∧ t.2.2.1.length = 1 then
        [(w.1.2, t.2.2.1.headD 0, w.2.2 ++ t.2.1, t.2.2.2)] else []) :=
    Primrec.list_flatMap (Primrec.fst.comp (hd.comp (Primrec.fst.comp Primrec.fst))) hif.to₂
  have houter : Primrec fun z : γ × ℕ =>
      (epsPaths (d z.1) (epsBound (d z.1)) z.2).flatMap (fun y =>
        (d z.1).1.flatMap (fun t =>
          if t.1 = y.1 ∧ t.2.2.1.length = 1 then
            [(z.2, t.2.2.1.headD 0, y.2 ++ t.2.1, t.2.2.2)] else [])) :=
    Primrec.list_flatMap
      (primrec_epsPaths (hd.comp Primrec.fst)
        (primrec_epsBound (hd.comp Primrec.fst)) Primrec.snd) hmid.to₂
  exact Primrec.list_flatMap (primrec_sts hd) houter.to₂

theorem primrec_invTerm {d : γ → RelCode} (hd : Primrec d) :
    Primrec fun x => invTerm (d x) := by
  have hcond : PrimrecPred fun w : (γ × ℕ) × (ℕ × List ℕ) => w.2.1 ∈ (d w.1.1).2.2 :=
    Primrec.list_mem.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp (hd.comp (Primrec.fst.comp Primrec.fst))))
  have hthen : Primrec fun w : (γ × ℕ) × (ℕ × List ℕ) => [(w.1.2, w.2.2)] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])
  have hif : Primrec fun w : (γ × ℕ) × (ℕ × List ℕ) =>
      if w.2.1 ∈ (d w.1.1).2.2 then [(w.1.2, w.2.2)] else [] :=
    Primrec.ite hcond hthen (Primrec.const [])
  have houter : Primrec fun z : γ × ℕ =>
      (epsPaths (d z.1) (epsBound (d z.1)) z.2).flatMap (fun y =>
        if y.1 ∈ (d z.1).2.2 then [(z.2, y.2)] else []) :=
    Primrec.list_flatMap
      (primrec_epsPaths (hd.comp Primrec.fst)
        (primrec_epsBound (hd.comp Primrec.fst)) Primrec.snd) hif.to₂
  exact Primrec.list_flatMap (primrec_sts hd) houter.to₂

theorem primrec_invLCode {d : γ → RelCode} (hd : Primrec d) :
    Primrec fun x => invLCode (d x) :=
  Primrec.pair (primrec_invTrans hd)
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp hd)) (primrec_invTerm hd))

/-! ## The product of a code with a letter automaton -/

theorem primrec_apStep {L : γ → LCode} {acc : γ → List (ℕ × List ℕ)} {a : γ → ℕ}
    (hL : Primrec L) (hacc : Primrec acc) (ha : Primrec a) :
    Primrec fun x => apStep (L x) (acc x) (a x) := by
  have hcond : PrimrecPred fun v : (γ × (ℕ × List ℕ)) × (ℕ × ℕ × List ℕ × ℕ) =>
      v.2.1 = v.1.2.1 ∧ v.2.2.1 = a v.1.1 := by
    have h1 : PrimrecPred fun v : (γ × (ℕ × List ℕ)) × (ℕ × ℕ × List ℕ × ℕ) =>
        v.2.1 = v.1.2.1 :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have h2 : PrimrecPred fun v : (γ × (ℕ × List ℕ)) × (ℕ × ℕ × List ℕ × ℕ) =>
        v.2.2.1 = a v.1.1 :=
      PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (ha.comp (Primrec.fst.comp Primrec.fst))
    exact h1.and h2
  have hthen : Primrec fun v : (γ × (ℕ × List ℕ)) × (ℕ × ℕ × List ℕ × ℕ) =>
      some (v.2.2.2.2, v.1.2.2 ++ v.2.2.2.1) :=
    Primrec.option_some.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  have hif : Primrec fun v : (γ × (ℕ × List ℕ)) × (ℕ × ℕ × List ℕ × ℕ) =>
      if v.2.1 = v.1.2.1 ∧ v.2.2.1 = a v.1.1 then some (v.2.2.2.2, v.1.2.2 ++ v.2.2.2.1)
      else none := Primrec.ite hcond hthen (Primrec.const none)
  have hfm : Primrec fun w : γ × (ℕ × List ℕ) => (L w.1).1.filterMap (fun t =>
      if t.1 = w.2.1 ∧ t.2.1 = a w.1 then some (t.2.2.2, w.2.2 ++ t.2.2.1) else none) :=
    Primrec.listFilterMap (Primrec.fst.comp (hL.comp Primrec.fst)) hif.to₂
  exact Primrec.list_flatMap hacc hfm.to₂

theorem primrec_allPathsOver {L : γ → LCode} {s : γ → ℕ} {y : γ → List ℕ}
    (hL : Primrec L) (hs : Primrec s) (hy : Primrec y) :
    Primrec fun x => allPathsOver (L x) (s x) (y x) := by
  have hg : Primrec fun x => [(s x, ([] : List ℕ))] :=
    Primrec.list_cons.comp (Primrec.pair hs (Primrec.const [])) (Primrec.const [])
  have hh : Primrec fun w : γ × (List (ℕ × List ℕ) × ℕ) =>
      apStep (L w.1) w.2.1 w.2.2 :=
    primrec_apStep (hL.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldl hy hg hh.to₂

theorem primrec_pair {q s : γ → ℕ} (hq : Primrec q) (hs : Primrec s) :
    Primrec fun x => pair (q x) (s x) :=
  Primrec.encode.comp (Primrec.sumInl.comp (Primrec.pair hq hs))

theorem primrec_prodTrans {c : γ → RelCode} {L : γ → LCode} (hc : Primrec c) (hL : Primrec L) :
    Primrec fun x => prodTrans (c x) (L x) := by
  -- the transitions coming from a transition of the code
  have hval : Primrec fun v : ((γ × (ℕ × List ℕ × List ℕ × ℕ)) × ℕ) × (ℕ × List ℕ) =>
      (pair v.1.1.2.1 v.1.2, v.1.1.2.2.1, v.2.2, pair v.1.1.2.2.2.2 v.2.1) :=
    Primrec.pair
      (primrec_pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair (Primrec.snd.comp Primrec.snd)
          (primrec_pair
            (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
            (Primrec.fst.comp Primrec.snd))))
  have hmap : Primrec fun w : (γ × (ℕ × List ℕ × List ℕ × ℕ)) × ℕ =>
      (allPathsOver (L w.1.1) w.2 w.1.2.2.2.1).map (fun z =>
        (pair w.1.2.1 w.2, w.1.2.2.1, z.2, pair w.1.2.2.2.2 z.1)) :=
    Primrec.list_map
      (primrec_allPathsOver (hL.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
      hval.to₂
  have hmid : Primrec fun z : γ × (ℕ × List ℕ × List ℕ × ℕ) =>
      (states (L z.1)).flatMap (fun s =>
        (allPathsOver (L z.1) s z.2.2.2.1).map (fun y =>
          (pair z.2.1 s, z.2.2.1, y.2, pair z.2.2.2.2 y.1))) :=
    Primrec.list_flatMap (primrec_states (hL.comp Primrec.fst)) hmap.to₂
  have h1 : Primrec fun x => (c x).1.flatMap (fun t =>
      (states (L x)).flatMap (fun s =>
        (allPathsOver (L x) s t.2.2.1).map (fun y =>
          (pair t.1 s, t.2.1, y.2, pair t.2.2.2 y.1)))) :=
    Primrec.list_flatMap (Primrec.fst.comp hc) hmid.to₂
  -- the transitions to the sink
  have hval2 : Primrec fun v : (γ × ℕ) × (ℕ × List ℕ) =>
      (pair v.1.2 v.2.1, ([] : List ℕ), v.2.2, sink) :=
    Primrec.pair (primrec_pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const sink)))
  have hmid2 : Primrec fun z : γ × ℕ =>
      (L z.1).2.2.map (fun e => (pair z.2 e.1, ([] : List ℕ), e.2, sink)) :=
    Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp (hL.comp Primrec.fst))) hval2.to₂
  have h2 : Primrec fun x => (c x).2.2.flatMap (fun q =>
      (L x).2.2.map (fun e => (pair q e.1, ([] : List ℕ), e.2, sink))) :=
    Primrec.list_flatMap (Primrec.snd.comp (Primrec.snd.comp hc)) hmid2.to₂
  -- the dummy loop carrying the alphabet
  have hval3 : Primrec fun z : γ × ℕ => (dummy, [z.2], ([] : List ℕ), dummy) :=
    Primrec.pair (Primrec.const dummy)
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
        (Primrec.pair (Primrec.const []) (Primrec.const dummy)))
  have h3 : Primrec fun x => (codeAlphabet (c x)).map (fun a =>
      (dummy, [a], ([] : List ℕ), dummy)) :=
    Primrec.list_map (primrec_codeAlphabet.comp hc) hval3.to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3

theorem primrec_prodCode {c : γ → RelCode} {L : γ → LCode} (hc : Primrec c) (hL : Primrec L) :
    Primrec fun x => prodCode (c x) (L x) := by
  have hmap : Primrec fun z : γ × ℕ => (L z.1).2.1.map (fun s => pair z.2 s) :=
    Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp (hL.comp Primrec.fst)))
      (primrec_pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hin : Primrec fun x => (c x).2.1.flatMap (fun q => (L x).2.1.map (fun s => pair q s)) :=
    Primrec.list_flatMap (Primrec.fst.comp (Primrec.snd.comp hc)) hmap.to₂
  exact Primrec.pair (primrec_prodTrans hc hL) (Primrec.pair hin (Primrec.const [sink]))

/-! ## The section and the composition -/

theorem primrec_secLCode {c : γ → RelCode} (hc : Primrec c) :
    Primrec fun x => secLCode (c x) :=
  primrec_unifLCode (primrec_invLCode (Split.primrec_splitCode hc))

theorem primrec_invCode {c : γ → RelCode} (hc : Primrec c) :
    Primrec fun x => invCode (c x) :=
  primrec_prodCode hc (primrec_secLCode hc)

/-- **The composition of a code with a section of it is computable in the code.** -/
theorem computable_invCode : Computable invCode := (primrec_invCode Primrec.id).to_comp

end LAut

end Transducers.Exercises
