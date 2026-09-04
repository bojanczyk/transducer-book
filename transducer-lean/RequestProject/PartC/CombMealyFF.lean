/-
Lemma `lem:terms-define-flip-flop` of Section *Combinators* of *Transducers* (M. Bojańczyk):
every flip-flop Mealy machine is definable by a regular term.

The construction is the book's.  A flip-flop machine has two kinds of input letters: those that
leave the state unchanged, and those that reset it to a fixed state.  A homomorphism annotates each
reset letter with the state that it produces,

    `A* → (A + Q)*`,

and the split function of Example `ex:split` cuts the annotated string at those annotations,
giving an element of `A* × (Q × A*)*`.  Each block then carries the state that the machine is in
while reading it -- the state cannot change inside a block, because a block contains a reset letter
only as its last letter -- so the output of the machine on a block is a homomorphic image of it,
and the state that determines which homomorphism is a coordinate of a *finite* type, which a term
can branch on (`Transducers.tfun_finCases`).  Concatenating the results gives the output.

The file also contains the renaming of the alphabets and states of a Mealy machine
(`Transducers.Mealy.transport`), which is what lets a machine over abstract alphabets be replaced
by one over the elements of types.
-/
import RequestProject.PartC.CombStrFam

namespace Transducers

namespace Mealy

variable {X Y Q X' Y' Q' : Type}

/-! ## Renaming the alphabets and the states of a Mealy machine -/

/-- The Mealy machine obtained by renaming the input alphabet, the output alphabet and the state
space of `M` along three bijections. -/
def transport (M : Mealy X Y Q) (eX : X' ≃ X) (eY : Y ≃ Y') (eQ : Q ≃ Q') : Mealy X' Y' Q' where
  init := eQ M.init
  step := fun q a =>
    (eQ (M.step (eQ.symm q) (eX a)).1, eY (M.step (eQ.symm q) (eX a)).2)

lemma run_transport (M : Mealy X Y Q) (eX : X' ≃ X) (eY : Y ≃ Y') (eQ : Q ≃ Q') :
    ∀ (q : Q) (l : List X'),
      (M.transport eX eY eQ).run (eQ q) l = (M.run q (l.map eX)).map eY := by
  intro q l
  induction l generalizing q with
  | nil => rfl
  | cons a l ih =>
      show ((M.transport eX eY eQ).step (eQ q) a).2
          :: (M.transport eX eY eQ).run ((M.transport eX eY eQ).step (eQ q) a).1 l = _
      have h1 : ((M.transport eX eY eQ).step (eQ q) a).1 = eQ (M.step q (eX a)).1 := by
        simp [transport]
      have h2 : ((M.transport eX eY eQ).step (eQ q) a).2 = eY (M.step q (eX a)).2 := by
        simp [transport]
      rw [h1, h2, ih]
      simp

lemma eval_transport (M : Mealy X Y Q) (eX : X' ≃ X) (eY : Y ≃ Y') (eQ : Q ≃ Q') (l : List X') :
    (M.transport eX eY eQ).eval l = (M.eval (l.map eX)).map eY :=
  run_transport M eX eY eQ M.init l

lemma letterTrans_transport (M : Mealy X Y Q) (eX : X' ≃ X) (eY : Y ≃ Y') (eQ : Q ≃ Q')
    (a : X') (q : Q') :
    (M.transport eX eY eQ).letterTrans a q = eQ (M.letterTrans (eX a) (eQ.symm q)) := rfl

lemma flipFlop_transport {M : Mealy X Y Q} (hM : M.FlipFlop) (eX : X' ≃ X) (eY : Y ≃ Y')
    (eQ : Q ≃ Q') : (M.transport eX eY eQ).FlipFlop := by
  intro a
  rcases hM (eX a) with hid | ⟨q₀, hq₀⟩
  · refine Or.inl (funext fun q => ?_)
    rw [letterTrans_transport, show M.letterTrans (eX a) (eQ.symm q) = eQ.symm q from
      congrFun hid _]
    simp
  · exact Or.inr ⟨eQ q₀, fun q => by rw [letterTrans_transport, hq₀]⟩

lemma reversible_transport {M : Mealy X Y Q} (hM : M.Reversible) (eX : X' ≃ X) (eY : Y ≃ Y')
    (eQ : Q ≃ Q') : (M.transport eX eY eQ).Reversible := by
  intro a
  have : (M.transport eX eY eQ).letterTrans a = eQ ∘ M.letterTrans (eX a) ∘ eQ.symm := rfl
  rw [this]
  exact (eQ.bijective.comp ((hM (eX a)).comp eQ.symm.bijective))

/-! ## The annotation of the reset letters of a flip-flop machine -/

open Classical in
/-- For a flip-flop machine, the state that the letter `a` resets to, and `none` when `a` leaves
the state unchanged. -/
noncomputable def ffTarget (M : Mealy X Y Q) (a : X) : Option Q :=
  if (∀ q, M.letterTrans a q = q) then none else some (M.letterTrans a M.init)

lemma ffTarget_spec (M : Mealy X Y Q) (hM : M.FlipFlop) (a : X) :
    (M.ffTarget a = none ∧ ∀ q, M.letterTrans a q = q) ∨
      (∃ r, M.ffTarget a = some r ∧ ∀ q, M.letterTrans a q = r) := by
  unfold ffTarget
  by_cases h : ∀ q, M.letterTrans a q = q
  · exact Or.inl ⟨if_pos h, h⟩
  · refine Or.inr ⟨M.letterTrans a M.init, if_neg h, ?_⟩
    rcases hM a with hid | ⟨q₀, hq₀⟩
    · exact absurd (fun q => by rw [hid]; rfl) h
    · intro q; rw [hq₀, hq₀]

/-- The homomorphism `A* → (A + Q)*` of step 1 of the proof: each reset letter is followed by the
state that it produces. -/
noncomputable def ffHom (M : Mealy X Y Q) (a : X) : List (X ⊕ Q) :=
  match M.ffTarget a with
  | none => [Sum.inl a]
  | some r => [Sum.inl a, Sum.inr r]

/-- **The run of a flip-flop machine, read off the split of its annotation.**  This is steps 2 and
3 of the book's proof: each block of the split is read in a single state, so the output on it is
the homomorphic image of the block determined by that state. -/
lemma ff_run (M : Mealy X Y Q) (hM : M.FlipFlop) :
    ∀ (q : Q) (w : List X),
      M.run q w =
        (splitList ((w.map M.ffHom).flatten)).1.map (fun a => (M.step q a).2) ++
          ((splitList ((w.map M.ffHom).flatten)).2.map
            (fun p => p.2.map (fun a => (M.step p.1 a).2))).flatten := by
  intro q w
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
      rcases ffTarget_spec M hM a with ⟨h0, hid⟩ | ⟨r, h0, hr⟩
      · have hfl : ((a :: w).map M.ffHom).flatten
            = Sum.inl a :: (w.map M.ffHom).flatten := by
          simp [ffHom, h0]
        rw [hfl, splitList_inl, run_cons, show (M.step q a).1 = q from hid q, ih q]
        simp
      · have hfl : ((a :: w).map M.ffHom).flatten
            = Sum.inl a :: Sum.inr r :: (w.map M.ffHom).flatten := by
          simp [ffHom, h0]
        rw [hfl, splitList_inl, splitList_inr, run_cons, show (M.step q a).1 = r from hr q, ih r]
        simp

end Mealy

/-! ## Lemma `lem:terms-define-flip-flop` -/

/-- The version of Lemma `lem:terms-define-flip-flop` for a machine whose alphabets and states are
the elements of types. -/
theorem tfun_flipFlop_eval {A B QT : Ty} (hA : Finite A.Elt) (hQ : Finite QT.Elt)
    (M : Mealy A.Elt B.Elt QT.Elt) (hM : M.FlipFlop) :
    IsRegularTermFun (A := .list A) (B := .list B) M.eval := by
  have h1 : IsRegularTermFun (A := .list A) (B := .list (.sum A QT))
      (fun l => (l.map M.ffHom).flatten) :=
    terms_define_string_homomorphisms (B := .sum A QT) hA M.ffHom
  have h3 : IsRegularTermFun (A := .list A) (B := .list B)
      (fun l => l.map (fun a => (M.step M.init a).2)) := tfun_mapRen hA _
  have h4 : IsRegularTermFun (A := .prod QT (.list A)) (B := .list B)
      (fun p => p.2.map (fun a => (M.step p.1 a).2)) :=
    tfun_finCases (F := QT) (T := .list A) (U := .list B) hQ
      (g := fun q v => v.map (fun a => (M.step q a).2)) (fun q => tfun_mapRen hA _)
  have h5 := (h4.mapList).comp (tfun_concat B)
  have h6 := (tfun_prodMap h3 h5).comp (tfun_append B)
  refine (h1.comp ((tfun_split A QT).comp h6)).congr ?_
  intro l
  exact (Mealy.ff_run M hM M.init l).symm

/-- **Lemma `lem:terms-define-flip-flop`.**  Every flip-flop Mealy machine is definable by a
regular term. -/
theorem terms_define_flip_flop {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsFlipFlopMealy g) : TermStrFun g := by
  obtain ⟨Q, hQ, M, hMg, hFF⟩ := h
  subst hMg
  haveI := hX
  haveI := hY
  haveI := hQ
  by_cases hne : Nonempty X
  case neg => exact termStrFun_of_isEmpty_dom _ (not_nonempty_iff.1 hne)
  by_cases hne' : Nonempty Y
  case neg => exact termStrFun_of_isEmpty_cod _ (not_nonempty_iff.1 hne')
  haveI := hne
  haveI := hne'
  haveI : Nonempty Q := ⟨M.init⟩
  obtain ⟨A, ⟨eA⟩, hAf⟩ := exists_ty_equiv X
  obtain ⟨B, ⟨eB⟩, hBf⟩ := exists_ty_equiv Y
  obtain ⟨QT, ⟨eQ⟩, hQf⟩ := exists_ty_equiv Q
  refine termStrFun_of_one A B hBf eA.symm eB ?_
  exact (tfun_flipFlop_eval hAf hQf (M.transport eA.symm eB eQ)
    (Mealy.flipFlop_transport hFF _ _ _)).congr
    (fun l => Mealy.eval_transport M eA.symm eB eQ l)

end Transducers
