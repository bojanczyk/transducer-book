/-
Part D, Section *A functional programming language*: a computation of the machine describes a
solution of the tiling problem.

This is the second half of the reduction proving Lemma `lem:tiling`.  A computation of the machine
`M` on the input `w` -- a sequence of configurations of a fixed width, the first of which is the
starting configuration and the last of which contains the accepting state -- is written in the
grid: the row `j` carries the letters of the configuration `j`, together with the letters of the
configuration below and the rôle each cell plays in the rewriting between the two.

The data of such a computation is `Transducers.TilingRed.CompData`, and
`Transducers.TilingRed.isSolution_gcell` says that the grid it builds is a solution.
-/
import RequestProject.PartD.TilingRows

namespace Transducers
namespace TilingRed

open PCP

variable {M : TM} {w : List ℕ} {x y : Cell}

/-! ## Introduction rules for the conditions on cells -/

lemma validB_intro
    (hk : x.k ≤ 1) (hnk : x.nk ≤ 1) (hrole : x.role ≤ 5)
    (hv : if x.k = 0 then x.v ∈ M.tapeSyms w else x.v ∈ M.states)
    (hnv : if x.nk = 0 then x.nv ∈ M.tapeSyms w else x.nv ∈ M.states)
    (haux4 : x.role = 4 → x.aux ∈ M.states) (haux : x.role ≠ 4 → x.aux = 0)
    (hkind0 : x.role = 0 → x.nk = x.k ∧ x.nv = x.v)
    (hkind1 : x.role = 1 → x.k = 1 ∧ x.nk = 0)
    (hkind2 : x.role = 2 → x.k = 0 ∧ x.nk = 1)
    (hkind3 : x.role = 3 → x.k = 0 ∧ x.nk = 1)
    (hkind4 : x.role = 4 → x.k = 1 ∧ x.nk = 0)
    (hkind5 : x.role = 5 → x.k = 0 ∧ x.nk = 0)
    (hlb : x.lb = true → (x.role = 0 ∨ x.role = 1 ∨ x.role = 3))
    (hrb : x.rb = true → (x.role = 0 ∨ x.role = 2 ∨ x.role = 5))
    (hacc : x.lb = true → x.acc = (decide (x.k = 1) && decide (x.v = M.qacc)))
    (htop1 : x.top = true → x.cnt ≤ w.length + 1)
    (htop2 : x.top = true → x.role = 0)
    (htop3 : x.top = true → x.cnt = 0 → x.k = 1 ∧ x.v = M.q0)
    (htop4 : x.top = true → x.cnt ≠ 0 → x.k = 0 ∧ x.v = w.getD (x.cnt - 1) 0)
    (htop5 : x.top = true → x.rb = true → x.cnt = w.length + 1)
    (htop6 : x.top = true → x.fin = false)
    (hntop : x.top = false → x.cnt = 0)
    (hfin : x.fin = true → (x.k = 0 ∧ x.v = 0 ∧ x.nk = 0 ∧ x.nv = 0 ∧ x.role = 0 ∧
       x.aux = 0 ∧ x.acc = false)) :
    validB M w x = true := by
  unfold validB
  cases hl : x.lb <;> cases hr : x.rb <;> cases ht : x.top <;> cases hf : x.fin <;>
    simp_all <;> omega

lemma horizB_intro
    (hlb : y.lb = false) (hrb : x.rb = false) (htop : x.top = y.top) (hfin : x.fin = y.fin)
    (hcnt : x.top = true → y.cnt = min (x.cnt + 1) (w.length + 1))
    (hacc : y.acc = (x.acc || (decide (y.k = 1) && decide (y.v = M.qacc))))
    (hr0 : x.role = 0 → (y.role = 0 ∨ y.role = 1 ∨ y.role = 3))
    (hr1 : x.role = 1 → y.role = 2 ∧ (x.v, y.v, y.nv, x.nv, true) ∈ M.trans)
    (hr2 : x.role = 2 → y.role = 0)
    (hr3 : x.role = 3 → y.role = 4 ∧ x.nv = y.aux ∧ y.nv = x.v)
    (hr4 : x.role = 4 → y.role = 5 ∧ (x.v, y.v, x.aux, y.nv, false) ∈ M.trans)
    (hr5 : x.role ≠ 0 → x.role ≠ 1 → x.role ≠ 2 → x.role ≠ 3 → x.role ≠ 4 → y.role = 0) :
    horizB M w x y = true := by
  unfold horizB
  cases hxt : x.top <;> split_ifs with h0 h1 h2 h3 h4 <;> simp_all

lemma vertB_intro
    (h1 : x.fin = false) (h2 : x.lb = y.lb) (h3 : x.rb = y.rb) (h4 : y.top = false)
    (h5 : y.cnt = 0) (h6 : y.fin = true → y.rb = true → x.acc = true)
    (h7 : y.fin = false → y.k = x.nk ∧ y.v = x.nv) :
    vertB x y = true := by
  unfold vertB
  cases hy : y.fin <;> cases hr : y.rb <;> simp_all

/-! ## The letters of a configuration -/

/-- The blank tape symbol. -/
def blank : Sym := Sym.tape 0

/-- The kind of a letter: `1` for a state, `0` for a tape symbol. -/
def kindOf : Sym → ℕ
  | Sym.state _ => 1
  | _ => 0

/-- The value of a letter. -/
def valOf : Sym → ℕ
  | Sym.tape a => a
  | Sym.state q => q
  | _ => 0

lemma kindOf_le (s : Sym) : kindOf s ≤ 1 := by cases s <;> simp [kindOf]

lemma alph_cases {s : Sym} (h : s ∈ M.alphabet w) :
    (kindOf s = 0 ∧ valOf s ∈ M.tapeSyms w) ∨ (kindOf s = 1 ∧ valOf s ∈ M.states) := by
  simp only [TM.alphabet, List.mem_append, List.mem_map] at h
  rcases h with ⟨a, ha, rfl⟩ | ⟨q, hq, rfl⟩
  · exact Or.inl ⟨rfl, ha⟩
  · exact Or.inr ⟨rfl, hq⟩

lemma blank_mem_alphabet (M : TM) (w : List ℕ) : blank ∈ M.alphabet w :=
  M.tape_mem_alphabet w (M.blank_mem_tapeSyms w)

/-! ## What happens between two consecutive rows -/

/-- **The action performed between a row and the row below it**: nothing, an application of a rule
`q a ⟶ b r` at a position, or an application of a rule `c q a ⟶ r c b` at a position. -/
inductive Act where
  /-- Nothing happens. -/
  | idle : Act
  /-- The rule `q a ⟶ b r` is applied at the position `p`. -/
  | right (p q a r b : ℕ) : Act
  /-- The rule `c q a ⟶ r c b` is applied at the position `p`. -/
  | left (p q a r b c : ℕ) : Act
  deriving DecidableEq, Inhabited

/-- The rôle of the cell at the position `i` of a row performing the action. -/
def roleAt : Act → ℕ → ℕ
  | .idle, _ => 0
  | .right p _ _ _ _, i => if i = p then 1 else if i = p + 1 then 2 else 0
  | .left p _ _ _ _ _, i =>
      if i = p then 3 else if i = p + 1 then 4 else if i = p + 2 then 5 else 0

/-- The new state recorded by the cell at the position `i` of a row performing the action. -/
def auxAt : Act → ℕ → ℕ
  | .left p _ _ r _ _, i => if i = p + 1 then r else 0
  | _, _ => 0

/-- The action transforms the letters of a row into the letters of the row below. -/
def StepAt (M : TM) (u v : List Sym) : Act → Prop
  | .idle => v = u
  | .right p q a r b => (q, a, r, b, true) ∈ M.trans ∧ p + 1 < u.length ∧
      u.getD p blank = Sym.state q ∧ u.getD (p + 1) blank = Sym.tape a ∧
      v.getD p blank = Sym.tape b ∧ v.getD (p + 1) blank = Sym.state r ∧
      ∀ i, i ≠ p → i ≠ p + 1 → v.getD i blank = u.getD i blank
  | .left p q a r b c => (q, a, r, b, false) ∈ M.trans ∧ p + 2 < u.length ∧
      u.getD p blank = Sym.tape c ∧ u.getD (p + 1) blank = Sym.state q ∧
      u.getD (p + 2) blank = Sym.tape a ∧
      v.getD p blank = Sym.state r ∧ v.getD (p + 1) blank = Sym.tape c ∧
      v.getD (p + 2) blank = Sym.tape b ∧
      ∀ i, i ≠ p → i ≠ p + 1 → i ≠ p + 2 → v.getD i blank = u.getD i blank

/-- Whether the accepting state occurs in the row at or before the position `i`. -/
def accUpTo (M : TM) (u : List Sym) (i : ℕ) : Bool :=
  (List.range (i + 1)).any fun p => u.getD p blank == Sym.state M.qacc

lemma accUpTo_zero (M : TM) (u : List Sym) :
    accUpTo M u 0 = (u.getD 0 blank == Sym.state M.qacc) := by simp [accUpTo]

lemma accUpTo_succ (M : TM) (u : List Sym) (i : ℕ) :
    accUpTo M u (i + 1) = (accUpTo M u i || (u.getD (i + 1) blank == Sym.state M.qacc)) := by
  simp [accUpTo, List.range_succ, Bool.or_assoc]

lemma accUpTo_of_mem (M : TM) {u : List Sym} {i : ℕ} (h : Sym.state M.qacc ∈ u)
    (hi : u.length ≤ i + 1) : accUpTo M u i = true := by
  obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp h
  refine List.any_eq_true.2 ⟨p, List.mem_range.2 (by omega), ?_⟩
  rw [List.getD_eq_getElem _ _ hp, hpe]
  simp

lemma beq_state_eq (s : Sym) (q : ℕ) :
    (s == Sym.state q) = (decide (kindOf s = 1) && decide (valOf s = q)) := by
  cases s with
  | tape a => simp [kindOf, valOf]
  | state q' => by_cases h : q' = q <;> simp [kindOf, valOf, h]
  | hash => simp [kindOf, valOf]
  | start => simp [kindOf, valOf]
  | star => simp [kindOf, valOf]
  | diamond => simp [kindOf, valOf]

/-! ## Reading the action off -/

section Step
variable {u v : List Sym} {A : Act} {N : ℕ}

lemma roleAt_le (A : Act) (i : ℕ) : roleAt A i ≤ 5 := by
  cases A <;> simp only [roleAt] <;> (try split_ifs) <;> omega

lemma roleAt_zero (A : Act) : roleAt A 0 = 0 ∨ roleAt A 0 = 1 ∨ roleAt A 0 = 3 := by
  cases A with
  | idle => simp [roleAt]
  | right p q a r b => by_cases hp : 0 = p <;> simp [roleAt, hp]
  | left p q a r b c => by_cases hp : 0 = p <;> simp [roleAt, hp]

lemma roleAt_last (h : StepAt M u v A) (hlen : u.length = N + 1) :
    roleAt A N = 0 ∨ roleAt A N = 2 ∨ roleAt A N = 5 := by
  cases A with
  | idle => simp [roleAt]
  | right p q a r b =>
      obtain ⟨-, hp, -⟩ := h
      rw [hlen] at hp
      by_cases h1 : N = p
      · omega
      · by_cases h2 : N = p + 1 <;> simp [roleAt, h1, h2]
  | left p q a r b c =>
      obtain ⟨-, hp, -⟩ := h
      rw [hlen] at hp
      by_cases h1 : N = p
      · omega
      · by_cases h2 : N = p + 1
        · omega
        · by_cases h3 : N = p + 2 <;> simp [roleAt, h1, h2, h3]

/-- What the action says about the cell at a position. -/
lemma stepAt_cell (h : StepAt M u v A) (i : ℕ) :
    (roleAt A i = 0 → v.getD i blank = u.getD i blank) ∧
    (roleAt A i = 1 → kindOf (u.getD i blank) = 1 ∧ kindOf (v.getD i blank) = 0) ∧
    (roleAt A i = 2 → kindOf (u.getD i blank) = 0 ∧ kindOf (v.getD i blank) = 1) ∧
    (roleAt A i = 3 → kindOf (u.getD i blank) = 0 ∧ kindOf (v.getD i blank) = 1) ∧
    (roleAt A i = 4 → kindOf (u.getD i blank) = 1 ∧ kindOf (v.getD i blank) = 0) ∧
    (roleAt A i = 5 → kindOf (u.getD i blank) = 0 ∧ kindOf (v.getD i blank) = 0) ∧
    (roleAt A i = 4 → auxAt A i ∈ M.states) ∧ (roleAt A i ≠ 4 → auxAt A i = 0) := by
  cases A with
  | idle =>
      have hv : v = u := h
      subst hv
      refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt]
  | right p q a r b =>
      obtain ⟨htr, hlen, e1, e2, e3, e4, hrest⟩ := h
      by_cases hip : i = p
      · subst hip
        rw [e1, e3]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, kindOf]
      · by_cases hip1 : i = p + 1
        · subst hip1
          rw [e2, e4]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, hip, kindOf]
        · rw [hrest i hip hip1]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, hip, hip1]
  | left p q a r b c =>
      obtain ⟨htr, hlen, e1, e2, e3, e4, e5, e6, hrest⟩ := h
      have hr : r ∈ M.states := M.target_mem_states htr
      by_cases hip : i = p
      · subst hip
        rw [e1, e4]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, kindOf]
      · by_cases hip1 : i = p + 1
        · subst hip1
          rw [e2, e5]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, hip, kindOf, hr]
        · by_cases hip2 : i = p + 2
          · subst hip2
            rw [e3, e6]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [roleAt, auxAt, hip, hip1, kindOf]
          · rw [hrest i hip hip1 hip2]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [roleAt, auxAt, hip, hip1, hip2]

/-- What the action says about two horizontally adjacent cells. -/
lemma stepAt_horiz (h : StepAt M u v A) (i : ℕ) :
    (roleAt A i = 0 → roleAt A (i + 1) = 0 ∨ roleAt A (i + 1) = 1 ∨ roleAt A (i + 1) = 3) ∧
    (roleAt A i = 1 → roleAt A (i + 1) = 2 ∧
       (valOf (u.getD i blank), valOf (u.getD (i + 1) blank), valOf (v.getD (i + 1) blank),
        valOf (v.getD i blank), true) ∈ M.trans) ∧
    (roleAt A i = 2 → roleAt A (i + 1) = 0) ∧
    (roleAt A i = 3 → roleAt A (i + 1) = 4 ∧ valOf (v.getD i blank) = auxAt A (i + 1) ∧
       valOf (v.getD (i + 1) blank) = valOf (u.getD i blank)) ∧
    (roleAt A i = 4 → roleAt A (i + 1) = 5 ∧
       (valOf (u.getD i blank), valOf (u.getD (i + 1) blank), auxAt A i,
        valOf (v.getD (i + 1) blank), false) ∈ M.trans) ∧
    (roleAt A i ≠ 0 → roleAt A i ≠ 1 → roleAt A i ≠ 2 → roleAt A i ≠ 3 → roleAt A i ≠ 4 →
       roleAt A (i + 1) = 0) := by
  cases A with
  | idle => refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt]
  | right p q a r b =>
      obtain ⟨htr, hlen, e1, e2, e3, e4, hrest⟩ := h
      by_cases hip : i = p
      · subst hip
        rw [e1, e2, e3, e4]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, valOf, htr]
      · by_cases hip1 : i = p + 1
        · subst hip1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt] <;> omega
        · by_cases hip2 : i + 1 = p
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, hip, hip1, hip2]
          · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [roleAt, auxAt, hip, hip1, hip2, show i + 1 ≠ p + 1 by omega]
  | left p q a r b c =>
      obtain ⟨htr, hlen, e1, e2, e3, e4, e5, e6, hrest⟩ := h
      by_cases hip : i = p
      · subst hip
        rw [e1, e2, e4, e5]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, valOf]
      · by_cases hip1 : i = p + 1
        · subst hip1
          rw [show p + 1 + 1 = p + 2 from rfl, e2, e3, e5, e6]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [roleAt, auxAt, hip, valOf, htr]
        · by_cases hip2 : i = p + 2
          · subst hip2
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [roleAt, auxAt, hip, hip1, show p + 2 + 1 ≠ p by omega,
                show p + 2 + 1 ≠ p + 1 by omega, show p + 2 + 1 ≠ p + 2 by omega]
          · by_cases hip3 : i + 1 = p
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [roleAt, auxAt, hip, hip1, hip2, hip3]
            · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                simp [roleAt, auxAt, hip, hip1, hip2, hip3,
                  show i + 1 ≠ p + 1 by omega, show i + 1 ≠ p + 2 by omega]

end Step

/-! ## The cells of the machine, as codes -/

section Cells
variable {M : TM} {w : List ℕ}

lemma validB_k_le (h : validB M w x = true) : x.k ≤ 1 := by
  simp only [validB, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_nk_le (h : validB M w x = true) : x.nk ≤ 1 := by
  simp only [validB, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_role_le (h : validB M w x = true) : x.role ≤ 5 := by
  simp only [validB, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_v_mem (h : validB M w x = true) : x.v ∈ M.tapeSyms w ++ M.states := by
  by_cases hk : x.k = 0
  · refine List.mem_append_left _ ?_
    simp only [validB, hk, Bool.and_eq_true] at h; simp at h; tauto
  · refine List.mem_append_right _ ?_
    simp only [validB, if_neg hk, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_nv_mem (h : validB M w x = true) : x.nv ∈ M.tapeSyms w ++ M.states := by
  by_cases hk : x.nk = 0
  · refine List.mem_append_left _ ?_
    simp only [validB, hk, Bool.and_eq_true] at h; simp at h; tauto
  · refine List.mem_append_right _ ?_
    simp only [validB, if_neg hk, Bool.and_eq_true] at h; simp at h; tauto

lemma validB_aux_mem (h : validB M w x = true) : x.aux ∈ 0 :: M.states := by
  by_cases hr : x.role = 4
  · have : x.aux ∈ M.states := by
      simp only [validB, hr, Bool.and_eq_true] at h; simp at h; tauto
    exact List.mem_cons_of_mem _ this
  · have : x.aux = 0 := by
      simp only [validB, Bool.and_eq_true] at h; simp [hr] at h; tauto
    simp [this]

lemma validB_cnt_le (h : validB M w x = true) : x.cnt ≤ w.length + 1 := by
  cases ht : x.top
  · have : x.cnt = 0 := by
      simp only [validB, ht, Bool.and_eq_true] at h; simp at h; tauto
    omega
  · exact validB_top_cnt h ht

/-- Every cell of the machine is enumerated. -/
lemma mem_allCells (h : validB M w x = true) : x ∈ allCells M w := by
  refine List.mem_filter.2 ⟨?_, h⟩
  refine List.mem_map.2 ⟨[x.k, x.v, x.nk, x.nv, x.role, x.aux,
    (if x.lb then 1 else 0), (if x.rb then 1 else 0), (if x.top then 1 else 0),
    (if x.fin then 1 else 0), (if x.acc then 1 else 0), x.cnt], ?_, ?_⟩
  · have hb : ∀ b : Bool, (if b then 1 else 0) ∈ [0, 1] := by intro b; cases b <;> simp
    simp only [fieldLists]
    refine cons_mem_tupleList ?_ (cons_mem_tupleList (validB_v_mem h)
      (cons_mem_tupleList ?_ (cons_mem_tupleList (validB_nv_mem h)
        (cons_mem_tupleList ?_ (cons_mem_tupleList (validB_aux_mem h)
          (cons_mem_tupleList (hb _) (cons_mem_tupleList (hb _)
            (cons_mem_tupleList (hb _) (cons_mem_tupleList (hb _)
              (cons_mem_tupleList (hb _) (cons_mem_tupleList ?_ nil_mem_tupleList)))))))))))
    · have := validB_k_le h; simp; omega
    · have := validB_nk_le h; simp; omega
    · have := validB_role_le h; simp [List.mem_range]; omega
    · have := validB_cnt_le h; simp [List.mem_range]; omega
  · rcases x with ⟨k, v, nk, nv, role, aux, lb, rb, top, fin, acc, cnt⟩
    cases lb <;> cases rb <;> cases top <;> cases fin <;> cases acc <;> simp [cellOfList]

private lemma le_foldr_max (x : Cell) :
    ∀ l : List Cell, x ∈ l → Encodable.encode x ≤ l.foldr (fun y m => max (Encodable.encode y) m) 0
  | [], h => absurd h (by simp)
  | y :: t, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · simp
      · exact le_trans (le_foldr_max x t h') (by simp)

lemma le_maxCode {x : Cell} (h : x ∈ allCells M w) : Encodable.encode x ≤ maxCode M w :=
  le_foldr_max x _ h

/-- A window of four cells of the machine satisfying the conditions is in the local
constraint. -/
lemma mem_constraint {a b c d : Cell} (hva : validB M w a = true) (hvb : validB M w b = true)
    (hvc : validB M w c = true) (hvd : validB M w d = true) (hwin : windowB M w a b c d = true) :
    (Encodable.encode a, Encodable.encode b, Encodable.encode c, Encodable.encode d) ∈
      (inst M w).constraint := by
  simp only [inst, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨a, mem_allCells hva, b, mem_allCells hvb, c, mem_allCells hvc, d,
    ⟨mem_allCells hvd, hwin⟩, rfl⟩

end Cells

/-! ## The grid built from a computation -/

/-- The cell at the position `(i,j)` of the grid built from a computation: the letter of the
configuration `j` at the position `i`, the letter of the configuration below, and the rôle the cell
plays in the action performed between the two.  The last row of the grid is blank. -/
def gcell (M : TM) (w : List ℕ) (N : ℕ) (cont : ℕ → List Sym) (act : ℕ → Act) (i j : ℕ) : Cell :=
  if j = N then
    { k := 0, v := 0, nk := 0, nv := 0, role := 0, aux := 0, lb := decide (i = 0),
      rb := decide (i = N), top := false, fin := true, acc := false, cnt := 0 }
  else
    { k := kindOf ((cont j).getD i blank), v := valOf ((cont j).getD i blank),
      nk := kindOf ((cont (j + 1)).getD i blank), nv := valOf ((cont (j + 1)).getD i blank),
      role := roleAt (act j) i, aux := auxAt (act j) i,
      lb := decide (i = 0), rb := decide (i = N), top := decide (j = 0), fin := false,
      acc := accUpTo M (cont j) i, cnt := if j = 0 then min i (w.length + 1) else 0 }

/-- **The data of a computation of the machine `M` on the input `w`**, written in a grid of
`N + 1` rows and `N + 1` columns: the configurations `cont j` and the actions `act j` performed
between consecutive ones.  The first configuration is the starting one, extended by blanks, the
first row does nothing, and the accepting state occurs in the last row but one. -/
structure CompData (M : TM) (w : List ℕ) (N : ℕ) (cont : ℕ → List Sym) (act : ℕ → Act) :
    Prop where
  /-- The grid is wide enough to hold the input, and has at least two rows. -/
  size : w.length + 1 ≤ N
  /-- All the configurations have the width of the grid. -/
  len : ∀ j ≤ N, (cont j).length = N + 1
  /-- The configurations are written in the alphabet of the machine. -/
  alph : ∀ j ≤ N, ∀ s ∈ cont j, s ∈ M.alphabet w
  /-- Consecutive configurations are related by the action performed between them. -/
  step : ∀ j < N, StepAt M (cont j) (cont (j + 1)) (act j)
  /-- The first row does nothing. -/
  act0 : act 0 = Act.idle
  /-- The first configuration is the starting one, extended by blanks. -/
  first : ∀ i, (cont 0).getD i blank =
      if i = 0 then Sym.state M.q0 else Sym.tape (w.getD (i - 1) 0)
  /-- The accepting state occurs in the last row but one. -/
  accept : Sym.state M.qacc ∈ cont (N - 1)

section Comp
variable {M : TM} {w : List ℕ} {N : ℕ} {cont : ℕ → List Sym} {act : ℕ → Act}

lemma alph_getD (h : CompData M w N cont act) {j : ℕ} (hj : j ≤ N) (i : ℕ) :
    (cont j).getD i blank ∈ M.alphabet w := by
  rcases lt_or_ge i (cont j).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h.alph j hj _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; exact blank_mem_alphabet M w

lemma getD_min (w : List ℕ) (i : ℕ) :
    w.getD (min i (w.length + 1) - 1) 0 = w.getD (i - 1) 0 := by
  rcases le_or_gt i w.length with hle | hgt
  · rw [show min i (w.length + 1) = i by omega]
  · rw [show min i (w.length + 1) = w.length + 1 by omega]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma one_le_N (h : CompData M w N cont act) : 1 ≤ N := le_trans (by omega) h.size

lemma kind_val_mem {s : Sym} (h : s ∈ M.alphabet w) :
    if kindOf s = 0 then valOf s ∈ M.tapeSyms w else valOf s ∈ M.states := by
  rcases alph_cases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [if_pos e1]; exact e2
  · rw [if_neg (by omega)]; exact e2

/-- Every cell of the grid built from a computation is a cell of the machine. -/
lemma valid_gcell (h : CompData M w N cont act) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    validB M w (gcell M w N cont act i j) = true := by
  by_cases hjN : j = N
  · subst hjN
    apply validB_intro <;> simp [gcell, M.blank_mem_tapeSyms]
  · have hjlt : j < N := lt_of_le_of_ne hj hjN
    have hstep := h.step j hjlt
    obtain ⟨c0, c1, c2, c3, c4, c5, ca4, ca0⟩ := stepAt_cell hstep i
    simp only [gcell, if_neg hjN]
    refine validB_intro ?hk ?hnk ?hrole ?hv ?hnv ?haux4 ?haux ?hkind0 ?hkind1 ?hkind2 ?hkind3
      ?hkind4 ?hkind5 ?hlb ?hrb ?hacc ?htop1 ?htop2 ?htop3 ?htop4 ?htop5 ?htop6 ?hntop ?hfin
    case hk => exact kindOf_le _
    case hnk => exact kindOf_le _
    case hrole => exact roleAt_le _ _
    case hv => exact kind_val_mem (alph_getD h hj i)
    case hnv => exact kind_val_mem (alph_getD h (j := j + 1) hjlt i)
    case haux4 => exact ca4
    case haux => exact ca0
    case hkind0 => intro hr; exact ⟨by rw [c0 hr], by rw [c0 hr]⟩
    case hkind1 => exact c1
    case hkind2 => exact c2
    case hkind3 => exact c3
    case hkind4 => exact c4
    case hkind5 => exact c5
    case hlb =>
      intro hlb
      have hi0 : i = 0 := of_decide_eq_true hlb
      subst hi0
      exact roleAt_zero _
    case hrb =>
      intro hrb
      have hiN : i = N := of_decide_eq_true hrb
      subst hiN
      exact roleAt_last hstep (h.len j hj)
    case hacc =>
      intro hlb
      have hi0 : i = 0 := of_decide_eq_true hlb
      subst hi0
      exact (accUpTo_zero M (cont j)).trans (beq_state_eq _ _)
    case htop1 =>
      intro ht
      have hj0 : j = 0 := of_decide_eq_true ht
      show (if j = 0 then min i (w.length + 1) else 0) ≤ w.length + 1
      rw [if_pos hj0]
      omega
    case htop2 =>
      intro ht
      have hj0 : j = 0 := of_decide_eq_true ht
      show roleAt (act j) i = 0
      rw [hj0, h.act0]
      rfl
    case htop3 =>
      intro ht hcnt
      have hj0 : j = 0 := of_decide_eq_true ht
      subst hj0
      have hcnt' : min i (w.length + 1) = 0 := hcnt
      have hi0 : i = 0 := by omega
      subst hi0
      have h0 : (cont 0).getD 0 blank = Sym.state M.q0 := by rw [h.first 0, if_pos rfl]
      show kindOf ((cont 0).getD 0 blank) = 1 ∧ valOf ((cont 0).getD 0 blank) = M.q0
      rw [h0]
      exact ⟨rfl, rfl⟩
    case htop4 =>
      intro ht hcnt
      have hj0 : j = 0 := of_decide_eq_true ht
      subst hj0
      have hcnt' : ¬ min i (w.length + 1) = 0 := hcnt
      have hi0 : i ≠ 0 := by omega
      have h0 : (cont 0).getD i blank = Sym.tape (w.getD (i - 1) 0) := by
        rw [h.first i, if_neg hi0]
      show kindOf ((cont 0).getD i blank) = 0 ∧
        valOf ((cont 0).getD i blank) = w.getD (min i (w.length + 1) - 1) 0
      rw [h0]
      exact ⟨rfl, (getD_min w i).symm⟩
    case htop5 =>
      intro ht hrb
      have hj0 : j = 0 := of_decide_eq_true ht
      have hiN : i = N := of_decide_eq_true hrb
      have hsize := h.size
      show (if j = 0 then min i (w.length + 1) else 0) = w.length + 1
      rw [if_pos hj0, hiN]
      omega
    case htop6 => intro _; rfl
    case hntop =>
      intro ht
      have hj0 : j ≠ 0 := of_decide_eq_false ht
      show (if j = 0 then min i (w.length + 1) else 0) = 0
      rw [if_neg hj0]
    case hfin => intro hf; exact absurd hf (by simp)

/-- Two horizontally adjacent cells of the grid built from a computation satisfy the horizontal
conditions. -/
lemma horiz_gcell (h : CompData M w N cont act) {i j : ℕ} (hi : i < N) (hj : j ≤ N) :
    horizB M w (gcell M w N cont act i j) (gcell M w N cont act (i + 1) j) = true := by
  by_cases hjN : j = N
  · subst hjN
    apply horizB_intro <;> simp [gcell, hi.ne]
  · have hjlt : j < N := lt_of_le_of_ne hj hjN
    have hstep := h.step j hjlt
    obtain ⟨r0, r1, r2, r3, r4, r5⟩ := stepAt_horiz hstep i
    simp only [gcell, if_neg hjN]
    refine horizB_intro ?hlb ?hrb ?htop ?hfin ?hcnt ?hacc ?hr0 ?hr1 ?hr2 ?hr3 ?hr4 ?hr5
    case hlb => simp
    case hrb => simp [hi.ne]
    case htop => rfl
    case hfin => rfl
    case hcnt =>
      intro ht
      have hj0 : j = 0 := of_decide_eq_true ht
      show (if j = 0 then min (i + 1) (w.length + 1) else 0) =
        min ((if j = 0 then min i (w.length + 1) else 0) + 1) (w.length + 1)
      rw [if_pos hj0]
      simp only [min_def]
      split_ifs <;> omega
    case hacc =>
      refine (accUpTo_succ M (cont j) i).trans ?_
      rw [beq_state_eq]
    case hr0 => exact r0
    case hr1 => exact r1
    case hr2 => exact r2
    case hr3 => exact r3
    case hr4 => exact r4
    case hr5 => exact r5

/-- Two vertically adjacent cells of the grid built from a computation satisfy the vertical
conditions. -/
lemma vert_gcell (h : CompData M w N cont act) {i j : ℕ} (hi : i ≤ N) (hj : j < N) :
    vertB (gcell M w N cont act i j) (gcell M w N cont act i (j + 1)) = true := by
  by_cases hj1 : j + 1 = N
  · simp only [gcell, if_neg hj.ne, if_pos hj1]
    refine vertB_intro rfl rfl rfl rfl rfl ?_ (by simp)
    intro _ hrb
    have hiN : i = N := of_decide_eq_true hrb
    have hmem : Sym.state M.qacc ∈ cont j := by
      have hacc := h.accept
      rwa [show N - 1 = j from by omega] at hacc
    show accUpTo M (cont j) i = true
    rw [hiN]
    exact accUpTo_of_mem M hmem (le_of_eq (h.len j hj.le))
  · simp only [gcell, if_neg hj.ne, if_neg hj1]
    exact vertB_intro rfl rfl rfl (by simp) (by simp) (by simp) (by simp)

lemma gcell_zero (h : CompData M w N cont act) : gcell M w N cont act 0 0 = startTile M := by
  have hN : (0 : ℕ) ≠ N := by have := one_le_N h; omega
  have h1 : cont 1 = cont 0 := by
    have hs := h.step 0 (by have := one_le_N h; omega)
    rw [h.act0] at hs
    exact hs
  have h0 : (cont 0).getD 0 blank = Sym.state M.q0 := by rw [h.first 0, if_pos rfl]
  simp only [gcell, if_neg hN, Nat.zero_add, h1, h0, accUpTo_zero, startTile]
  simp [kindOf, valOf, h.act0, roleAt, auxAt, beq_state_eq, hN]

lemma gcell_last (h : CompData M w N cont act) : gcell M w N cont act N N = finalTile := by
  have hN : N ≠ 0 := by have := one_le_N h; omega
  simp only [gcell, if_pos rfl, finalTile, Cell.mk.injEq, decide_eq_false_iff_not,
    decide_eq_true_eq]
  simp [hN]

/-- **The grid built from a computation is a solution of the tiling instance.** -/
lemma isSolution_gcell (h : CompData M w N cont act) :
    Tiling.IsSolution (inst M w) N (fun i j => Encodable.encode (gcell M w N cont act i j)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    simp only [inst]
    exact le_maxCode (mem_allCells (valid_gcell h hi hj))
  · show Encodable.encode (gcell M w N cont act 0 0) = Encodable.encode (startTile M)
    rw [gcell_zero h]
  · show Encodable.encode (gcell M w N cont act N N) = Encodable.encode finalTile
    rw [gcell_last h]
  · intro i hi j hj
    refine mem_constraint (valid_gcell h hi.le hj.le) (valid_gcell h hi hj.le)
      (valid_gcell h hi.le hj) (valid_gcell h hi hj) ?_
    simp only [windowB, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨valid_gcell h hi.le hj.le, valid_gcell h hi hj.le⟩, valid_gcell h hi.le hj⟩,
      valid_gcell h hi hj⟩, horiz_gcell h hi hj.le⟩, horiz_gcell h hi hj⟩,
      vert_gcell h hi.le hj⟩, vert_gcell h hi hj⟩

/-- **A computation of the machine gives a solution of the tiling instance.** -/
lemma solvable_of_compData (h : CompData M w N cont act) : Tiling.Solvable (inst M w) :=
  ⟨N, _, isSolution_gcell h⟩

end Comp

end TilingRed
end Transducers
