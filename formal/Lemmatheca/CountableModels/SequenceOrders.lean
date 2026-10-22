import Lemmatheca.BackAndForth.BackAndForthStrictTheory
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Sum.Order
import Mathlib.Logic.Equiv.Option

/-! The actual named dense-order theory and its three countable models. -/
namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open QuantifierElimination.Shared

abbrev sequenceLanguage := binaryRelLanguage[[ℕ]]

def sequenceAxiom (n : ℕ) : sequenceLanguage.Sentence :=
  .rel (.inl .rel) ![.func (Sum.inr n : sequenceLanguage.Functions 0) Fin.elim0, .func (Sum.inr (n + 1) : sequenceLanguage.Functions 0) Fin.elim0]

def sequenceTheory : sequenceLanguage.Theory :=
  (binaryRelLanguage.lhomWithConstants ℕ).onTheory strictDloTheory ∪ Set.range sequenceAxiom

section Models

variable (M : Type) [sequenceLanguage.Structure M]

def namedValue (n : ℕ) : M := ↑(binaryRelLanguage.con n)

def sequenceRelation (x y : M) : Prop :=
  Structure.RelMap (L := sequenceLanguage) (.inl .rel) ![x, y]

def upperTail : Set M := {x | ∀ n, sequenceRelation M (namedValue M n) x}

inductive TailShape
  | empty
  | noLeast
  | least
  deriving DecidableEq

noncomputable def tailShape : TailShape := by
  classical
  exact if h : (upperTail M).Nonempty then
    if ∃ u : M, u ∈ upperTail M ∧ ∀ x ∈ upperTail M, ¬ sequenceRelation M x u then
      .least else .noLeast else .empty

abbrev LowerIndex := Unit ⊕ (ℕ × Bool)

def lowerCell : LowerIndex → Set M
  | .inl _ => {x | sequenceRelation M x (namedValue M 0)}
  | .inr (n, false) => {namedValue M n}
  | .inr (n, true) => {x | sequenceRelation M (namedValue M n) x ∧
      sequenceRelation M x (namedValue M (n + 1))}

private theorem iso_named {N : Type} [sequenceLanguage.Structure N]
    (e : M ≃[sequenceLanguage] N) (n : ℕ) : e (namedValue M n) = namedValue N n := by
  exact e.map_constants (binaryRelLanguage.con n)

private theorem iso_relation {N : Type} [sequenceLanguage.Structure N]
    (e : M ≃[sequenceLanguage] N) (x y : M) :
    sequenceRelation N (e x) (e y) ↔ sequenceRelation M x y := by
  have h := e.map_rel (.inl .rel) ![x, y]
  have hv : e ∘ ![x, y] = ![e x, e y] := by ext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

private theorem iso_tail {N : Type} [sequenceLanguage.Structure N]
    (e : M ≃[sequenceLanguage] N) (x : M) : x ∈ upperTail M ↔ e x ∈ upperTail N := by
  constructor
  · intro hx n
    rw [← iso_named M e n]
    exact (iso_relation M e _ _).mpr (hx n)
  · intro hx n
    have h := hx n
    rw [← iso_named M e n] at h
    exact (iso_relation M e _ _).mp h

private theorem iso_least_forward {N : Type} [sequenceLanguage.Structure N]
    (e : M ≃[sequenceLanguage] N)
    (h : ∃ u : M, u ∈ upperTail M ∧ ∀ x ∈ upperTail M, ¬ sequenceRelation M x u) :
    ∃ u : N, u ∈ upperTail N ∧ ∀ x ∈ upperTail N, ¬ sequenceRelation N x u := by
  obtain ⟨u, hu, hl⟩ := h
  refine ⟨e u, (iso_tail M e u).mp hu, fun x hx hxu => ?_⟩
  have hx' : e.symm x ∈ upperTail M := by
    apply (iso_tail M e _).mpr
    simpa only [Language.Equiv.apply_symm_apply] using hx
  apply hl _ hx'
  apply (iso_relation M e _ u).mp
  simpa only [Language.Equiv.apply_symm_apply] using hxu

variable [Nonempty M] [M ⊨ sequenceTheory]

omit [Nonempty M] in
theorem sequence_axioms : QuantifierElimination.DloAxioms (sequenceRelation M) ∧
    ∀ n, sequenceRelation M (namedValue M n) (namedValue M (n + 1)) := by
  let : binaryRelLanguage.Structure M := (binaryRelLanguage.lhomWithConstants ℕ).reduct M
  let : (binaryRelLanguage.lhomWithConstants ℕ).IsExpansionOn M :=
    LHom.isExpansionOn_reduct _ _
  have hred : M ⊨ strictDloTheory := (LHom.onTheory_model _ strictDloTheory).mp
    ((inferInstance : M ⊨ sequenceTheory).mono Set.subset_union_left)
  let := hred
  refine ⟨model_strictDloTheory_iff.mp hred, fun n => ?_⟩
  have h : M ⊨ sequenceAxiom n :=
    Theory.realize_sentence_of_mem sequenceTheory (Or.inr (Set.mem_range_self n))
  change M ⊨ sequenceAxiom n at h
  change Structure.RelMap (L := sequenceLanguage) (.inl .rel)
    (fun i : Fin 2 =>
      ((![.func (Sum.inr n : sequenceLanguage.Functions 0) Fin.elim0,
        .func (Sum.inr (n + 1) : sequenceLanguage.Functions 0) Fin.elim0] i :
        sequenceLanguage.Term (Empty ⊕ Fin 0))).realize (Sum.elim default default)) at h
  have hv : (fun i : Fin 2 =>
      ((![.func (Sum.inr n : sequenceLanguage.Functions 0) Fin.elim0,
        .func (Sum.inr (n + 1) : sequenceLanguage.Functions 0) Fin.elim0] i :
        sequenceLanguage.Term (Empty ⊕ Fin 0))).realize (Sum.elim default default)) =
      ![namedValue M n, namedValue M (n + 1)] := by
    funext i
    fin_cases i
    · exact funMap_eq_coe_constants (L := sequenceLanguage) (M := M)
    · exact funMap_eq_coe_constants (L := sequenceLanguage) (M := M)
  rw [hv] at h
  exact h

omit [Nonempty M] in
theorem upperTail_upward {x y : M} (hx : x ∈ upperTail M) (hxy : sequenceRelation M x y) :
    y ∈ upperTail M := by
  intro n
  exact (sequence_axioms M).1.trans _ _ _ (hx n) hxy

omit [Nonempty M] in
theorem upperTail_iff_upperBound (x : M) :
    x ∈ upperTail M ↔ ∀ n, sequenceRelation M (namedValue M n) x ∨ namedValue M n = x := by
  constructor
  · intro hx n
    exact Or.inl (hx n)
  · intro h n
    rcases h (n + 1) with hlt | heq
    · exact (sequence_axioms M).1.trans _ _ _ ((sequence_axioms M).2 n) hlt
    · exact heq ▸ (sequence_axioms M).2 n

omit [Nonempty M] [M ⊨ sequenceTheory] in
theorem tailShape_iso {N : Type} [sequenceLanguage.Structure N] (e : M ≃[sequenceLanguage] N) :
    tailShape M = tailShape N := by
  classical
  have hne : (upperTail M).Nonempty ↔ (upperTail N).Nonempty := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨e x, (iso_tail M e x).mp hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨e.symm x, (iso_tail M e _).mpr ?_⟩
      simpa only [Language.Equiv.apply_symm_apply] using hx
  have hl : (∃ u : M, u ∈ upperTail M ∧ ∀ x ∈ upperTail M, ¬ sequenceRelation M x u) ↔
      (∃ u : N, u ∈ upperTail N ∧ ∀ x ∈ upperTail N, ¬ sequenceRelation N x u) :=
    ⟨iso_least_forward M e, iso_least_forward N e.symm⟩
  simp only [tailShape, hne, hl]

omit [Nonempty M] in
theorem lowerCell_partition (x : M) :
    x ∉ upperTail M ↔ ∃! i : LowerIndex, x ∈ lowerCell M i := by
  classical
  let : LinearOrder M := orderOfAxioms (sequenceRelation M) (sequence_axioms M).1
  have hc : StrictMono (namedValue M) := strictMono_nat_of_lt_succ (sequence_axioms M).2
  have hb (i : ℕ × Bool) (hx : x < namedValue M 0) (hi : x ∈ lowerCell M (.inr i)) : False := by
    rcases i with ⟨i, b⟩
    cases b with
    | false =>
      change x = namedValue M i at hi
      rw [hi] at hx
      exact not_lt_of_ge (hc.monotone (Nat.zero_le i)) hx
    | true =>
      change namedValue M i < x ∧ x < namedValue M (i + 1) at hi
      exact lt_asymm hx (lt_of_le_of_lt (hc.monotone (Nat.zero_le i)) hi.1)
  have hsg (i j : ℕ) (hi : x = namedValue M i)
      (hj : namedValue M j < x ∧ x < namedValue M (j + 1)) : False := by
    rw [hi] at hj
    have hl := hc.lt_iff_lt.mp hj.1
    have hu := hc.lt_iff_lt.mp hj.2
    omega
  have hgg (i j : ℕ) (hi : namedValue M i < x ∧ x < namedValue M (i + 1))
      (hj : namedValue M j < x ∧ x < namedValue M (j + 1)) : i = j := by
    have hij := hc.lt_iff_lt.mp (lt_trans hi.1 hj.2)
    have hji := hc.lt_iff_lt.mp (lt_trans hj.1 hi.2)
    omega
  have huniq (i j : LowerIndex) (hi : x ∈ lowerCell M i) (hj : x ∈ lowerCell M j) : i = j := by
    rcases i with u | ⟨i, bi⟩
    · rcases j with v | j
      · exact congrArg Sum.inl (Subsingleton.elim u v)
      · exact False.elim (hb j hi hj)
    · rcases j with u | ⟨j, bj⟩
      · exact False.elim (hb (i, bi) hj hi)
      · cases bi with
        | false =>
          cases bj with
          | false =>
            have he : namedValue M i = namedValue M j := hi.symm.trans hj
            exact congrArg (fun k => Sum.inr (k, false)) (hc.injective he)
          | true => exact False.elim (hsg i j hi hj)
        | true =>
          cases bj with
          | false => exact False.elim (hsg j i hj hi)
          | true => exact congrArg (fun k => Sum.inr (k, true)) (hgg i j hi hj)
  constructor
  · intro ht
    have hn : ∃ n, ¬ namedValue M n < x := by
      change ¬∀ n, namedValue M n < x at ht
      simpa only [not_forall] using ht
    have hbound : x ≤ namedValue M (Nat.find hn) := le_of_not_gt (Nat.find_spec hn)
    obtain ⟨i, hi⟩ : ∃ i : LowerIndex, x ∈ lowerCell M i := by
      rcases lt_or_eq_of_le hbound with hlt | heq
      · cases hfind : Nat.find hn with
        | zero =>
          refine ⟨.inl (), ?_⟩
          change x < namedValue M 0
          simpa only [hfind] using hlt
        | succ k =>
          have hprev : namedValue M k < x := by
            by_contra hnot
            exact Nat.find_min hn (by omega) hnot
          refine ⟨.inr (k, true), hprev, ?_⟩
          change x < namedValue M (k + 1)
          simpa only [hfind] using hlt
      · exact ⟨.inr (Nat.find hn, false), heq⟩
    exact ⟨i, hi, fun j hj => huniq j i hj hi⟩
  · rintro ⟨i, hi, _⟩ ht
    change ∀ n, namedValue M n < x at ht
    rcases i with u | ⟨i, b⟩
    · change x < namedValue M 0 at hi
      exact lt_asymm hi (ht 0)
    · cases b with
      | false =>
        have h := ht i
        rw [show x = namedValue M i from hi] at h
        exact lt_irrefl _ h
      | true => exact lt_asymm hi.2 (ht (i + 1))

omit [Nonempty M] in
theorem lowerCell_orders :
    (Nonempty (lowerCell M (.inl ())) ∧
      QuantifierElimination.DloAxioms (fun x y : lowerCell M (.inl ()) => sequenceRelation M x y)) ∧
    ∀ n, Nonempty (lowerCell M (.inr (n, true))) ∧
      QuantifierElimination.DloAxioms
        (fun x y : lowerCell M (.inr (n, true)) => sequenceRelation M x y) := by
  let h := (sequence_axioms M).1
  have hlo : QuantifierElimination.DloAxioms
      (fun x y : lowerCell M (.inl ()) => sequenceRelation M x y) := by
    refine ⟨fun x => h.irrefl x, fun x y z => h.trans x y z,
      ?_, ?_, ?_, ?_⟩
    · intro x y
      rcases h.total x y with hr | he | hr
      · exact Or.inl hr
      · exact Or.inr (Or.inl (Subtype.ext he))
      · exact Or.inr (Or.inr hr)
    · intro x y hxy
      obtain ⟨z, hxz, hzy⟩ := h.dense x y hxy
      exact ⟨⟨z, h.trans z y _ hzy y.property⟩, hxz, hzy⟩
    · intro x
      obtain ⟨y, hyx⟩ := h.noMin x
      exact ⟨⟨y, h.trans y x _ hyx x.property⟩, hyx⟩
    · intro x
      obtain ⟨y, hxy, hy0⟩ := h.dense x _ x.property
      exact ⟨⟨y, hy0⟩, hxy⟩
  refine ⟨⟨?_, hlo⟩, fun n => ?_⟩
  · obtain ⟨x, hx⟩ := h.noMin (namedValue M 0)
    exact ⟨⟨x, hx⟩⟩
  · have hnn := (sequence_axioms M).2 n
    constructor
    · obtain ⟨x, hnx, hxn⟩ := h.dense _ _ hnn
      exact ⟨⟨x, hnx, hxn⟩⟩
    · refine ⟨fun x => h.irrefl x, fun x y z => h.trans x y z,
        ?_, ?_, ?_, ?_⟩
      · intro x y
        rcases h.total x y with hr | he | hr
        · exact Or.inl hr
        · exact Or.inr (Or.inl (Subtype.ext he))
        · exact Or.inr (Or.inr hr)
      · intro x y hxy
        obtain ⟨z, hxz, hzy⟩ := h.dense x y hxy
        exact ⟨⟨z, h.trans _ x z x.property.1 hxz,
          h.trans z y _ hzy y.property.2⟩, hxz, hzy⟩
      · intro x
        obtain ⟨y, hny, hyx⟩ := h.dense _ x x.property.1
        exact ⟨⟨y, hny, h.trans y x _ hyx x.property.2⟩, hyx⟩
      · intro x
        obtain ⟨y, hxy, hyn⟩ := h.dense x _ x.property.2
        exact ⟨⟨y, h.trans _ x y x.property.1 hxy, hyn⟩, hxy⟩

omit [Nonempty M] in
theorem tail_noLeast_order (h : tailShape M = .noLeast) :
    Nonempty (upperTail M) ∧
      QuantifierElimination.DloAxioms (fun x y : upperTail M => sequenceRelation M x y) := by
  classical
  have hne : (upperTail M).Nonempty := by
    by_contra hn
    simp [tailShape, hn] at h
  have hnl : ¬∃ u : M, u ∈ upperTail M ∧ ∀ x ∈ upperTail M, ¬ sequenceRelation M x u := by
    intro hl
    simp [tailShape, hne, hl] at h
  let hR := (sequence_axioms M).1
  refine ⟨hne.to_subtype, ⟨fun x => hR.irrefl x, fun x y z => hR.trans x y z,
    ?_, ?_, ?_, ?_⟩⟩
  · intro x y
    rcases hR.total x y with hr | he | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl (Subtype.ext he))
    · exact Or.inr (Or.inr hr)
  · intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := hR.dense x y hxy
    exact ⟨⟨z, upperTail_upward M x.property hxz⟩, hxz, hzy⟩
  · intro x
    by_contra hn
    exact hnl ⟨x, x.property, fun y hy hyx => hn ⟨⟨y, hy⟩, hyx⟩⟩
  · intro x
    obtain ⟨y, hxy⟩ := hR.noMax x
    exact ⟨⟨y, upperTail_upward M x.property hxy⟩, hxy⟩

omit [Nonempty M] in
theorem tail_least_remainder_order (u : M) (hu : u ∈ upperTail M)
    (hleast : ∀ x ∈ upperTail M, ¬ sequenceRelation M x u) :
    Nonempty {x : M // x ∈ upperTail M ∧ x ≠ u} ∧
      QuantifierElimination.DloAxioms
        (fun x y : {x : M // x ∈ upperTail M ∧ x ≠ u} => sequenceRelation M x y) := by
  let hR := (sequence_axioms M).1
  have hux (x : {x : M // x ∈ upperTail M ∧ x ≠ u}) : sequenceRelation M u x := by
    rcases hR.total u x with hr | he | hr
    · exact hr
    · exact False.elim (x.property.2 he.symm)
    · exact False.elim (hleast x x.property.1 hr)
  have hmem (x : M) (hx : sequenceRelation M u x) : x ∈ upperTail M ∧ x ≠ u :=
    ⟨upperTail_upward M hu hx, fun he => hR.irrefl u (he ▸ hx)⟩
  refine ⟨?_, ⟨fun x => hR.irrefl x, fun x y z => hR.trans x y z, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨x, hx⟩ := hR.noMax u
    exact ⟨⟨x, hmem x hx⟩⟩
  · intro x y
    rcases hR.total x y with hr | he | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl (Subtype.ext he))
    · exact Or.inr (Or.inr hr)
  · intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := hR.dense x y hxy
    exact ⟨⟨z, hmem z (hR.trans u x z (hux x) hxz)⟩, hxz, hzy⟩
  · intro x
    obtain ⟨y, huy, hyx⟩ := hR.dense u x (hux x)
    exact ⟨⟨y, hmem y huy⟩, hyx⟩
  · intro x
    obtain ⟨y, hxy⟩ := hR.noMax x
    exact ⟨⟨y, hmem y (hR.trans u x y (hux x) hxy)⟩, hxy⟩

private def cellRank : LowerIndex → ℕ
  | .inl _ => 0
  | .inr (n, false) => 2 * n + 1
  | .inr (n, true) => 2 * n + 2

private theorem cellRank_injective : Function.Injective cellRank := by
  intro i j h
  rcases i with u | ⟨i, bi⟩ <;> rcases j with v | ⟨j, bj⟩
  · exact congrArg Sum.inl (Subsingleton.elim u v)
  · cases bj <;> simp only [cellRank] at h <;> omega
  · cases bi <;> simp only [cellRank] at h <;> omega
  · cases bi <;> cases bj <;> simp only [cellRank] at h
    · exact congrArg (fun n => Sum.inr (n, false)) (by omega)
    · omega
    · omega
    · exact congrArg (fun n => Sum.inr (n, true)) (by omega)

omit [Nonempty M] in
private theorem cells_before {i j : LowerIndex} {x y : M}
    (hi : x ∈ lowerCell M i) (hj : y ∈ lowerCell M j)
    (hij : cellRank i < cellRank j) : sequenceRelation M x y := by
  let : LinearOrder M := orderOfAxioms (sequenceRelation M) (sequence_axioms M).1
  have hc : StrictMono (namedValue M) := strictMono_nat_of_lt_succ (sequence_axioms M).2
  change x < y
  rcases i with u | ⟨i, bi⟩ <;> rcases j with v | ⟨j, bj⟩
  · exact False.elim (Nat.lt_irrefl _ hij)
  · change x < namedValue M 0 at hi
    cases bj with
    | false =>
      change y = namedValue M j at hj
      rw [hj]
      exact lt_of_lt_of_le hi (hc.monotone (Nat.zero_le j))
    | true =>
      change namedValue M j < y ∧ y < namedValue M (j + 1) at hj
      exact lt_trans (lt_of_lt_of_le hi (hc.monotone (Nat.zero_le j))) hj.1
  · exact False.elim (Nat.not_lt_zero _ hij)
  · cases bi with
    | false =>
      change x = namedValue M i at hi
      rw [hi]
      cases bj with
      | false =>
        change y = namedValue M j at hj
        rw [hj]
        exact hc (by simp only [cellRank] at hij; omega)
      | true =>
        change namedValue M j < y ∧ y < namedValue M (j + 1) at hj
        exact lt_of_le_of_lt (hc.monotone (by simp only [cellRank] at hij; omega)) hj.1
    | true =>
      change namedValue M i < x ∧ x < namedValue M (i + 1) at hi
      cases bj with
      | false =>
        change y = namedValue M j at hj
        rw [hj]
        exact lt_of_lt_of_le hi.2 (hc.monotone (by simp only [cellRank] at hij; omega))
      | true =>
        change namedValue M j < y ∧ y < namedValue M (j + 1) at hj
        exact lt_trans (lt_of_lt_of_le hi.2 (hc.monotone
          (by simp only [cellRank] at hij; omega))) hj.1

omit [Nonempty M] in
private theorem cell_before_tail {i : LowerIndex} {x y : M}
    (hi : x ∈ lowerCell M i) (hy : y ∈ upperTail M) : sequenceRelation M x y := by
  let h := (sequence_axioms M).1
  rcases i with u | ⟨i, b⟩
  · exact h.trans _ _ _ hi (hy 0)
  · cases b with
    | false => exact (show x = namedValue M i from hi).symm ▸ hy i
    | true => exact h.trans _ _ _ hi.2 (hy (i + 1))

omit [Nonempty M] in
private theorem cell_not_tail {i : LowerIndex} {x : M} (hi : x ∈ lowerCell M i) :
    x ∉ upperTail M := by
  intro ht
  let h := (sequence_axioms M).1
  rcases i with u | ⟨i, b⟩
  · exact h.irrefl x (h.trans x _ x hi (ht 0))
  · cases b with
    | false =>
      have hh := ht i
      rw [show x = namedValue M i from hi] at hh
      exact h.irrefl _ hh
    | true => exact h.irrefl x (h.trans x _ x hi.2 (ht (i + 1)))

omit [Nonempty M] in
private theorem relation_asymm {x y : M} (h : sequenceRelation M x y) :
    ¬ sequenceRelation M y x := by
  intro h'
  exact (sequence_axioms M).1.irrefl x ((sequence_axioms M).1.trans x y x h h')

private theorem dlo_equiv {A B : Type} [Countable A] [Countable B]
    (r : A → A → Prop) (s : B → B → Prop) (hA : Nonempty A) (hB : Nonempty B)
    (hr : QuantifierElimination.DloAxioms r) (hs : QuantifierElimination.DloAxioms s) :
    ∃ e : A ≃ B, ∀ x y, s (e x) (e y) ↔ r x y := by
  let := hA
  let := hB
  let : binaryRelLanguage.Structure A := binaryRelStructure A r
  let : binaryRelLanguage.Structure B := binaryRelStructure B s
  let : A ⊨ strictDloTheory := model_strictDloTheory_iff.mpr hr
  let : B ⊨ strictDloTheory := model_strictDloTheory_iff.mpr hs
  obtain ⟨e⟩ := BackAndForth.strictDlo_countable_models_isomorphic A B
  refine ⟨e.toEquiv, fun x y => ?_⟩
  exact e.map_rel .rel ![x, y]

omit [Nonempty M] in
private theorem glue_cells {N : Type} [sequenceLanguage.Structure N] [N ⊨ sequenceTheory]
    (C : ∀ i : LowerIndex, lowerCell M i ≃ lowerCell N i)
    (hC : ∀ i (x y : lowerCell M i),
      sequenceRelation N (C i x) (C i y) ↔ sequenceRelation M x y)
    (U : upperTail M ≃ upperTail N)
    (hU : ∀ x y : upperTail M, sequenceRelation N (U x) (U y) ↔ sequenceRelation M x y) :
    Nonempty (M ≃[sequenceLanguage] N) := by
  classical
  let idx (x : M) (hx : x ∉ upperTail M) := ((lowerCell_partition M x).mp hx).choose
  have hidx (x : M) (hx : x ∉ upperTail M) : x ∈ lowerCell M (idx x hx) :=
    (((lowerCell_partition M x).mp hx).choose_spec).1
  let F (x : M) : N := if hx : x ∈ upperTail M then U ⟨x, hx⟩
    else C (idx x hx) ⟨x, hidx x hx⟩
  have hFT (x : M) (hx : x ∈ upperTail M) : F x = (U ⟨x, hx⟩).val := by
    simp only [F, dite_eq_left hx]
  have hFC (x : M) (i : LowerIndex) (hi : x ∈ lowerCell M i) :
      F x = (C i ⟨x, hi⟩).val := by
    have hn := cell_not_tail M hi
    have he : idx x hn = i := ((((lowerCell_partition M x).mp hn).choose_spec).2 i hi).symm
    simp only [F, dite_eq_right hn]
    cases he
    rfl
  have hFCell (x : M) (i : LowerIndex) (hi : x ∈ lowerCell M i) :
      F x ∈ lowerCell N i := hFC x i hi ▸ (C i ⟨x, hi⟩).property
  have hFTiff (x : M) : F x ∈ upperTail N ↔ x ∈ upperTail M := by
    by_cases hx : x ∈ upperTail M
    · exact iff_of_true (hFT x hx ▸ (U ⟨x, hx⟩).property) hx
    · exact iff_of_false (cell_not_tail N (hFCell x _ (hidx x hx))) hx
  have hFi : Function.Injective F := by
    intro x y hxy
    by_cases hx : x ∈ upperTail M
    · have hy := (hFTiff y).mp (hxy ▸ (hFTiff x).mpr hx)
      have he : U ⟨x, hx⟩ = U ⟨y, hy⟩ := Subtype.ext
        ((hFT x hx).symm.trans (hxy.trans (hFT y hy)))
      exact congrArg Subtype.val (U.injective he)
    · have hy : y ∉ upperTail M := by
        intro hy
        exact hx ((hFTiff x).mp (hxy.symm ▸ (hFTiff y).mpr hy))
      let i := idx x hx
      let j := idx y hy
      have hi := hidx x hx
      have hj := hidx y hy
      have hFi := hFCell x i hi
      have hFj := hFCell y j hj
      have hn : F y ∉ upperTail N := fun h => hy ((hFTiff y).mp h)
      obtain ⟨k, _, hk⟩ := (lowerCell_partition N (F y)).mp hn
      have hij : i = j := (hk i (hxy ▸ hFi)).trans (hk j hFj).symm
      have hj' : y ∈ lowerCell M i := hij.symm ▸ hj
      have he : C i ⟨x, hi⟩ = C i ⟨y, hj'⟩ := Subtype.ext
        ((hFC x i hi).symm.trans (hxy.trans (hFC y i hj')))
      exact congrArg Subtype.val ((C i).injective he)
  have hFs : Function.Surjective F := by
    intro y
    by_cases hy : y ∈ upperTail N
    · let x := U.symm ⟨y, hy⟩
      refine ⟨x.val, (hFT x.val x.property).trans ?_⟩
      exact congrArg Subtype.val (U.apply_symm_apply ⟨y, hy⟩)
    · obtain ⟨i, hi, _⟩ := (lowerCell_partition N y).mp hy
      let x := (C i).symm ⟨y, hi⟩
      refine ⟨x.val, (hFC x.val i x.property).trans ?_⟩
      exact congrArg Subtype.val ((C i).apply_symm_apply ⟨y, hi⟩)
  have hFR (x y : M) : sequenceRelation N (F x) (F y) ↔ sequenceRelation M x y := by
    by_cases hx : x ∈ upperTail M
    · by_cases hy : y ∈ upperTail M
      · rw [hFT x hx, hFT y hy]
        exact hU ⟨x, hx⟩ ⟨y, hy⟩
      · obtain ⟨j, hj, _⟩ := (lowerCell_partition M y).mp hy
        exact iff_of_false
          (relation_asymm N (cell_before_tail N (hFCell y j hj) ((hFTiff x).mpr hx)))
          (relation_asymm M (cell_before_tail M hj hx))
    · obtain ⟨i, hi, _⟩ := (lowerCell_partition M x).mp hx
      by_cases hy : y ∈ upperTail M
      · exact iff_of_true
          (cell_before_tail N (hFCell x i hi) ((hFTiff y).mpr hy))
          (cell_before_tail M hi hy)
      · obtain ⟨j, hj, _⟩ := (lowerCell_partition M y).mp hy
        by_cases hij : i = j
        · subst j
          rw [hFC x i hi, hFC y i hj]
          exact hC i ⟨x, hi⟩ ⟨y, hj⟩
        · rcases lt_trichotomy (cellRank i) (cellRank j) with hlt | heq | hgt
          · exact iff_of_true (cells_before N (hFCell x i hi) (hFCell y j hj) hlt)
              (cells_before M hi hj hlt)
          · exact False.elim (hij (cellRank_injective heq))
          · exact iff_of_false
              (relation_asymm N (cells_before N (hFCell y j hj) (hFCell x i hi) hgt))
              (relation_asymm M (cells_before M hj hi hgt))
  have hFN (n : ℕ) : F (namedValue M n) = namedValue N n := by
    have hi : namedValue M n ∈ lowerCell M (.inr (n, false)) := rfl
    exact (hFC _ _ hi).trans (C (.inr (n, false)) ⟨_, hi⟩).property
  let E := Equiv.ofBijective F ⟨hFi, hFs⟩
  refine ⟨{ E with map_fun' := ?_, map_rel' := ?_ }⟩
  · intro n f a
    cases f with
    | inl f => exact f.elim
    | inr c =>
      cases n with
      | zero =>
        change F (Structure.funMap (L := sequenceLanguage) (Sum.inr c) a) =
          Structure.funMap (L := sequenceLanguage) (Sum.inr c) (F ∘ a)
        have h1 : Structure.funMap (L := sequenceLanguage) (Sum.inr c) a = namedValue M c :=
          funMap_eq_coe_constants (L := sequenceLanguage) (M := M)
        have h2 : Structure.funMap (L := sequenceLanguage) (Sum.inr c) (F ∘ a) = namedValue N c :=
          funMap_eq_coe_constants (L := sequenceLanguage) (M := N)
        exact (congrArg F h1).trans ((hFN c).trans h2.symm)
      | succ n => exact c.elim
  · intro n R a
    cases R with
    | inl R =>
      cases R
      have hv : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
      have hw : F ∘ a = ![F (a 0), F (a 1)] := by ext i; fin_cases i <;> rfl
      change Structure.RelMap (L := sequenceLanguage) (.inl .rel) (F ∘ a) ↔
        Structure.RelMap (L := sequenceLanguage) (.inl .rel) a
      rw [hw, hv]
      exact hFR (a 0) (a 1)
    | inr R => exact R.elim

private def tailRemoveEquiv (u : M) (hu : u ∈ upperTail M) :
    {x : upperTail M // x ≠ ⟨u, hu⟩} ≃ {x : M // x ∈ upperTail M ∧ x ≠ u} where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nonempty M] in
private theorem least_tail_lt (u : M) (_hu : u ∈ upperTail M)
    (hl : ∀ x ∈ upperTail M, ¬ sequenceRelation M x u)
    (x : upperTail M) (hx : x.val ≠ u) : sequenceRelation M u x := by
  rcases (sequence_axioms M).1.total u x with h | he | h
  · exact h
  · exact False.elim (hx he.symm)
  · exact False.elim (hl x x.property h)

omit [Nonempty M] in
private theorem join_tail_equiv {N : Type} [sequenceLanguage.Structure N] [N ⊨ sequenceTheory]
    (u : M) (hu : u ∈ upperTail M) (hl : ∀ x ∈ upperTail M, ¬ sequenceRelation M x u)
    (v : N) (hv : v ∈ upperTail N) (hl' : ∀ x ∈ upperTail N, ¬ sequenceRelation N x v)
    (R : {x : M // x ∈ upperTail M ∧ x ≠ u} ≃ {x : N // x ∈ upperTail N ∧ x ≠ v})
    (hR : ∀ x y, sequenceRelation N (R x) (R y) ↔ sequenceRelation M x y) :
    ∃ U : upperTail M ≃ upperTail N,
      ∀ x y, sequenceRelation N (U x) (U y) ↔ sequenceRelation M x y := by
  classical
  let uT : upperTail M := ⟨u, hu⟩
  let vT : upperTail N := ⟨v, hv⟩
  let V := ((tailRemoveEquiv M u hu).trans R).trans (tailRemoveEquiv N v hv).symm
  let U := ((Equiv.optionSubtypeNe uT).symm.trans V.optionCongr).trans
    (Equiv.optionSubtypeNe vT)
  have hUu : U uT = vT := by
    simp only [U, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self,
      Equiv.optionCongr_apply, Option.map_none, Equiv.optionSubtypeNe_none]
  have hUr (x : {x : M // x ∈ upperTail M ∧ x ≠ u}) :
      U ⟨x.val, x.property.1⟩ = ⟨(R x).val, (R x).property.1⟩ := by
    have hn : (⟨x.val, x.property.1⟩ : upperTail M) ≠ uT :=
      fun h => x.property.2 (congrArg Subtype.val h)
    simp only [U, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hn,
      Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
    rfl
  refine ⟨U, fun x y => ?_⟩
  by_cases hx : x = uT
  · subst x
    by_cases hy : y = uT
    · subst y
      rw [hUu]
      exact iff_of_false ((sequence_axioms N).1.irrefl v) ((sequence_axioms M).1.irrefl u)
    · rw [hUu]
      have hyM : y.val ≠ u := fun h => hy (Subtype.ext h)
      have hyN : (U y).val ≠ v := by
        intro h
        exact hy (U.injective ((Subtype.ext h).trans hUu.symm))
      exact iff_of_true (least_tail_lt N v hv hl' (U y) hyN)
        (least_tail_lt M u hu hl y hyM)
  · by_cases hy : y = uT
    · subst y
      rw [hUu]
      exact iff_of_false (hl' (U x) (U x).property) (hl x x.property)
    · let rx : {x : M // x ∈ upperTail M ∧ x ≠ u} :=
        ⟨x.val, x.property, fun h => hx (Subtype.ext h)⟩
      let ry : {x : M // x ∈ upperTail M ∧ x ≠ u} :=
        ⟨y.val, y.property, fun h => hy (Subtype.ext h)⟩
      have hUx : U x = ⟨(R rx).val, (R rx).property.1⟩ := hUr rx
      have hUy : U y = ⟨(R ry).val, (R ry).property.1⟩ := hUr ry
      rw [hUx, hUy]
      exact hR rx ry

omit [Nonempty M] in
theorem same_tail_isomorphism [Countable M] {N : Type} [sequenceLanguage.Structure N]
    [Nonempty N] [Countable N] [N ⊨ sequenceTheory] :
    Nonempty (M ≃[sequenceLanguage] N) ↔ tailShape M = tailShape N := by
  classical
  constructor
  · rintro ⟨e⟩
    exact tailShape_iso M e
  · intro hs
    have hcells : ∀ i : LowerIndex, ∃ e : lowerCell M i ≃ lowerCell N i,
        ∀ x y, sequenceRelation N (e x) (e y) ↔ sequenceRelation M x y := by
      intro i
      rcases i with u | ⟨n, b⟩
      · cases u
        exact dlo_equiv _ _ (lowerCell_orders M).1.1 (lowerCell_orders N).1.1
          (lowerCell_orders M).1.2 (lowerCell_orders N).1.2
      · cases b with
        | false =>
          let E : lowerCell M (.inr (n, false)) ≃ lowerCell N (.inr (n, false)) :=
            { toFun := fun _ => ⟨namedValue N n, rfl⟩
              invFun := fun _ => ⟨namedValue M n, rfl⟩
              left_inv := fun x => Subtype.ext x.property.symm
              right_inv := fun x => Subtype.ext x.property.symm }
          refine ⟨E, fun x y => ?_⟩
          have hxy : x = y := Subtype.ext (x.property.trans y.property.symm)
          rw [hxy]
          exact iff_of_false ((sequence_axioms N).1.irrefl (E y)) ((sequence_axioms M).1.irrefl y)
        | true =>
          exact dlo_equiv _ _ ((lowerCell_orders M).2 n).1 ((lowerCell_orders N).2 n).1
            ((lowerCell_orders M).2 n).2 ((lowerCell_orders N).2 n).2
    choose C hC using hcells
    have emptyShape (X : Type) [sequenceLanguage.Structure X] (h : tailShape X = .empty) :
        IsEmpty (upperTail X) := by
      refine ⟨fun x => ?_⟩
      have hne : (upperTail X).Nonempty := ⟨x, x.property⟩
      by_cases hl : ∃ u : X, u ∈ upperTail X ∧ ∀ x ∈ upperTail X, ¬ sequenceRelation X x u
      · simp [tailShape, hne, hl] at h
      · simp [tailShape, hne, hl] at h
    have leastShape (X : Type) [sequenceLanguage.Structure X] (h : tailShape X = .least) :
        ∃ u : X, u ∈ upperTail X ∧ ∀ x ∈ upperTail X, ¬ sequenceRelation X x u := by
      by_cases hne : (upperTail X).Nonempty
      · by_cases hl : ∃ u : X, u ∈ upperTail X ∧ ∀ x ∈ upperTail X, ¬ sequenceRelation X x u
        · exact hl
        · simp [tailShape, hne, hl] at h
      · simp [tailShape, hne] at h
    cases hSM : tailShape M with
    | empty =>
      let := emptyShape M hSM
      let := emptyShape N (hs.symm.trans hSM)
      let U : upperTail M ≃ upperTail N := Equiv.equivOfIsEmpty _ _
      exact glue_cells M C hC U (fun x => isEmptyElim x)
    | noLeast =>
      obtain ⟨U, hU⟩ := dlo_equiv _ _
        (tail_noLeast_order M hSM).1 (tail_noLeast_order N (hs.symm.trans hSM)).1
        (tail_noLeast_order M hSM).2 (tail_noLeast_order N (hs.symm.trans hSM)).2
      exact glue_cells M C hC U hU
    | least =>
      obtain ⟨u, hu, hl⟩ := leastShape M hSM
      obtain ⟨v, hv, hl'⟩ := leastShape N (hs.symm.trans hSM)
      obtain ⟨R, hR⟩ := dlo_equiv _ _
        (tail_least_remainder_order M u hu hl).1 (tail_least_remainder_order N v hv hl').1
        (tail_least_remainder_order M u hu hl).2 (tail_least_remainder_order N v hv hl').2
      obtain ⟨U, hU⟩ := join_tail_equiv M u hu hl v hv hl' R hR
      exact glue_cells M C hC U hU

end Models

end Lemmatheca.ModelTheory.CountableModels
