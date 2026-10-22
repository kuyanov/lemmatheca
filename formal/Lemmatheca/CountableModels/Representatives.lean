import Lemmatheca.CountableModels.SequenceOrders
import Lemmatheca.CountableModels.Spectrum
import Mathlib.Data.Sum.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.Order.Field.Rat

namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open QuantifierElimination.Shared

def representativeCarrier : Fin 3 → Type
  | 0 => ℚ
  | 1 => ℚ ⊕ₗ ℚ
  | 2 => ℚ ⊕ₗ (Unit ⊕ₗ ℚ)

private theorem rational_order_properties : DenselyOrdered ℚ ∧ NoMinOrder ℚ ∧ NoMaxOrder ℚ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem two_order_properties : DenselyOrdered (ℚ ⊕ₗ ℚ) ∧
    NoMinOrder (ℚ ⊕ₗ ℚ) ∧ NoMaxOrder (ℚ ⊕ₗ ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

private theorem three_order_properties : DenselyOrdered (ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) ∧
    NoMinOrder (ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) ∧ NoMaxOrder (ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

@[instance_reducible] private noncomputable def representativeOrder : (i : Fin 3) →
    LinearOrder (representativeCarrier i)
  | 0 => inferInstanceAs (LinearOrder ℚ)
  | 1 => inferInstanceAs (LinearOrder (ℚ ⊕ₗ ℚ))
  | 2 => inferInstanceAs (LinearOrder (ℚ ⊕ₗ (Unit ⊕ₗ ℚ)))

attribute [instance] representativeOrder

def representativeNames : (i : Fin 3) → ℕ → representativeCarrier i
  | 0, n => (n : ℚ)
  | 1, n => toLex (.inl (n : ℚ))
  | 2, n => toLex (.inl (n : ℚ))

noncomputable instance representativeStructure (i : Fin 3) :
    sequenceLanguage.Structure (representativeCarrier i) :=
  let : binaryRelLanguage.Structure (representativeCarrier i) :=
    binaryRelStructure _ (· < ·)
  Diagrams.namedExpansion (representativeNames i)

private theorem representative_namedValue (i : Fin 3) (n : ℕ) :
    namedValue (representativeCarrier i) n = representativeNames i n := rfl

private theorem representative_relation (i : Fin 3) (x y : representativeCarrier i) :
    sequenceRelation (representativeCarrier i) x y ↔ x < y := Iff.rfl

private theorem representative_increasing (i : Fin 3) (n : ℕ) :
    representativeNames i n < representativeNames i (n + 1) := by
  fin_cases i
  · change (n : ℚ) < ((n + 1 : ℕ) : ℚ)
    exact_mod_cast Nat.lt_succ_self n
  · change (toLex (.inl (n : ℚ)) : ℚ ⊕ₗ ℚ) < toLex (.inl ((n + 1 : ℕ) : ℚ))
    apply Sum.Lex.inl_lt_inl_iff.mpr
    exact_mod_cast Nat.lt_succ_self n
  · change (toLex (.inl (n : ℚ)) : ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) < toLex (.inl ((n + 1 : ℕ) : ℚ))
    apply Sum.Lex.inl_lt_inl_iff.mpr
    exact_mod_cast Nat.lt_succ_self n

private theorem representative_axiom (i : Fin 3) (n : ℕ) :
    (representativeCarrier i ⊨ sequenceAxiom n) ↔
      representativeNames i n < representativeNames i (n + 1) := by
  let M := representativeCarrier i
  change Structure.RelMap (L := sequenceLanguage) (.inl .rel)
    (fun j : Fin 2 =>
      ((![.func (Sum.inr n : sequenceLanguage.Functions 0) Fin.elim0,
        .func (Sum.inr (n + 1) : sequenceLanguage.Functions 0) Fin.elim0] j :
        sequenceLanguage.Term (Empty ⊕ Fin 0))).realize (Sum.elim default default)) ↔ _
  have hv : (fun j : Fin 2 =>
      ((![.func (Sum.inr n : sequenceLanguage.Functions 0) Fin.elim0,
        .func (Sum.inr (n + 1) : sequenceLanguage.Functions 0) Fin.elim0] j :
        sequenceLanguage.Term (Empty ⊕ Fin 0))).realize (Sum.elim default default)) =
      ![namedValue M n, namedValue M (n + 1)] := by
    funext j
    fin_cases j
    · exact funMap_eq_coe_constants (L := sequenceLanguage) (M := M)
    · exact funMap_eq_coe_constants (L := sequenceLanguage) (M := M)
  rw [hv]
  exact Iff.rfl

theorem representative_model (i : Fin 3) : representativeCarrier i ⊨ sequenceTheory := by
  let B := representativeCarrier i
  let : DenselyOrdered B := by
    fin_cases i
    · exact rational_order_properties.1
    · exact two_order_properties.1
    · exact three_order_properties.1
  let : NoMinOrder B := by
    fin_cases i
    · exact rational_order_properties.2.1
    · exact two_order_properties.2.1
    · exact three_order_properties.2.1
  let : NoMaxOrder B := by
    fin_cases i
    · exact rational_order_properties.2.2
    · exact two_order_properties.2.2
    · exact three_order_properties.2.2
  let : binaryRelLanguage.Structure B := binaryRelStructure B (· < ·)
  let : (binaryRelLanguage.lhomWithConstants ℕ).IsExpansionOn B :=
    Diagrams.namedExpansion_isExpansion (representativeNames i)
  have hDlo : B ⊨ strictDloTheory := model_strictDloTheory
  constructor
  intro σ hσ
  rcases hσ with ⟨τ, hτ, rfl⟩ | ⟨n, rfl⟩
  · exact (LHom.realize_onSentence B (binaryRelLanguage.lhomWithConstants ℕ) τ).mpr
      (strictDloTheory.realize_sentence_of_mem hτ)
  · exact (representative_axiom i n).mpr (representative_increasing i n)

theorem representative_countable (i : Fin 3) : Countable (representativeCarrier i) := by
  fin_cases i <;> dsimp [representativeCarrier, Lex] <;> infer_instance

theorem representative_infinite (i : Fin 3) : Infinite (representativeCarrier i) := by
  fin_cases i <;> dsimp [representativeCarrier, Lex] <;> infer_instance

noncomputable def representative (i : Fin 3) : CountableModel sequenceTheory :=
  let : representativeCarrier i ⊨ sequenceTheory := representative_model i
  let : Countable (representativeCarrier i) := representative_countable i
  let : Infinite (representativeCarrier i) := representative_infinite i
  { model := Theory.ModelType.of sequenceTheory (representativeCarrier i)
    countable_carrier := representative_countable i
    infinite_carrier := representative_infinite i }

def representativeShape : Fin 3 → TailShape
  | 0 => .empty
  | 1 => .noLeast
  | 2 => .least

private theorem rational_not_above_naturals (q : ℚ) : ¬ ∀ n : ℕ, (n : ℚ) < q := by
  obtain ⟨n, hn⟩ := exists_nat_gt q
  exact fun h => (not_lt_of_ge hn.le) (h n)

private theorem sum_tail {β : Type} [LT β] (x : ℚ ⊕ₗ β) :
    (∀ n : ℕ, (toLex (.inl (n : ℚ)) : ℚ ⊕ₗ β) < x) ↔
      ∃ y : β, x = toLex (.inr y) := by
  obtain ⟨x, rfl⟩ := toLex.surjective x
  cases x with
  | inl q =>
    constructor
    · intro h
      exact (rational_not_above_naturals q (fun n => Sum.Lex.inl_lt_inl_iff.mp (h n))).elim
    · rintro ⟨y, h⟩
      cases h
  | inr y =>
    exact ⟨fun _ => ⟨y, rfl⟩, fun _ n => Sum.Lex.inl_lt_inr _ _⟩

private theorem second_tail (x : ℚ ⊕ₗ ℚ) :
    x ∈ upperTail (representativeCarrier 1) ↔ ∃ q : ℚ, x = toLex (.inr q) := by
  change (∀ n : ℕ, (toLex (.inl (n : ℚ)) : ℚ ⊕ₗ ℚ) < x) ↔ _
  exact sum_tail x

private theorem third_tail (x : ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) :
    x ∈ upperTail (representativeCarrier 2) ↔
      ∃ q : Unit ⊕ₗ ℚ, x = toLex (.inr q) := by
  change (∀ n : ℕ, (toLex (.inl (n : ℚ)) : ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) < x) ↔ _
  exact sum_tail x

theorem representative_shape (i : Fin 3) :
    tailShape (representativeCarrier i) = representativeShape i := by
  classical
  fin_cases i
  · have hU : ¬ (upperTail (representativeCarrier 0)).Nonempty := by
      rintro ⟨x, hx⟩
      change ∀ n : ℕ, (n : ℚ) < x at hx
      exact rational_not_above_naturals x hx
    simp [tailShape, hU, representativeShape]
  · have hU : (upperTail (representativeCarrier 1)).Nonempty :=
      ⟨toLex (.inr (0 : ℚ)), (second_tail _).mpr ⟨0, rfl⟩⟩
    have hleast : ¬ ∃ u : representativeCarrier 1, u ∈ upperTail (representativeCarrier 1) ∧
        ∀ x ∈ upperTail (representativeCarrier 1), ¬ sequenceRelation (representativeCarrier 1) x u := by
      rintro ⟨u, hu, hmin⟩
      obtain ⟨q, rfl⟩ := (second_tail u).mp hu
      have hw : (toLex (.inr (q - 1)) : ℚ ⊕ₗ ℚ) ∈ upperTail (representativeCarrier 1) :=
        (second_tail _).mpr ⟨q - 1, rfl⟩
      apply hmin _ hw
      apply (representative_relation 1 _ _).mpr
      change (toLex (.inr (q - 1)) : ℚ ⊕ₗ ℚ) < toLex (.inr q)
      exact Sum.Lex.inr_lt_inr_iff.mpr (by linarith)
    simp [tailShape, hU, hleast, representativeShape]
  · let u : representativeCarrier 2 := toLex (.inr (toLex (.inl ())))
    have hu : u ∈ upperTail (representativeCarrier 2) :=
      (third_tail _).mpr ⟨toLex (.inl ()), rfl⟩
    have hleast : ∃ u : representativeCarrier 2, u ∈ upperTail (representativeCarrier 2) ∧
        ∀ x ∈ upperTail (representativeCarrier 2), ¬ sequenceRelation (representativeCarrier 2) x u := by
      refine ⟨u, hu, fun x hx hxu => ?_⟩
      obtain ⟨y, rfl⟩ := (third_tail x).mp hx
      have hh := (representative_relation 2 _ _).mp hxu
      change (toLex (.inr y) : ℚ ⊕ₗ (Unit ⊕ₗ ℚ)) < toLex (.inr (toLex (.inl ()))) at hh
      have hy : y < (toLex (.inl ()) : Unit ⊕ₗ ℚ) := Sum.Lex.inr_lt_inr_iff.mp hh
      obtain ⟨y, rfl⟩ := toLex.surjective y
      cases y with
      | inl z => cases z; exact (lt_irrefl _ hy)
      | inr q => exact Sum.Lex.not_inr_lt_inl hy
    simp [tailShape, show (upperTail (representativeCarrier 2)).Nonempty from ⟨u, hu⟩,
      hleast, representativeShape]

end Lemmatheca.ModelTheory.CountableModels
