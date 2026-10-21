import Lemmatheca.Ultraproducts.Ultraproducts
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Lemmatheca.FiltersAndUltrafilters.FiltersAndUltrafilters
import Lemmatheca.ArithmeticTheories.ArithmeticTheories
import Mathlib.Tactic.FinCases

/-! The natural-order ultrapower and its element represented by the identity. -/

namespace Lemmatheca.Entry.Ultraproducts

open FirstOrder FirstOrder.Language Filter
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.Ultraproducts

@[instance_reducible] def naturalOrderStructure : binaryRelLanguage.Structure ℕ :=
  binaryRelStructure ℕ (· < ·)

attribute [local instance] naturalOrderStructure

abbrev NaturalPower (U : Ultrafilter ℕ) :=
  (U : Filter ℕ).Product (fun _ : ℕ => ℕ)

def powerLt (U : Ultrafilter ℕ) (x y : NaturalPower U) : Prop :=
  Structure.RelMap (L := binaryRelLanguage) .rel ![x, y]

def identityElement (U : Ultrafilter ℕ) : NaturalPower U :=
  ((fun n : ℕ => n) : NaturalPower U)

theorem identity_above_and_outside (U : Ultrafilter ℕ)
    (hU : ¬Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ)) :
    (∀ k : ℕ, powerLt U (diagonal (L := binaryRelLanguage) U k) (identityElement U)) ∧
      identityElement U ∉ Set.range (diagonal (L := binaryRelLanguage) (A := ℕ) U) := by
  have hcof := (Lemmatheca.SetTheory.FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mp hU
  have hlarge (k : ℕ) : ∀ᶠ n in U, k < n :=
    hcof (by rw [Nat.cofinite_eq_atTop]; exact eventually_gt_atTop k)
  constructor
  · intro k
    have h := (FirstOrder.Language.relMap_quotient_mk'
      (L := binaryRelLanguage) ((U : Filter ℕ).productSetoid (fun _ : ℕ => ℕ))
      BinaryRelationSymbol.rel ![(fun _ : ℕ => k), (fun n : ℕ => n)]).mpr (hlarge k)
    change Structure.RelMap (L := binaryRelLanguage) .rel
      ![((fun _ : ℕ => k) : NaturalPower U), ((fun n : ℕ => n) : NaturalPower U)]
    convert h using 1
    funext j
    fin_cases j <;> rfl
  · rintro ⟨k, hk⟩
    change ((fun _ : ℕ => k) : NaturalPower U) =
      ((fun n : ℕ => n) : NaturalPower U) at hk
    have heq : ∀ᶠ n in U, k = n := Quotient.exact hk
    obtain ⟨n, hkn, hlt⟩ := (heq.and (hlarge k)).exists
    exact (Nat.ne_of_lt hlt) hkn

namespace Arithmetic

open Lemmatheca.ModelTheory.ArithmeticTheories

abbrev Power (U : Ultrafilter ℕ) :=
  (U : Filter ℕ).Product (fun _ : ℕ => ℕ)

theorem coordinate_operations (U : Ultrafilter ℕ) :
    zeroValue (Power U) = ((fun _ : ℕ => 0) : Power U) ∧
    (∀ f : ℕ → ℕ, succValue (Power U) (f : Power U) =
      ((fun n => f n + 1) : Power U)) ∧
    (∀ f g : ℕ → ℕ, addValue (Power U) (f : Power U) (g : Power U) =
      ((fun n => f n + g n) : Power U)) ∧
    (∀ f g : ℕ → ℕ, mulValue (Power U) (f : Power U) (g : Power U) =
      ((fun n => f n * g n) : Power U)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := FirstOrder.Language.Ultraproduct.funMap_cast (L := language)
      (u := U) (M := fun _ : ℕ => ℕ) FunctionSymbol.zero (fun j => j.elim0)
    have heq : (Fin.elim0 : Fin 0 → Power U) =
        (fun i : Fin 0 => ((i.elim0 : ℕ → ℕ) : Power U)) := by
      funext i
      exact i.elim0
    change Structure.funMap (L := language) FunctionSymbol.zero Fin.elim0 = _
    rw [heq]
    exact h
  · intro f
    have h := FirstOrder.Language.Ultraproduct.funMap_cast (L := language)
      (u := U) (M := fun _ : ℕ => ℕ) FunctionSymbol.succ (fun _ => f)
    exact h
  · intro f g
    have h := FirstOrder.Language.Ultraproduct.funMap_cast (L := language)
      (u := U) (M := fun _ : ℕ => ℕ) FunctionSymbol.add ![f, g]
    change Structure.funMap (L := language) FunctionSymbol.add ![(f : Power U), (g : Power U)] = _
    convert h using 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · rfl
  · intro f g
    have h := FirstOrder.Language.Ultraproduct.funMap_cast (L := language)
      (u := U) (M := fun _ : ℕ => ℕ) FunctionSymbol.mul ![f, g]
    change Structure.funMap (L := language) FunctionSymbol.mul ![(f : Power U), (g : Power U)] = _
    convert h using 1
    · congr 1
      funext i
      fin_cases i <;> rfl
    · rfl

theorem sentence_transfer (U : Ultrafilter ℕ) (σ : language.Sentence) :
    Power U ⊨ σ ↔ ℕ ⊨ σ := by
  exact ((diagonal (L := language) U).map_sentence σ).symm

theorem models_true_arithmetic (U : Ultrafilter ℕ) : Power U ⊨ trueArithmetic := by
  have hn : ℕ ⊨ trueArithmetic := by
    change ℕ ⊨ language.completeTheory ℕ
    infer_instance
  exact ((diagonal (L := language) U).theory_model_iff trueArithmetic).mp hn

theorem models_PA (U : Ultrafilter ℕ) : Power U ⊨ PA := by
  exact ((diagonal (L := language) U).theory_model_iff PA).mp nat_models_PA

theorem diagonal_numeral (U : Ultrafilter ℕ) (n : ℕ) :
    diagonal (L := language) U n = numeralValue (Power U) n := by
  have h := HomClass.realize_term (diagonal (L := language) (A := ℕ) U)
    (t := numeral n) (v := Empty.elim)
  have hv : diagonal (L := language) U ∘ (Empty.elim : Empty → ℕ) =
      (Empty.elim : Empty → Power U) := funext fun z => z.elim
  rw [hv] at h
  change numeralValue (Power U) n = diagonal (L := language) U (numeralValue ℕ n) at h
  rw [numeral_value_nat] at h
  exact h.symm

theorem identity_not_numeral (U : Ultrafilter ℕ)
    (hU : ¬ Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ))
    (n : ℕ) : identityElement U ≠ numeralValue (Power U) n := by
  rw [← diagonal_numeral U n]
  intro heq
  apply (identity_above_and_outside U hU).2
  exact ⟨n, heq.symm⟩

theorem standard_copy_proper (U : Ultrafilter ℕ)
    (hU : ¬ Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ)) :
    standardCopy (Power U) ≠ Set.univ := by
  intro h
  have hm : identityElement U ∈ standardCopy (Power U) := by rw [h]; trivial
  obtain ⟨n, hn⟩ := hm
  exact identity_not_numeral U hU n hn.symm

theorem standard_copy_not_definable (U : Ultrafilter ℕ)
    (hU : ¬ Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ))
    {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) (a : Fin k → Power U) :
    ¬ DefinesWithParameters (Power U) φ a (standardCopy (Power U)) := by
  let : Power U ⊨ PA := models_PA U
  exact standard_copy_undefinable (Power U) (standard_copy_proper U hU) φ a

end Arithmetic

end Lemmatheca.Entry.Ultraproducts
