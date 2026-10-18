import Lemmatheca.MathematicalLogic.Ultraproducts
import Lemmatheca.MathematicalLogic.FirstOrderSemantics
import Lemmatheca.SetTheory.FiltersAndUltrafilters
import Mathlib.Tactic.FinCases

/-! The natural-order ultrapower and its element represented by the identity. -/

namespace Lemmatheca.Entry.Ultraproducts

open FirstOrder FirstOrder.Language Filter
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.Ultraproducts

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

end Lemmatheca.Entry.Ultraproducts
