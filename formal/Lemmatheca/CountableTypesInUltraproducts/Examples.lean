import Lemmatheca.CountableTypesInUltraproducts.Parameters
import Lemmatheca.Ultraproducts.Examples

namespace Lemmatheca.Entry.CountableTypesInUltraproducts

open FirstOrder FirstOrder.Language Filter
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.ModelTheory.Ultraproducts
open Lemmatheca.ModelTheory.Ultraproducts.CountableTypes
open Lemmatheca.Entry.Ultraproducts

attribute [local instance] naturalOrderStructure

/-- The literal native formula saying that the element named k is below the variable. -/
def lowerBoundFormula (k : ℕ) : binaryRelLanguage[[ℕ]].Formula (Fin 1) :=
  BoundedFormula.rel (.inl .rel) ![.func (binaryRelLanguage.con k) Fin.elim0, .var (.inl 0)]

def lowerBounds : Set (binaryRelLanguage[[ℕ]].Formula (Fin 1)) :=
  Set.range lowerBoundFormula

theorem lower_bound_realize {N : Type*} [binaryRelLanguage.Structure N]
    (names : ℕ → N) (a : Fin 1 → N) (k : ℕ) :
    let : binaryRelLanguage[[ℕ]].Structure N :=
      Lemmatheca.ModelTheory.Diagrams.namedExpansion names
    (lowerBoundFormula k).Realize a ↔ Structure.RelMap (L := binaryRelLanguage) .rel ![names k, a 0] := by
  let : binaryRelLanguage[[ℕ]].Structure N :=
    Lemmatheca.ModelTheory.Diagrams.namedExpansion names
  dsimp only
  change Structure.RelMap (L := binaryRelLanguage) .rel
    (fun j => Term.realize (Sum.elim a (default : Fin 0 → N))
      (![Term.func (binaryRelLanguage.con k) Fin.elim0,
        Term.var (.inl (0 : Fin 1))] j)) ↔ _
  apply iff_of_eq
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem finite_bounds {N : Type*} [binaryRelLanguage.Structure N]
    (names : ℕ → N)
    (h : ∀ s : Finset ℕ, ∃ b : N, ∀ k ∈ s,
      Structure.RelMap (L := binaryRelLanguage) .rel ![names k, b]) :
    let : binaryRelLanguage[[ℕ]].Structure N :=
      Lemmatheca.ModelTheory.Diagrams.namedExpansion names
    Lemmatheca.ModelTheory.Types.FinitelyRealized N lowerBounds := by
  classical
  let : binaryRelLanguage[[ℕ]].Structure N :=
    Lemmatheca.ModelTheory.Diagrams.namedExpansion names
  dsimp only
  intro s hs
  have origins (θ : s) : ∃ k, lowerBoundFormula k = θ.val := hs θ.property
  choose k hk using origins
  let t := Finset.univ.image k
  obtain ⟨b, hb⟩ := h t
  refine ⟨fun _ => b, fun θ hθ => ?_⟩
  have heq : lowerBoundFormula (k ⟨θ, hθ⟩) = θ := hk ⟨θ, hθ⟩
  rw [← heq]
  apply (lower_bound_realize names _ _).mpr
  exact hb _ (Finset.mem_image.mpr ⟨⟨θ, hθ⟩, Finset.mem_univ _, rfl⟩)

theorem standard_bounds_omitted :
    let : binaryRelLanguage[[ℕ]].Structure ℕ :=
      Lemmatheca.ModelTheory.Diagrams.namedExpansion (L := binaryRelLanguage) id
    Lemmatheca.ModelTheory.Types.FinitelyRealized ℕ lowerBounds ∧
      Lemmatheca.ModelTheory.Types.Omits ℕ lowerBounds := by
  classical
  let : binaryRelLanguage[[ℕ]].Structure ℕ :=
    Lemmatheca.ModelTheory.Diagrams.namedExpansion (L := binaryRelLanguage) id
  dsimp only
  constructor
  · apply finite_bounds id
    intro s
    refine ⟨s.sup id + 1, fun k hk => ?_⟩
    change k < s.sup id + 1
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  · rintro ⟨a, ha⟩
    have hh := (lower_bound_realize id a (a 0)).mp
      (ha _ (Set.mem_range_self (a 0)))
    exact Nat.lt_irrefl (a 0) hh

theorem identity_realizes_bounds (U : Ultrafilter ℕ)
    (hU : ¬Lemmatheca.SetTheory.FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ)) :
    let : binaryRelLanguage[[ℕ]].Structure (NaturalPower U) :=
      Lemmatheca.ModelTheory.Diagrams.namedExpansion (diagonal (L := binaryRelLanguage) U)
    Lemmatheca.ModelTheory.Types.FinitelyRealized (NaturalPower U) lowerBounds ∧
      Lemmatheca.ModelTheory.Types.Realizes lowerBounds (fun _ : Fin 1 => identityElement U) := by
  let : binaryRelLanguage[[ℕ]].Structure (NaturalPower U) :=
    Lemmatheca.ModelTheory.Diagrams.namedExpansion (diagonal (L := binaryRelLanguage) U)
  dsimp only
  have ha : Lemmatheca.ModelTheory.Types.Realizes lowerBounds
      (fun _ : Fin 1 => identityElement U) := by
    rintro θ ⟨k, rfl⟩
    apply (lower_bound_realize (diagonal (L := binaryRelLanguage) U) _ k).mpr
    exact (identity_above_and_outside U hU).1 k
  exact ⟨fun s hs => ⟨_, fun θ hθ => ha θ (hs hθ)⟩, ha⟩

theorem principal_bounds_omitted (i₀ : ℕ) :
    let : binaryRelLanguage[[ℕ]].Structure (NaturalPower (pure i₀)) :=
      Lemmatheca.ModelTheory.Diagrams.namedExpansion
        (diagonal (L := binaryRelLanguage) (pure i₀))
    Lemmatheca.ModelTheory.Types.FinitelyRealized (NaturalPower (pure i₀)) lowerBounds ∧
      Lemmatheca.ModelTheory.Types.Omits (NaturalPower (pure i₀)) lowerBounds := by
  classical
  let V : Ultrafilter ℕ := pure i₀
  let d := diagonal (L := binaryRelLanguage) (A := ℕ) V
  let : binaryRelLanguage[[ℕ]].Structure (NaturalPower V) :=
    Lemmatheca.ModelTheory.Diagrams.namedExpansion d
  dsimp only
  obtain ⟨e, he, hd, _⟩ := principal_ultrapower_inverse (L := binaryRelLanguage) (A := ℕ) i₀
  constructor
  · apply finite_bounds d
    intro s
    refine ⟨d (s.sup id + 1), fun k hk => ?_⟩
    have hh := (d.map_rel .rel ![k, s.sup id + 1]).mpr
      (show k < s.sup id + 1 from Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
    convert hh using 1
    funext j
    fin_cases j <;> rfl
  · rintro ⟨a, ha⟩
    let k := e (a 0)
    have hh := (lower_bound_realize d a k).mp (ha _ (Set.mem_range_self k))
    have hm := (e.map_rel .rel ![d k, a 0]).mpr hh
    have hdk : e (d k) = k := hd k
    have hlt : e (d k) < e (a 0) := by
      change Structure.RelMap (L := binaryRelLanguage) .rel ![e (d k), e (a 0)]
      convert hm using 1
      funext j
      fin_cases j <;> rfl
    rw [hdk] at hlt
    exact Nat.lt_irrefl k hlt

end Lemmatheca.Entry.CountableTypesInUltraproducts
