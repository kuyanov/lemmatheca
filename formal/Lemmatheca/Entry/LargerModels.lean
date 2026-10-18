import Lemmatheca.MathematicalLogic.LargerModels
import Lemmatheca.MathematicalLogic.Compactness
import Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-! Concrete examples for model-size thresholds and independence. -/

namespace Lemmatheca.Entry.LargerModels

open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.MathematicalLogic.LargerModels
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

universe u

/-- Even a language with arbitrarily many constants has a one-element structure. -/
theorem constants_singleton_model (α : Type u) :
    ∃ M : Theory.ModelType.{u, 0, u} (∅ : (constantsOn α).Theory), Subsingleton M := by
  let : (constantsOn α).Structure (ULift.{u} Unit) :=
    Lemmatheca.MathematicalLogic.Compactness.constantStructure _ _
  refine ⟨Theory.ModelType.of _ (ULift.{u} Unit), ?_⟩
  change Subsingleton (ULift.{u} Unit)
  infer_instance

/-- Arbitrarily many constant symbols also fit a countably infinite domain. -/
theorem constants_countable_model (α : Type u) :
    ∃ M : Theory.ModelType.{u, 0, u} (∅ : (constantsOn α).Theory), #M = ℵ₀ := by
  let : (constantsOn α).Structure (ULift.{u} ℕ) :=
    Lemmatheca.MathematicalLogic.Compactness.constantStructure _ _
  refine ⟨Theory.ModelType.of _ (ULift.{u} ℕ), ?_⟩
  change #(ULift.{u} ℕ) = ℵ₀
  simp

/-- Distinct named elements can attain the exact cardinality of their index set. -/
theorem distinct_names_exact_model (α : Type u) [Nonempty α] :
    ∃ M : Theory.ModelType.{u, 0, u} (Language.empty.distinctConstantsTheory (Set.univ : Set α)),
      #M = #α := by
  classical
  let : Inhabited α := Classical.inhabited_of_nonempty inferInstance
  let : Language.empty.Structure α :=
    Lemmatheca.MathematicalLogic.Compactness.constantStructure _ _
  let : (constantsOn α).Structure α := constantsOn.structure id
  let : Language.empty[[α]].Structure α := withConstantsStructure _ _
  have hm : α ⊨ Language.empty.distinctConstantsTheory (Set.univ : Set α) := by
    rw [model_distinctConstantsTheory]
    intro a _ b _ hab
    exact hab
  let := hm
  exact ⟨Theory.ModelType.of _ α, rfl⟩

theorem equality_independence :
    Independent (∅ : Language.empty.Theory) (allPairEqual Language.empty) := by
  rw [independent_iff_two_models]
  let : Language.empty.Structure Unit :=
    Lemmatheca.MathematicalLogic.Compactness.constantStructure _ _
  let : Language.empty.Structure Bool :=
    Lemmatheca.MathematicalLogic.Compactness.constantStructure _ _
  constructor
  · have hm : Unit ⊨ insert (allPairEqual Language.empty) (∅ : Language.empty.Theory) := by
      constructor
      intro φ hφ
      obtain rfl := Set.mem_singleton_iff.mp (by simpa using hφ)
      exact allPairEqual_realize.mpr inferInstance
    let := hm
    exact Theory.Model.isSatisfiable Unit
  · have hm : Bool ⊨ insert (allPairEqual Language.empty).not
        (∅ : Language.empty.Theory) := by
      constructor
      intro φ hφ
      obtain rfl := Set.mem_singleton_iff.mp (by simpa using hφ)
      rw [Sentence.realize_not, allPairEqual_realize]
      intro hs
      have hbad := hs.elim false true
      cases hbad
    let := hm
    exact Theory.Model.isSatisfiable Bool

end Lemmatheca.Entry.LargerModels
