import Lemmatheca.IntermediatePropositionalKripkeCompleteness.Canonical
import Lemmatheca.PropositionalWeakExcludedMiddle.Frames
import Lemmatheca.PropositionalDummettLinearity.Frames

/-! All compound schema instances control the order of the restricted canonical worlds. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula Canonical Extensions Kripke

universe v

theorem kc_axioms_consistent : Consistent (WeakExcludedMiddle.axioms (α := ℕ)) := by
  intro h
  let M := singleton.{0, 0} (fun _ : ℕ => false)
  apply sound h M PUnit.unit
  intro B hB
  obtain ⟨A, rfl⟩ := hB
  apply WeakExcludedMiddle.directed_cone_forces_wem M PUnit.unit
  intro u v _ _
  exact ⟨u, le_rfl, le_of_eq (Subsingleton.elim v u)⟩

theorem lc_axioms_consistent : Consistent (Dummett.axioms (α := ℕ)) := by
  intro h
  let M := singleton.{0, 0} (fun _ : ℕ => false)
  apply sound h M PUnit.unit
  intro B hB
  obtain ⟨⟨A, C⟩, rfl⟩ := hB
  apply Dummett.linear_cone_forces_linearity M PUnit.unit
  intro u v _ _
  exact Or.inl (le_of_eq (Subsingleton.elim u v))

theorem kc_union_consistent
    (P Q R : World (WeakExcludedMiddle.axioms (α := ℕ))) (hPQ : P ≤ Q) (hPR : P ≤ R) :
    Consistent (Q.val.val ∪ R.val.val) := by
  intro h
  obtain ⟨L, _, hR, hQ⟩ := inconsistent_union_package Q.val.val R.val.val
    Q.val.property.closed R.val.property.closed h
  have hW : disj (neg (package L)) (neg (neg (package L))) ∈ P.val.val :=
    P.property ⟨package L, rfl⟩
  rcases P.val.property.disjunction hW with hn | hnn
  · exact R.val.property.consistent
      (.negElim (.assumption hR) (.assumption (hPR hn)))
  · exact Q.val.property.consistent
      (.negElim (.assumption hQ) (.assumption (hPQ hnn)))

/-- The joint future is the specified earlier extension of the actual union. -/
noncomputable def kc_jointWorld
    (P Q R : World (WeakExcludedMiddle.axioms (α := ℕ))) (hPQ : P ≤ Q) (hPR : P ≤ R) :
    World (WeakExcludedMiddle.axioms (α := ℕ)) :=
  ⟨extensionWorld (Q.val.val ∪ R.val.val) falsum (kc_union_consistent P Q R hPQ hPR),
    fun _ hB => extension_contains (Q.val.val ∪ R.val.val) falsum (Or.inl (Q.property hB))⟩

theorem kc_jointWorld_spec
    (P Q R : World (WeakExcludedMiddle.axioms (α := ℕ))) (hPQ : P ≤ Q) (hPR : P ≤ R) :
    (kc_jointWorld P Q R hPQ hPR).val.val = extension (Q.val.val ∪ R.val.val) falsum ∧
      Q ≤ kc_jointWorld P Q R hPQ hPR ∧ R ≤ kc_jointWorld P Q R hPQ hPR := by
  refine ⟨rfl, ?_, ?_⟩
  · intro B hB
    exact extension_contains (Q.val.val ∪ R.val.val) falsum (Or.inl hB)
  · intro B hB
    exact extension_contains (Q.val.val ∪ R.val.val) falsum (Or.inr hB)

theorem kc_canonical_directed :
    WeakExcludedMiddle.DirectedFutureCones (World (WeakExcludedMiddle.axioms (α := ℕ))) := by
  intro P Q R hPQ hPR
  exact ⟨kc_jointWorld P Q R hPQ hPR, (kc_jointWorld_spec P Q R hPQ hPR).2⟩

theorem lc_canonical_linear :
    Dummett.LocallyLinear (World (Dummett.axioms (α := ℕ))) := by
  classical
  intro P Q R hPQ hPR
  by_cases hQR : Q ≤ R
  · exact Or.inl hQR
  apply Or.inr
  by_contra hRQ
  have hQR' : ¬ Q.val.val ⊆ R.val.val := hQR
  have hRQ' : ¬ R.val.val ⊆ Q.val.val := hRQ
  obtain ⟨B, hBQ, hBR⟩ := Set.not_subset.mp hQR'
  obtain ⟨C, hCR, hCQ⟩ := Set.not_subset.mp hRQ'
  have hL : disj (impl B C) (impl C B) ∈ P.val.val := P.property ⟨(B, C), rfl⟩
  rcases P.val.property.disjunction hL with hBC | hCB
  · exact hCQ (Q.val.property.closed
      (.implElim (.assumption (hPQ hBC)) (.assumption hBQ)))
  · exact hBR (R.val.property.closed
      (.implElim (.assumption (hPR hCB)) (.assumption hCR)))

/-- These two lift facts keep the same order conditions in an arbitrary world universe. -/
theorem kc_lifted_directed : WeakExcludedMiddle.DirectedFutureCones
    (ULift.{v} (World (WeakExcludedMiddle.axioms (α := ℕ)))) := by
  intro P Q R hPQ hPR
  obtain ⟨U, hQU, hRU⟩ := kc_canonical_directed P.down Q.down R.down hPQ hPR
  exact ⟨ULift.up U, hQU, hRU⟩

theorem lc_lifted_linear : Dummett.LocallyLinear
    (ULift.{v} (World (Dummett.axioms (α := ℕ)))) := by
  intro P Q R hPQ hPR
  exact lc_canonical_linear P.down Q.down R.down hPQ hPR

end Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical
