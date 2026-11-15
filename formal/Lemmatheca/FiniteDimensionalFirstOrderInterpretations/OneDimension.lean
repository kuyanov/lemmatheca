import Lemmatheca.FiniteDimensionalFirstOrderInterpretations.Core

namespace Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations
open FirstOrder FirstOrder.Language
universe u v u' v' w z
noncomputable section
variable {L : Language.{u,v}} {K : Language.{u',v'}} {M : Type w} [K.Structure M]
namespace InterpretationData

/-- The old designated element variable becomes coordinate zero in each block. -/
def fromOne (O : Lemmatheca.MathematicalLogic.InterpretingTheories.InterpretationData L K) :
    InterpretationData L K 1 where
  positive := by decide
  domain := O.domain.relabel (fun _ => 0)
  functionGraph f := (O.functionGraph f).relabel
    (Sum.elim (fun i => Sum.inl (i,0)) (fun _ => Sum.inr 0))
  relationFormula R := (O.relationFormula R).relabel (fun i => (i,0))

variable (O : Lemmatheca.MathematicalLogic.InterpretingTheories.InterpretationData L K)

/-- The specified comparison reads the sole coordinate, rather than choosing a bijection. -/
def oneDomainEquiv : (fromOne O).Domain M ≃ O.Domain M where
  toFun x := ⟨x.val 0, by
    simpa only [fromOne, Formula.realize_relabel, Function.comp_def] using x.property⟩
  invFun x := ⟨fun _ => x.val, by
    simpa only [fromOne, Formula.realize_relabel, Function.comp_def] using x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    rw [Fin.eq_zero i]
  right_inv _ := rfl

theorem oneDomainEquiv_value (x : (fromOne O).Domain M) :
    (oneDomainEquiv O x).val = x.val 0 := by
  rfl

private theorem one_graph_iff {n : ℕ} (f : L.Functions n)
    (x : Fin n → (fromOne O).Domain M) (y : Fin 1 → M) :
    ((fromOne O).guardedGraph f).Realize
      (Sum.elim ((fromOne O).coordinates M x) y) ↔
      (O.guardedGraph f).Realize
        (Sum.elim (fun i => (oneDomainEquiv O (x i)).val) (fun _ => y 0)) := by
  simp only [guardedGraph, fromOne, Formula.realize_inf, Formula.realize_relabel,
    Lemmatheca.MathematicalLogic.InterpretingTheories.InterpretationData.guardedGraph,
    Formula.realize_inf]
  apply and_congr
  · rfl
  · apply Iff.of_eq
    congr 1
    funext a
    cases a <;> rfl

theorem fromOne_graphs (h : O.GoodGraphs M) : (fromOne O).GoodGraphs M := by
  intro n f x
  obtain ⟨z, hz, hu⟩ := h n f (fun i => oneDomainEquiv O (x i))
  refine ⟨fun _ => z, (one_graph_iff O f x (fun _ => z)).mpr hz, ?_⟩
  intro y hy
  have he := hu (y 0) ((one_graph_iff O f x y).mp hy)
  funext j
  rw [Fin.eq_zero j]
  exact he

theorem fromOne_good (h : O.Good M) : (fromOne O).Good M := by
  obtain ⟨x⟩ := h.1
  exact ⟨⟨(oneDomainEquiv O).symm x⟩, fromOne_graphs O h.2⟩

theorem fromOne_isomorphism (h : O.GoodGraphs M) :
    letI := O.inducedStructure h
    letI := (fromOne O).inducedStructure (fromOne_graphs O h)
    ∃ e : (fromOne O).Domain M ≃[L] O.Domain M,
      e.toEquiv = oneDomainEquiv O := by
  let := O.inducedStructure h
  let := (fromOne O).inducedStructure (fromOne_graphs O h)
  refine ⟨{
    toEquiv := oneDomainEquiv O
    map_fun' := ?_
    map_rel' := ?_
  }, rfl⟩
  · intro n f x
    apply Subtype.ext
    apply (O.induced_fun_graph h f (fun i => oneDomainEquiv O (x i)) _).mp
    apply (one_graph_iff O f x (Structure.funMap f x).val).mp
    exact ((fromOne O).induced_fun_graph (fromOne_graphs O h) f x _).mpr rfl
  · intro n R x
    change (O.relationFormula R).Realize (fun i => (oneDomainEquiv O (x i)).val) ↔
      ((fromOne O).relationFormula R).Realize ((fromOne O).coordinates M x)
    simp only [fromOne, Formula.realize_relabel]
    rfl

theorem fromOne_translation {α : Type z} (h : O.GoodGraphs M)
    (A : L.Formula α) (v : α → (fromOne O).Domain M) :
    ((fromOne O).translate A).Realize ((fromOne O).coordinates M v) ↔
      (O.translate A).Realize (fun a => (oneDomainEquiv O (v a)).val) := by
  let := O.inducedStructure h
  let := (fromOne O).inducedStructure (fromOne_graphs O h)
  obtain ⟨e, he⟩ := fromOne_isomorphism O h
  have hv : (fun a => (e (v a)).val) = (fun a => (oneDomainEquiv O (v a)).val) := by
    funext a
    change (e.toEquiv (v a)).val = _
    rw [he]
  have ho := O.realize_translate h A (fun a => e (v a))
  rw [hv] at ho
  have hiso : A.Realize (fun a => e (v a)) ↔ A.Realize v :=
    StrongHomClass.realize_formula e A
  exact ((fromOne O).realize_translate (fromOne_graphs O h) A v).trans
    (hiso.symm.trans ho.symm)

end InterpretationData
end
end Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations
