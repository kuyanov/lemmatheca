import Lemmatheca.BooleanAlgebrasOfFormulas.BooleanAlgebrasOfFormulas

namespace Lemmatheca.Entry.BooleanAlgebrasOfFormulas

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.BooleanAlgebrasOfFormulas

theorem all_true_singleton_not_definable :
    ¬ ∃ A : PropFormula ℕ, truthSet (classOf A) = {fun _ => true} := by
  rintro ⟨A, hA⟩
  obtain ⟨n, hn⟩ := (atoms A).exists_notMem
  let v : Valuation ℕ := fun _ => true
  let w : Valuation ℕ := fun a => if a = n then false else true
  have hv : eval v A = true := by
    have hm : v ∈ truthSet (classOf A) := by rw [hA]; exact Set.mem_singleton v
    exact hm
  have he : eval w A = eval v A := by
    apply eval_congr
    intro a ha
    have han : a ≠ n := fun h => hn (h ▸ ha)
    simp [w, v, han]
  have hw : w ∈ truthSet (classOf A) := he.trans hv
  have hwv : w = v := Set.mem_singleton_iff.mp (hA ▸ hw)
  have h := congrFun hwv n
  simp [w, v] at h

end Lemmatheca.Entry.BooleanAlgebrasOfFormulas
