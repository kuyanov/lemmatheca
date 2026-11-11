import Lemmatheca.AntiDiagonalNormalization.Uniform

namespace Lemmatheca.Entry.AntiDiagonalNormalization

open Lemmatheca.ComputabilityTheory
open UniversalComputation EffectiveEnumerations AntiDiagonalNormalization

/-- Divergence everywhere vacuously avoids all domain fixed points. -/
theorem empty_partial_fpf : PartialFPF (fun _ => Part.none) := by
  intro e j hj
  simp at hj

theorem no_total_partial_fpf (d : ℕ) (hd : PartialFPF (phi d)) :
    ¬ ∀ n, (phi d n).Dom := by
  intro ht
  obtain ⟨p, hp⟩ := phi_complete
    (Nat.Partrec.none : Nat.Partrec (fun _ : ℕ => (Part.none : Part ℕ)))
  have hn : ¬ (phi p 0).Dom := by rw [hp]; simp
  exact selector_avoids d p 0 hd hn (ht (selector d p 0))

theorem domain_totalizer_not_function :
    let c₀ := Encodable.encode (Nat.Partrec.Code.const 0)
    let c₁ := Encodable.encode (Nat.Partrec.Code.const 1)
    TotalizesAvoiding (fun _ => Part.none) (fun _ => Part.some c₀) (fun _ => c₁) ∧
      (∀ n x, phi ((fun _ : ℕ => c₁) n) x = Part.some 1 ∧
        phi ((fun _ : ℕ => c₀) n) x = Part.some 0) := by
  have heval (v x : ℕ) : phi (Encodable.encode (Nat.Partrec.Code.const v)) x = Part.some v := by
    simp only [phi, Denumerable.ofNat_encode, Nat.Partrec.Code.eval_const]
  dsimp only
  refine ⟨⟨⟨Computable.const _, ?_⟩, ?_⟩, ?_⟩
  · intro n j hj
    have hj0 : j = Encodable.encode (Nat.Partrec.Code.const 0) := Part.mem_some_iff.mp hj
    subst j
    ext x
    change (phi (Encodable.encode (Nat.Partrec.Code.const 1)) x).Dom ↔
      (phi (Encodable.encode (Nat.Partrec.Code.const 0)) x).Dom
    rw [heval, heval]
    simp
  · intro n hn
    exact not_false
  · intro n x
    exact ⟨heval 1 x, heval 0 x⟩

end Lemmatheca.Entry.AntiDiagonalNormalization
