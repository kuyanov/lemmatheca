import Lemmatheca.RicesTheorem.RicesTheorem

namespace Lemmatheca.ComputabilityTheory.RicesTheorem

open Encodable Denumerable
open Nat.Partrec (Code)
open UniversalComputation

theorem syntax_counterexample :
    ComputablePred (fun e : ℕ => e = 0) ∧
    encode (Code.comp Code.zero Code.zero) = 6 ∧ phi 0 = phi 6 ∧
    ¬ Extensional ({0} : Set ℕ) := by
  have hp : phi 0 = phi 6 := by
    funext x
    rw [show (0 : ℕ) = encode Code.zero from rfl,
      show (6 : ℕ) = encode (Code.comp Code.zero Code.zero) from rfl]
    simp only [phi, ofNat_encode, Code.eval]
    change Part.some 0 = (Part.some 0).bind (fun _ => Part.some 0)
    simp only [Part.bind_some]
  refine ⟨(Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred, rfl, hp, ?_⟩
  intro he
  have h := he 0 6 hp
  simp at h

def promiseTest (e : ℕ) : Part ℕ :=
  (phi e 0).map (fun n => if n = 0 then 1 else 0)

theorem promiseTest_spec :
    Partrec promiseTest ∧
    (∀ e, (promiseTest e).Dom ↔ (phi e 0).Dom) ∧
    (∀ e, 1 ∈ promiseTest e ↔ 0 ∈ phi e 0) ∧
    (∀ e, 0 ∈ promiseTest e ↔ ∃ y, y ∈ phi e 0 ∧ y ≠ 0) := by
  have hc : Computable (fun n : ℕ => if n = 0 then 1 else 0) :=
    ComputablePred.ite (Computable.const 1) (Computable.const 0)
      (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred
  refine ⟨(phi_recursive.comp Computable.id (Computable.const 0)).map
    (hc.comp Computable.snd).to₂, fun _ => Iff.rfl, ?_, ?_⟩
  · intro e
    simp only [promiseTest, Part.mem_map_iff]
    constructor
    · rintro ⟨y, hy, hb⟩
      by_cases hz : y = 0
      · simpa [hz] using hy
      · simp [hz] at hb
    · intro h
      exact ⟨0, h, by simp⟩
  · intro e
    simp only [promiseTest, Part.mem_map_iff]
    constructor
    · rintro ⟨y, hy, hb⟩
      refine ⟨y, hy, ?_⟩
      intro hz
      simp [hz] at hb
    · rintro ⟨y, hy, hz⟩
      exact ⟨y, hy, by simp [hz]⟩

theorem promiseTest_total_inputs (e : ℕ) (he : e ∈ totality) :
    ∃ b, b ∈ promiseTest e ∧ (b = 0 ∨ b = 1) ∧
      (b = 1 ↔ 0 ∈ phi e 0) := by
  classical
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp (he 0)
  by_cases hz : y = 0
  · refine ⟨1, (promiseTest_spec.2.2.1 e).mpr (by simpa [hz] using hy), Or.inr rfl, ?_⟩
    simp [show 0 ∈ phi e 0 by simpa [hz] using hy]
  · refine ⟨0, (promiseTest_spec.2.2.2 e).mpr ⟨y, hy, hz⟩, Or.inl rfl, ?_⟩
    simp only [zero_ne_one, false_iff]
    intro h
    exact hz (Part.mem_unique hy h)

theorem promiseTest_boundary :
    (∃ e, e ∈ totality ∧ 1 ∈ promiseTest e) ∧
    (∃ e, e ∈ totality ∧ 0 ∈ promiseTest e) ∧
    (∃ e, ¬ (promiseTest e).Dom) := by
  obtain ⟨e0, h0⟩ := phi_complete (f := fun _ => Part.some 0) Nat.Partrec.zero
  obtain ⟨e1, h1⟩ := phi_complete (f := fun _ => Part.some 1)
    (Nat.Partrec.of_primrec (Nat.Primrec.const 1))
  obtain ⟨eb, hb⟩ := phi_complete Nat.Partrec.none
  exact ⟨⟨e0, by simp [totality, h0], by simp [promiseTest, h0]⟩,
    ⟨e1, by simp [totality, h1], by simp [promiseTest, h1]⟩,
    ⟨eb, by simp [promiseTest, hb]⟩⟩

end Lemmatheca.ComputabilityTheory.RicesTheorem
