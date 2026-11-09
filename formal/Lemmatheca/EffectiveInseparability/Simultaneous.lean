import Lemmatheca.EffectiveInseparability.Race

/-! Simultaneous self-reference from one tagged master program. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveInseparability

open UniversalComputation EffectiveEnumerations UniformSelfReference

def JointlyRE (R : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  REPred (fun t : ℕ × (ℕ × (ℕ × ℕ)) => R t.1 t.2.1 t.2.2.1 t.2.2.2)

def recognize (R : ℕ → ℕ → ℕ → ℕ → Prop) (u v a x : ℕ) : Part ℕ :=
  Part.assert (R u v a x) fun _ => Part.some 0

noncomputable def simultaneousMaster (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop)
    (z a y : ℕ) : Part ℕ :=
  if y.unpair.1 = 0 then
    recognize R₀ (specialize z 0) (specialize z 1) a y.unpair.2
  else recognize R₁ (specialize z 0) (specialize z 1) a y.unpair.2

def MasterSelector (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop) (h : ℕ → ℕ) : Prop :=
  Primrec h ∧ ∀ a y, phi (h a) y = simultaneousMaster R₀ R₁ (h a) a y

def leftSelector (h : ℕ → ℕ) (a : ℕ) : ℕ := specialize (h a) 0

def rightSelector (h : ℕ → ℕ) (a : ℕ) : ℕ := specialize (h a) 1

def SimultaneousDomains (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop) (u v : ℕ → ℕ) : Prop :=
  (∀ a, indexSet (u a) = {x | R₀ (u a) (v a) a x}) ∧
    ∀ a, indexSet (v a) = {x | R₁ (u a) (v a) a x}

private theorem recognize_partial (R : ℕ → ℕ → ℕ → ℕ → Prop) (hR : JointlyRE R) :
    Partrec (fun t : ℕ × (ℕ × (ℕ × ℕ)) => recognize R t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  exact (hR.map (Computable.const 0).to₂).of_eq fun t => by
    apply Part.ext
    intro n
    simp [recognize, eq_comm]

theorem simultaneous_master_partial (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop)
    (h₀ : JointlyRE R₀) (h₁ : JointlyRE R₁) :
    Partrec (fun t : ℕ × (ℕ × ℕ) => simultaneousMaster R₀ R₁ t.1 t.2.1 t.2.2) := by
  classical
  have hu : Computable (fun t : ℕ × (ℕ × ℕ) => specialize t.1 0) :=
    specialize_primitive.to_comp.comp Computable.fst (Computable.const 0)
  have hv : Computable (fun t : ℕ × (ℕ × ℕ) => specialize t.1 1) :=
    specialize_primitive.to_comp.comp Computable.fst (Computable.const 1)
  have ha : Computable (fun t : ℕ × (ℕ × ℕ) => t.2.1) :=
    Computable.fst.comp Computable.snd
  have hy : Computable (fun t : ℕ × (ℕ × ℕ) => t.2.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.snd))
  have hm : Computable (fun t : ℕ × (ℕ × ℕ) =>
      (specialize t.1 0, (specialize t.1 1, (t.2.1, t.2.2.unpair.2)))) :=
    hu.pair (hv.pair (ha.pair hy))
  have ht : Computable (fun t : ℕ × (ℕ × ℕ) => decide (t.2.2.unpair.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.snd)))
      (Computable.const 0)
  exact (Partrec.cond ht ((recognize_partial R₀ h₀).comp hm)
    ((recognize_partial R₁ h₁).comp hm)).of_eq fun t => by
      simp only [Bool.cond_decide]
      rfl

theorem master_selector_exists (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop)
    (h₀ : JointlyRE R₀) (h₁ : JointlyRE R₁) :
    ∃ h, MasterSelector R₀ R₁ h := by
  exact parameterized_partial_recursion (simultaneous_master_partial R₀ R₁ h₀ h₁)

theorem specified_simultaneous_selectors (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop)
    (h : ℕ → ℕ) (hh : MasterSelector R₀ R₁ h) :
    Primrec (leftSelector h) ∧ Primrec (rightSelector h) ∧
      SimultaneousDomains R₀ R₁ (leftSelector h) (rightSelector h) := by
  refine ⟨specialize_primitive.comp hh.1 (Primrec.const 0),
    specialize_primitive.comp hh.1 (Primrec.const 1), ?_, ?_⟩
  · intro a
    ext x
    change (phi (specialize (h a) 0) x).Dom ↔ _
    rw [specialize_eval, hh.2 a (Nat.pair 0 x)]
    simp [simultaneousMaster, recognize, leftSelector, rightSelector, Part.assert]
  · intro a
    ext x
    change (phi (specialize (h a) 1) x).Dom ↔ _
    rw [specialize_eval, hh.2 a (Nat.pair 1 x)]
    simp [simultaneousMaster, recognize, leftSelector, rightSelector, Part.assert]

theorem simultaneous_recursion (R₀ R₁ : ℕ → ℕ → ℕ → ℕ → Prop)
    (h₀ : JointlyRE R₀) (h₁ : JointlyRE R₁) :
    ∃ h, MasterSelector R₀ R₁ h ∧ Primrec (leftSelector h) ∧ Primrec (rightSelector h) ∧
      SimultaneousDomains R₀ R₁ (leftSelector h) (rightSelector h) := by
  obtain ⟨h, hh⟩ := master_selector_exists R₀ R₁ h₀ h₁
  exact ⟨h, hh, specified_simultaneous_selectors R₀ R₁ h hh⟩

end Lemmatheca.ComputabilityTheory.EffectiveInseparability
