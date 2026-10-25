import Lemmatheca.ComputablyInseparableSets.Separation

/-! The specified least-stage race of two negative certificate searches. -/

namespace Lemmatheca.ComputabilityTheory.ComputableSeparation

open UniversalComputation

def CoEnumerable (P : Set ℕ) : Prop := REPred (fun x => x ∉ P)

noncomputable def raceStage (R S : ℕ → ℕ → Prop) (x : ℕ) : Part ℕ := by
  classical
  exact Nat.rfind fun t => Part.some (decide (R x t ∨ S x t))

noncomputable def negativeRace (R S : ℕ → ℕ → Prop) (x : ℕ) : Part ℕ := by
  classical
  exact (raceStage R S x).map fun t => if R x t then 0 else 1

theorem raceStage_spec (R S : ℕ → ℕ → Prop) (x t : ℕ) :
    t ∈ raceStage R S x ↔ (R x t ∨ S x t) ∧
      ∀ i < t, ¬ R x i ∧ ¬ S x i := by
  classical
  change (t ∈ Nat.rfind (fun i => Part.some (decide (R x i ∨ S x i)))) ↔ _
  erw [Nat.mem_rfind]
  simp only [Part.mem_some_iff, true_eq_decide_iff, false_eq_decide_iff, not_or]

theorem negativeRace_partial (R S : ℕ → ℕ → Prop)
    (hR : PrimrecPred (fun p : ℕ × ℕ => R p.1 p.2))
    (hS : PrimrecPred (fun p : ℕ × ℕ => S p.1 p.2)) :
    Nat.Partrec (negativeRace R S) := by
  classical
  have hc : Computable₂ (fun x t => decide (R x t ∨ S x t)) := (hR.or hS).decide.to_comp
  have hs : Partrec (raceStage R S) := Partrec.rfind hc.partrec₂
  have hout : Computable₂ (fun x t => if R x t then (0 : ℕ) else 1) :=
    (Primrec.ite hR (Primrec.const 0) (Primrec.const 1)).to_comp.to₂
  exact Partrec.nat_iff.mp (hs.map hout)

theorem negativeRace_domain (R S : ℕ → ℕ → Prop) (x : ℕ) :
    (negativeRace R S x).Dom ↔ (∃ t, R x t) ∨ (∃ t, S x t) := by
  classical
  rw [negativeRace, Part.map_Dom]
  change (Nat.rfind (fun t => Part.some (decide (R x t ∨ S x t)))).Dom ↔ _
  constructor
  · intro hd
    obtain ⟨t, ht, _⟩ := Nat.rfind_dom.mp hd
    have h : R x t ∨ S x t := by simpa using ht
    exact h.elim (fun hr => Or.inl ⟨t, hr⟩) (fun hs => Or.inr ⟨t, hs⟩)
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact Nat.rfind_dom.mpr ⟨t, by simpa using (Or.inl ht : R x t ∨ S x t),
        fun {_} _ => trivial⟩
    · exact Nat.rfind_dom.mpr ⟨t, by simpa using (Or.inr ht : R x t ∨ S x t),
        fun {_} _ => trivial⟩

theorem negativeRace_at_stage (R S : ℕ → ℕ → Prop) (x t : ℕ)
    (ht : t ∈ raceStage R S x) :
    negativeRace R S x = Part.some (@ite ℕ (R x t) (Classical.propDecidable _) 0 1) := by
  classical
  simp only [negativeRace, Part.eq_some_iff.mpr ht, Part.map_some]

noncomputable def raceTotal (R S : ℕ → ℕ → Prop)
    (hcover : ∀ x, ∃ t, R x t ∨ S x t) (x : ℕ) : ℕ := by
  classical
  exact if R x (Nat.find (hcover x)) then 0 else 1

theorem negativeRace_total_value (R S : ℕ → ℕ → Prop)
    (hcover : ∀ x, ∃ t, R x t ∨ S x t) (x : ℕ) :
    negativeRace R S x = Part.some (raceTotal R S hcover x) := by
  classical
  have ht : Nat.find (hcover x) ∈ raceStage R S x := by
    apply (raceStage_spec R S x _).mpr
    exact ⟨Nat.find_spec (hcover x), fun i hi => not_or.mp (Nat.find_min (hcover x) hi)⟩
  exact negativeRace_at_stage R S x _ ht

theorem raceTotal_computable (R S : ℕ → ℕ → Prop)
    (hR : PrimrecPred (fun p : ℕ × ℕ => R p.1 p.2))
    (hS : PrimrecPred (fun p : ℕ × ℕ => S p.1 p.2))
    (hcover : ∀ x, ∃ t, R x t ∨ S x t) :
    Computable (raceTotal R S hcover) := by
  apply (Partrec.nat_iff.mpr (negativeRace_partial R S hR hS)).of_eq_tot
  intro x
  rw [negativeRace_total_value R S hcover]
  exact Part.mem_some _

def negativeSeparator (R S : ℕ → ℕ → Prop)
    (hcover : ∀ x, ∃ t, R x t ∨ S x t) : Set ℕ :=
  {x | raceTotal R S hcover x = 1}

theorem negativeSeparator_spec (P Q : Set ℕ) (R S : ℕ → ℕ → Prop)
    (hR : PrimrecPred (fun p : ℕ × ℕ => R p.1 p.2))
    (hS : PrimrecPred (fun p : ℕ × ℕ => S p.1 p.2))
    (hRP : ∀ x, x ∉ P ↔ ∃ t, R x t)
    (hSQ : ∀ x, x ∉ Q ↔ ∃ t, S x t)
    (hcover : ∀ x, ∃ t, R x t ∨ S x t) :
    ComputablePred (fun x => x ∈ negativeSeparator R S hcover) ∧
      Separator P Q (negativeSeparator R S hcover) := by
  classical
  refine ⟨(Primrec.eq.decide.to_comp.comp (raceTotal_computable R S hR hS hcover)
    (Computable.const 1)).computablePred, ?_, ?_⟩
  · intro x hx
    have hn : ¬ R x (Nat.find (hcover x)) := fun hr => (hRP x).mpr ⟨_, hr⟩ hx
    simp [negativeSeparator, raceTotal, hn]
  · apply Set.disjoint_left.mpr
    intro x hc hq
    have hn : ¬ S x (Nat.find (hcover x)) := fun hs => (hSQ x).mpr ⟨_, hs⟩ hq
    have hr := (Nat.find_spec (hcover x)).resolve_right hn
    simp [negativeSeparator, raceTotal, hr] at hc

theorem disjoint_negative_cover (P Q : Set ℕ) (R S : ℕ → ℕ → Prop)
    (hRP : ∀ x, x ∉ P ↔ ∃ t, R x t)
    (hSQ : ∀ x, x ∉ Q ↔ ∃ t, S x t) (hPQ : Disjoint P Q) :
    ∀ x, ∃ t, R x t ∨ S x t := by
  classical
  intro x
  by_cases hp : x ∈ P
  · have hq : x ∉ Q := fun hq => Set.disjoint_left.mp hPQ hp hq
    obtain ⟨t, ht⟩ := (hSQ x).mp hq
    exact ⟨t, Or.inr ht⟩
  · obtain ⟨t, ht⟩ := (hRP x).mp hp
    exact ⟨t, Or.inl ht⟩

theorem coEnumerable_separation (P Q : Set ℕ)
    (hP : CoEnumerable P) (hQ : CoEnumerable Q) (hPQ : Disjoint P Q) :
    ComputablySeparable P Q := by
  obtain ⟨R, hR, hRP⟩ := (enumerable_iff_primitive_certificate (fun x => x ∉ P)).mp hP
  obtain ⟨S, hS, hSQ⟩ := (enumerable_iff_primitive_certificate (fun x => x ∉ Q)).mp hQ
  let hcover := disjoint_negative_cover P Q R S hRP hSQ hPQ
  exact ⟨negativeSeparator R S hcover, negativeSeparator_spec P Q R S hR hS hRP hSQ hcover⟩

end Lemmatheca.ComputabilityTheory.ComputableSeparation
