import Lemmatheca.DekkerDeficiencyAndHypersimpleSets.Basic
import Lemmatheca.SimpleSets.Construction

/-! The original Post threshold construction has a computably bounded complement. -/
namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open SimpleSets HyperimmuneDegrees EffectiveEnumerations

noncomputable section

theorem post_complement_principal_bound (n : ℕ) :
    increasingList postSetᶜ post_complement_infinite n ≤ 2 * n := by
  classical
  let f := increasingList postSetᶜ post_complement_infinite
  obtain ⟨hmono, hrange⟩ := (increasing_list_correct postSetᶜ post_complement_infinite).1
  by_contra hbound
  have hlt : 2 * n < f n := Nat.lt_of_not_ge hbound
  let E := postSetᶜ ∩ Set.Iic (2 * n)
  have hpreimage (x : E) : ∃ i : ℕ, i < n ∧ f i = x.val := by
    have hmem : x.val ∈ Set.range f := by
      rw [hrange]
      exact x.property.1
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, ?_, hi⟩
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hm : f n ≤ f i := hmono.monotone hni
    have hx : x.val ≤ 2 * n := x.property.2
    omega
  let g : E → Fin n := fun x => ⟨(hpreimage x).choose, (hpreimage x).choose_spec.1⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.val = f (g x).val := (hpreimage x).choose_spec.2.symm
      _ = f (g y).val := congrArg f (congrArg Fin.val hxy)
      _ = y.val := (hpreimage y).choose_spec.2
  have hcard : E.ncard ≤ n := by
    simpa only [Nat.card_coe_set_eq, Nat.card_fin] using
      Nat.card_le_card_of_injective g hginj
  have hmany : n + 1 ≤ E.ncard := (omission_bound n).2
  omega

theorem post_simple_not_hypersimple : Simple postSet ∧ ¬ Hypersimple postSet := by
  refine ⟨post_simple, ?_⟩
  rintro ⟨_, hInf, hHyper⟩
  apply hHyper
  refine ⟨fun n => 2 * n,
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp,
    Filter.Eventually.of_forall ?_⟩
  intro n
  exact post_complement_principal_bound n

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
