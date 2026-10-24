import Lemmatheca.Absoluteness.Absoluteness
import Lemmatheca.CumulativeHierarchy.CumulativeHierarchy

namespace Lemmatheca.Entry.Absoluteness
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.MembershipModels
universe u
noncomputable section

def zero : ZFSet.{u} := ∅
def one : ZFSet.{u} := {zero}
def two : ZFSet.{u} := {zero,one}
def three : ZFSet.{u} := {zero,one,two}
def four : ZFSet.{u} := {zero,one,two,three}

theorem finite_domains :
    one.{u} = ZFSet.vonNeumann 1 ∧ two.{u} = ZFSet.vonNeumann 2 ∧
    one.{u}.IsTransitive ∧ two.{u}.IsTransitive ∧ four.{u}.IsTransitive ∧
    one.{u} ⊆ two.{u} := by
  have h1 : one.{u} = ZFSet.vonNeumann 1 := by
    simpa only [one,zero] using
      (Lemmatheca.SetTheory.CumulativeHierarchy.finite_stages.{u}).2.1.symm
  have h2 : two.{u} = ZFSet.vonNeumann 2 := by
    simpa only [two,one,zero] using
      (Lemmatheca.SetTheory.CumulativeHierarchy.finite_stages.{u}).2.2.1.symm
  refine ⟨h1,h2,h1.symm ▸ ZFSet.isTransitive_vonNeumann 1,
    h2.symm ▸ ZFSet.isTransitive_vonNeumann 2,?_,?_⟩
  · simp [ZFSet.IsTransitive,four,three,two,one,zero,ZFSet.subset_def]
  · intro z hz
    exact ZFSet.mem_pair.mpr (Or.inl (ZFSet.mem_singleton.mp hz))

def membershipExistence : SigmaOne 0 := .ex (.ex (.matrix (.mem 0 1)))

private theorem membershipExistence_realize (D : ZFSet.{u}) :
    setSatisfies D membershipExistence.toShared Fin.elim0 ↔
      ∃ x y : D, x.val ∈ y.val := by
  let := actualMembershipStructure D
  change (memScoped (0 : Fin 2) 1).ex.ex.Realize Empty.elim Fin.elim0 ↔ _
  simp only [BoundedFormula.realize_ex]
  rfl

theorem finite_direction_counterexample :
    ¬setSatisfies one.{u} membershipExistence.toShared Fin.elim0 ∧
    setSatisfies two.{u} membershipExistence.toShared Fin.elim0 ∧
    setSatisfies one.{u} membershipExistence.neg.toShared Fin.elim0 ∧
    ¬setSatisfies two.{u} membershipExistence.neg.toShared Fin.elim0 := by
  have h1 : ¬setSatisfies one.{u} membershipExistence.toShared Fin.elim0 := by
    rw [membershipExistence_realize]
    rintro ⟨a,b,hab⟩
    have hb : b.val = zero := ZFSet.mem_singleton.mp b.property
    rw [hb] at hab
    exact ZFSet.notMem_empty _ hab
  have h2 : setSatisfies two.{u} membershipExistence.toShared Fin.elim0 := by
    apply (membershipExistence_realize _).mpr
    exact ⟨⟨zero,by simp [two]⟩,⟨one,by simp [two]⟩,by simp [one]⟩
  refine ⟨h1,h2,?_,?_⟩
  · exact (sigma_neg_realize _ membershipExistence Fin.elim0).mpr h1
  · intro h
    exact (sigma_neg_realize _ membershipExistence Fin.elim0).mp h h2

theorem specified_membership_witness :
    universeSatisfies (DeltaZero.mem (0 : Fin 2) 1).toShared ![zero.{u},one.{u}] := by
  change zero.{u} ∈ one.{u}
  simp [one]

theorem pair_existence_counterexample :
    zero.{u} ∈ two.{u} ∧ one.{u} ∈ two.{u} ∧
    {zero.{u},one.{u}} = two.{u} ∧ two.{u} ∉ two.{u} ∧
    ¬∃ a : Fin 3 → two.{u}, (a 1).val = zero.{u} ∧ (a 2).val = one.{u} ∧
      setSatisfies two.{u} (pairTest (0 : Fin 3) 1 2).toShared a := by
  refine ⟨by simp [two],by simp [two],rfl,ZFSet.mem_irrefl _,?_⟩
  rintro ⟨a,h1,h2,ha⟩
  have hp := (pairTest_correct (0 : Fin 3) 1 2 _).mp
    ((bounded_to_universe two finite_domains.2.2.2.1 _ a).mp ha)
  rw [h1,h2] at hp
  have hm := (a 0).property
  rw [hp] at hm
  exact ZFSet.mem_irrefl _ hm

theorem internal_subset_candidates (z : ZFSet.{u}) (hz : z ∈ four.{u}) :
    z ⊆ two.{u} ↔ z = zero.{u} ∨ z = one.{u} ∨ z = two.{u} := by
  constructor
  · intro hs
    simp only [four,ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · have hm : two.{u} ∈ three.{u} := by simp [three]
      exact (ZFSet.mem_irrefl _ (hs hm)).elim
  · rintro (rfl | rfl | rfl)
    · exact ZFSet.empty_subset _
    · exact finite_domains.2.2.2.2.2
    · exact fun _ h => h

theorem power_parameters :
    three.{u} ∈ four.{u} ∧ two.{u} ∈ four.{u} ∧
    three.{u} ∈ ZFSet.vonNeumann 4 ∧ two.{u} ∈ ZFSet.vonNeumann 4 ∧
    ({one.{u}} : ZFSet.{u}) ∈ ZFSet.vonNeumann 4 := by
  refine ⟨by simp [four],by simp [four],?_,?_,?_⟩ <;>
    norm_num [ZFSet.mem_vonNeumann,three,two,one,zero,
      ZFSet.rank_insert,ZFSet.rank_singleton]

private theorem powerFormula_set (D : ZFSet.{u}) (hD : D.IsTransitive)
    {n} (p x : Fin n) (a : Fin n → D) :
    setSatisfies D (powerSetFormula p x) a ↔
      ∀ z : D, z.val ∈ (a p).val ↔ z.val ⊆ (a x).val := by
  let := actualMembershipStructure D
  change ((memScoped (Fin.last n) p.castSucc).iff
    (subsetTest (Fin.last n) x.castSucc).toShared).all.Realize Empty.elim a ↔ _
  rw [BoundedFormula.realize_all]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_iff]
  have hm : (memScoped (Fin.last n) p.castSucc).Realize Empty.elim (Fin.snoc a z) ↔
      z.val ∈ (a p).val := by
    change (Fin.snoc (α := fun _ : Fin (n+1) => D) a z (Fin.last n)).val ∈
      (Fin.snoc (α := fun _ : Fin (n+1) => D) a z p.castSucc).val ↔ _
    simp only [Fin.snoc_last,Fin.snoc_castSucc]
  rw [hm]
  change (z.val ∈ (a p).val ↔ setSatisfies D
    (subsetTest (Fin.last n) x.castSucc).toShared (Fin.snoc a z)) ↔ _
  rw [bounded_to_universe D hD,subsetTest_correct]
  simp only [Fin.snoc_last,Fin.snoc_castSucc]
private theorem powerFormula_universe {n} (p x : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (powerSetFormula p x) a ↔
      ∀ z : ZFSet.{u}, z ∈ a p ↔ z ⊆ a x := by
  let := universeMembershipStructure.{u}
  change ((memScoped (Fin.last n) p.castSucc).iff
    (subsetTest (Fin.last n) x.castSucc).toShared).all.Realize Empty.elim a ↔ _
  rw [BoundedFormula.realize_all]
  apply forall_congr'
  intro z
  rw [BoundedFormula.realize_iff]
  have hm : (memScoped (Fin.last n) p.castSucc).Realize Empty.elim (Fin.snoc a z) ↔
      z ∈ a p := by
    change Fin.snoc (α := fun _ : Fin (n+1) => ZFSet.{u}) a z (Fin.last n) ∈
      Fin.snoc (α := fun _ : Fin (n+1) => ZFSet.{u}) a z p.castSucc ↔ _
    simp only [Fin.snoc_last,Fin.snoc_castSucc]
  rw [hm]
  change (z ∈ a p ↔ universeSatisfies
    (subsetTest (Fin.last n) x.castSucc).toShared (Fin.snoc a z)) ↔ _
  rw [subsetTest_correct]
  simp only [Fin.snoc_last,Fin.snoc_castSucc]

theorem power_internal_true (a : Fin 2 → four.{u})
    (hp : (a 0).val = three.{u}) (hx : (a 1).val = two.{u}) :
    setSatisfies four.{u} (powerSetFormula (0 : Fin 2) 1) a := by
  apply (powerFormula_set four finite_domains.2.2.2.2.1 _ _ a).mpr
  intro z
  rw [hp,hx,internal_subset_candidates z.val z.property]
  simp only [three,ZFSet.mem_insert_iff,ZFSet.mem_singleton]

theorem power_external_false :
    ({one.{u}} : ZFSet.{u}) ⊆ two.{u} ∧ ({one.{u}} : ZFSet.{u}) ∉ three.{u} ∧
    ¬universeSatisfies (powerSetFormula (0 : Fin 2) 1) ![three.{u},two.{u}] := by
  have h0 : zero.{u} ≠ one.{u} := by
    intro h
    have hm : zero.{u} ∈ one.{u} := by simp [one]
    rw [←h] at hm
    exact ZFSet.mem_irrefl _ hm
  have hn0 : ({one.{u}} : ZFSet.{u}) ≠ zero.{u} := by
    intro h
    have hm : one.{u} ∈ ({one.{u}} : ZFSet.{u}) := by simp
    rw [h] at hm
    exact ZFSet.notMem_empty _ hm
  have hn1 : ({one.{u}} : ZFSet.{u}) ≠ one.{u} := by
    intro h
    have hm : one.{u} ∈ ({one.{u}} : ZFSet.{u}) := by simp
    rw [h] at hm
    exact ZFSet.mem_irrefl _ hm
  have hn2 : ({one.{u}} : ZFSet.{u}) ≠ two.{u} := by
    intro h
    have hm : zero.{u} ∈ two.{u} := by simp [two]
    rw [←h] at hm
    exact h0 (ZFSet.mem_singleton.mp hm)
  have hs : ({one.{u}} : ZFSet.{u}) ⊆ two.{u} := by
    intro z hz
    exact ZFSet.mem_singleton.mp hz ▸ (by simp [two])
  have hn : ({one.{u}} : ZFSet.{u}) ∉ three.{u} := by
    simpa only [three,ZFSet.mem_insert_iff,ZFSet.mem_singleton,not_or] using ⟨hn0,hn1,hn2⟩
  refine ⟨hs,hn,?_⟩
  intro h
  exact hn (((powerFormula_universe (0 : Fin 2) 1 _).mp h {one}).mpr hs)

theorem power_larger_domain_false (a : Fin 2 → ZFSet.vonNeumann (4 : Ordinal.{u}))
    (hp : (a 0).val = three.{u}) (hx : (a 1).val = two.{u}) :
    ¬setSatisfies (ZFSet.vonNeumann 4) (powerSetFormula (0 : Fin 2) 1) a := by
  intro h
  let z : ZFSet.vonNeumann (4 : Ordinal.{u}) := ⟨{one.{u}},power_parameters.2.2.2.2⟩
  have hz := (powerFormula_set _ (ZFSet.isTransitive_vonNeumann 4) _ _ a).mp h z
  rw [hp,hx] at hz
  exact power_external_false.2.1 (hz.mpr power_external_false.1)

end
end Lemmatheca.Entry.Absoluteness
