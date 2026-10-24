import Lemmatheca.RankReflection.RankModels

namespace Lemmatheca.Entry.RankReflection
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.RankReflection
universe u
noncomputable section

def singletonHierarchy : Hierarchy.{u} where
  level := fun _ => {∅}
  transitive := by
    intro a y hy z hz
    have hy0 : y = ∅ := ZFSet.mem_singleton.mp hy
    rw [hy0] at hz
    exact (ZFSet.notMem_empty z hz).elim
  monotone := fun _ _ hx => hx
  continuous := by
    intro l hl x
    exact ⟨fun h => ⟨0,hl.pos,h⟩,fun ⟨_,_,h⟩ => h⟩

theorem singletonHierarchy_spec :
    NonemptyUnion singletonHierarchy.{u} ∧
    (∀ x : ZFSet.{u}, InUnion singletonHierarchy x ↔ x = ∅) ∧
    (∀ (F : Finset NativePackedFormula) (a : Ordinal.{u}),
      ReflectsNative singletonHierarchy F a) ∧
    ¬unionSatisfies singletonHierarchy.{u} infinityAxiom Fin.elim0 := by
  have hIn (x : ZFSet.{u}) : InUnion singletonHierarchy x ↔ x = ∅ := by
    change (∃ a : Ordinal.{u}, x ∈ ({∅} : ZFSet.{u})) ↔ x = ∅
    simp only [ZFSet.mem_singleton, exists_const]
  refine ⟨⟨0,∅,ZFSet.mem_singleton.mpr rfl⟩,hIn,?_,?_⟩
  · intro F a
    refine ⟨⟨∅,ZFSet.mem_singleton.mpr rfl⟩,?_⟩
    intro p hp xs
    let := actualMembershipStructure (singletonHierarchy.level a)
    let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure
      (UnionDomain singletonHierarchy.{u}) (fun x y => x.val ∈ y.val)
    let e : singletonHierarchy.level a ≃[membershipLanguage] UnionDomain singletonHierarchy.{u} :=
      { toEquiv :=
          { toFun := intoUnion singletonHierarchy a
            invFun := fun x => ⟨x.val,ZFSet.mem_singleton.mpr ((hIn x.val).mp x.property)⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext rfl }
        map_fun' := by intro n f; exact Empty.elim f
        map_rel' := by intro n r ys; cases r; rfl }
    have he := (StrongHomClass.realize_boundedFormula e p.2
      (v := Empty.elim) (xs := xs)).symm
    have hEmpty : e ∘ (Empty.elim : Empty → singletonHierarchy.level a) =
        (Empty.elim : Empty → UnionDomain singletonHierarchy.{u}) := Subsingleton.elim _ _
    rw [hEmpty] at he
    exact he
  · intro h
    let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure
      (UnionDomain singletonHierarchy.{u}) (fun x y => x.val ∈ y.val)
    change (inductiveScoped 0).toShared.ex.Realize Empty.elim Fin.elim0 at h
    obtain ⟨a,ha⟩ := BoundedFormula.realize_ex.mp h
    have hz := (BoundedFormula.realize_inf.mp ha).1
    obtain ⟨z,hz⟩ := BoundedFormula.realize_ex.mp hz
    have hm := (BoundedFormula.realize_inf.mp hz).2
    change z.val ∈ a.val at hm
    rw [(hIn a.val).mp a.property] at hm
    exact ZFSet.notMem_empty _ hm

theorem finite_quantifier_order_example :
    (∀ n : ℕ, ∃ k : ℕ, n ≤ k) ∧ ¬∃ k : ℕ, ∀ n : ℕ, n ≤ k := by
  refine ⟨fun n => ⟨n,le_rfl⟩,?_⟩
  rintro ⟨k,hk⟩
  exact Nat.not_succ_le_self k (hk (k+1))

end
end Lemmatheca.Entry.RankReflection
