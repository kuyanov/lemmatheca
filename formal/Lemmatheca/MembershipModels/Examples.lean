import Lemmatheca.MembershipModels.Relativization

namespace Lemmatheca.Entry.MembershipModels
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
universe u v
noncomputable section

def nontransitiveSingleton : ZFSet := {({∅} : ZFSet)}

private theorem singleton_empty_ne_empty : ({∅} : ZFSet.{u}) ≠ ∅ := by
  intro h
  have he : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [h] at he
  exact ZFSet.notMem_empty _ he

theorem nontransitiveSingleton_spec :
    (∀ a b : nontransitiveSingleton, ¬ a.val ∈ b.val) ∧
    (∃ a : nontransitiveSingleton, a.val ≠ ∅) ∧
    ¬ nontransitiveSingleton.IsTransitive := by
  refine ⟨?_, ⟨⟨{∅}, ZFSet.mem_singleton.mpr rfl⟩, singleton_empty_ne_empty⟩, ?_⟩
  · intro a b
    have ha : a.val = {∅} := ZFSet.mem_singleton.mp a.property
    have hb : b.val = {∅} := ZFSet.mem_singleton.mp b.property
    rw [ha, hb, ZFSet.mem_singleton]
    exact singleton_empty_ne_empty
  · intro h
    have he : (∅ : ZFSet) ∈ ({∅} : ZFSet) := ZFSet.mem_singleton.mpr rfl
    have hd : ({∅} : ZFSet) ∈ nontransitiveSingleton := ZFSet.mem_singleton.mpr rfl
    have hz := h.mem_trans he hd
    exact singleton_empty_ne_empty (ZFSet.mem_singleton.mp hz).symm

def upwardMemberSentence : membershipLanguage.Sentence :=
  (memScoped (α := Empty) (n := 2) 0 1).ex.all

private theorem memScoped_realize {M : Type u} (E : M → M → Prop)
    {α : Type v} {n : ℕ} (i j : Fin n) (a : α → M) (xs : Fin n → M) :
    let := binaryRelStructure M E
    (memScoped i j).Realize a xs ↔ E (xs i) (xs j) := by rfl
private theorem upwardMember_realize {M : Type u} (E : M → M → Prop) :
    let := binaryRelStructure M E
    M ⊨ upwardMemberSentence ↔ ∀ x : M, ∃ y : M, E x y := by
  simp [upwardMemberSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.Realize, memScoped_realize, Fin.snoc]

theorem transitive_domain_counterexample :
    let D : ZFSet := {∅}
    D.IsTransitive ∧
    (letI := actualMembershipStructure D; ¬ (D ⊨ upwardMemberSentence)) ∧
    (letI := universeMembershipStructure; ZFSet ⊨ upwardMemberSentence) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hy0 : y = ∅ := ZFSet.mem_singleton.mp hy
    rw [hy0]
    exact ZFSet.empty_subset _
  · apply (upwardMember_realize (fun x y : ({∅} : ZFSet) => x.val ∈ y.val)).not.mpr
    intro h
    obtain ⟨y,hy⟩ := h ⟨∅, ZFSet.mem_singleton.mpr rfl⟩
    have hy0 : y.val = ∅ := ZFSet.mem_singleton.mp y.property
    rw [hy0] at hy
    exact ZFSet.notMem_empty _ hy
  · apply (upwardMember_realize (fun x y : ZFSet => x ∈ y)).mpr
    exact fun x => ⟨{x}, ZFSet.mem_singleton.mpr rfl⟩

end
end Lemmatheca.Entry.MembershipModels
