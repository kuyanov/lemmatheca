import Lemmatheca.CardinalSaturationAndHomogeneity.PartialMaps

namespace Lemmatheca.ModelTheory.PartialElementaryMaps
open FirstOrder FirstOrder.Language
universe u v w w'
noncomputable section
local instance cardinalAdjoinPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

def PointMatch (p : Map L M N) (a : M) (b : N) : Prop :=
  ∀ φ : L.Formula (p.dom ⊕ Fin 1),
    φ.Realize (Sum.elim (Subtype.val : p.dom → M) (fun _ => a)) ↔
      φ.Realize (Sum.elim p.toFun (fun _ => b))

def adjoinFun (p : Map L M N) (a : M) (b : N) : ↥(insert a p.dom : Set M) → N :=
  fun x => if h : x.val = a then b
    else p.toFun ⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left h⟩

/-- The graph really is the old function together with the supplied new pair. -/
def adjoinMap (p : Map L M N) (a : M) (b : N)
    (ha : a ∉ p.dom) (hb : b ∉ p.range) (hmatch : PointMatch p a b) : Map L M N where
  dom := insert a p.dom
  toFun := adjoinFun p a b
  injective := by
    intro x y hxy
    by_cases hx : x.val = a
    · by_cases hy : y.val = a
      · exact Subtype.ext (hx.trans hy.symm)
      · have hy' : y.val ∈ p.dom := (Set.mem_insert_iff.mp y.property).resolve_left hy
        have hya : y.val ≠ a := fun he => ha (he ▸ hy')
        have he : b = p.toFun ⟨y.val,hy'⟩ := by simpa only [adjoinFun,dite_eq_left hx,dite_eq_right hya] using hxy
        exact False.elim (hb ⟨⟨y.val,hy'⟩,he.symm⟩)
    · by_cases hy : y.val = a
      · have hx' : x.val ∈ p.dom := (Set.mem_insert_iff.mp x.property).resolve_left hx
        have he : p.toFun ⟨x.val,hx'⟩ = b := by simpa only [adjoinFun,dite_eq_right hx,dite_eq_left hy] using hxy
        exact False.elim (hb ⟨⟨x.val,hx'⟩,he⟩)
      · have he : p.toFun ⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left hx⟩ =
            p.toFun ⟨y.val,(Set.mem_insert_iff.mp y.property).resolve_left hy⟩ := by
          simpa only [adjoinFun,dite_eq_right hx,dite_eq_right hy] using hxy
        exact Subtype.ext (congrArg (fun t : p.dom => t.val) (p.injective he))
  elementary := by
    intro n φ c
    let index (i : Fin n) : p.dom ⊕ Fin 1 :=
      if h : (c i).val = a then .inr 0
      else .inl ⟨(c i).val,(Set.mem_insert_iff.mp (c i).property).resolve_left h⟩
    have hsource : Sum.elim (Subtype.val : p.dom → M) (fun _ : Fin 1 => a) ∘ index =
        Subtype.val ∘ c := by
      funext i
      by_cases h : (c i).val = a <;> simp [index,h]
    have htarget : Sum.elim p.toFun (fun _ : Fin 1 => b) ∘ index =
        adjoinFun p a b ∘ c := by
      funext i
      by_cases h : (c i).val = a <;> simp [index,adjoinFun,h]
    have hm := hmatch (φ.relabel index)
    rw [Formula.realize_relabel,Formula.realize_relabel,hsource,htarget] at hm
    exact hm.symm

theorem adjoin_map_spec (p : Map L M N) (a : M) (b : N)
    (ha : a ∉ p.dom) (hb : b ∉ p.range) (hmatch : PointMatch p a b) :
    p ≤ adjoinMap p a b ha hb hmatch ∧
      (adjoinMap p a b ha hb hmatch).dom = insert a p.dom ∧
      (adjoinMap p a b ha hb hmatch).range = insert b p.range ∧
      (adjoinMap p a b ha hb hmatch).toFun ⟨a,Set.mem_insert a p.dom⟩ = b := by
  have hold (x : p.dom) : adjoinFun p a b ⟨x.val,Set.mem_insert_of_mem a x.property⟩ = p.toFun x := by
    have hx : x.val ≠ a := fun he => ha (he ▸ x.property)
    simp only [adjoinFun,dite_eq_right hx]
  refine ⟨?_,rfl,?_,?_⟩
  · intro xy hxy
    obtain ⟨hx,hval⟩ := hxy
    exact ⟨Set.mem_insert_of_mem a hx,(hold ⟨xy.1,hx⟩).trans hval⟩
  · ext y
    constructor
    · rintro ⟨x,hx⟩
      by_cases he : x.val = a
      · exact Or.inl (by simpa [adjoinMap,adjoinFun,he] using hx.symm)
      · exact Or.inr ⟨⟨x.val,(Set.mem_insert_iff.mp x.property).resolve_left he⟩,
          by simpa only [adjoinMap,adjoinFun,dite_eq_right he] using hx⟩
    · rintro (rfl | ⟨x,hx⟩)
      · exact ⟨⟨a,Set.mem_insert a p.dom⟩,by simp [adjoinMap,adjoinFun]⟩
      · exact ⟨⟨x.val,Set.mem_insert_of_mem a x.property⟩,(hold x).trans hx⟩
  · simp [adjoinMap,adjoinFun]

end
end Lemmatheca.ModelTheory.PartialElementaryMaps
