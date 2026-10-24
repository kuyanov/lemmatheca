import Lemmatheca.ForcingAndGenericFilters.Cohen

namespace Lemmatheca.Entry.ForcingAndGenericFilters
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters

abbrev FourPoint := Bool × Bool

def c : FourPoint := (false,false)
def a : FourPoint := (true,false)
def b : FourPoint := (false,true)
def one : FourPoint := (true,true)
def candidate : Set FourPoint := {one,a,b}

theorem four_point_order (x y : FourPoint) :
    x ≤ y ↔ x = c ∨ y = one ∨ x = y := by
  rcases x with ⟨x0,x1⟩
  rcases y with ⟨y0,y1⟩
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> decide

theorem compatible_not_directed :
    candidate.Nonempty ∧ IsUpperSet candidate ∧
    (∀ p ∈ candidate, ∀ q ∈ candidate, Compatible p q) ∧
    ¬a ≤ b ∧ ¬b ≤ a ∧ Compatible a b ∧
    (∀ r, r ≤ a → r ≤ b → r = c) ∧ c ∉ candidate ∧
    ¬IsPFilter candidate := by
  have hm (x : FourPoint) : x ∈ candidate ↔ x = one ∨ x = a ∨ x = b := Iff.rfl
  have ha : a ∈ candidate := by simp [candidate]
  have hb : b ∈ candidate := by simp [candidate]
  have hc : c ∉ candidate := by simp only [hm]; decide
  have hbelow : ∀ r : FourPoint, r ≤ a → r ≤ b → r = c := by decide
  refine ⟨?_,?_,?_,?_,?_,?_,hbelow,hc,?_⟩
  · exact ⟨one,by simp [candidate]⟩
  · unfold IsUpperSet
    simp only [hm]
    decide
  · simp only [hm,Compatible]
    decide
  · decide
  · decide
  · exact ⟨c,by decide,by decide⟩
  · intro hF
    obtain ⟨r,hr,hra,hrb⟩ := hF.Directed a (by exact ha) b (by exact hb)
    have heq := hbelow r hra hrb
    subst r
    exact hc hr

end Lemmatheca.Entry.ForcingAndGenericFilters
