import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-! Gluing compatible closed prefixes without changing their objects or maps. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.OrdinalDiagrams
open CategoryTheory CategoryTheory.SmallObject
universe u v w
variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J] {β : J}

/-- Restriction of a diagram below a cut to a closed prefix of that cut. -/
def restrictionBelow (G : Set.Iio β ⥤ C) (i : Set.Iio β) : Set.Iic i.val ⥤ C :=
  (show Set.Iic i.val →o Set.Iio β from
    ⟨fun a => ⟨a.val, lt_of_le_of_lt a.property i.property⟩, fun _ _ h => h⟩).monotone.functor ⋙ G

set_option backward.isDefEq.respectTransparency false in
/-- Compatible finite or transfinite closed prefixes form one diagram, with literal restrictions. -/
theorem glue_closed_diagrams
    (F : ∀ i : Set.Iio β, Set.Iic i.val ⥤ C)
    (h : ∀ (i k : Set.Iio β) (hik : i ≤ k), restrictionLE (F k) hik = F i) :
    ∃ G : Set.Iio β ⥤ C, ∀ i, restrictionBelow G i = F i := by
  let V (i : Set.Iio β) : C := (F i).obj ⟨i.val, le_rfl⟩
  have he (i k : Set.Iio β) (hik : i ≤ k) :
      V i = (F k).obj ⟨i.val, hik⟩ :=
    (Functor.congr_obj (h i k hik) ⟨i.val, le_rfl⟩).symm
  let G : Set.Iio β ⥤ C :=
    { obj := V
      map := fun {i k} f => eqToHom (he i k (leOfHom f)) ≫
        (F k).map (homOfLE (leOfHom f))
      map_id := by
        intro i
        simp
      map_comp := by
        intro i j k f g
        have hjk := h j k (leOfHom g)
        have hm := Functor.congr_hom hjk.symm
          (homOfLE (leOfHom f) : (⟨i.val, leOfHom f⟩ : Set.Iic j.val) ⟶ ⟨j.val, le_rfl⟩)
        dsimp [restrictionLE] at hm
        change (F j).map (homOfLE (leOfHom f)) = eqToHom _ ≫
          (F k).map (homOfLE (show i.val ≤ j.val from leOfHom f)) ≫ eqToHom _ at hm
        simp only [Category.assoc]
        rw [hm]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← (F k).map_comp]
        simp }
  refine ⟨G, fun k => ?_⟩
  refine CategoryTheory.Functor.ext (fun i : Set.Iic k.val => he ⟨i.val, lt_of_le_of_lt i.property k.property⟩ k i.property) ?_
  intro i j f
  dsimp only [restrictionBelow, Functor.comp_map, G]
  have hm := Functor.congr_hom (h ⟨j.val, lt_of_le_of_lt j.property k.property⟩ k j.property).symm
    (homOfLE (leOfHom f) : (⟨i.val, leOfHom f⟩ : Set.Iic j.val) ⟶ ⟨j.val, le_rfl⟩)
  dsimp [restrictionLE] at hm
  change (F ⟨j.val, lt_of_le_of_lt j.property k.property⟩).map (homOfLE (leOfHom f)) = eqToHom _ ≫
    (F k).map (homOfLE (show i.val ≤ j.val from leOfHom f)) ≫ eqToHom _ at hm
  change eqToHom _ ≫
    (F ⟨j.val, lt_of_le_of_lt j.property k.property⟩).map (homOfLE (leOfHom f)) = _
  rw [hm]
  simp only [eqToHom_trans_assoc]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- Adjoining a cocone point keeps every earlier closed prefix literally unchanged. -/
theorem restrictionLE_ofCocone {K : Type w} [LinearOrder K] {b : K}
    {G : Set.Iio b ⥤ C} (c : CategoryTheory.Limits.Cocone G) (i : Set.Iio b) :
    restrictionLE (SuccStruct.ofCocone c) i.property.le = restrictionBelow G i := by
  refine CategoryTheory.Functor.ext (fun a : Set.Iic i.val =>
    SuccStruct.ofCocone_obj_eq c a.val (lt_of_le_of_lt a.property i.property)) ?_
  intro a b f
  change (SuccStruct.ofCocone c).map (homOfLE (leOfHom f)) = _
  rw [SuccStruct.ofCocone_map c a.val b.val (leOfHom f) (lt_of_le_of_lt b.property i.property)]
  rfl

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.OrdinalDiagrams
