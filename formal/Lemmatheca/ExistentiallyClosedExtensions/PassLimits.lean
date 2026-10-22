import Lemmatheca.ExistentiallyClosedExtensions.PassPrefixes
import Lemmatheca.ExistentiallyClosedExtensions.OrdinalDiagrams
import Lemmatheca.ExistentiallyClosedExtensions.BoundedLimits

namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
open FirstOrder FirstOrder.Language Cardinal CategoryTheory CategoryTheory.Limits
open CategoryTheory.SmallObject
open Lemmatheca.ModelTheory
open InductiveTheories OrdinalDiagrams
universe u v w
variable {L : Language.{u, v}} {J : Type (max u v w)}
    [LinearOrder J] [SuccOrder J] [OrderBot J]
variable {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u, v, max u v w} T} {schedule : J → Request L A}
    {B₀ : CodedModel T κ} {e₀ : A ≃[L] B₀.asModel}

private def copyData {i : J} (p : Data T κ A schedule B₀ e₀ i)
    (F : Set.Iic i ⥤ CodedModel T κ) (h : F = p.F) :
    Data T κ A schedule B₀ e₀ i where
  F := F
  starts := by cases h; exact p.starts
  handled := by cases h; exact p.handled
  limit_cover := by cases h; exact p.limit_cover

private theorem extend_limit_data {j : J} (hj : Order.IsSuccLimit j)
    (p : ∀ i : Set.Iio j, Data T κ A schedule B₀ e₀ i.val)
    (F : Set.Iic j ⥤ CodedModel T κ)
    (hF : ∀ i : Set.Iio j, SmallObject.restrictionLE F i.property.le = (p i).F)
    (hcover : ∀ b : (F.obj ⟨j, le_rfl⟩).asModel,
      ∃ (i : Set.Iio j) (a : (F.obj ⟨i.val, i.property.le⟩).asModel),
        codedHom (F.map (homOfLE i.property.le)) a = b) :
    ∃ q : Data T κ A schedule B₀ e₀ j, ∀ i : Set.Iio j,
      restrict q i.property.le = p i := by
  have hbot : (⊥ : J) < j := bot_lt_iff_ne_bot.mpr hj.ne_bot
  let old (i : Set.Iio j) := copyData (p i)
    (SmallObject.restrictionLE F i.property.le) (hF i)
  let q : Data T κ A schedule B₀ e₀ j :=
    { F := F
      starts := (old ⟨⊥, hbot⟩).starts
      handled := by
        intro i hi
        have hs : Order.succ i < j := hj.succ_lt hi
        exact (old ⟨Order.succ i, hs⟩).handled i
          (Order.lt_succ_of_not_isMax (not_isMax_iff.mpr ⟨j, hi⟩))
      limit_cover := by
        intro β hβ b
        by_cases hbj : β.val < j
        · obtain ⟨α, hα, a, ha⟩ := (old ⟨β.val, hbj⟩).limit_cover
            ⟨β.val, le_rfl⟩ hβ b
          exact ⟨⟨α.val, α.property.trans β.property⟩, hα, a, ha⟩
        · have he : β = ⟨j, le_rfl⟩ := Subtype.ext (le_antisymm β.property (le_of_not_gt hbj))
          subst β
          obtain ⟨i, a, ha⟩ := hcover b
          exact ⟨⟨i.val, i.property.le⟩, i.property, a, ha⟩ }
  refine ⟨q, fun i => ?_⟩
  apply Data.ext
  exact hF i

theorem limit_extension (hT : IsInductive.{u, v, w} T) (hω : ℵ₀ ≤ κ)
    (hJ : #J ≤ κ) {j : J} (hj : Order.IsSuccLimit j)
    (p : ∀ i : Set.Iio j, Data T κ A schedule B₀ e₀ i.val)
    (hp : ∀ (i k : Set.Iio j) (hik : i ≤ k), restrict (p k) hik = p i) :
    ∃ q : Data T κ A schedule B₀ e₀ j, ∀ i : Set.Iio j,
      restrict q i.property.le = p i := by
  classical
  obtain ⟨G, hG⟩ := glue_closed_diagrams (fun i => (p i).F)
    (fun i k hik => congrArg Data.F (hp i k hik))
  let V (i : Set.Iio j) := (G.obj i).asModel
  let f (i k : Set.Iio j) (h : i ≤ k) : V i ↪[L] V k := codedHom (G.map (homOfLE h))
  let : Nonempty (Set.Iio j) := ⟨⟨⊥, bot_lt_iff_ne_bot.mpr hj.ne_bot⟩⟩
  let : DirectedSystem (fun i => V i) (fun i k h => f i k h) :=
    { map_self := by
        intro i a
        have h := G.map_id i
        exact congrArg (fun g => codedHom g a) h
      map_map := by
        intro k m i him hmk a
        have h := G.map_comp (homOfLE him) (homOfLE hmk)
        exact (congrArg (fun g => codedHom g a) h).symm }
  obtain ⟨C, e, he, hcov⟩ := bounded_coded_directLimit T hT κ hω
    ((Cardinal.mk_subtype_le _).trans hJ) V
    (fun i => codedModel_card_le T κ (G.obj i)) f
  let c : Cocone G :=
    { pt := C
      ι :=
        { app := fun i => e.toEmbedding.comp (DirectLimit.of L (Set.Iio j) (fun i => V i) f i)
          naturality := by
            intro i k h
            change (e.toEmbedding.comp (DirectLimit.of L (Set.Iio j) (fun i => V i) f k)).comp
              (codedHom (G.map h)) = e.toEmbedding.comp
                (DirectLimit.of L (Set.Iio j) (fun i => V i) f i)
            apply DFunLike.ext
            intro a
            exact he i k (leOfHom h) a } }
  let F := SuccStruct.ofCocone c
  apply extend_limit_data hj p F
    (fun i => (restrictionLE_ofCocone c i).trans (hG i))
  intro b
  let itop := SuccStruct.ofCoconeObjIsoPt c
  obtain ⟨i, a, ha⟩ := hcov (codedHom itop.hom b)
  refine ⟨i, codedHom (SuccStruct.ofCoconeObjIso c i.val i.property).inv a, ?_⟩
  change codedHom ((SuccStruct.ofCocone c).map (homOfLE i.property.le))
    (codedHom (SuccStruct.ofCoconeObjIso c i.val i.property).inv a) = b
  rw [SuccStruct.ofCocone_map_to_top]
  let ii := SuccStruct.ofCoconeObjIso c i.val i.property
  have hi : codedHom ii.hom (codedHom ii.inv a) = a :=
    congrArg (fun g => codedHom g a) ii.inv_hom_id
  change codedHom itop.inv (e (DirectLimit.of L (Set.Iio j) (fun i => V i) f i
    (codedHom ii.hom (codedHom ii.inv a)))) = b
  rw [hi]
  rw [ha]
  exact congrArg (fun g => codedHom g b) itop.hom_inv_id

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
