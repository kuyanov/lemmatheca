import Lemmatheca.ExistentiallyClosedExtensions.Basics
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language Cardinal CategoryTheory
open Lemmatheca.ModelTheory
open CategoryTheory.SmallObject
universe u v w z
variable {L : Language.{u, v}}

instance codedModelCategory (T : L.Theory) (κ : Cardinal.{max u v w}) :
    Category (CodedModel T κ) where
  Hom C D := C.asModel ↪[L] D.asModel
  id C := Embedding.refl L C.asModel
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def codedHom {T : L.Theory} {κ : Cardinal.{max u v w}}
    {C D : CodedModel T κ} (f : C ⟶ D) : C.asModel ↪[L] D.asModel := f

namespace PassPrefix
variable {J : Type z} [LinearOrder J] [SuccOrder J] [OrderBot J]
variable (T : L.Theory) (κ : Cardinal.{max u v w})
    (A : Theory.ModelType.{u, v, max u v w} T) (schedule : J → Request L A)
    (B₀ : CodedModel T κ) (e₀ : A ≃[L] B₀.asModel)

structure Data (j : J) where
  F : Set.Iic j ⥤ CodedModel T κ
  starts : F.obj ⟨⊥, bot_le⟩ = B₀
  handled : ∀ (i : J) (hi : i < j),
    let before : Set.Iic j := ⟨i, hi.le⟩
    let after : Set.Iic j := ⟨Order.succ i, Order.succ_le_of_lt hi⟩
    let initial : A ≃[L] (F.obj ⟨⊥, bot_le⟩).asModel := starts.symm ▸ e₀
    let baseBefore := (F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic j) ≤ before from bot_le))).comp initial.toEmbedding
    let baseAfter := (F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic j) ≤ after from bot_le))).comp initial.toEmbedding
    (schedule i).Possible T baseBefore → (schedule i).Realized baseAfter
  limit_cover : ∀ (i : Set.Iic j), Order.IsSuccLimit i.val →
    ∀ b : (F.obj i).asModel,
      ∃ (k : Set.Iic j) (hk : k < i) (a : (F.obj k).asModel),
        codedHom (F.map (homOfLE hk.le)) a = b

variable {T κ A schedule B₀ e₀}

def Data.initial {j : J} (p : Data T κ A schedule B₀ e₀ j) :
    A ≃[L] (p.F.obj ⟨⊥, bot_le⟩).asModel := p.starts.symm ▸ e₀

@[ext] theorem Data.ext {j : J} (p q : Data T κ A schedule B₀ e₀ j)
    (h : p.F = q.F) : p = q := by
  cases p
  cases q
  cases h
  rfl

def restrict {i j : J} (p : Data T κ A schedule B₀ e₀ j) (h : i ≤ j) :
    Data T κ A schedule B₀ e₀ i where
  F := SmallObject.restrictionLE p.F h
  starts := p.starts
  handled k hk := p.handled k (lt_of_lt_of_le hk h)
  limit_cover β hβ b := by
    obtain ⟨α, hα, a, ha⟩ := p.limit_cover ⟨β.val, β.property.trans h⟩ hβ b
    exact ⟨⟨α.val, (show α.val ≤ β.val from hα.le).trans β.property⟩, hα, a, ha⟩

@[simp] theorem restrict_refl {j : J} (p : Data T κ A schedule B₀ e₀ j) :
    restrict p le_rfl = p := rfl

@[simp] theorem restrict_restrict {i j k : J} (p : Data T κ A schedule B₀ e₀ k)
    (hij : i ≤ j) (hjk : j ≤ k) :
    restrict (restrict p hjk) hij = restrict p (hij.trans hjk) := rfl

def presheaf : Jᵒᵖ ⥤ Type (max u v w z) where
  obj j := Data T κ A schedule B₀ e₀ j.unop
  map h := TypeCat.ofHom (fun p => restrict p (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

end PassPrefix
end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
