import Lemmatheca.ExistentiallyClosedExtensions.PassPrefixExtension

/-! The actual small witness choice at a successor stage of the fixed-base pass. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language Cardinal CategoryTheory
open CategoryTheory.SmallObject
universe u v w z
variable {L : Language.{u,v}}

private theorem choose_successor (T : L.Theory) (κ : Cardinal.{max u v w})
    (hω : Cardinal.aleph0 ≤ κ) (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (A : Theory.ModelType.{u,v,max u v w} T) (B : CodedModel T κ)
    (f : A ↪[L] B.asModel) (r : Request L A) :
    ∃ (C : CodedModel T κ) (g : B.asModel ↪[L] C.asModel),
      r.Possible T f → r.Realized (g.comp f) := by
  classical
  by_cases h : r.Possible T f
  · let s : Request L B.asModel := ⟨r.arity, r.formula, r.existential, f ∘ r.parameters⟩
    have hs : s.Possible T (Embedding.refl L B.asModel) := by
      obtain ⟨N, g, hg⟩ := h
      exact ⟨N, g, hg⟩
    obtain ⟨C, g, hg⟩ := small_possible_extension T κ hω hL B.asModel
      (codedModel_card_le T κ B) s hs
    exact ⟨C, g, fun _ => hg⟩
  · exact ⟨B, Embedding.refl L B.asModel, fun hr => (h hr).elim⟩

private theorem realized_cast {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u,v,max u v w} T} (r : Request L A)
    {B C : CodedModel T κ} (h : B = C) (f : A ↪[L] B.asModel) :
    r.Realized ((codedHom (eqToHom h)).comp f) ↔ r.Realized f := by
  cases h
  rfl

private theorem possible_cast {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u,v,max u v w} T} (r : Request L A)
    {B C : CodedModel T κ} (h : B = C) (f : A ↪[L] B.asModel) :
    r.Possible T ((codedHom (eqToHom h)).comp f) ↔ r.Possible T f := by
  cases h
  rfl

private theorem initial_cast {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u,v,max u v w} T} {B C B₀ : CodedModel T κ}
    (h : B = C) (s : B = B₀) (e : A ≃[L] B₀.asModel) :
    (codedHom (eqToHom h)).comp (show A ≃[L] B.asModel from s.symm ▸ e).toEmbedding =
      (show A ≃[L] C.asModel from (h.symm.trans s).symm ▸ e).toEmbedding := by
  cases h
  rfl

private theorem codedHom_comp {T : L.Theory} {κ : Cardinal.{max u v w}}
    {B C D : CodedModel T κ} (f : B ⟶ C) (g : C ⟶ D) :
    codedHom (f ≫ g) = (codedHom g).comp (codedHom f) := rfl

namespace PassPrefix
variable {J : Type z} [LinearOrder J] [SuccOrder J] [OrderBot J]
variable {T : L.Theory} {κ : Cardinal.{max u v w}}
variable {A : Theory.ModelType.{u,v,max u v w} T} {schedule : J → Request L A}
variable {B₀ : CodedModel T κ} {e₀ : A ≃[L] B₀.asModel} {j : J}

omit [OrderBot J] in
private theorem restriction_extend_succ (hj : ¬IsMax j)
    (F : Set.Iic j ⥤ CodedModel T κ) {X : CodedModel T κ}
    (τ : F.obj ⟨j, by simp⟩ ⟶ X) :
    restrictionLE (SuccStruct.extendToSucc hj F τ) (Order.le_succ j) = F := by
  exact CategoryTheory.Functor.ext_of_iso (SuccStruct.extendToSuccRestrictionLEIso hj F τ)
    (fun i => SuccStruct.extendToSucc_obj_eq hj F τ i.val i.property)
    (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem handled_new_step (p : Data T κ A schedule B₀ e₀ j)
    (hj : ¬IsMax j) (C : CodedModel T κ)
    (τ : p.F.obj ⟨j, le_rfl⟩ ⟶ C)
    (hτ : (schedule j).Possible T
        ((codedHom (p.F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic j) ≤ ⟨j,le_rfl⟩ from bot_le)))).comp p.initial.toEmbedding) →
      (schedule j).Realized (τ.comp
        ((codedHom (p.F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic j) ≤ ⟨j,le_rfl⟩ from bot_le)))).comp p.initial.toEmbedding)))
    (s : (SuccStruct.extendToSucc hj p.F τ).obj ⟨⊥, bot_le⟩ = B₀) :
    let F := SuccStruct.extendToSucc hj p.F τ
    let initial : A ≃[L] (F.obj ⟨⊥,bot_le⟩).asModel := s.symm ▸ e₀
    (schedule j).Possible T
      ((codedHom (F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic (Order.succ j)) ≤ ⟨j,Order.le_succ j⟩ from bot_le)))).comp initial.toEmbedding) →
    (schedule j).Realized
      ((codedHom (F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic (Order.succ j)) ≤ ⟨Order.succ j,le_rfl⟩ from bot_le)))).comp initial.toEmbedding) := by
  classical
  have hn : ¬ Order.succ j ≤ j := by
    simpa only [Order.succ_le_iff_isMax] using hj
  have hinit := initial_cast
    (SuccStruct.extendToSucc.obj_eq p.F C ⟨⊥, bot_le⟩) s e₀
  dsimp only [SuccStruct.extendToSucc]
  simp only [SuccStruct.extendToSucc.map, dite_eq_left (le_refl j),
    dite_eq_left (bot_le : (⊥ : J) ≤ j), dite_eq_right hn]
  dsimp only [SuccStruct.extendToSucc.objIso, SuccStruct.extendToSucc.objSuccIso,
    eqToIso.hom, eqToIso.inv]
  simp only [codedHom_comp, Embedding.comp_assoc, possible_cast, realized_cast]
  rw [hinit]
  simpa only [Data.initial, codedHom] using hτ

/-- A genuine small witness extension handles the next scheduled original-base request. -/
theorem successor_extension (hω : Cardinal.aleph0 ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ) (hj : ¬IsMax j)
    (p : Data T κ A schedule B₀ e₀ j) :
    ∃ q : Data T κ A schedule B₀ e₀ (Order.succ j), restrict q (Order.le_succ j) = p := by
  classical
  let f : A ↪[L] (p.F.obj ⟨j, le_rfl⟩).asModel :=
    (codedHom (p.F.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic j) ≤ ⟨j,le_rfl⟩ from bot_le)))).comp
      p.initial.toEmbedding
  obtain ⟨C, τ, hτ⟩ := choose_successor T κ hω hL A (p.F.obj ⟨j, le_rfl⟩) f (schedule j)
  let G := SuccStruct.extendToSucc hj p.F (show p.F.obj ⟨j,le_rfl⟩ ⟶ C from τ)
  have hF : restrictionLE G (Order.le_succ j) = p.F := restriction_extend_succ hj p.F τ
  obtain ⟨q, _hqF, hq⟩ := extend_with_handled hj p G hF (fun s =>
    handled_new_step p hj C τ hτ s)
  exact ⟨q, hq⟩

end PassPrefix
end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
