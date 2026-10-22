import Lemmatheca.ExistentiallyClosedExtensions.PassPrefixes

/-! Old clauses of a request prefix survive a specified successor extension. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
open FirstOrder FirstOrder.Language Cardinal CategoryTheory CategoryTheory.SmallObject
universe u v w z
variable {L : Language.{u, v}} {J : Type z} [LinearOrder J] [SuccOrder J] [OrderBot J]
variable {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u, v, max u v w} T} {schedule : J → Request L A}
    {B₀ : CodedModel T κ} {e₀ : A ≃[L] B₀.asModel}

/-- The single new clause uses the original model map induced by this exact extended diagram. -/
def FinalHandled {j : J} (G : Set.Iic (Order.succ j) ⥤ CodedModel T κ)
    (s : G.obj ⟨⊥, bot_le⟩ = B₀) : Prop :=
  let initial : A ≃[L] (G.obj ⟨⊥, bot_le⟩).asModel := s.symm ▸ e₀
  let before : Set.Iic (Order.succ j) := ⟨j, Order.le_succ j⟩
  let after : Set.Iic (Order.succ j) := ⟨Order.succ j, le_rfl⟩
  let baseBefore := (G.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic (Order.succ j)) ≤ before from bot_le))).comp initial.toEmbedding
  let baseAfter := (G.map (homOfLE (show (⟨⊥, bot_le⟩ : Set.Iic (Order.succ j)) ≤ after from bot_le))).comp initial.toEmbedding
  (schedule j).Possible T baseBefore → (schedule j).Realized baseAfter

/-- Only the last handled clause is new; all previous clauses are transported literally. -/
theorem extend_with_handled {j : J} (hj : ¬ IsMax j)
    (p : Data T κ A schedule B₀ e₀ j)
    (G : Set.Iic (Order.succ j) ⥤ CodedModel T κ)
    (hF : restrictionLE G (Order.le_succ j) = p.F)
    (hnew : ∀ s, FinalHandled (schedule := schedule) (e₀ := e₀) G s) :
    ∃ q : Data T κ A schedule B₀ e₀ (Order.succ j),
      q.F = G ∧ restrict q (Order.le_succ j) = p := by
  rcases p with ⟨F,hs,hh,hl⟩
  dsimp only at hF
  subst F
  refine ⟨{ F := G, starts := hs, handled := ?_, limit_cover := ?_ }, rfl, ?_⟩
  · intro i hi
    obtain hi | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · exact hh i hi
    · exact hnew hs
  · intro i hi b
    have hij : i.val ≤ j := (Order.IsSuccLimit.le_succ_iff hi).mp i.property
    obtain ⟨k,hk,a,ha⟩ := hl ⟨i.val,hij⟩ hi b
    exact ⟨⟨k.val,k.property.trans (Order.le_succ j)⟩, hk, a, ha⟩
  · apply Data.ext
    rfl

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
