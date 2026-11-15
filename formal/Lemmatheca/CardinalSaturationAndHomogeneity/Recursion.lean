import Lemmatheca.CardinalSaturationAndHomogeneity.Sizes

namespace Lemmatheca.ModelTheory.CardinalSaturation

open FirstOrder FirstOrder.Language PartialElementaryMaps Cardinal Ordinal
universe u v w w' z
noncomputable section
local instance cardinalRecursionPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- A total union operation, used only on the proved nonempty chains below. -/
private def fallbackUnion (p : Map L M N) (C : Set (Map L M N)) : Map L M N :=
  if h : IsChain (· ≤ ·) C ∧ C.Nonempty then Map.chainUnion C h.1 h.2 else p

def mapSequence (p : Map L M N) (step : Ordinal.{z} → Map L M N → Map L M N)
    (α : Ordinal.{z}) : Map L M N :=
  Ordinal.limitRecOn α p step (fun α _ f =>
    fallbackUnion p (Set.range (fun β : Set.Iio α => f β.val β.property)))

theorem mapSequence_zero (p : Map L M N) (step : Ordinal.{z} → Map L M N → Map L M N) :
    mapSequence p step 0 = p := by
  exact Ordinal.limitRecOn_zero _ _ _

theorem mapSequence_succ (p : Map L M N) (step : Ordinal.{z} → Map L M N → Map L M N)
    (α : Ordinal.{z}) : mapSequence p step (α + 1) = step α (mapSequence p step α) := by
  exact Ordinal.limitRecOn_add_one α _ _ _

private theorem mapSequence_limit (p : Map L M N) (step : Ordinal.{z} → Map L M N → Map L M N)
    (α : Ordinal.{z}) (hα : Order.IsSuccLimit α) :
    mapSequence p step α = fallbackUnion p
      (Set.range (fun β : Set.Iio α => mapSequence p step β.val)) := by
  exact Ordinal.limitRecOn_limit α _ _ _ hα

theorem mapSequence_monotone (p : Map L M N)
    (step : Ordinal.{z} → Map L M N → Map L M N)
    (hs : ∀ α q, q ≤ step α q) : Monotone (mapSequence p step) := by
  have h : ∀ α : Ordinal.{z}, ∀ β ≤ α, mapSequence p step β ≤ mapSequence p step α := by
    intro α
    induction α using Ordinal.limitRecOn with
    | zero =>
      intro β hβ
      have hβ0 : β = 0 := le_antisymm hβ (show 0 ≤ β from bot_le)
      rw [hβ0]
    | add_one α ih =>
      intro β hβ
      rcases eq_or_lt_of_le hβ with rfl | hlt
      · exact le_rfl
      · exact (ih β (Order.lt_succ_iff.mp hlt)).trans
          (by rw [mapSequence_succ]; exact hs α _)
    | limit α hα ih =>
      intro β hβ
      rcases eq_or_lt_of_le hβ with rfl | hlt
      · exact le_rfl
      · let C := Set.range (fun γ : Set.Iio α => mapSequence p step γ.val)
        have hc : IsChain (· ≤ ·) C := by
          rintro q ⟨γ, rfl⟩ r ⟨δ, rfl⟩ _
          rcases le_total γ.val δ.val with h | h
          · exact Or.inl (ih δ.val δ.property γ.val h)
          · exact Or.inr (ih γ.val γ.property δ.val h)
        have hn : C.Nonempty := ⟨_, ⟨⟨0, hα.bot_lt⟩, rfl⟩⟩
        rw [mapSequence_limit p step α hα]
        unfold fallbackUnion
        rw [dite_eq_left ⟨hc, hn⟩]
        exact (Map.chain_union_spec C hc hn).2.2 _ ⟨⟨β, hlt⟩, rfl⟩
  exact fun _ _ hαβ => h _ _ hαβ

private theorem mapSequence_limit_spec (p : Map L M N)
    (step : Ordinal.{z} → Map L M N → Map L M N)
    (hs : ∀ α q, q ≤ step α q) (α : Ordinal.{z}) (hα : Order.IsSuccLimit α) :
    (mapSequence p step α).dom = ⋃ β : Set.Iio α, (mapSequence p step β.val).dom ∧
    (mapSequence p step α).range = ⋃ β : Set.Iio α, (mapSequence p step β.val).range := by
  let C := Set.range (fun β : Set.Iio α => mapSequence p step β.val)
  have hc : IsChain (· ≤ ·) C := by
    rintro q ⟨γ, rfl⟩ r ⟨δ, rfl⟩ _
    rcases le_total γ.val δ.val with h | h
    · exact Or.inl (mapSequence_monotone p step hs h)
    · exact Or.inr (mapSequence_monotone p step hs h)
  have hn : C.Nonempty := ⟨_, ⟨⟨0, hα.bot_lt⟩, rfl⟩⟩
  rw [mapSequence_limit p step α hα]
  unfold fallbackUnion
  rw [dite_eq_left ⟨hc, hn⟩]
  obtain ⟨hd, hr, _⟩ := Map.chain_union_spec C hc hn
  constructor
  · rw [hd]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨q, ⟨β, rfl⟩⟩, hx⟩
      exact ⟨β, hx⟩
    · rintro ⟨β, hx⟩
      exact ⟨⟨_, ⟨β, rfl⟩⟩, hx⟩
  · rw [hr]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨q, ⟨β, rfl⟩⟩, hx⟩
      exact ⟨β, hx⟩
    · rintro ⟨β, hx⟩
      exact ⟨⟨_, ⟨β, rfl⟩⟩, hx⟩

theorem mapSequence_continuous (p : Map L M N)
    (step : Ordinal.{z} → Map L M N → Map L M N)
    (hs : ∀ α q, q ≤ step α q) :
    ContinuousIncreasing (fun α => (mapSequence p step α).dom) ∧
    ContinuousIncreasing (fun α => (mapSequence p step α).range) := by
  constructor
  · exact ⟨fun _ _ h => Map.dom_mono (mapSequence_monotone p step hs h),
      fun α hα => (mapSequence_limit_spec p step hs α hα).1⟩
  · exact ⟨fun _ _ h => Map.range_mono (mapSequence_monotone p step hs h),
      fun α hα => (mapSequence_limit_spec p step hs α hα).2⟩

theorem ordinal_enumeration {κ : Cardinal.{z}} [Nonempty M] (hsize : AtMost κ M) :
    ∃ m : Ordinal.{z} → M, ∀ x, ∃ α < κ.ord, m α = x := by
  classical
  have hm : Cardinal.lift.{z} (#M) ≤ Cardinal.lift.{w} (#κ.ord.ToType) := by
    simpa only [AtMost, Cardinal.mk_toType, Cardinal.card_ord] using hsize
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.mp hm
  let m (α : Ordinal.{z}) : M := if h : α < κ.ord then
    Function.invFun e (Ordinal.ToType.mk ⟨α, h⟩) else Classical.choice ‹Nonempty M›
  refine ⟨m, fun x => ?_⟩
  let i := Ordinal.ToType.mk.symm (e x)
  let α := i.val
  have hα : α < κ.ord := i.property
  refine ⟨α, hα, ?_⟩
  simp only [m, dite_eq_left hα]
  change Function.invFun e (Ordinal.ToType.mk (Ordinal.ToType.mk.symm (e x))) = x
  rw [OrderIso.apply_symm_apply]
  exact Function.leftInverse_invFun e.injective x

private theorem inverse_graph (p : Map L M N) (a : M) (b : N) :
    (b, a) ∈ p.symm.graph ↔ (a, b) ∈ p.graph := by
  constructor
  · rintro ⟨hb, he⟩
    let d := p.rangeEquiv.symm ⟨b, hb⟩
    have hda : d.val = a := he
    have hdb : p.toFun d = b := congrArg Subtype.val (p.rangeEquiv.apply_symm_apply ⟨b, hb⟩)
    rw [← hda]
    exact ⟨d.property, hdb⟩
  · rintro ⟨ha, he⟩
    have hb : b ∈ p.range := ⟨⟨a, ha⟩, he⟩
    refine ⟨hb, ?_⟩
    have heq : (⟨b, hb⟩ : p.range) = p.rangeEquiv ⟨a, ha⟩ := Subtype.ext he.symm
    change p.symm.toFun (⟨b, hb⟩ : p.range) = a
    rw [heq]
    exact p.symm_apply ⟨a, ha⟩

theorem inverse_inverse (p : Map L M N) : p.symm.symm = p := by
  apply Map.graph_injective
  ext xy
  exact (inverse_graph p.symm xy.2 xy.1).trans (inverse_graph p xy.1 xy.2)

end
end Lemmatheca.ModelTheory.CardinalSaturation
