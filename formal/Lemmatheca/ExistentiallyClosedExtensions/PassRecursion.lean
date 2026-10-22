import Lemmatheca.ExistentiallyClosedExtensions.PassLimits
import Lemmatheca.ExistentiallyClosedExtensions.PassSuccessor

namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
open FirstOrder FirstOrder.Language Cardinal CategoryTheory Opposite
open CategoryTheory.SmallObject
open Lemmatheca.ModelTheory
open InductiveTheories
universe u v w
variable {L : Language.{u, v}} {J : Type (max u v w)}
    [LinearOrder J] [SuccOrder J] [OrderBot J]
variable {T : L.Theory} {κ : Cardinal.{max u v w}}
    {A : Theory.ModelType.{u, v, max u v w} T} {schedule : J → Request L A}
    {B₀ : CodedModel T κ} {e₀ : A ≃[L] B₀.asModel}

def initialData : Data T κ A schedule B₀ e₀ (⊥ : J) where
  F := (Functor.const (Set.Iic (⊥ : J))).obj B₀
  starts := rfl
  handled i hi := (not_lt_of_ge bot_le hi).elim
  limit_cover i hi := by
    have he : i.val = ⊥ := le_antisymm i.property bot_le
    exact (hi.ne_bot he).elim

theorem exists_prefix_of_successors [WellFoundedLT J]
    (hT : IsInductive.{u, v, w} T) (hω : ℵ₀ ≤ κ) (hJ : #J ≤ κ)
    (hs : ∀ (j : J) (_ : ¬IsMax j) (p : Data T κ A schedule B₀ e₀ j),
      ∃ q : Data T κ A schedule B₀ e₀ (Order.succ j), restrict q (Order.le_succ j) = p)
    (j : J) : Nonempty (Data T κ A schedule B₀ e₀ j) := by
  classical
  let F := presheaf (T := T) (κ := κ) (A := A) (schedule := schedule) (B₀ := B₀) (e₀ := e₀)
  let d : F.WellOrderInductionData := Functor.WellOrderInductionData.ofExists
    (fun j hj => hs j hj)
    (by
      intro j hj x
      let p (i : Set.Iio j) : Data T κ A schedule B₀ e₀ i.val := x.val (op i)
      have hp (i k : Set.Iio j) (hik : i ≤ k) : restrict (p k) hik = p i := by
        exact x.property (homOfLE hik).op
      obtain ⟨q, hq⟩ := limit_extension hT hω hJ hj p hp
      exact ⟨q, fun i hi => hq ⟨i, hi⟩⟩)
  exact ⟨(d.sectionsMk (initialData (J := J))).val (op j)⟩

theorem exists_prefix [WellFoundedLT J]
    (hT : IsInductive.{u, v, w} T) (hω : ℵ₀ ≤ κ)
    (hL : Cardinal.lift (#L.Symbols) ≤ κ) (hJ : #J ≤ κ) (j : J) :
    Nonempty (Data T κ A schedule B₀ e₀ j) :=
  exists_prefix_of_successors hT hω hJ (fun _ hj p => successor_extension hω hL hj p) j

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions.PassPrefix
