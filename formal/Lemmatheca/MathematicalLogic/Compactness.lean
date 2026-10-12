import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Encoding

/-! Finite-size and unnamed-element applications of semantic compactness. -/
namespace Lemmatheca.MathematicalLogic.Compactness
open FirstOrder FirstOrder.Language Cardinal
universe u v w
variable {L : Language.{u, v}}
noncomputable section

/-- Interpret every function as a fixed value and every relation as false. -/
@[instance_reducible]
def constantStructure (L : Language.{u, v}) (M : Type w) [Inhabited M] : L.Structure M where
  funMap _ _ := default
  RelMap _ _ := False

theorem exact_size_sentence {M : Type w} [L.Structure M] (n : ℕ) :
    M ⊨ (Sentence.cardGe L n ⊓ (Sentence.cardGe L (n + 1)).not) ↔ #M = n := by
  rw [Sentence.realize_inf, Sentence.realize_not, Sentence.realize_cardGe,
    Sentence.realize_cardGe]
  constructor
  · rintro ⟨hn, hnext⟩
    rw [Nat.cast_add, Nat.cast_one] at hnext
    exact le_antisymm (lt_natCast_add_one_iff.mp (lt_of_not_ge hnext)) hn
  · intro hM
    simp [hM]

theorem finite_model_exact_size (L : Language.{u, v}) (n : ℕ) (hn : 0 < n) :
    ∃ M : Theory.ModelType.{u, v, max u v}
      ({Sentence.cardGe L n ⊓ (Sentence.cardGe L (n + 1)).not} : L.Theory),
      #M = n := by
  let M := ULift.{max u v} (Fin n)
  let : Inhabited M := ⟨⟨⟨0, hn⟩⟩⟩
  let : L.Structure M := constantStructure L M
  have hcard : #M = n := by simp [M]
  let : M ⊨ ({Sentence.cardGe L n ⊓ (Sentence.cardGe L (n + 1)).not} : L.Theory) := by
    refine ⟨?_⟩
    intro A hA
    obtain rfl := Set.mem_singleton_iff.mp hA
    exact (exact_size_sentence n).mpr hcard
  exact ⟨Theory.ModelType.of _ M, hcard⟩

private theorem finite_size_bound (Γ : Finset L.Sentence) :
    ∃ N : ℕ, ∀ A ∈ Γ, A ∈ L.infiniteTheory →
      ∃ n ≤ N, A = Sentence.cardGe L n := by
  classical
  let r (A : Γ) : ℕ :=
    if hA : (A : L.Sentence) ∈ L.infiniteTheory then Classical.choose hA else 0
  refine ⟨Finset.univ.sup r, fun A hA hInf => ?_⟩
  have hr : Sentence.cardGe L (r ⟨A, hA⟩) = A := by
    simpa only [r, dite_eq_left hInf] using Classical.choose_spec hInf
  exact ⟨r ⟨A, hA⟩, Finset.le_sup (Finset.mem_univ _), hr.symm⟩

theorem infinite_model_of_unbounded_sizes (T : L.Theory)
    (h : ∀ n : ℕ, ∃ M : Theory.ModelType.{u, v, max u v} T, (n : Cardinal) ≤ #M) :
    ∃ M : Theory.ModelType.{u, v, max u v} T, Infinite M := by
  have hsat : (T ∪ L.infiniteTheory).IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    obtain ⟨N, hN⟩ := finite_size_bound Γ
    obtain ⟨M, hM⟩ := h N
    let : M ⊨ (↑Γ : L.Theory) := by
      refine ⟨?_⟩
      intro A hA
      rcases hΓ hA with hT | hInf
      · exact Theory.realize_sentence_of_mem T hT
      · obtain ⟨n, hn, rfl⟩ := hN A hA hInf
        exact (Sentence.realize_cardGe L n).mpr ((Nat.cast_le.mpr hn).trans hM)
    exact Theory.Model.isSatisfiable M
  obtain ⟨U⟩ := hsat
  let : U ⊨ T := U.is_model.mono Set.subset_union_left
  have hInf : U ⊨ L.infiniteTheory := U.is_model.mono Set.subset_union_right
  exact ⟨Theory.ModelType.of T U, (L.model_infiniteTheory_iff).mp hInf⟩

theorem finite_fragment_infiniteTheory_has_finite_model
    (Γ : Finset L.Sentence) (hΓ : (↑Γ : L.Theory) ⊆ L.infiniteTheory) :
    ∃ M : Theory.ModelType.{u, v, max u v} (↑Γ : L.Theory), Finite M := by
  obtain ⟨N, hN⟩ := finite_size_bound Γ
  let M := ULift.{max u v} (Fin (N + 1))
  let : Inhabited M := ⟨⟨0⟩⟩
  let : L.Structure M := constantStructure L M
  have hcard : #M = N + 1 := by simp [M]
  let : M ⊨ (↑Γ : L.Theory) := by
    refine ⟨?_⟩
    intro A hA
    obtain ⟨n, hn, rfl⟩ := hN A hA (hΓ hA)
    apply (Sentence.realize_cardGe L n).mpr
    rw [hcard]
    exact_mod_cast hn.trans (Nat.le_succ N)
  exact ⟨Theory.ModelType.of _ M, (inferInstance : Finite M)⟩

theorem finitude_not_axiomatizable (L : Language.{u, v}) :
    ¬ ∃ T : L.Theory, ∀ (M : Type (max u v)) (_ : L.Structure M),
      Nonempty M → (M ⊨ T ↔ Finite M) := by
  rintro ⟨T, hT⟩
  have hsize : ∀ n : ℕ, ∃ M : Theory.ModelType.{u, v, max u v} T,
      (n : Cardinal) ≤ #M := by
    intro n
    let M := ULift.{max u v} (Fin (n + 1))
    let : Inhabited M := ⟨⟨0⟩⟩
    let : L.Structure M := constantStructure L M
    let : M ⊨ T := (hT M inferInstance inferInstance).mpr inferInstance
    refine ⟨Theory.ModelType.of _ M, ?_⟩
    change (n : Cardinal) ≤ #M
    have hcard : #M = n + 1 := by simp [M]
    rw [hcard]
    exact_mod_cast Nat.le_succ n
  obtain ⟨M, hM⟩ := infinite_model_of_unbounded_sizes T hsize
  let := hM
  let : Finite M := (hT M inferInstance inferInstance).mp M.is_model
  exact not_finite M

theorem exists_unnamed_element [Countable L.Symbols] (T : L.Theory)
    (M : Type w) [L.Structure M] [M ⊨ T] [Infinite M] :
    ∃ N : Theory.ModelType.{u, v, max u v} T,
      ∃ x : N, ∀ t : L.Term Empty, x ≠ t.realize Empty.elim := by
  obtain ⟨N, hN⟩ := T.exists_large_model_of_infinite_model (Order.succ ℵ₀ : Cardinal.{max u v}) M
  have hlarge : (Order.succ ℵ₀ : Cardinal.{max u v}) ≤ #N := by simpa using hN
  have hns : ¬ Function.Surjective (fun t : L.Term Empty =>
      (t.realize Empty.elim : N)) := by
    intro hsurj
    let : Countable N := Function.Surjective.countable hsurj
    have hsmall : #N ≤ ℵ₀ := mk_le_aleph0
    exact (Order.lt_succ ℵ₀).not_ge (hlarge.trans hsmall)
  obtain ⟨x, hx⟩ := not_forall.mp hns
  refine ⟨N, x, fun t ht => ?_⟩
  exact hx ⟨t, ht.symm⟩

end
end Lemmatheca.MathematicalLogic.Compactness
