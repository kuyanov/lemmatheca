import Lemmatheca.HenkinCompleteness.HenkinLogic

/-! Countable witness and sentence-deciding extensions. -/
namespace Lemmatheca.MathematicalLogic.HenkinCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u, v}} {α : Type w} {n : ℕ}
noncomputable section
local instance : DecidableEq (L.Formula α) := Classical.decEq _

variable {S T : Set (L.Formula α)}

private theorem consistent_insert_of_derives {A : L.Formula α}
    (hT : Consistent T) (hA : Derives T A) : Consistent (insert A T) := by
  intro hbot
  apply hT
  simpa only [Set.union_self] using derives_cut hA hbot

private theorem consistent_insert_choice (hT : Consistent T) (A : L.Formula α) :
    Consistent (insert A T) ∨ Consistent (insert A.not T) := by
  classical
  by_cases hA : Consistent (insert A T)
  · exact Or.inl hA
  · right
    have hbot : Derives (insert A T) ⊥ := Classical.not_not.mp hA
    have hnA : Derives T A.not := derives_imp_iff.mpr hbot
    exact consistent_insert_of_derives hT hnA

/-- All assumptions of a finite proof inside an increasing union occur together
at a single finite stage. The supremum is zero for an empty assumption set. -/
private theorem finite_subset_stage (D : ℕ → Set (L.Formula α)) (hD : Monotone D)
    (Γ : Finset (L.Formula α)) (hΓ : (↑Γ : Set (L.Formula α)) ⊆ ⋃ n, D n) :
    ∃ n, (↑Γ : Set (L.Formula α)) ⊆ D n := by
  classical
  choose r hr using fun A : Γ => Set.mem_iUnion.mp (hΓ A.property)
  refine ⟨Finset.univ.sup r, fun A hA => ?_⟩
  exact hD (Finset.le_sup (Finset.mem_univ (⟨A, hA⟩ : Γ))) (hr ⟨A, hA⟩)

private theorem consistent_union (D : ℕ → Set (L.Formula α)) (hD : Monotone D)
    (hcon : ∀ n, Consistent (D n)) : Consistent (⋃ n, D n) := by
  rintro ⟨Γ, hΓ, hp⟩
  obtain ⟨n, hn⟩ := finite_subset_stage D hD Γ hΓ
  exact hcon n ⟨Γ, hn, hp⟩

private def decisionStep (T : Set (L.Formula α)) (A : L.Formula α) : Set (L.Formula α) :=
  by
    classical
    exact if Consistent (insert A T) then insert A T else insert A.not T

private theorem decisionStep_contains (T : Set (L.Formula α)) (A : L.Formula α) :
    T ⊆ decisionStep T A := by
  classical
  simp only [decisionStep]
  split <;> exact Set.subset_insert _ _

private theorem decisionStep_consistent (hT : Consistent T) (A : L.Formula α) :
    Consistent (decisionStep T A) := by
  classical
  simp only [decisionStep]
  split
  · assumption
  · exact (consistent_insert_choice hT A).resolve_left ‹¬ Consistent (insert A T)›

private def decisionStages (T : Set (L.Formula α)) (e : ℕ → L.Formula α)
    (n : ℕ) : Set (L.Formula α) :=
  Nat.rec T (fun n U => decisionStep U (e n)) n

private theorem decisionStages_mono (T : Set (L.Formula α)) (e : ℕ → L.Formula α) :
    Monotone (decisionStages T e) := by
  apply monotone_nat_of_le_succ
  intro n
  exact decisionStep_contains (decisionStages T e n) (e n)

private theorem decisionStages_consistent (hT : Consistent T) (e : ℕ → L.Formula α)
    (n : ℕ) : Consistent (decisionStages T e n) := by
  induction n with
  | zero => exact hT
  | succ n ih => exact decisionStep_consistent ih (e n)

private theorem term_empty_fv {n m : ℕ} (t : L.Term (Empty ⊕ Fin n))
    (f : Fin n → Fin m) :
    (t.relabel (Sum.elim Empty.elim (Sum.inr ∘ f))).varFinsetLeft = (∅ : Finset ℕ) := by
  induction t with
  | var x => cases x with
    | inl x => exact Empty.elim x
    | inr i => rfl
  | func fn ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, ih]
    ext i
    simp

private theorem aux_term_empty_fv {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (Empty.elim : Empty → ℕ ⊕ Fin 0) n)).varFinsetLeft = ∅ := by
  have haux : BoundedFormula.relabelAux (Empty.elim : Empty → ℕ ⊕ Fin 0) n =
      Sum.elim Empty.elim (Sum.inr ∘ Fin.natAdd 0) := by
    funext x
    cases x with
    | inl x => exact Empty.elim x
    | inr i => rfl
  rw [haux]
  exact term_empty_fv t (Fin.natAdd 0)

private theorem bounded_empty_fv {n : ℕ} (A : L.BoundedFormula Empty n) :
    (A.relabel (Empty.elim : Empty → ℕ ⊕ Fin 0)).freeVarFinset = ∅ := by
  induction A with
  | falsum => rfl
  | equal t u =>
    simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset, aux_term_empty_fv]
  | rel r ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset, aux_term_empty_fv]
    ext i
    simp
  | imp A B ihA ihB =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset] at *
    rw [ihA, ihB, Finset.empty_union]
  | all A ih =>
    simpa only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset, BoundedFormula.castLE_rfl] using ih

private theorem sentence_relabel_empty_support (A : L.Sentence) : (A.relabel (Empty.elim : Empty → ℕ)).freeVarFinset = ∅ := by
  change (BoundedFormula.relabel (Sum.inl ∘ (Empty.elim : Empty → ℕ)) A).freeVarFinset = ∅
  have hf : Sum.inl ∘ (Empty.elim : Empty → ℕ) = (Empty.elim : Empty → ℕ ⊕ Fin 0) := by
    funext x
    exact Empty.elim x
  rw [hf]
  exact bounded_empty_fv A

/-- An original-language sentence has no added auxiliary name in its support. -/
theorem fresh_liftTheory (T : L.Theory) (c : ℕ) : FreshFor c (liftTheory T) := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := hA
  rw [sentence_relabel_empty_support]
  exact Finset.notMem_empty c

private def witnessFreshName (Γ : Finset (L.Formula ℕ)) (φ : L.BoundedFormula ℕ 1) : ℕ :=
  Classical.choose ((Γ.biUnion BoundedFormula.freeVarFinset ∪ φ.freeVarFinset).exists_notMem)

private theorem witnessFreshName_spec (Γ : Finset (L.Formula ℕ))
    (φ : L.BoundedFormula ℕ 1) :
    witnessFreshName Γ φ ∉ Γ.biUnion BoundedFormula.freeVarFinset ∪ φ.freeVarFinset :=
  Classical.choose_spec ((Γ.biUnion BoundedFormula.freeVarFinset ∪ φ.freeVarFinset).exists_notMem)

private def witnessAdditions (e : ℕ → L.BoundedFormula ℕ 1)
    (n : ℕ) : Finset (L.Formula ℕ) :=
  Nat.rec ∅ (fun n Γ => insert (witnessAxiom (e n) (witnessFreshName Γ (e n))) Γ) n

private def witnessTheories (T : L.Theory) (e : ℕ → L.BoundedFormula ℕ 1)
    (n : ℕ) : Set (L.Formula ℕ) :=
  liftTheory T ∪ ↑(witnessAdditions e n)

private theorem witnessTheories_mono (T : L.Theory) (e : ℕ → L.BoundedFormula ℕ 1) :
    Monotone (witnessTheories T e) := by
  apply monotone_nat_of_le_succ
  intro n A hA
  rcases hA with hA | hA
  · exact Or.inl hA
  · exact Or.inr (Finset.mem_insert_of_mem hA)

private theorem witnessTheories_consistent {T : L.Theory} (hT : Consistent T)
    (e : ℕ → L.BoundedFormula ℕ 1) (n : ℕ) : Consistent (witnessTheories T e n) := by
  induction n with
  | zero => simpa only [witnessTheories, witnessAdditions, Nat.rec_zero,
      Finset.coe_empty, Set.union_empty] using consistent_liftTheory hT
  | succ n ih =>
    have hname := witnessFreshName_spec (witnessAdditions e n) (e n)
    have hbody : witnessFreshName (witnessAdditions e n) (e n) ∉ (e n).freeVarFinset :=
      fun h => hname (Finset.mem_union_right _ h)
    have hctx : FreshFor (witnessFreshName (witnessAdditions e n) (e n))
        (witnessTheories T e n) := by
      intro A hA
      rcases hA with hA | hA
      · exact fresh_liftTheory T _ A hA
      · intro hmem
        apply hname
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨A, hA, hmem⟩)
    have hcon := consistent_add_witness ih (e n)
      (witnessFreshName (witnessAdditions e n) (e n)) hctx hbody
    simpa only [witnessTheories, witnessAdditions, Nat.rec_add_one,
      Finset.coe_insert, Set.union_insert] using hcon

theorem consistent_henkin_extension [Countable L.Symbols] {T : L.Theory}
    (hT : Consistent T) :
    ∃ H : Set (L.Formula ℕ), liftTheory T ⊆ H ∧ Consistent H ∧ Henkin H := by
  let : Countable (L.BoundedFormula ℕ 1) :=
    Function.Injective.countable
      (f := fun φ : L.BoundedFormula ℕ 1 => (⟨1, φ⟩ : Σ n, L.BoundedFormula ℕ n))
      sigma_mk_injective
  obtain ⟨e, he⟩ := exists_surjective_nat (L.BoundedFormula ℕ 1)
  refine ⟨⋃ n, witnessTheories T e n, ?_,
    consistent_union _ (witnessTheories_mono T e) (witnessTheories_consistent hT e), ?_⟩
  · intro A hA
    exact Set.mem_iUnion.mpr ⟨0, Or.inl hA⟩
  · intro φ
    obtain ⟨n, hn⟩ := he φ
    refine ⟨witnessFreshName (witnessAdditions e n) (e n), Set.mem_iUnion.mpr ⟨n + 1, ?_⟩⟩
    right
    change witnessAxiom φ (witnessFreshName (witnessAdditions e n) (e n)) ∈
      insert (witnessAxiom (e n) (witnessFreshName (witnessAdditions e n) (e n)))
        (witnessAdditions e n)
    rw [hn]
    exact Finset.mem_insert_self _ _

theorem lindenbaum_extension [Countable L.Symbols] [Countable α] (hT : Consistent T) :
    ∃ S : Set (L.Formula α), T ⊆ S ∧ Consistent S ∧ Complete S := by
  obtain ⟨e, he⟩ := exists_surjective_nat (L.Formula α)
  refine ⟨⋃ n, decisionStages T e n, ?_,
    consistent_union _ (decisionStages_mono T e) (decisionStages_consistent hT e), ?_⟩
  · intro A hA
    exact Set.mem_iUnion.mpr ⟨0, hA⟩
  · intro A
    obtain ⟨n, hn⟩ := he A
    have hstage : A ∈ decisionStages T e (n + 1) ∨ A.not ∈ decisionStages T e (n + 1) := by
      change A ∈ decisionStep (decisionStages T e n) (e n) ∨
        A.not ∈ decisionStep (decisionStages T e n) (e n)
      rw [hn]
      simp only [decisionStep]
      split
      · exact Or.inl (Set.mem_insert _ _)
      · exact Or.inr (Set.mem_insert _ _)
    exact hstage.imp (fun h => Set.mem_iUnion.mpr ⟨n + 1, h⟩)
      (fun h => Set.mem_iUnion.mpr ⟨n + 1, h⟩)


end
end Lemmatheca.MathematicalLogic.HenkinCompleteness
