import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.Truth

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v
noncomputable section
local instance namesPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
local instance namesFormulaDecidable {L : Language.{u,v}} {α : Type} : DecidableEq (Formula L α) := Classical.decEq _
variable {L : Language.{u,v}} {α : Type}

/-- The recovery map uses the certificate's inhabited auxiliary reserve, even for empty original names. -/
def recovery (f : α → ℕ) : ℕ ⊕ ℕ → α ⊕ ℕ :=
  Sum.elim (fun n => if h : ∃ a, f a = n then .inl (Classical.choose h) else .inr 0) Sum.inr

theorem recovery_original (f : α → ℕ) (hf : Function.Injective f) (a : α) :
    recovery f (.inl (f a)) = .inl a := by
  have he : ∃ b, f b = f a := ⟨a,rfl⟩
  simp only [recovery,Sum.elim_inl,dite_eq_left he]
  exact congrArg Sum.inl (hf (Classical.choose_spec he))

theorem recovery_reserve (f : α → ℕ) (n : ℕ) : recovery f (.inr n) = .inr n := by
  rfl

theorem recovery_unused (f : α → ℕ) (n : ℕ) (hn : n ∉ Set.range f) :
    recovery f (.inl n) = .inr 0 := by
  simp only [Set.mem_range,not_exists] at hn
  simp only [recovery,Sum.elim_inl,dite_eq_right (not_exists.mpr hn)]

theorem recovery_end_formula (f : α → ℕ) (hf : Function.Injective f) (A : Formula L α) :
    ((A.rename f).rename (Sum.inl : ℕ → ℕ ⊕ ℕ)).rename (recovery f) =
      A.rename (Sum.inl : α → α ⊕ ℕ) := by
  rw [BoundedFormula.rename_comp,BoundedFormula.rename_comp]
  congr 1
  funext a
  exact recovery_original f hf a

theorem finite_renaming_reflection (f : α → ℕ) (hf : Function.Injective f)
    (Δ : NaturalDeduction.Context L α) (A : Formula L α) :
    NaturalDeduction.Derives false false L (Δ.image (fun B => B.rename f)) (A.rename f) →
      NaturalDeduction.Derives false false L Δ A := by
  rintro ⟨p⟩
  refine ⟨?_⟩
  unfold NaturalDeduction.Proof at p ⊢
  have hp := p.rename (recovery f)
  have hc : ((Δ.image (fun B => B.rename f)).image
      (fun B => B.rename (Sum.inl : ℕ → ℕ ⊕ ℕ))).image
      (fun B => B.rename (recovery f)) =
      Δ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ)) := by
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro B _
    exact recovery_end_formula f hf B
  rw [hc,recovery_end_formula f hf A] at hp
  exact hp

theorem renaming_reflection (f : α → ℕ) (hf : Function.Injective f)
    (Γ : Set (Formula L α)) (A : Formula L α) :
    NaturalDeduction.TheoryDerives false false L ((fun B => B.rename f) '' Γ) (A.rename f) →
      NaturalDeduction.TheoryDerives false false L Γ A := by
  rintro ⟨p⟩
  let pick (C : {B // B ∈ p.assumptions}) : Formula L α :=
    Classical.choose (p.allowed C.val C.property)
  have pick_spec (C : {B // B ∈ p.assumptions}) : pick C ∈ Γ ∧ (pick C).rename f = C.val :=
    Classical.choose_spec (p.allowed C.val C.property)
  let Δ := p.assumptions.attach.image pick
  have hΔ : ∀ B ∈ Δ, B ∈ Γ := by
    intro B hB
    obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp hB
    exact (pick_spec C).1
  have he : Δ.image (fun B => B.rename f) = p.assumptions := by
    ext C
    constructor
    · intro hC
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hB
      rw [(pick_spec D).2]
      exact D.property
    · intro hC
      exact Finset.mem_image.mpr ⟨pick ⟨C,hC⟩,
        Finset.mem_image.mpr ⟨⟨C,hC⟩,Finset.mem_attach _ _,rfl⟩,(pick_spec ⟨C,hC⟩).2⟩
  have hp : NaturalDeduction.Derives false false L (Δ.image (fun B => B.rename f)) (A.rename f) := by
    rw [he]
    exact ⟨p.derivation⟩
  obtain ⟨q⟩ := finite_renaming_reflection f hf Δ A hp
  exact ⟨⟨Δ,hΔ,q⟩⟩

variable (α) [Countable α]

def originalCode : α ↪ ℕ :=
  ⟨Classical.choose (exists_injective_nat α), Classical.choose_spec (exists_injective_nat α)⟩

def reservedEmbedding (a : α) : ℕ := 2 * originalCode α a

theorem reserved_injective : Function.Injective (reservedEmbedding α) := by
  intro a b h
  apply (originalCode α).injective
  unfold reservedEmbedding at h
  omega

theorem original_compl_infinite : (insert 0 (Set.range (reservedEmbedding α)))ᶜ.Infinite := by
  have hi : (Set.range (fun n : ℕ => 2*n+1)).Infinite :=
    Set.infinite_range_of_injective (by intro n m h; dsimp at h; omega)
  apply hi.mono
  rintro x ⟨n,rfl⟩ h
  rcases Set.mem_insert_iff.mp h with hz | ⟨a,ha⟩
  · dsimp at hz; omega
  · dsimp at ha
    unfold reservedEmbedding at ha
    omega

def originalUniverse : PrimeHenkin.Universe where
  carrier := insert 0 (Set.range (reservedEmbedding α))
  nonempty := ⟨0,Set.mem_insert 0 _⟩
  infinite_compl := original_compl_infinite α

theorem original_odds (n : ℕ) : 2*n+1 ∉ (originalUniverse α).carrier := by
  intro h
  rcases Set.mem_insert_iff.mp h with hz | ⟨a,ha⟩
  · omega
  · unfold reservedEmbedding at ha
    omega

variable {α}

theorem renamed_supported (A : Formula L α) :
    PrimeHenkin.Supported (originalUniverse α).carrier (A.rename (reservedEmbedding α)) := by
  classical
  intro c hc
  change c ∈ (A.subst (fun a => .var (reservedEmbedding α a))).freeVarFinset at hc
  rw [BoundedFormula.freeVarFinset_subst] at hc
  obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hc
  have he : c = reservedEmbedding α a := Finset.mem_singleton.mp ha
  subst c
  exact Set.mem_insert_of_mem 0 (Set.mem_range_self a)

theorem renamed_eligible (Γ : Set (Formula L α)) (hΓ : ∀ B ∈ Γ, B.EqualityFree) :
    (fun B => B.rename (reservedEmbedding α)) '' Γ ⊆ PrimeHenkin.eligible (originalUniverse α).carrier := by
  rintro B ⟨C,hC,rfl⟩
  exact ⟨(C.equalityFree_map _).mpr (hΓ C hC),renamed_supported C⟩

variable [Countable L.Symbols]

omit [Countable L.Symbols] in
theorem renamed_nonderivable [_countableSymbols : Countable L.Symbols] (Γ : Set (Formula L α)) (A : Formula L α)
    (hN : ¬ NaturalDeduction.TheoryDerives false false L Γ A) :
    ¬PrimeHenkin.Provable ((fun B => B.rename (reservedEmbedding α)) '' Γ)
      (A.rename (reservedEmbedding α)) := by
  intro h
  exact hN (renaming_reflection (reservedEmbedding α) (reserved_injective α) Γ A h)

/-- Original names select this exact supported prime extension after reserved embedding. -/
def originalWorld (Γ : Set (Formula L α)) (A : Formula L α)
    (hΓ : ∀ B ∈ Γ, B.EqualityFree) (hA : A.EqualityFree)
    (hN : ¬NaturalDeduction.TheoryDerives false false L Γ A) : World L :=
  supportedWorld (originalUniverse α) ((fun B => B.rename (reservedEmbedding α)) '' Γ)
    (A.rename (reservedEmbedding α)) (renamed_eligible Γ hΓ)
    ⟨(A.equalityFree_map _).mpr hA,renamed_supported A⟩ (renamed_nonderivable Γ A hN)

def originalAssignment (w : World L) : α → Domain w := numericalAssignment w ∘ reservedEmbedding α

theorem original_countermodel (Γ : Set (Formula L α)) (A : Formula L α)
    (hΓ : ∀ B ∈ Γ, B.EqualityFree) (hA : A.EqualityFree)
    (hN : ¬NaturalDeduction.TheoryDerives false false L Γ A) :
    let w := originalWorld Γ A hΓ hA hN
    Kripke.Countermodel canonicalModel w Γ A (originalAssignment w) := by
  let w := originalWorld Γ A hΓ hA hN
  have hc := supported_countermodel (originalUniverse α)
    ((fun B => B.rename (reservedEmbedding α)) '' Γ) (A.rename (reservedEmbedding α))
    (renamed_eligible Γ hΓ) ⟨(A.equalityFree_map _).mpr hA,renamed_supported A⟩
    (renamed_nonderivable Γ A hN)
  change Kripke.Countermodel canonicalModel w _ _ _ at hc
  constructor
  · intro B hB
    exact (Kripke.holds_rename canonicalModel B (reservedEmbedding α) w (numericalAssignment w)).mp
      (hc.1 _ (Set.mem_image_of_mem _ hB))
  · intro hA'
    exact hc.2 ((Kripke.holds_rename canonicalModel A (reservedEmbedding α) w (numericalAssignment w)).mpr hA')

end
end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
