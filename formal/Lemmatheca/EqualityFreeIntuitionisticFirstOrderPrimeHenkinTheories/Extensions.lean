import Lemmatheca.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories.Construction
namespace Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
universe u v
noncomputable section
variable {L : Language.{u,v}}
local instance extensionsFormulaDecidableEq : DecidableEq (Fml L) := Classical.decEq _

private theorem from_single {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    {A C : Fml L} (hA : A ∈ eligible U.carrier) (hC : C ∈ T)
    (p : Proof false false L {C} A) : A ∈ T := by
  apply hT.closed A hA
  exact ⟨⟨{C}, by intro B hB; exact (Finset.mem_singleton.mp hB) ▸ hC, p⟩⟩

private theorem from_pair {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    {A B C : Fml L} (hA : A ∈ eligible U.carrier) (hB : B ∈ T) (hC : C ∈ T)
    (p : Proof false false L {B, C} A) : A ∈ T := by
  apply hT.closed A hA
  refine ⟨⟨{B,C}, ?_, p⟩⟩
  intro D hD
  rcases Finset.mem_insert.mp hD with rfl | hD
  · exact hB
  · exact (Finset.mem_singleton.mp hD) ▸ hC

private theorem binary_support {U : Set ℕ} (A B : Fml L)
    (hA : Supported U A) (hB : Supported U B) :
    ∀ c ∈ A.freeVarFinset ∪ B.freeVarFinset, c ∈ U := by
  intro c hc
  exact (Finset.mem_union.mp hc).elim (hA c) (hB c)


theorem conjunction_membership {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A B : Fml L) (hA : A ∈ eligible U.carrier) (hB : B ∈ eligible U.carrier) :
    (.conj A B) ∈ T ↔ A ∈ T ∧ B ∈ T := by
  constructor
  · intro h
    exact ⟨from_single hT hA h (.conjElimLeft (.assumption (Finset.mem_singleton_self _))),
      from_single hT hB h (.conjElimRight (.assumption (Finset.mem_singleton_self _)))⟩
  · rintro ⟨ha,hb⟩
    have he : (.conj A B) ∈ eligible U.carrier :=
      ⟨⟨hA.1,hB.1⟩,binary_support A B hA.2 hB.2⟩
    exact from_pair hT he ha hb (.conjIntro
      (.assumption (Finset.mem_insert_self _ _))
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))

theorem disjunction_membership {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A B : Fml L) (hA : A ∈ eligible U.carrier) (hB : B ∈ eligible U.carrier) :
    (.disj A B) ∈ T ↔ A ∈ T ∨ B ∈ T := by
  constructor
  · exact hT.prime
  · intro h
    have he : (.disj A B) ∈ eligible U.carrier :=
      ⟨⟨hA.1,hB.1⟩,binary_support A B hA.2 hB.2⟩
    rcases h with ha | hb
    · exact from_single hT he ha (.disjIntroLeft (.assumption (Finset.mem_singleton_self _)))
    · exact from_single hT he hb (.disjIntroRight (.assumption (Finset.mem_singleton_self _)))

theorem existential_membership {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (D : Body L) (hD : D.EqualityFree ∧ Supported U.carrier D) :
    (.ex D) ∈ T ↔ ∃ t : L.Term ℕ, TermSupported U.carrier t ∧ D.instantiate t ∈ T := by
  constructor
  · intro h
    obtain ⟨c,hc,hi⟩ := hT.witness h
    exact ⟨.var c, by intro x hx; exact (Finset.mem_singleton.mp hx) ▸ hc, hi⟩
  · rintro ⟨t,_,hi⟩
    exact from_single hT hD hi (.exIntro t (.assumption (Finset.mem_singleton_self _)))

theorem universal_instance {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (D : Body L) (hD : D.EqualityFree ∧ Supported U.carrier D)
    (t : L.Term ℕ) (ht : TermSupported U.carrier t) (hall : (.all D) ∈ T) :
    D.instantiate t ∈ T := by
  exact from_single hT
    ⟨(instantiate_equalityFree D t).mpr hD.1, instantiate_supported D t hD.2 ht⟩
    hall (.allElim t (.assumption (Finset.mem_singleton_self _)))

theorem negation_implication_membership {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A : Fml L) (hA : A ∈ eligible U.carrier) :
    (.neg A) ∈ T ↔ (.impl A .falsum) ∈ T := by
  have hf : (.falsum : Fml L) ∈ eligible U.carrier :=
    ⟨trivial, by intro c hc; exact False.elim (Finset.notMem_empty c hc)⟩
  have hi : (.impl A .falsum) ∈ eligible U.carrier :=
    ⟨⟨hA.1,hf.1⟩,binary_support A .falsum hA.2 hf.2⟩
  constructor
  · intro hn
    exact from_single hT hi hn (.impIntro (.negElim
      (.assumption (Finset.mem_insert_self _ _))
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  · intro himp
    exact from_single hT hA himp (.negIntro (.impElim
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      (.assumption (Finset.mem_insert_self _ _))))

theorem adjoin_complement_infinite (U : Universe) (c : ℕ) : (insert c U.carrier)ᶜ.Infinite := by
  have h := U.infinite_compl.sdiff (Set.finite_singleton c)
  convert h using 1
  ext x
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, not_or, Set.mem_sdiff,
    Set.mem_singleton_iff]
  exact and_comm

/-- Retaining the given universe and adding one actual new parameter. -/
def adjoin (U : Universe) (c : ℕ) : Universe where
  carrier := insert c U.carrier
  nonempty := U.nonempty.mono (Set.subset_insert c U.carrier)
  infinite_compl := adjoin_complement_infinite U c

section CountableLanguage
variable [Countable L.Symbols]

theorem missing_implication {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A B : Fml L) (hA : A ∈ eligible U.carrier) (hB : B ∈ eligible U.carrier)
    (hnot : (.impl A B) ∉ T) :
    ∃ (V : Universe) (S : Set (Fml L)), Theory V S ∧ Extends U T V S ∧ A ∈ S ∧ B ∉ S := by
  classical
  have hI : (.impl A B) ∈ eligible U.carrier :=
    ⟨⟨hA.1,hB.1⟩,fun c hc => (Finset.mem_union.mp hc).elim (hA.2 c) (hB.2 c)⟩
  have ha : Avoids (insert A T) B := by
    intro hp
    exact hnot (hT.closed _ hI ((provable_deduction T A B).mp hp))
  have hs : insert A T ⊆ eligible U.carrier := by
    intro C hC
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · exact hA
    · exact hT.supported hC
  refine ⟨enlargement U,extension U (insert A T) B,
    extension_prime U _ B hs hB ha,⟨Set.subset_union_left,?_⟩,?_,
    extension_omits U _ B hs hB ha⟩
  · exact (Set.subset_insert A T).trans (extension_contains U _ B)
  · exact extension_contains U _ B (Set.mem_insert A T)

theorem missing_negation {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A : Fml L) (hA : A ∈ eligible U.carrier) (hnot : (.neg A) ∉ T) :
    ∃ (V : Universe) (S : Set (Fml L)), Theory V S ∧ Extends U T V S ∧ A ∈ S := by
  have hnotI : (.impl A .falsum) ∉ T := by
    intro hI
    exact hnot ((negation_implication_membership hT A hA).mpr hI)
  obtain ⟨V,S,hS,hExt,hAS,_⟩ := missing_implication hT A .falsum hA
    ⟨trivial,by simp [Supported,BoundedFormula.freeVarFinset]⟩ hnotI
  exact ⟨V,S,hS,hExt,hAS⟩

theorem missing_universal {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (D : Body L) (hD : D.EqualityFree ∧ Supported U.carrier D)
    (hnot : (.all D) ∉ T) (c : ℕ) (hc : c ∉ U.carrier) :
    ∃ (V : Universe) (S : Set (Fml L)), Theory V S ∧ Extends U T V S ∧
      c ∈ V.carrier ∧ D.instantiate (.var c) ∉ S := by
  classical
  have hall : (.all D) ∈ eligible U.carrier := hD
  have hfT : ∀ A ∈ T, c ∉ A.freeVarFinset := by
    intro A hA hmem
    exact hc ((hT.supported hA).2 c hmem)
  have hfD : c ∉ D.freeVarFinset := fun hmem => hc (hD.2 c hmem)
  have ha : Avoids T (D.instantiate (.var c)) := by
    intro hp
    exact hnot (hT.closed _ hall (fresh_all_intro D c hfT hfD hp))
  have hs : T ⊆ eligible (adjoin U c).carrier := by
    intro A hA
    exact ⟨(hT.supported hA).1,supported_mono (Set.subset_insert c U.carrier)
      (hT.supported hA).2⟩
  have hI : D.instantiate (.var c) ∈ eligible (adjoin U c).carrier := by
    refine ⟨(instantiate_equalityFree D _).mpr hD.1,
      instantiate_supported D _ (supported_mono (Set.subset_insert c U.carrier) hD.2) ?_⟩
    intro d hd
    have he := Finset.mem_singleton.mp hd
    exact he ▸ Set.mem_insert c U.carrier
  refine ⟨enlargement (adjoin U c),extension (adjoin U c) T (D.instantiate (.var c)),
    extension_prime _ _ _ hs hI ha,⟨?_,extension_contains _ _ _⟩,?_,
    extension_omits _ _ _ hs hI ha⟩
  · exact (Set.subset_insert c U.carrier).trans Set.subset_union_left
  · exact Or.inl (Set.mem_insert c U.carrier)

theorem future_implication {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A B : Fml L) (hA : A ∈ eligible U.carrier) (hB : B ∈ eligible U.carrier) :
    (.impl A B) ∈ T ↔ ∀ (V : Universe) (S : Set (Fml L)),
      Theory V S → Extends U T V S → A ∈ S → B ∈ S := by
  classical
  constructor
  · intro hI V S hS hExt hAS
    have hBS : B ∈ eligible V.carrier :=
      ⟨hB.1,supported_mono hExt.1 hB.2⟩
    apply hS.closed B hBS
    let Δ : Finset (Fml L) := {.impl A B,A}
    refine ⟨⟨Δ,?_,Proof.impElim (A := A) (Proof.assumption (by simp [Δ]))
      (Proof.assumption (by simp [Δ]))⟩⟩
    intro C hC
    simp only [Δ,Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact hExt.2 hI
    · exact hAS
  · intro hfuture
    by_contra hnot
    obtain ⟨V,S,hS,hExt,hAS,hnotBS⟩ := missing_implication hT A B hA hB hnot
    exact hnotBS (hfuture V S hS hExt hAS)

theorem future_universal {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (D : Body L) (hD : D.EqualityFree ∧ Supported U.carrier D) :
    (.all D) ∈ T ↔ ∀ (V : Universe) (S : Set (Fml L)), Theory V S → Extends U T V S →
      ∀ t : L.Term ℕ, TermSupported V.carrier t → D.instantiate t ∈ S := by
  classical
  constructor
  · intro hall V S hS hExt t ht
    exact universal_instance hS D ⟨hD.1,supported_mono hExt.1 hD.2⟩ t ht (hExt.2 hall)
  · intro hfuture
    by_contra hnot
    obtain ⟨c,hc⟩ := U.infinite_compl.nonempty
    obtain ⟨V,S,hS,hExt,hcV,hnotI⟩ := missing_universal hT D hD hnot c hc
    apply hnotI
    apply hfuture V S hS hExt (.var c)
    intro d hd
    have he := Finset.mem_singleton.mp hd
    exact he ▸ hcV

theorem future_negation {U : Universe} {T : Set (Fml L)} (hT : Theory U T)
    (A : Fml L) (hA : A ∈ eligible U.carrier) :
    (.neg A) ∈ T ↔ ∀ (V : Universe) (S : Set (Fml L)),
      Theory V S → Extends U T V S → A ∉ S := by
  classical
  constructor
  · intro hn V S hS hExt hAS
    have hI := (negation_implication_membership hT A hA).mp hn
    have hf := (future_implication hT A .falsum hA
      ⟨trivial,by simp [Supported,BoundedFormula.freeVarFinset]⟩).mp hI V S hS hExt hAS
    exact hS.proper hf
  · intro hfuture
    by_contra hnot
    obtain ⟨V,S,hS,hExt,hAS⟩ := missing_negation hT A hA hnot
    exact hfuture V S hS hExt hAS
end CountableLanguage
end
end Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
