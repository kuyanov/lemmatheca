import Lemmatheca.HenkinCompleteness.HenkinBasic

/-! Syntactic consistency, fresh witnesses and equality congruence. -/
namespace Lemmatheca.MathematicalLogic.HenkinCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u, v}} {α : Type w} {n : ℕ}
noncomputable section
local instance : DecidableEq (L.Formula α) := Classical.decEq _

variable {S T : Set (L.Formula ℕ)}

theorem derives_liftTheory_iff {T : L.Theory} (A : L.Sentence) :
    Derives (liftTheory T) (A.relabel Empty.elim) ↔ Derives T A := by
  classical
  constructor
  · rintro ⟨Γ, hΓ, hp⟩
    have hpre : ∀ B : Γ, ∃ C : L.Sentence, C ∈ T ∧ Formula.relabel Empty.elim C = B.1 := by
      intro B
      exact hΓ B.property
    let f : Γ → L.Sentence := fun B => Classical.choose (hpre B)
    let Δ := Γ.attach.image f
    have hΔ : (↑Δ : L.Theory) ⊆ T := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
      exact (Classical.choose_spec (hpre B)).1
    have himage : Δ.image (Formula.relabel Empty.elim) = Γ := by
      ext B
      constructor
      · rintro hB
        rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
        rcases Finset.mem_image.mp hC with ⟨D, hD, rfl⟩
        have hd := (Classical.choose_spec (hpre D)).2
        rw [hd]
        exact D.property
      · intro hB
        refine Finset.mem_image.mpr ⟨f ⟨B, hB⟩, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩
        · exact (Classical.choose_spec (hpre ⟨B, hB⟩)).2
    refine ⟨Δ, hΔ, Proof.parameterCloseMap (Empty.elim : Empty → ℕ) (fun x => x.elim) ?_⟩
    simpa only [himage] using hp
  · rintro ⟨Γ, hΓ, hp⟩
    refine ⟨Γ.image (Formula.relabel Empty.elim), ?_, .rename Empty.elim hp⟩
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
    exact ⟨C, hΓ hC, rfl⟩

theorem consistent_liftTheory {T : L.Theory} (hT : Consistent T) :
    Consistent (liftTheory T) := by
  intro h
  apply hT
  apply (derives_liftTheory_iff (⊥ : L.Sentence)).mp
  simpa only [Formula.relabel, BoundedFormula.relabel_bot] using h

theorem derives_neg_elim {U : Set (L.Formula α)} {A : L.Formula α}
    (hA : Derives U A) (hnA : Derives U A.not) : Derives U ⊥ := by
  rcases hA with ⟨Γ, hΓ, hp⟩
  rcases hnA with ⟨Δ, hΔ, hq⟩
  refine ⟨Γ ∪ Δ, ?_, .negElim (.weakening hp (Finset.subset_union_left))
    (.weakening hq (Finset.subset_union_right))⟩
  intro B hB
  rcases Finset.mem_union.mp hB with hB | hB
  · exact hΓ hB
  · exact hΔ hB

theorem derives_imp_elim {U : Set (L.Formula α)} {A B : L.Formula α}
    (hAB : Derives U (A.imp B)) (hA : Derives U A) : Derives U B := by
  rcases hAB with ⟨Γ, hΓ, hp⟩
  rcases hA with ⟨Δ, hΔ, hq⟩
  refine ⟨Γ ∪ Δ, ?_, .impElim (.weakening hp (Finset.subset_union_left))
    (.weakening hq (Finset.subset_union_right))⟩
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hΓ hC
  · exact hΔ hC

theorem derives_and_intro {U : Set (L.Formula α)} {A B : L.Formula α}
    (hA : Derives U A) (hB : Derives U B) : Derives U (A ⊓ B) := by
  rcases hA with ⟨Γ, hΓ, hp⟩
  rcases hB with ⟨Δ, hΔ, hq⟩
  refine ⟨Γ ∪ Δ, ?_, .conjIntro (.weakening hp (Finset.subset_union_left))
    (.weakening hq (Finset.subset_union_right))⟩
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · exact hΓ hC
  · exact hΔ hC

theorem derives_iff_mem (hS : Consistent S) (hC : Complete S) (A : L.Formula ℕ) :
    Derives S A ↔ A ∈ S := by
  constructor
  · intro h
    rcases hC A with hA | hnA
    · exact hA
    · exact (hS (derives_neg_elim h (derives_assumption hnA))).elim
  · exact derives_assumption

theorem bot_not_mem (hS : Consistent S) : (⊥ : L.Formula ℕ) ∉ S := by
  exact fun h => hS (derives_assumption h)

theorem not_mem_iff (hS : Consistent S) (hC : Complete S) (A : L.Formula ℕ) :
    A.not ∈ S ↔ A ∉ S := by
  constructor
  · intro hnA hA
    exact hS (derives_neg_elim (derives_assumption hA) (derives_assumption hnA))
  · intro h
    exact (hC A).resolve_left h

theorem and_mem_iff (hS : Consistent S) (hC : Complete S) (A B : L.Formula ℕ) :
    A ⊓ B ∈ S ↔ A ∈ S ∧ B ∈ S := by
  constructor
  · intro h
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption h
    exact ⟨(derives_iff_mem hS hC A).mp ⟨Γ, hΓ, .conjElimLeft hp⟩,
      (derives_iff_mem hS hC B).mp ⟨Γ, hΓ, .conjElimRight hp⟩⟩
  · rintro ⟨hA, hB⟩
    exact (derives_iff_mem hS hC _).mp
      (derives_and_intro (derives_assumption hA) (derives_assumption hB))

theorem or_mem_iff (hS : Consistent S) (hC : Complete S) (A B : L.Formula ℕ) :
    A ⊔ B ∈ S ↔ A ∈ S ∨ B ∈ S := by
  classical
  constructor
  · intro hAB
    by_contra h
    have hnA := (not_mem_iff hS hC A).mpr (fun hA => h (Or.inl hA))
    have hnB := (not_mem_iff hS hC B).mpr (fun hB => h (Or.inr hB))
    apply hS
    let Γ : Finset (L.Formula ℕ) := {A ⊔ B, A.not, B.not}
    refine ⟨Γ, ?_, ?_⟩
    · intro C hC
      change C ∈ Γ at hC
      simp only [Γ, Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl | rfl
      · exact hAB
      · exact hnA
      · exact hnB
    · apply Proof.disjElim (A := A) (B := B) (.assumption (by simp [Γ]))
      · exact .negElim (A := A) (.assumption (by simp)) (.assumption (by simp [Γ]))
      · exact .negElim (A := B) (.assumption (by simp)) (.assumption (by simp [Γ]))
  · intro h
    rcases h with hA | hB
    · obtain ⟨Γ, hΓ, hp⟩ := derives_assumption hA
      exact (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, .disjIntroLeft hp⟩
    · obtain ⟨Γ, hΓ, hp⟩ := derives_assumption hB
      exact (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, .disjIntroRight hp⟩

theorem imp_mem_iff (hS : Consistent S) (hC : Complete S) (A B : L.Formula ℕ) :
    A.imp B ∈ S ↔ (A ∉ S ∨ B ∈ S) := by
  classical
  constructor
  · intro hAB
    by_cases hA : A ∈ S
    · exact Or.inr ((derives_iff_mem hS hC B).mp
        (derives_imp_elim (derives_assumption hAB) (derives_assumption hA)))
    · exact Or.inl hA
  · intro h
    apply (derives_iff_mem hS hC _).mp
    apply derives_imp_iff.mpr
    rcases h with hnA | hB
    · have hd := derives_neg_elim (derives_assumption (Set.mem_insert A S))
        (derives_assumption (Set.mem_insert_of_mem A ((not_mem_iff hS hC A).mpr hnA)))
      exact derives_explosion hd
    · exact derives_assumption (Set.mem_insert_of_mem A hB)

theorem instantiate_not (φ : L.BoundedFormula α 1) (t : L.Term α) :
    instantiate φ.not t = (instantiate φ t).not := by
  simp [instantiate, BoundedFormula.not, BoundedFormula.toFormula,
    BoundedFormula.subst, BoundedFormula.mapTermRel, Bot.bot]

private theorem derives_not_imp_parts {U : Set (L.Formula α)} {A B : L.Formula α}
    (h : Derives U (A.imp B).not) : Derives U A ∧ Derives U B.not := by
  rcases h with ⟨Γ, hΓ, hp⟩
  constructor
  · refine ⟨Γ, hΓ, .classicalContradiction ?_⟩
    have hi : Proof L (insert A.not Γ) (A.imp B) := by
      apply Proof.impIntro
      exact .falsumElim (.negElim (A := A) (.assumption (by simp))
        (.assumption (by simp)))
    exact .negElim hi (.weakening hp (Finset.subset_insert _ _))
  · refine ⟨Γ, hΓ, .negIntro ?_⟩
    have hi : Proof L (insert B Γ) (A.imp B) :=
      .impIntro (.assumption (by simp))
    exact .negElim hi (.weakening hp (Finset.subset_insert _ _))

theorem consistent_add_witness (hT : Consistent T) (φ : L.BoundedFormula ℕ 1) (c : ℕ)
    (hcT : FreshFor c T) (hcφ : c ∉ φ.freeVarFinset) :
    Consistent (insert (witnessAxiom φ c) T) := by
  intro hf
  have hn : Derives T (witnessAxiom φ c).not := derives_imp_iff.mpr hf
  obtain ⟨hex, hninst⟩ := derives_not_imp_parts hn
  have hni : Derives T (instantiate φ.not (.var c)) := by
    simpa only [instantiate_not] using hninst
  obtain ⟨Γ, hΓ, hp⟩ := hni
  have hcneg : c ∉ φ.not.freeVarFinset := by
    simpa [BoundedFormula.not, BoundedFormula.freeVarFinset] using hcφ
  have hdec : (Classical.decEq ℕ) = instDecidableEqNat := Subsingleton.elim _ _
  have hcneg' : c ∉ @BoundedFormula.freeVarFinset L ℕ (Classical.decEq ℕ) 1 φ.not := by
    rw [hdec]
    exact hcneg
  have hcΓ' : ∀ A ∈ Γ, c ∉ @BoundedFormula.freeVarFinset L ℕ (Classical.decEq ℕ) 0 A := by
    intro A hA
    rw [hdec]
    exact hcT A (hΓ hA)
  have hAll : Derives T φ.not.all :=
    ⟨Γ, hΓ, .allIntroParameter c hcneg' hcΓ' hp⟩
  exact hT (derives_neg_elim hAll hex)

theorem ex_mem_iff (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (φ : L.BoundedFormula ℕ 1) :
    φ.ex ∈ S ↔ ∃ t : L.Term ℕ, instantiate φ t ∈ S := by
  constructor
  · intro hex
    obtain ⟨c, hc⟩ := hH φ
    refine ⟨.var c, (derives_iff_mem hS hC _).mp ?_⟩
    exact derives_imp_elim (derives_assumption hc) (derives_assumption hex)
  · rintro ⟨t, ht⟩
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption ht
    exact (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, .exIntro t hp⟩

section
local instance : DecidableEq ℕ := Classical.decEq _
private theorem notAll_exNot {Γ : Finset (L.Formula ℕ)} {φ : L.BoundedFormula ℕ 1}
    (hp : Proof L Γ φ.all.not) : Proof L Γ φ.not.ex := by
  classical
  let names := φ.freeVarFinset ∪ Γ.biUnion (fun A => A.freeVarFinset)
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset names
  have hcφ : c ∉ φ.freeVarFinset := fun h => hc (Finset.mem_union_left _ h)
  have hcΓ : ∀ A ∈ Γ, c ∉ A.freeVarFinset := by
    intro A hA h
    exact hc (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A, hA, h⟩))
  apply Proof.classicalContradiction
  apply Proof.negElim (A := φ.all)
  · apply Proof.allIntroParameter c hcφ
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · simpa [BoundedFormula.not, BoundedFormula.ex, BoundedFormula.freeVarFinset,
          Bot.bot] using hcφ
      · exact hcΓ A hA
    · apply Proof.classicalContradiction
      apply Proof.negElim (A := φ.not.ex)
      · apply Proof.exIntro (φ := φ.not) (.var c)
        rw [instantiate_not]
        exact .assumption (by simp)
      · exact .assumption (by simp)
  · exact .weakening hp (Finset.subset_insert _ _)

end

theorem all_mem_iff (hS : Consistent S) (hC : Complete S) (hH : Henkin S)
    (φ : L.BoundedFormula ℕ 1) :
    φ.all ∈ S ↔ ∀ t : L.Term ℕ, instantiate φ t ∈ S := by
  classical
  constructor
  · intro hAll t
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption hAll
    exact (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, .allElim t hp⟩
  · intro ht
    by_contra hAll
    have hnAll := (not_mem_iff hS hC φ.all).mpr hAll
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption hnAll
    have hex := (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, notAll_exNot hp⟩
    obtain ⟨t, hnt⟩ := (ex_mem_iff hS hC hH φ.not).mp hex
    rw [instantiate_not] at hnt
    exact ((not_mem_iff hS hC _).mp hnt) (ht t)

theorem termEquivalent_equivalence (hS : Consistent S) (hC : Complete S) :
    Equivalence (TermEquivalent S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (derives_iff_mem hS hC _).mp ⟨∅, by simp, .equalIntro t⟩
  · intro t u h
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption h
    exact (derives_iff_mem hS hC _).mp ⟨Γ, hΓ, hp.equal_symmetry⟩
  · intro t u v htu huv
    obtain ⟨Γ, hΓ, hp⟩ := derives_assumption htu
    obtain ⟨Δ, hΔ, hq⟩ := derives_assumption huv
    apply (derives_iff_mem hS hC _).mp
    refine ⟨Γ ∪ Δ, ?_, Proof.equal_transitivity (.weakening hp Finset.subset_union_left)
      (.weakening hq Finset.subset_union_right)⟩
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hΓ hA
    · exact hΔ hA

private theorem derives_equalSlots {k : ℕ} (φ : L.BoundedFormula ℕ k)
    (ts us : Fin k → L.Term ℕ)
    (h : ∀ i, Derives S ((ts i).equal (us i)))
    (hp : Derives S (instantiateSlots φ ts)) :
    Derives S (instantiateSlots φ us) := by
  classical
  choose Γ hΓ hpΓ using h
  obtain ⟨Δ, hΔ, hpΔ⟩ := hp
  let U := Δ ∪ Finset.univ.biUnion Γ
  refine ⟨U, ?_, .equalSlots φ ts us (fun i => .weakening (hpΓ i) ?_)
    (.weakening hpΔ ?_)⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hΔ hA
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hA
      exact hΓ i hi
  · intro A hA
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩)
  · exact Finset.subset_union_left

theorem function_congruence (hS : Consistent S) (hC : Complete S)
    {k : ℕ} (f : L.Functions k) (ts us : Fin k → L.Term ℕ)
    (h : ∀ i, TermEquivalent S (ts i) (us i)) :
    TermEquivalent S (.func f ts) (.func f us) := by
  have hmem := derives_iff_mem hS hC
  let φ : L.BoundedFormula ℕ k :=
    (Term.func f (fun i => (ts i).relabel Sum.inl)).bdEqual
      (.func f (fun i => .var (.inr i)))
  have hinst (xs : Fin k → L.Term ℕ) :
      instantiateSlots φ xs = (Term.func f ts).equal (.func f xs) := by
    simp [φ, instantiateSlots, BoundedFormula.toFormula, Term.bdEqual,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Term.equal,
      Term.subst, Term.relabel]
  apply (hmem _).mp
  have heq : ∀ i, Derives S ((ts i).equal (us i)) :=
    fun i => derives_assumption (h i)
  have href : Derives S ((Term.func f ts).equal (.func f ts)) :=
    ⟨∅, by simp, .equalIntro _⟩
  rw [← hinst ts] at href
  have hd := derives_equalSlots φ ts us heq href
  simpa only [hinst] using hd

theorem relation_congruence (hS : Consistent S) (hC : Complete S)
    {k : ℕ} (r : L.Relations k) (ts us : Fin k → L.Term ℕ)
    (h : ∀ i, TermEquivalent S (ts i) (us i)) :
    r.formula ts ∈ S ↔ r.formula us ∈ S := by
  have hmem := derives_iff_mem hS hC
  let φ : L.BoundedFormula ℕ k := .rel r (fun i => .var (.inr i))
  have hinst (xs : Fin k → L.Term ℕ) : instantiateSlots φ xs = r.formula xs := by
    simp [φ, instantiateSlots, BoundedFormula.toFormula,
      BoundedFormula.subst, BoundedFormula.mapTermRel, Relations.formula, Relations.boundedFormula,
      Term.subst, Term.relabel]
  have heq : ∀ i, Derives S ((ts i).equal (us i)) := fun i => derives_assumption (h i)
  constructor
  · intro ht
    have hd : Derives S (instantiateSlots φ ts) := by rw [hinst]; exact derives_assumption ht
    exact (hmem _).mp (by simpa only [hinst] using derives_equalSlots φ ts us heq hd)
  · intro hu
    have heq' : ∀ i, Derives S ((us i).equal (ts i)) := by
      intro i
      obtain ⟨Γ, hΓ, hp⟩ := heq i
      exact ⟨Γ, hΓ, hp.equal_symmetry⟩
    have hd : Derives S (instantiateSlots φ us) := by rw [hinst]; exact derives_assumption hu
    exact (hmem _).mp (by simpa only [hinst] using derives_equalSlots φ us ts heq' hd)


end
end Lemmatheca.MathematicalLogic.HenkinCompleteness
