import Lemmatheca.ChangingLanguages.ChangingLanguages

/-! The paired Henkin construction in the shared first-order syntax. Named
sentences are encoded by `Formula.equivSentence`; their derivability is the
existing native nineteen-rule natural-deduction calculus in the expanded language. -/
namespace Lemmatheca.MathematicalLogic.JointConsistency
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.HenkinCompleteness
open Lemmatheca.MathematicalLogic.ChangingLanguages
universe u v w w'
variable {L L₀ L₁ L₂ : Language.{u, v}}
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The canonical map between supported sublanguages. -/
def inclusion {S T : Finset L.Symbols} (h : S ⊆ T) :
    supportedLanguage S →ᴸ supportedLanguage T where
  onFunction := fun {_} f => ⟨f.1, h f.2⟩
  onRelation := fun {_} R => ⟨R.1, h R.2⟩

abbrev commonLeft (S T : Finset L.Symbols) :
    supportedLanguage (S ∩ T) →ᴸ supportedLanguage S := inclusion Finset.inter_subset_left
abbrev commonRight (S T : Finset L.Symbols) :
    supportedLanguage (S ∩ T) →ᴸ supportedLanguage T := inclusion Finset.inter_subset_right

/-- No common sentence has opposite provable truth values on the two sides. -/
def Inseparable (j₁ : L₀ →ᴸ L₁) (j₂ : L₀ →ᴸ L₂)
    (T₁ : L₁.Theory) (T₂ : L₂.Theory) : Prop :=
  ¬ ∃ A : L₀.Sentence,
    Derives T₁ (j₁.onSentence A) ∧ Derives T₂ (j₂.onSentence A).not

/-- Interpret the free names as actual new constant symbols. -/
def namedTheory (U : Set (L.Formula ℕ)) : L[[ℕ]].Theory := Formula.equivSentence '' U

/-- Native derivability in the actual language expanded by common constants. -/
def NamedDerives (U : Set (L.Formula ℕ)) (A : L.Formula ℕ) : Prop :=
  Derives (namedTheory U) (Formula.equivSentence A)

/-- The construction permits separators to mention the common auxiliary names. -/
def NamedInseparable (j₁ : L₀ →ᴸ L₁) (j₂ : L₀ →ᴸ L₂)
    (U : Set (L₁.Formula ℕ)) (V : Set (L₂.Formula ℕ)) : Prop :=
  ¬ ∃ A : L₀.Formula ℕ,
    NamedDerives U (j₁.onFormula A) ∧ NamedDerives V (j₂.onFormula A).not

/-- Bind exactly one auxiliary name, leaving every other name free. -/
def bindName (c : ℕ) (A : L.Formula ℕ) : L.Formula ℕ :=
  (A.relabel (fun n => if n = c then Sum.inr () else Sum.inl n)).iExs Unit

/-- The explicit bridge used for semantic arguments about named native proofs. -/
theorem namedDerives_iff (U : Set (L.Formula ℕ)) (A : L.Formula ℕ) :
    NamedDerives U A ↔
      ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M] (a : ℕ → M),
        (∀ B ∈ U, B.Realize a) → A.Realize a := by
  constructor
  · intro h M _ _ a hU
    let := constantsOn.structure a
    have hmodel : M ⊨ namedTheory U := by
      constructor
      rintro B ⟨C, hC, rfl⟩
      exact (Formula.realize_equivSentence_symm M (Formula.equivSentence C) a).mp
        (by simpa using hU C hC)
    have hA := derives_sound h (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem (namedTheory U) hB)
    simpa using (Formula.realize_equivSentence_symm M (Formula.equivSentence A) a).mpr hA
  · intro h
    apply ChangingLanguages.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
    rw [Formula.realize_equivSentence]
    apply h M (fun n => (L.con n : M))
    intro B hB
    exact (Formula.realize_equivSentence M B).mp
      (Theory.realize_sentence_of_mem (namedTheory U) ⟨B, hB, rfl⟩)

private theorem derives_double_neg {α : Type*} {U : Set (L.Formula α)}
    {A : L.Formula α} (h : Derives U A) : Derives U A.not.not := by
  obtain ⟨Γ, hΓ, hp⟩ := h
  exact ⟨Γ, hΓ, .negIntro (.negElim (.weakening hp (Finset.subset_insert _ _))
    (.assumption (Finset.mem_insert_self _ _)))⟩

private theorem derives_not_bot {α : Type*} (U : Set (L.Formula α)) :
    Derives U (⊥ : L.Formula α).not := by
  exact ⟨∅, by simp, .negIntro (.assumption (by simp))⟩

private theorem named_mono {U V : Set (L.Formula ℕ)} {A : L.Formula ℕ}
    (h : NamedDerives U A) (hUV : U ⊆ V) : NamedDerives V A :=
  derives_mono h (Set.image_mono hUV)

private theorem named_assumption {U : Set (L.Formula ℕ)} {A : L.Formula ℕ}
    (h : A ∈ U) : NamedDerives U A := derives_assumption ⟨A, h, rfl⟩

theorem inseparable_consistent {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (h : Inseparable j₁ j₂ T₁ T₂) :
    Consistent T₁ ∧ Consistent T₂ := by
  constructor
  · intro hbot
    exact h ⟨⊥, hbot, derives_not_bot T₂⟩
  · intro hbot
    exact h ⟨(⊥ : L₀.Sentence).not, derives_not_bot T₁, derives_explosion hbot⟩

theorem inseparable_mono {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ U₁ : L₁.Theory} {T₂ U₂ : L₂.Theory}
    (h : Inseparable j₁ j₂ T₁ T₂) (h₁ : U₁ ⊆ T₁) (h₂ : U₂ ⊆ T₂) :
    Inseparable j₁ j₂ U₁ U₂ := by
  rintro ⟨A, hA, hnA⟩
  exact h ⟨A, derives_mono hA h₁, derives_mono hnA h₂⟩

theorem inseparable_symm {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (h : Inseparable j₁ j₂ T₁ T₂) :
    Inseparable j₂ j₁ T₂ T₁ := by
  rintro ⟨A, hA, hnA⟩
  exact h ⟨A.not, hnA, derives_double_neg hA⟩

private theorem named_consistent {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) : Consistent (namedTheory U) ∧ Consistent (namedTheory V) := by
  constructor
  · intro hbot
    exact h ⟨⊥, hbot, derives_not_bot (namedTheory V)⟩
  · intro hbot
    exact h ⟨(⊥ : L₀.Formula ℕ).not, derives_not_bot (namedTheory U), derives_explosion hbot⟩

private theorem open_consistent_of_named [Countable L.Symbols]
    {U : Set (L.Formula ℕ)} (h : Consistent (namedTheory U)) : Consistent U := by
  obtain ⟨M, inst, hne, _, hM⟩ := countable_model_existence h
  let := inst
  let := hne
  let : L.Structure M := (L.lhomWithConstants ℕ).reduct M
  apply consistent_of_model (fun n => (L.con n : M))
  intro A hA
  exact (Formula.realize_equivSentence M A).mp
    (Theory.realize_sentence_of_mem (namedTheory U) ⟨A, hA, rfl⟩)

theorem namedInseparable_consistent [Countable L₁.Symbols] [Countable L₂.Symbols]
    {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) : Consistent U ∧ Consistent V := by
  exact ⟨open_consistent_of_named (named_consistent h).1,
    open_consistent_of_named (named_consistent h).2⟩

theorem namedInseparable_mono {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U U' : Set (L₁.Formula ℕ)} {V V' : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) (h₁ : U' ⊆ U) (h₂ : V' ⊆ V) :
    NamedInseparable j₁ j₂ U' V' := by
  rintro ⟨A, hA, hnA⟩
  exact h ⟨A, named_mono hA h₁, named_mono hnA h₂⟩

theorem namedInseparable_symm {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) : NamedInseparable j₂ j₁ V U := by
  rintro ⟨A, hA, hnA⟩
  exact h ⟨A.not, hnA, derives_double_neg hA⟩

theorem realize_bindName {M : Type w} [L.Structure M] (a : ℕ → M)
    (c : ℕ) (A : L.Formula ℕ) :
    (bindName c A).Realize a ↔ ∃ x : M, A.Realize (Function.update a c x) := by
  simp only [bindName, Formula.realize_iExs, Formula.realize_relabel]
  have he (b : Unit → M) :
      Sum.elim a b ∘ (fun n => if n = c then Sum.inr () else Sum.inl n) =
        Function.update a c (b ()) := by
    funext n
    by_cases hn : n = c <;> simp [hn, Function.update]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b (), he b ▸ hb⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun _ => x, (he (fun _ => x)).symm ▸ hx⟩

theorem named_bind_intro {U : Set (L.Formula ℕ)} {A : L.Formula ℕ} (c : ℕ)
    (h : NamedDerives U A) : NamedDerives U (bindName c A) := by
  apply (namedDerives_iff _ _).mpr
  intro M _ _ a hU
  apply (realize_bindName a c A).mpr
  refine ⟨a c, ?_⟩
  simpa using (namedDerives_iff U A).mp h M a hU

private theorem realize_update_fresh {n : ℕ} {M : Type w} [L.Structure M]
    (A : L.BoundedFormula ℕ n) (c : ℕ) (hc : c ∉ A.freeVarFinset)
    (a : ℕ → M) (x : M) (xs : Fin n → M) :
    A.Realize (Function.update a c x) xs ↔ A.Realize a xs := by
  have h₁ := BoundedFormula.realize_restrictFreeVar (φ := A) (f := id)
    (v := fun i : A.freeVarFinset => a i) (xs := xs) a (fun _ => rfl)
  have h₂ := BoundedFormula.realize_restrictFreeVar (φ := A) (f := id)
    (v := fun i : A.freeVarFinset => a i) (xs := xs) (Function.update a c x)
    (fun i => by
      have hi : (i : ℕ) ≠ c := fun he => hc (he ▸ i.property)
      simp [Function.update, hi])
  exact h₂.symm.trans h₁

theorem named_bind_neg {U : Set (L.Formula ℕ)} {A : L.Formula ℕ} (c : ℕ)
    (hf : FreshFor c U) (h : NamedDerives U A.not) :
    NamedDerives U (bindName c A).not := by
  apply (namedDerives_iff _ _).mpr
  intro M _ _ a hU
  rw [Formula.realize_not, realize_bindName]
  rintro ⟨x, hx⟩
  have hU' : ∀ B ∈ U, B.Realize (Function.update a c x) := by
    intro B hB
    exact (realize_update_fresh B c (hf B hB) a x default).mpr (hU B hB)
  exact (namedDerives_iff U A.not).mp h M (Function.update a c x) hU' hx

private theorem realize_exClosure_iff {M : Type w} [L.Structure M] [Nonempty M]
    (A : L.Formula ℕ) : M ⊨ A.exClosure ↔ ∃ a : ℕ → M, A.Realize a := by
  rw [← Formula.exists_realize_equivSentence_iff_realize_exClosure]
  apply exists_congr
  intro a
  simpa using (Formula.realize_equivSentence_symm M (Formula.equivSentence A) a).symm

private theorem liftTheory_truth {M : Type w} [L.Structure M]
    (T : L.Theory) (h : M ⊨ T) (a : ℕ → M) :
    ∀ A ∈ liftTheory T, A.Realize a := by
  rintro A ⟨B, hB, rfl⟩
  simpa only [Formula.realize_relabel, Unique.eq_default, Sentence.Realize] using
    h.realize_of_mem B hB

theorem initial_names {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (h : Inseparable j₁ j₂ T₁ T₂) :
    NamedInseparable j₁ j₂ (liftTheory T₁) (liftTheory T₂) := by
  rintro ⟨A, h₁, h₂⟩
  apply h
  refine ⟨A.exClosure, ChangingLanguages.deductive_completeness ?_,
    ChangingLanguages.deductive_completeness ?_⟩
  · apply Theory.models_sentence_iff.mpr
    intro M
    let : L₀.Structure M := j₁.reduct M
    rw [j₁.realize_onSentence (M := M), realize_exClosure_iff]
    let a : ℕ → M := fun _ => Classical.choice inferInstance
    refine ⟨a, ?_⟩
    rw [← j₁.realize_onFormula (M := M)]
    exact (namedDerives_iff _ _).mp h₁ M a (liftTheory_truth T₁ M.is_model a)
  · apply Theory.models_sentence_iff.mpr
    intro M
    let : L₀.Structure M := j₂.reduct M
    rw [Sentence.realize_not, j₂.realize_onSentence (M := M), realize_exClosure_iff]
    rintro ⟨a, ha⟩
    have hn := (namedDerives_iff _ _).mp h₂ M a (liftTheory_truth T₂ M.is_model a)
    apply hn
    change Formula.Realize (j₂.onFormula A) a
    rwa [j₂.realize_onFormula (M := M)]

theorem pair_decision {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) (A : L₁.Formula ℕ) :
    NamedInseparable j₁ j₂ (insert A U) V ∨
      NamedInseparable j₁ j₂ (insert A.not U) V := by
  by_contra hchoices
  obtain ⟨hleft, hright⟩ := not_or.mp hchoices
  obtain ⟨B, hUB, hVnB⟩ := Classical.not_not.mp hleft
  obtain ⟨C, hUC, hVnC⟩ := Classical.not_not.mp hright
  apply h
  refine ⟨B ⊔ C, (namedDerives_iff _ _).mpr ?_, (namedDerives_iff _ _).mpr ?_⟩
  · intro M _ _ a hU
    rw [show j₁.onFormula (B ⊔ C) = j₁.onFormula B ⊔ j₁.onFormula C from rfl,
      Formula.realize_sup]
    by_cases hA : A.Realize a
    · left
      apply (namedDerives_iff _ _).mp hUB M a
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact hA
      · exact hU D hD
    · right
      apply (namedDerives_iff _ _).mp hUC M a
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact hA
      · exact hU D hD
  · intro M _ _ a hV
    rw [show j₂.onFormula (B ⊔ C) = j₂.onFormula B ⊔ j₂.onFormula C from rfl,
      Formula.realize_not, Formula.realize_sup]
    exact fun hBC => hBC.elim ((namedDerives_iff _ _).mp hVnB M a hV)
      ((namedDerives_iff _ _).mp hVnC M a hV)

private theorem realize_map_bindName (j : L₀ →ᴸ L₁) {M : Type w} [L₁.Structure M]
    (a : ℕ → M) (c : ℕ) (A : L₀.Formula ℕ) :
    (j.onFormula (bindName c A)).Realize a ↔
      ∃ x : M, (j.onFormula A).Realize (Function.update a c x) := by
  let : L₀.Structure M := j.reduct M
  simpa only [j.realize_onFormula] using realize_bindName a c A

theorem pair_witness {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) (φ : L₁.BoundedFormula ℕ 1) (c : ℕ)
    (hcU : FreshFor c U) (hcV : FreshFor c V) (hcφ : c ∉ φ.freeVarFinset) :
    NamedInseparable j₁ j₂ (insert (witnessAxiom φ c) U) V := by
  rintro ⟨A, hUA, hVnA⟩
  apply h
  refine ⟨bindName c A, (namedDerives_iff _ _).mpr ?_, (namedDerives_iff _ _).mpr ?_⟩
  · intro M _ _ a hU
    rw [realize_map_bindName]
    have hw : ∃ x : M, (witnessAxiom φ c).Realize (Function.update a c x) := by
      by_cases hex : Formula.Realize φ.ex a
      · obtain ⟨x, hx⟩ := (BoundedFormula.realize_ex).mp hex
        refine ⟨x, ?_⟩
        change (Formula.Realize φ.ex (Function.update a c x)) →
          (instantiate φ (.var c)).Realize (Function.update a c x)
        intro _
        rw [instantiate_realize]
        have hs : (Fin.snoc (default : Fin 0 → M) x : Fin 1 → M) = fun _ => x := by
          funext i
          have hi : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
          subst i
          rfl
        simpa [hs, Term.realize, Function.update] using
          (realize_update_fresh φ c hcφ a x (Fin.snoc default x)).mpr hx
      · refine ⟨a c, ?_⟩
        change (Formula.Realize φ.ex (Function.update a c (a c))) → _
        intro hbad
        exact False.elim (hex (by simpa using hbad))
    obtain ⟨x, hx⟩ := hw
    refine ⟨x, (namedDerives_iff _ _).mp hUA M (Function.update a c x) ?_⟩
    intro B hB
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · exact hx
    · exact (realize_update_fresh B c (hcU B hB) a x default).mpr (hU B hB)
  · intro M _ _ a hV
    change ¬ (j₂.onFormula (bindName c A)).Realize a
    rw [realize_map_bindName]
    rintro ⟨x, hx⟩
    apply (namedDerives_iff _ _).mp hVnA M (Function.update a c x) ?_ hx
    intro B hB
    exact (realize_update_fresh B c (hcV B hB) a x default).mpr (hV B hB)

private theorem named_derives_stage (D : ℕ → Set (L.Formula ℕ)) (hD : Monotone D)
    {A : L.Formula ℕ} (h : NamedDerives (⋃ n, D n) A) :
    ∃ n, NamedDerives (D n) A := by
  obtain ⟨Γ, hΓ, hp⟩ := h
  have hs : ∀ B : Γ, ∃ n, B.1 ∈ namedTheory (D n) := by
    intro B
    obtain ⟨C, hC, hCB⟩ := hΓ B.property
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hC
    exact ⟨n, C, hn, hCB⟩
  choose r hr using hs
  refine ⟨Finset.univ.sup r, Γ, ?_, hp⟩
  intro B hB
  obtain ⟨C, hC, hCB⟩ := hr ⟨B, hB⟩
  exact ⟨C, hD (Finset.le_sup (Finset.mem_univ (⟨B, hB⟩ : Γ))) hC, hCB⟩

theorem pair_limit {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    (U : ℕ → Set (L₁.Formula ℕ)) (V : ℕ → Set (L₂.Formula ℕ))
    (hU : Monotone U) (hV : Monotone V) (h : ∀ n, NamedInseparable j₁ j₂ (U n) (V n)) :
    NamedInseparable j₁ j₂ (⋃ n, U n) (⋃ n, V n) := by
  rintro ⟨A, hA, hnA⟩
  obtain ⟨n, hn⟩ := named_derives_stage U hU hA
  obtain ⟨m, hm⟩ := named_derives_stage V hV hnA
  exact h (max n m) ⟨A, named_mono hn (hU (le_max_left _ _)),
    named_mono hm (hV (le_max_right _ _))⟩

/-- All conclusions needed from the coordinated countable construction. -/
structure PairedExtension (j₁ : L₀ →ᴸ L₁) (j₂ : L₀ →ᴸ L₂)
    (T₁ : L₁.Theory) (T₂ : L₂.Theory) where
  left : Set (L₁.Formula ℕ)
  right : Set (L₂.Formula ℕ)
  left_contains : liftTheory T₁ ⊆ left
  right_contains : liftTheory T₂ ⊆ right
  left_consistent : Consistent left
  right_consistent : Consistent right
  left_complete : Complete left
  right_complete : Complete right
  left_henkin : Henkin left
  right_henkin : Henkin right
  inseparable : NamedInseparable j₁ j₂ left right

private structure FiniteStage (j₁ : L₀ →ᴸ L₁) (j₂ : L₀ →ᴸ L₂)
    (T₁ : L₁.Theory) (T₂ : L₂.Theory) where
  left : Finset (L₁.Formula ℕ)
  right : Finset (L₂.Formula ℕ)
  valid : NamedInseparable j₁ j₂ (liftTheory T₁ ∪ ↑left) (liftTheory T₂ ∪ ↑right)

private def FiniteStage.swap {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂) :
    FiniteStage j₂ j₁ T₂ T₁ := ⟨s.right, s.left, namedInseparable_symm s.valid⟩

private def FiniteStage.decide {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (A : L₁.Formula ℕ) : FiniteStage j₁ j₂ T₁ T₂ := by
  classical
  let B := if NamedInseparable j₁ j₂ (insert A (liftTheory T₁ ∪ ↑s.left))
      (liftTheory T₂ ∪ ↑s.right) then A else A.not
  refine ⟨insert B s.left, s.right, ?_⟩
  simp only [Finset.coe_insert, Set.union_insert]
  dsimp only [B]
  split
  · assumption
  · exact (pair_decision s.valid A).resolve_left ‹_›

private theorem FiniteStage.decide_contains {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (A : L₁.Formula ℕ) : s.left ⊆ (s.decide A).left ∧ s.right = (s.decide A).right :=
  ⟨Finset.subset_insert _ _, rfl⟩

private theorem FiniteStage.decide_mem {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (A : L₁.Formula ℕ) : A ∈ (s.decide A).left ∨ A.not ∈ (s.decide A).left := by
  classical
  dsimp only [FiniteStage.decide]
  split <;> simp

private def FiniteStage.freshName {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (φ : L₁.BoundedFormula ℕ 1) : ℕ := Classical.choose
  ((s.left.biUnion BoundedFormula.freeVarFinset ∪
    s.right.biUnion BoundedFormula.freeVarFinset ∪ φ.freeVarFinset).exists_notMem)

private theorem FiniteStage.freshName_spec {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (φ : L₁.BoundedFormula ℕ 1) :
    FreshFor (s.freshName φ) (liftTheory T₁ ∪ ↑s.left) ∧
    FreshFor (s.freshName φ) (liftTheory T₂ ∪ ↑s.right) ∧
    s.freshName φ ∉ φ.freeVarFinset := by
  have hn := Classical.choose_spec
    ((s.left.biUnion BoundedFormula.freeVarFinset ∪
      s.right.biUnion BoundedFormula.freeVarFinset ∪ φ.freeVarFinset).exists_notMem)
  change s.freshName φ ∉ _ at hn
  refine ⟨?_, ?_, fun h => hn (Finset.mem_union_right _ h)⟩
  · intro A hA hc
    rcases hA with hA | hA
    · exact fresh_liftTheory T₁ _ A hA hc
    · exact hn (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨A, hA, hc⟩)))
  · intro A hA hc
    rcases hA with hA | hA
    · exact fresh_liftTheory T₂ _ A hA hc
    · exact hn (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨A, hA, hc⟩)))

private def FiniteStage.witness {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (φ : L₁.BoundedFormula ℕ 1) : FiniteStage j₁ j₂ T₁ T₂ := by
  refine ⟨insert (witnessAxiom φ (s.freshName φ)) s.left, s.right, ?_⟩
  simp only [Finset.coe_insert, Set.union_insert]
  exact pair_witness s.valid φ (s.freshName φ) (s.freshName_spec φ).1
    (s.freshName_spec φ).2.1 (s.freshName_spec φ).2.2

private theorem advance_stage {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (s : FiniteStage j₁ j₂ T₁ T₂)
    (A : L₁.Formula ℕ) (B : L₂.Formula ℕ)
    (φ : L₁.BoundedFormula ℕ 1) (ψ : L₂.BoundedFormula ℕ 1) :
    ∃ s' : FiniteStage j₁ j₂ T₁ T₂,
      s.left ⊆ s'.left ∧ s.right ⊆ s'.right ∧
      (A ∈ s'.left ∨ A.not ∈ s'.left) ∧ (B ∈ s'.right ∨ B.not ∈ s'.right) ∧
      (∃ c, witnessAxiom φ c ∈ s'.left) ∧ (∃ c, witnessAxiom ψ c ∈ s'.right) := by
  let s₁ := s.decide A
  let s₂ := s₁.witness φ
  let s₃ := (s₂.swap.decide B).swap
  let s₄ := (s₃.swap.witness ψ).swap
  have h₁ : s.left ⊆ s₁.left := (s.decide_contains A).1
  have h₂ : s₁.left ⊆ s₂.left := Finset.subset_insert _ _
  have h₃ : s₂.left = s₃.left := rfl
  have h₄ : s₃.left = s₄.left := rfl
  have k₁ : s.right = s₁.right := rfl
  have k₂ : s₁.right = s₂.right := rfl
  have k₃ : s₂.right ⊆ s₃.right := Finset.subset_insert _ _
  have k₄ : s₃.right ⊆ s₄.right := Finset.subset_insert _ _
  have hleft : s₁.left ⊆ s₄.left := by simpa only [← h₄, ← h₃] using h₂
  have hright : s₂.right ⊆ s₄.right := k₃.trans k₄
  refine ⟨s₄, h₁.trans hleft, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [k₁, k₂] using hright
  · exact (s.decide_mem A).imp (hleft ·) (hleft ·)
  · exact (s₂.swap.decide_mem B).imp (k₄ ·) (k₄ ·)
  · refine ⟨s₁.freshName φ, ?_⟩
    have hm : witnessAxiom φ (s₁.freshName φ) ∈ s₂.left := Finset.mem_insert_self _ _
    simpa only [← h₄, ← h₃] using hm
  · exact ⟨s₃.swap.freshName ψ, Finset.mem_insert_self _ _⟩

theorem paired_henkin_extension [Countable L₁.Symbols] [Countable L₂.Symbols]
    {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {T₁ : L₁.Theory} {T₂ : L₂.Theory} (h : Inseparable j₁ j₂ T₁ T₂) :
    Nonempty (PairedExtension j₁ j₂ T₁ T₂) := by
  let : Countable (L₁.BoundedFormula ℕ 1) := Function.Injective.countable
    (f := fun φ : L₁.BoundedFormula ℕ 1 => (⟨1, φ⟩ : Σ n, L₁.BoundedFormula ℕ n))
    sigma_mk_injective
  let : Countable (L₂.BoundedFormula ℕ 1) := Function.Injective.countable
    (f := fun φ : L₂.BoundedFormula ℕ 1 => (⟨1, φ⟩ : Σ n, L₂.BoundedFormula ℕ n))
    sigma_mk_injective
  obtain ⟨e₁, he₁⟩ := exists_surjective_nat (L₁.Formula ℕ)
  obtain ⟨e₂, he₂⟩ := exists_surjective_nat (L₂.Formula ℕ)
  obtain ⟨b₁, hb₁⟩ := exists_surjective_nat (L₁.BoundedFormula ℕ 1)
  obtain ⟨b₂, hb₂⟩ := exists_surjective_nat (L₂.BoundedFormula ℕ 1)
  let start : FiniteStage j₁ j₂ T₁ T₂ :=
    ⟨∅, ∅, by simpa only [Finset.coe_empty, Set.union_empty] using initial_names h⟩
  let step (n : ℕ) (s : FiniteStage j₁ j₂ T₁ T₂) : FiniteStage j₁ j₂ T₁ T₂ :=
    Classical.choose (advance_stage s (e₁ n) (e₂ n) (b₁ n) (b₂ n))
  let seq : ℕ → FiniteStage j₁ j₂ T₁ T₂ := Nat.rec start step
  have hs (n : ℕ) :
      (seq n).left ⊆ (seq (n + 1)).left ∧ (seq n).right ⊆ (seq (n + 1)).right ∧
      (e₁ n ∈ (seq (n + 1)).left ∨ (e₁ n).not ∈ (seq (n + 1)).left) ∧
      (e₂ n ∈ (seq (n + 1)).right ∨ (e₂ n).not ∈ (seq (n + 1)).right) ∧
      (∃ c, witnessAxiom (b₁ n) c ∈ (seq (n + 1)).left) ∧
      (∃ c, witnessAxiom (b₂ n) c ∈ (seq (n + 1)).right) :=
    Classical.choose_spec (advance_stage (seq n) (e₁ n) (e₂ n) (b₁ n) (b₂ n))
  let U (n : ℕ) : Set (L₁.Formula ℕ) := liftTheory T₁ ∪ ↑(seq n).left
  let V (n : ℕ) : Set (L₂.Formula ℕ) := liftTheory T₂ ∪ ↑(seq n).right
  have hU : Monotone U := by
    apply monotone_nat_of_le_succ
    intro n A hA
    exact hA.elim Or.inl (fun hA => Or.inr ((hs n).1 hA))
  have hV : Monotone V := by
    apply monotone_nat_of_le_succ
    intro n A hA
    exact hA.elim Or.inl (fun hA => Or.inr ((hs n).2.1 hA))
  have hpair := pair_limit U V hU hV (fun n => (seq n).valid)
  have hcons := namedInseparable_consistent hpair
  refine ⟨{
    left := ⋃ n, U n
    right := ⋃ n, V n
    left_contains := fun A hA => Set.mem_iUnion.mpr ⟨0, Or.inl hA⟩
    right_contains := fun A hA => Set.mem_iUnion.mpr ⟨0, Or.inl hA⟩
    left_consistent := hcons.1
    right_consistent := hcons.2
    left_complete := ?_
    right_complete := ?_
    left_henkin := ?_
    right_henkin := ?_
    inseparable := hpair }⟩
  · intro A
    obtain ⟨n, rfl⟩ := he₁ A
    exact (hs n).2.2.1.imp
      (fun hA => Set.mem_iUnion.mpr ⟨n + 1, Or.inr hA⟩)
      (fun hA => Set.mem_iUnion.mpr ⟨n + 1, Or.inr hA⟩)
  · intro A
    obtain ⟨n, rfl⟩ := he₂ A
    exact (hs n).2.2.2.1.imp
      (fun hA => Set.mem_iUnion.mpr ⟨n + 1, Or.inr hA⟩)
      (fun hA => Set.mem_iUnion.mpr ⟨n + 1, Or.inr hA⟩)
  · intro φ
    obtain ⟨n, rfl⟩ := hb₁ φ
    obtain ⟨c, hc⟩ := (hs n).2.2.2.2.1
    exact ⟨c, Set.mem_iUnion.mpr ⟨n + 1, Or.inr hc⟩⟩
  · intro φ
    obtain ⟨n, rfl⟩ := hb₂ φ
    obtain ⟨c, hc⟩ := (hs n).2.2.2.2.2
    exact ⟨c, Set.mem_iUnion.mpr ⟨n + 1, Or.inr hc⟩⟩

theorem common_agreement {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (h : NamedInseparable j₁ j₂ U V) (hU : Complete U) (hV : Complete V)
    (A : L₀.Formula ℕ) : j₁.onFormula A ∈ U ↔ j₂.onFormula A ∈ V := by
  constructor
  · intro hA
    by_contra hnA
    exact h ⟨A, named_assumption hA, named_assumption ((hV _).resolve_left hnA)⟩
  · intro hA
    by_contra hnA
    exact namedInseparable_symm h ⟨A, named_assumption hA,
      named_assumption ((hU _).resolve_left hnA)⟩

theorem every_term_named {U : Set (L.Formula ℕ)}
    (hU : Consistent U) (hC : Complete U) (hH : Henkin U) (t : L.Term ℕ) :
    ∃ n : ℕ, TermEquivalent U t (.var n) := by
  let φ : L.BoundedFormula ℕ 1 := (.var (.inr 0) : L.Term (ℕ ⊕ Fin 1)).bdEqual
    (t.relabel Sum.inl)
  have hinst (s : L.Term ℕ) : instantiate φ s = s.equal t := by
    simp [φ, instantiate, BoundedFormula.subst, BoundedFormula.mapTermRel,
      BoundedFormula.toFormula, Term.bdEqual, Term.equal, Term.subst,
      Term.relabel]
  have hex : Derives U φ.ex := by
    refine ⟨∅, by simp, .exIntro t ?_⟩
    rw [hinst]
    exact .equalIntro t
  obtain ⟨n, hn⟩ := hH φ
  have heq : Derives U ((Term.var n).equal t) := by
    rw [← hinst]
    exact derives_imp_elim (derives_assumption hn) hex
  obtain ⟨Γ, hΓ, hp⟩ := heq
  exact ⟨n, (derives_iff_mem hU hC _).mp ⟨Γ, hΓ, hp.equal_symmetry⟩⟩

private theorem nameValue_surjective {U : Set (L.Formula ℕ)}
    (hU : Consistent U) (hC : Complete U) (hH : Henkin U) :
    Function.Surjective (nameValue U hU hC) := by
  intro x
  obtain ⟨t, rfl⟩ := Quotient.exists_rep x
  obtain ⟨n, hn⟩ := every_term_named hU hC hH t
  exact ⟨n, (Quotient.sound hn).symm⟩

theorem common_term_isomorphism
    {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (hU : Consistent U) (hUC : Complete U) (hUH : Henkin U)
    (hV : Consistent V) (hVC : Complete V) (hVH : Henkin V)
    (h : ∀ A : L₀.Formula ℕ, j₁.onFormula A ∈ U ↔ j₂.onFormula A ∈ V) :
    ∃ e : @Language.Equiv L₀ (TermModel U hU hUC) (TermModel V hV hVC)
      (j₁.reduct _) (j₂.reduct _),
      ∀ n, e (nameValue U hU hUC n) = nameValue V hV hVC n := by
  let a := nameValue U hU hUC
  let b := nameValue V hV hVC
  have ha : Function.Surjective a := nameValue_surjective hU hUC hUH
  have hb : Function.Surjective b := nameValue_surjective hV hVC hVH
  have heq (m n : ℕ) : a m = a n ↔ b m = b n := by
    have hc := h ((Term.var m).equal (.var n))
    change TermEquivalent U (.var m) (.var n) ↔ TermEquivalent V (.var m) (.var n) at hc
    exact ⟨fun hx => Quotient.sound (hc.mp (Quotient.exact hx)),
      fun hx => Quotient.sound (hc.mpr (Quotient.exact hx))⟩
  let r (x : TermModel U hU hUC) : ℕ := Classical.choose (ha x)
  have hr (x : TermModel U hU hUC) : a (r x) = x := Classical.choose_spec (ha x)
  let f (x : TermModel U hU hUC) := b (r x)
  have hf (n : ℕ) : f (a n) = b n := (heq _ _).mp (hr (a n))
  have hfi : Function.Injective f := by
    intro x y hxy
    rw [← hr x, ← hr y]
    exact (heq _ _).mpr hxy
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨n, rfl⟩ := hb y
    exact ⟨a n, hf n⟩
  let e₀ : TermModel U hU hUC ≃ TermModel V hV hVC := Equiv.ofBijective f ⟨hfi, hfs⟩
  have he (n : ℕ) : e₀ (a n) = b n := hf n
  let : L₀.Structure (TermModel U hU hUC) := j₁.reduct _
  let : L₀.Structure (TermModel V hV hVC) := j₂.reduct _
  refine ⟨{ toEquiv := e₀, map_fun' := ?_, map_rel' := ?_ }, he⟩
  · intro k F xs
    choose ns hns using fun i => ha (xs i)
    have hxs : xs = fun i => a (ns i) := funext (fun i => (hns i).symm)
    have hys : e₀ ∘ xs = fun i => b (ns i) := by
      funext i
      dsimp only [Function.comp_apply]
      rw [← hns i, he]
    let t : L₀.Term ℕ := .func F (fun i => .var (ns i))
    obtain ⟨m, hm⟩ := every_term_named hU hUC hUH (j₁.onTerm t)
    have hm' : TermEquivalent V (j₂.onTerm t) (.var m) := by
      exact (h (t.equal (.var m))).mp hm
    have hv₁ : (j₁.onTerm t).realize a = a m :=
      (term_value hU hUC _).trans (Quotient.sound hm)
    have hv₂ : (j₂.onTerm t).realize b = b m :=
      (term_value hV hVC _).trans (Quotient.sound hm')
    change e₀ (Structure.funMap (L := L₁) (j₁.onFunction F) xs) =
      Structure.funMap (L := L₂) (j₂.onFunction F) (e₀ ∘ xs)
    rw [hys, hxs]
    change e₀ ((j₁.onTerm t).realize a) = (j₂.onTerm t).realize b
    rw [hv₁, he, hv₂]
  · intro k R xs
    choose ns hns using fun i => ha (xs i)
    have hxs : xs = fun i => a (ns i) := funext (fun i => (hns i).symm)
    have hys : e₀ ∘ xs = fun i => b (ns i) := by
      funext i
      dsimp only [Function.comp_apply]
      rw [← hns i, he]
    let A : L₀.Formula ℕ := R.formula (fun i => .var (ns i))
    have ht₁ : Structure.RelMap (L := L₁) (j₁.onRelation R) (fun i => a (ns i)) ↔
        j₁.onFormula A ∈ U := by
      exact formula_truth hU hUC hUH (j₁.onFormula A)
    have ht₂ : Structure.RelMap (L := L₂) (j₂.onRelation R) (fun i => b (ns i)) ↔
        j₂.onFormula A ∈ V := by
      exact formula_truth hV hVC hVH (j₂.onFormula A)
    change Structure.RelMap (L := L₂) (j₂.onRelation R) (e₀ ∘ xs) ↔
      Structure.RelMap (L := L₁) (j₁.onRelation R) xs
    rw [hys, hxs]
    exact ht₂.trans ((h A).symm.trans ht₁.symm)

theorem common_named_term_isomorphism
    {j₁ : L₀ →ᴸ L₁} {j₂ : L₀ →ᴸ L₂}
    {U : Set (L₁.Formula ℕ)} {V : Set (L₂.Formula ℕ)}
    (hU : Consistent U) (hUC : Complete U) (hUH : Henkin U)
    (hV : Consistent V) (hVC : Complete V) (hVH : Henkin V)
    (h : ∀ A : L₀.Formula ℕ, j₁.onFormula A ∈ U ↔ j₂.onFormula A ∈ V) :
    ∃ e : @Language.Equiv L₀[[ℕ]] (TermModel U hU hUC) (TermModel V hV hVC)
      ((j₁.addConstants ℕ).reduct _) ((j₂.addConstants ℕ).reduct _),
      ∀ n, e (nameValue U hU hUC n) = nameValue V hV hVC n := by
  obtain ⟨e, he⟩ := common_term_isomorphism hU hUC hUH hV hVC hVH h
  let : L₀.Structure (TermModel U hU hUC) := j₁.reduct _
  let : L₀.Structure (TermModel V hV hVC) := j₂.reduct _
  let : L₀[[ℕ]].Structure (TermModel U hU hUC) := (j₁.addConstants ℕ).reduct _
  let : L₀[[ℕ]].Structure (TermModel V hV hVC) := (j₂.addConstants ℕ).reduct _
  refine ⟨{ toEquiv := e.toEquiv, map_fun' := ?_, map_rel' := ?_ }, he⟩
  · intro k F xs
    cases F with
    | inl F => exact e.map_fun F xs
    | inr c =>
      cases k with
      | zero => exact he c
      | succ k => exact isEmptyElim c
  · intro k R xs
    cases R with
    | inl R => exact e.map_rel R xs
    | inr R => exact isEmptyElim R

/-- Keep the first structure; transport private second-side symbols, then use
constant functions and false relations for all unused ambient symbols. -/
@[instance_reducible]
def glueStructure (S T : Finset L.Symbols) {M : Type w} {N : Type w'}
    [(supportedLanguage S).Structure M] [(supportedLanguage T).Structure N]
    (e : M ≃ N) (m₀ : M) : L.Structure M where
  funMap := fun {n} f xs =>
    if hf : Sum.inl ⟨n, f⟩ ∈ S then
      Structure.funMap (L := supportedLanguage S) ⟨f, hf⟩ xs
    else if hf : Sum.inl ⟨n, f⟩ ∈ T then
      e.symm (Structure.funMap (L := supportedLanguage T) ⟨f, hf⟩ (e ∘ xs))
    else m₀
  RelMap := fun {n} R xs =>
    if hR : Sum.inr ⟨n, R⟩ ∈ S then
      Structure.RelMap (L := supportedLanguage S) ⟨R, hR⟩ xs
    else if hR : Sum.inr ⟨n, R⟩ ∈ T then
      Structure.RelMap (L := supportedLanguage T) ⟨R, hR⟩ (e ∘ xs)
    else False

theorem glue_structure_models (S T : Finset L.Symbols)
    {M : Type w} {N : Type w'}
    [sM : (supportedLanguage S).Structure M] [sN : (supportedLanguage T).Structure N]
    [Nonempty M] [Nonempty N]
    (e : @Language.Equiv (supportedLanguage (S ∩ T)) M N
      ((commonLeft S T).reduct M) ((commonRight S T).reduct N))
    (T₁ : (supportedLanguage S).Theory) (T₂ : (supportedLanguage T).Theory)
    (h₁ : M ⊨ T₁) (h₂ : N ⊨ T₂) (m₀ : M) :
    let e₀ : M ≃ N := @Language.Equiv.toEquiv _ _ _
      ((commonLeft S T).reduct M) ((commonRight S T).reduct N) e
    letI := glueStructure S T e₀ m₀
    M ⊨ ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂) := by
  classical
  let e₀ : M ≃ N := @Language.Equiv.toEquiv _ _ _
    ((commonLeft S T).reduct M) ((commonRight S T).reduct N) e
  let : L.Structure M := glueStructure S T e₀ m₀
  let hleft : (supportInclusion S).IsExpansionOn M := {
    map_onFunction := by
      intro n f xs
      rcases f with ⟨f, hf⟩
      change (glueStructure S T e₀ m₀).funMap f xs = _
      exact dite_eq_left hf
    map_onRelation := by
      intro n R xs
      rcases R with ⟨R, hR⟩
      change (glueStructure S T e₀ m₀).RelMap R xs = _
      exact dite_eq_left hR }
  have hS : M ⊨ (supportInclusion S).onTheory T₁ :=
    (LHom.onTheory_model _ _).mpr h₁
  have hT : M ⊨ (supportInclusion T).onTheory T₂ := by
    let : (supportedLanguage T).Structure M := (supportInclusion T).reduct M
    let eT : M ≃[supportedLanguage T] N := {
      toEquiv := e₀
      map_fun' := by
        intro n f xs
        rcases f with ⟨f, hfT⟩
        change e₀ ((glueStructure S T e₀ m₀).funMap f xs) =
          @Structure.funMap (supportedLanguage T) N sN n ⟨f, hfT⟩ (e₀ ∘ xs)
        by_cases hfS : Sum.inl ⟨n, f⟩ ∈ S
        · rw [show (glueStructure S T e₀ m₀).funMap f xs =
              @Structure.funMap (supportedLanguage S) M sM n ⟨f, hfS⟩ xs by
              exact dite_eq_left hfS
            ]
          exact @Language.Equiv.map_fun' _ _ _
            ((commonLeft S T).reduct M) ((commonRight S T).reduct N)
            e n ⟨f, Finset.mem_inter.mpr ⟨hfS, hfT⟩⟩ xs
        · have hv : (glueStructure S T e₀ m₀).funMap f xs =
              e₀.symm (@Structure.funMap (supportedLanguage T) N sN n ⟨f, hfT⟩ (e₀ ∘ xs)) :=
              (dite_eq_right hfS).trans (dite_eq_left hfT)
          rw [hv]
          exact e₀.apply_symm_apply _
      map_rel' := by
        intro n R xs
        rcases R with ⟨R, hRT⟩
        change @Structure.RelMap (supportedLanguage T) N sN n ⟨R, hRT⟩ (e₀ ∘ xs) ↔
          (glueStructure S T e₀ m₀).RelMap R xs
        by_cases hRS : Sum.inr ⟨n, R⟩ ∈ S
        · rw [show (glueStructure S T e₀ m₀).RelMap R xs =
              @Structure.RelMap (supportedLanguage S) M sM n ⟨R, hRS⟩ xs by
              exact dite_eq_left hRS
            ]
          exact @Language.Equiv.map_rel' _ _ _
            ((commonLeft S T).reduct M) ((commonRight S T).reduct N)
            e n ⟨R, Finset.mem_inter.mpr ⟨hRS, hRT⟩⟩ xs
        · have hv : (glueStructure S T e₀ m₀).RelMap R xs =
              @Structure.RelMap (supportedLanguage T) N sN n ⟨R, hRT⟩ (e₀ ∘ xs) :=
              (dite_eq_right hRS).trans (dite_eq_left hRT)
          rw [hv] }
    have hM : M ⊨ T₂ := ⟨fun A hA =>
      (StrongHomClass.realize_sentence eT A).mpr (h₂.realize_of_mem A hA)⟩
    exact (LHom.onTheory_model _ _).mpr hM
  exact hS.union hT

theorem glue_models (S T : Finset L.Symbols)
    {M : Type w} {N : Type w'}
    [(supportedLanguage S).Structure M] [(supportedLanguage T).Structure N]
    [Nonempty M] [Nonempty N]
    (e : @Language.Equiv (supportedLanguage (S ∩ T)) M N
      ((commonLeft S T).reduct M) ((commonRight S T).reduct N))
    (T₁ : (supportedLanguage S).Theory) (T₂ : (supportedLanguage T).Theory)
    (h₁ : M ⊨ T₁) (h₂ : N ⊨ T₂) :
    ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂).IsSatisfiable  := by
  let e₀ : M ≃ N := @Language.Equiv.toEquiv _ _ _
    ((commonLeft S T).reduct M) ((commonRight S T).reduct N) e
  let m₀ : M := Classical.choice inferInstance
  let : L.Structure M := glueStructure S T e₀ m₀
  let : M ⊨ ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂) :=
    glue_structure_models S T e T₁ T₂ h₁ h₂ m₀
  exact Theory.Model.isSatisfiable M

/-- The finite-vocabulary theorem needed for sentence interpolation. -/
theorem joint_model_iff (S T : Finset L.Symbols)
    (T₁ : (supportedLanguage S).Theory) (T₂ : (supportedLanguage T).Theory) :
    ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂).IsSatisfiable ↔
      Inseparable (commonLeft S T) (commonRight S T) T₁ T₂ := by
  constructor
  · intro hsat
    rintro ⟨A, hA, hnA⟩
    let M := hsat.some
    have ha := derives_sound (derives_map (supportInclusion S) hA) (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem
        ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂) (Or.inl hB))
    have hna := derives_sound (derives_map (supportInclusion T) hnA) (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem
        ((supportInclusion S).onTheory T₁ ∪ (supportInclusion T).onTheory T₂) (Or.inr hB))
    have hsame : (supportInclusion S).onSentence ((commonLeft S T).onSentence A) =
        (supportInclusion T).onSentence ((commonRight S T).onSentence A) := by
      calc
        _ = ((supportInclusion S).comp (commonLeft S T)).onSentence A :=
          (congrFun (LHom.comp_onBoundedFormula (supportInclusion S) (commonLeft S T)) A).symm
        _ = ((supportInclusion T).comp (commonRight S T)).onSentence A := rfl
        _ = _ := congrFun (LHom.comp_onBoundedFormula (supportInclusion T) (commonRight S T)) A
    apply hna
    change Formula.Realize ((supportInclusion T).onSentence ((commonRight S T).onSentence A)) default
    rw [← hsame]
    exact ha
  · intro h
    obtain ⟨H⟩ := paired_henkin_extension h
    let M := TermModel H.left H.left_consistent H.left_complete
    let N := TermModel H.right H.right_consistent H.right_complete
    let : Nonempty M := term_model_nonempty H.left_consistent H.left_complete
    let : Nonempty N := term_model_nonempty H.right_consistent H.right_complete
    have hM : M ⊨ T₁ := by
      constructor
      intro A hA
      have ht := (formula_truth H.left_consistent H.left_complete H.left_henkin
        (A.relabel Empty.elim)).mpr (H.left_contains ⟨A, hA, rfl⟩)
      simpa only [Formula.realize_relabel, Unique.eq_default, Sentence.Realize] using ht
    have hN : N ⊨ T₂ := by
      constructor
      intro A hA
      have ht := (formula_truth H.right_consistent H.right_complete H.right_henkin
        (A.relabel Empty.elim)).mpr (H.right_contains ⟨A, hA, rfl⟩)
      simpa only [Formula.realize_relabel, Unique.eq_default, Sentence.Realize] using ht
    obtain ⟨e, _⟩ := common_term_isomorphism H.left_consistent H.left_complete H.left_henkin
      H.right_consistent H.right_complete H.right_henkin
      (common_agreement H.inseparable H.left_complete H.right_complete)
    exact glue_models S T e T₁ T₂ hM hN

end
end Lemmatheca.MathematicalLogic.JointConsistency
