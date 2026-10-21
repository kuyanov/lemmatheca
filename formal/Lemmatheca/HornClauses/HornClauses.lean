import Lemmatheca.Resolution.Resolution

/-! Finite Horn rules, their shared propositional clause semantics, and forward closure. -/
namespace Lemmatheca.MathematicalLogic.HornClauses

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Resolution

universe u

structure Rule (α : Type u) where
  body : Finset α
  head : Option α
  deriving DecidableEq

variable {α : Type u} [DecidableEq α]

def IsHorn (C : Clause α) : Prop :=
  ∀ p q, pos p ∈ C → pos q ∈ C → p = q

def ruleClause (r : Rule α) : Clause α :=
  r.body.image neg ∪ r.head.toFinset.image pos

def Holds (r : Rule α) (X : Set α) : Prop :=
  (∀ p ∈ r.body, p ∈ X) → match r.head with
    | some p => p ∈ X
    | none => False

def TheoryModels (Γ : Set (Rule α)) (X : Set α) : Prop := ∀ r ∈ Γ, Holds r X

def models (Γ : Finset (Rule α)) (X : Set α) : Prop := TheoryModels (↑Γ) X

def clauseSet (Γ : Finset (Rule α)) : ClauseSet α := Γ.image ruleClause

noncomputable def formula (Γ : Finset (Rule α)) : PropFormula α :=
  cnfFormula ((clauseSet Γ).toList.map Finset.toList)

def support (Γ : Finset (Rule α)) : Finset α :=
  Γ.biUnion fun r => r.body ∪ r.head.toFinset

def step (Γ : Finset (Rule α)) (X : Finset α) : Finset α :=
  X ∪ Γ.biUnion fun r => match r.head with
    | some p => if r.body ⊆ X then {p} else ∅
    | none => ∅

def stage (Γ : Finset (Rule α)) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => step Γ (stage Γ n)

def closure (Γ : Finset (Rule α)) : Finset α := stage Γ (support Γ).card

def Closed (Γ : Finset (Rule α)) (X : Set α) : Prop :=
  ∀ r ∈ Γ, ∀ p, r.head = some p → (∀ b ∈ r.body, b ∈ X) → p ∈ X

def constraintsPass (Γ : Finset (Rule α)) (X : Finset α) : Bool :=
  decide (∀ r ∈ Γ, r.head = none → ¬r.body ⊆ X)

def accepts (Γ : Finset (Rule α)) : Bool := constraintsPass Γ (closure Γ)

def valuation (X : Finset α) : Valuation α := fun p => decide (p ∈ X)

theorem ruleClause_isHorn (r : Rule α) : IsHorn (ruleClause r) := by
  rcases r with ⟨B, h⟩
  cases h <;> simp [IsHorn, ruleClause, pos, neg]

theorem horn_iff_rule (C : Clause α) : IsHorn C ↔ ∃ r : Rule α, ruleClause r = C := by
  constructor
  · intro hC
    let B := (C.filter fun l => l.positive = false).image PropLiteral.atom
    have hB (a : α) : a ∈ B ↔ neg a ∈ C := by
      constructor
      · intro ha
        obtain ⟨l, hl, he⟩ := Finset.mem_image.mp ha
        have hs := (Finset.mem_filter.mp hl).2
        have hm := (Finset.mem_filter.mp hl).1
        rcases l with ⟨b, s⟩
        cases s <;> simp_all [neg]
      · intro ha
        exact Finset.mem_image.mpr ⟨neg a, Finset.mem_filter.mpr ⟨ha, rfl⟩, rfl⟩
    by_cases hh : ∃ p, pos p ∈ C
    · obtain ⟨p, hp⟩ := hh
      refine ⟨⟨B, some p⟩, ?_⟩
      ext ⟨a, b⟩
      cases b with
      | false => simpa [ruleClause, neg, pos] using hB a
      | true =>
        have he : a = p ↔ pos a ∈ C := by
          constructor
          · rintro rfl
            exact hp
          · intro ha
            exact hC a p ha hp
        simpa [ruleClause, neg, pos] using he
    · refine ⟨⟨B, none⟩, ?_⟩
      ext ⟨a, b⟩
      cases b with
      | false => simpa [ruleClause, neg, pos] using hB a
      | true =>
        have hna : (⟨a, true⟩ : PropLiteral α) ∉ C := fun ha => hh ⟨a, ha⟩
        simp [ruleClause, neg, hna]
  · rintro ⟨r, rfl⟩
    exact ruleClause_isHorn r

omit [DecidableEq α] in
theorem empty_rules (p : α) (X : Set α) :
    (Holds ⟨∅, some p⟩ X ↔ p ∈ X) ∧ ¬Holds ⟨∅, none⟩ X := by
  simp [Holds]

theorem clause_bridge (r : Rule α) (v : Valuation α) :
    ClauseSat v (ruleClause r) ↔ Holds r {p | v p = true} := by
  rcases r with ⟨B, h⟩
  cases h with
  | none =>
    simp only [ruleClause, Option.toFinset_none, Finset.image_empty, Finset.union_empty,
      ClauseSat, Finset.mem_image, LiteralSat, neg, Holds, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, ⟨a, ha, rfl⟩, ht⟩ hall
      simp [hall a ha] at ht
    · intro hn
      change ¬ ∀ a ∈ B, v a = true at hn
      push Not at hn
      obtain ⟨a, ha, hv⟩ := hn
      exact ⟨neg a, ⟨a, ha, rfl⟩, Bool.eq_false_iff.mpr hv⟩
  | some p =>
    simp only [ruleClause, Option.toFinset_some, Finset.image_singleton, ClauseSat,
      Finset.mem_union, Finset.mem_image, Finset.mem_singleton, Holds, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, (⟨a, ha, rfl⟩ | rfl), ht⟩ hall
      · have ht' : v a = false := ht
        simp [hall a ha] at ht'
      · exact ht
    · intro hi
      by_cases hall : ∀ a ∈ B, v a = true
      · exact ⟨pos p, Or.inr rfl, hi hall⟩
      · push Not at hall
        obtain ⟨a, ha, hv⟩ := hall
        exact ⟨neg a, Or.inl ⟨a, ha, rfl⟩, Bool.eq_false_iff.mpr hv⟩

theorem theory_bridge (Γ : Finset (Rule α)) (v : Valuation α) :
    Models v (clauseSet Γ) ↔ models Γ {p | v p = true} := by
  simp only [Models, clauseSet, Finset.mem_image, models, TheoryModels, Finset.mem_coe]
  constructor
  · intro h r hr
    exact (clause_bridge r v).mp (h _ ⟨r, hr, rfl⟩)
  · intro h C ⟨r, hr, he⟩
    subst C
    exact (clause_bridge r v).mpr (h r hr)

theorem formula_bridge (Γ : Finset (Rule α)) (v : Valuation α) :
    eval v (formula Γ) = true ↔ models Γ {p | v p = true} := by
  rw [formula, list_cnf]
  have he : ofCnf ((clauseSet Γ).toList.map Finset.toList) = clauseSet Γ := by
    simp [ofCnf, List.map_map, Function.comp_def, Finset.toList_toFinset]
  rw [he, theory_bridge]

theorem step_inflation (Γ : Finset (Rule α)) (X : Finset α) : X ⊆ step Γ X := by
  exact Finset.subset_union_left

theorem step_monotone (Γ : Finset (Rule α)) {X Y : Finset α} (h : X ⊆ Y) :
    step Γ X ⊆ step Γ Y := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union_left _ (h hp)
  · apply Finset.mem_union_right
    obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    cases hh : r.head with
    | none => simp [hh] at hp
    | some q =>
      simp only [hh] at hp ⊢
      split_ifs at hp with hb
      · simpa [Finset.Subset.trans hb h] using hp
      · simp at hp

theorem stage_support (Γ : Finset (Rule α)) (n : ℕ) : stage Γ n ⊆ support Γ := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ih hp
    · obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
      apply Finset.mem_biUnion.mpr
      refine ⟨r, hr, Finset.mem_union_right _ ?_⟩
      cases hh : r.head with
      | none => simp [hh] at hp
      | some q =>
        simp only [hh] at hp ⊢
        split_ifs at hp with hb
        · simpa using hp
        · simp at hp

theorem stage_increasing (Γ : Finset (Rule α)) (n : ℕ) :
    stage Γ n ⊆ stage Γ (n + 1) := by
  exact step_inflation Γ _

theorem stage_le_closed (Γ : Finset (Rule α)) {Y : Set α} (hY : Closed Γ Y) (n : ℕ) :
    ∀ p ∈ stage Γ n, p ∈ Y := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ih p hp
    · obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hp
      cases hh : r.head with
      | none => simp [hh] at hp
      | some q =>
        simp only [hh] at hp
        split_ifs at hp with hb
        · have he : p = q := Finset.mem_singleton.mp hp
          subst p
          exact hY r hr q hh (fun b hb' => ih b (hb hb'))
        · simp at hp

theorem stationary (Γ : Finset (Rule α)) {k : ℕ}
    (h : stage Γ (k + 1) = stage Γ k) (m : ℕ) :
    stage Γ (k + m) = stage Γ k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, stage, ih]
    exact h

private theorem fixed_or_card (Γ : Finset (Rule α)) (n : ℕ) :
    stage Γ (n + 1) = stage Γ n ∨ n ≤ (stage Γ n).card := by
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    rcases ih with hf | hc
    · left
      change step Γ (stage Γ (n + 1)) = stage Γ (n + 1)
      rw [hf]
      exact hf
    · by_cases hf : stage Γ (n + 1) = stage Γ n
      · left
        change step Γ (stage Γ (n + 1)) = stage Γ (n + 1)
        rw [hf]
        exact hf
      · right
        have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨stage_increasing Γ n, Ne.symm hf⟩)
        omega

theorem stabilization (Γ : Finset (Rule α)) : step Γ (closure Γ) = closure Γ := by
  rcases fixed_or_card Γ (support Γ).card with hf | hc
  · exact hf
  · have he : closure Γ = support Γ :=
      Finset.eq_of_subset_of_card_le (stage_support Γ _) hc
    apply Finset.Subset.antisymm
    · rw [he]
      have hs := stage_support Γ ((support Γ).card + 1)
      change step Γ (closure Γ) ⊆ support Γ at hs
      rw [he] at hs
      exact hs
    · exact step_inflation Γ _

theorem closure_is_least (Γ : Finset (Rule α)) :
    Closed Γ (↑(closure Γ)) ∧
      ∀ Y : Set α, Closed Γ Y → ∀ p ∈ closure Γ, p ∈ Y := by
  constructor
  · intro r hr p hh hb
    rw [← stabilization Γ]
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    simp [hh, show r.body ⊆ closure Γ from hb]
  · intro Y hY
    exact stage_le_closed Γ hY _

theorem models_least (Γ : Finset (Rule α)) {X : Set α} (h : models Γ X) :
    ∀ p ∈ closure Γ, p ∈ X := by
  apply (closure_is_least Γ).2 X
  intro r hr p hh hb
  have hs := h r hr hb
  simpa [hh] using hs

theorem definite_least_model (Γ : Finset (Rule α))
    (hd : ∀ r ∈ Γ, r.head ≠ none) :
    models Γ (↑(closure Γ)) ∧
      ∀ Y : Set α, models Γ Y → ∀ p ∈ closure Γ, p ∈ Y := by
  constructor
  · intro r hr hb
    cases hh : r.head with
    | none => exact False.elim (hd r hr hh)
    | some p => exact (closure_is_least Γ).1 r hr p hh hb
  · intro Y hY
    exact models_least Γ hY

theorem constraintsPass_iff (Γ : Finset (Rule α)) (X : Finset α) :
    constraintsPass Γ X = true ↔ ∀ r ∈ Γ, r.head = none → ¬r.body ⊆ X := by
  simp [constraintsPass]

theorem satisfies_iff (Γ : Finset (Rule α)) :
    (∃ X : Set α, models Γ X) ↔ constraintsPass Γ (closure Γ) = true := by
  constructor
  · rintro ⟨X, hX⟩
    apply (constraintsPass_iff Γ _).mpr
    intro r hr hh hb
    have hf := hX r hr (fun p hp => models_least Γ hX p (hb hp))
    simp [hh] at hf
  · intro h
    refine ⟨↑(closure Γ), ?_⟩
    intro r hr hb
    cases hh : r.head with
    | none => exact (constraintsPass_iff Γ _).mp h r hr hh hb
    | some p => exact (closure_is_least Γ).1 r hr p hh hb

theorem accepted_least_model (Γ : Finset (Rule α)) (h : accepts Γ = true) :
    models Γ (↑(closure Γ)) := by
  intro r hr hb
  cases hh : r.head with
  | none => exact (constraintsPass_iff Γ _).mp h r hr hh hb
  | some p => exact (closure_is_least Γ).1 r hr p hh hb

theorem accepts_correct (Γ : Finset (Rule α)) :
    accepts Γ = true ↔ Sat (clauseSet Γ) := by
  constructor
  · intro h
    refine ⟨valuation (closure Γ), (theory_bridge Γ _).mpr ?_⟩
    simpa [valuation] using accepted_least_model Γ h
  · rintro ⟨v, hv⟩
    exact (satisfies_iff Γ).mp ⟨{p | v p = true}, (theory_bridge Γ v).mp hv⟩

theorem positive_consequence (Γ : Finset (Rule α))
    (hs : ∃ X : Set α, models Γ X) (p : α) :
    (∀ X : Set α, models Γ X → p ∈ X) ↔ p ∈ closure Γ := by
  constructor
  · intro h
    exact h _ (accepted_least_model Γ ((satisfies_iff Γ).mp hs))
  · intro hp X hX
    exact models_least Γ hX p hp

omit [DecidableEq α] in
theorem constraint_univ (B : Finset α) : ¬Holds ⟨B, none⟩ (Set.univ : Set α) := by
  simp [Holds]

omit [DecidableEq α] in
theorem model_intersection (Γ : Set (Rule α)) {𝓜 : Set (Set α)}
    (hn : 𝓜.Nonempty) (hm : ∀ X ∈ 𝓜, TheoryModels Γ X) :
    TheoryModels Γ (⋂₀ 𝓜) := by
  intro r hr hb
  have hbody (X : Set α) (hX : X ∈ 𝓜) : ∀ p ∈ r.body, p ∈ X :=
    fun p hp => Set.mem_sInter.mp (hb p hp) X hX
  cases hh : r.head with
  | none =>
    obtain ⟨X, hX⟩ := hn
    have hf := hm X hX r hr (hbody X hX)
    simp [hh] at hf
  | some p =>
    apply Set.mem_sInter.mpr
    intro X hX
    have hp := hm X hX r hr (hbody X hX)
    simpa [hh] using hp

theorem nonHorn_intersection_counterexample {p q : α} (hpq : p ≠ q) :
    ClauseSat (valuation {p}) {pos p, pos q} ∧
    ClauseSat (valuation {q}) {pos p, pos q} ∧
    ({p} : Finset α) ∩ {q} = ∅ ∧
    ¬ClauseSat (valuation (∅ : Finset α)) {pos p, pos q} := by
  simp [ClauseSat, LiteralSat, valuation, pos, hpq, hpq.symm]

end Lemmatheca.MathematicalLogic.HornClauses
