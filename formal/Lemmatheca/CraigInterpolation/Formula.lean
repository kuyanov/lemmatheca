import Lemmatheca.CraigInterpolation.CraigInterpolation

namespace Lemmatheca.MathematicalLogic.CraigInterpolation
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ChangingLanguages
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section
local instance {β : Type*} : DecidableEq β := Classical.decEq _

/-- The original symbol's inclusion into the language with fresh constants. -/
def originalSymbol (α : Type w) : L.Symbols → L[[α]].Symbols
  | .inl ⟨n,f⟩ => .inl ⟨n,Sum.inl f⟩
  | .inr ⟨n,R⟩ => .inr ⟨n,Sum.inl R⟩

private theorem term_symbols_relabel (t : L.Term α) (f : α → β) :
    termSymbols (t.relabel f) = termSymbols t := by
  induction t with
  | var _ => rfl
  | func F ts ih => simp only [Term.relabel,termSymbols,ih]

private theorem formula_symbols_relabelEquiv {n : ℕ} (A : L.BoundedFormula α n) (e : α ≃ β) :
    formulaSymbols (BoundedFormula.relabelEquiv e A) = formulaSymbols A := by
  induction A with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp [BoundedFormula.relabelEquiv,BoundedFormula.mapTermRelEquiv,BoundedFormula.mapTermRel,
      formulaSymbols,term_symbols_relabel]
  | rel R ts =>
    simp [BoundedFormula.relabelEquiv,BoundedFormula.mapTermRelEquiv,BoundedFormula.mapTermRel,
      formulaSymbols,term_symbols_relabel]
  | imp A B ihA ihB =>
    simp only [BoundedFormula.relabelEquiv,BoundedFormula.mapTermRelEquiv,
      Equiv.coe_fn_mk,BoundedFormula.mapTermRel,formulaSymbols] at *
    rw [ihA,ihB]
  | all A ih => exact ih

private theorem old_symbol_injective : Function.Injective (originalSymbol (L := L) α) := by
  rintro (⟨n,f⟩ | ⟨n,R⟩) (⟨m,g⟩ | ⟨m,S⟩) h
  all_goals simp only [originalSymbol,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
    Sum.inr_ne_inl] at h
  · cases h; rfl
  · cases h; rfl

private theorem old_term_symbols (t : L[[α]].Term β) (s : L.Symbols) :
    s ∈ termSymbols (Term.constantsVarsEquiv t) ↔ originalSymbol α s ∈ termSymbols t := by
  induction t with
  | var _ => simp [Term.constantsVarsEquiv,termSymbols]
  | @func n F ts ih =>
    cases n with
    | zero =>
      cases F with
      | inl F =>
        change s ∈ termSymbols (.func F (fun i => (ts i).constantsToVars)) ↔ _
        simp only [termSymbols,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_univ,
          true_and,Term.constantsVarsEquiv_apply] at *
        constructor
        · rintro (rfl | ⟨i,hi⟩)
          · exact Or.inl rfl
          · exact Or.inr ⟨i,(ih i).mp hi⟩
        · rintro (h | ⟨i,hi⟩)
          · exact Or.inl (old_symbol_injective h)
          · exact Or.inr ⟨i,(ih i).mpr hi⟩
      | inr c =>
        cases s with
        | inl x =>
          rcases x with ⟨m,f⟩
          cases m <;> simp [Term.constantsVarsEquiv,Term.constantsToVars,termSymbols,originalSymbol]
          all_goals intro h; cases h
        | inr x => simp [Term.constantsVarsEquiv,Term.constantsToVars,termSymbols,originalSymbol]
    | succ n =>
      cases F with
      | inl F =>
        change s ∈ termSymbols (.func F (fun i => (ts i).constantsToVars)) ↔ _
        simp only [termSymbols,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_univ,
          true_and,Term.constantsVarsEquiv_apply] at *
        constructor
        · rintro (rfl | ⟨i,hi⟩)
          · exact Or.inl rfl
          · exact Or.inr ⟨i,(ih i).mp hi⟩
        · rintro (h | ⟨i,hi⟩)
          · exact Or.inl (old_symbol_injective h)
          · exact Or.inr ⟨i,(ih i).mpr hi⟩
      | inr c => exact isEmptyElim c

private theorem old_term_left_symbols {n : ℕ} (t : L[[α]].Term (β ⊕ Fin n)) (s : L.Symbols) :
    s ∈ termSymbols (Term.constantsVarsEquivLeft t) ↔ originalSymbol α s ∈ termSymbols t := by
  rw [Term.constantsVarsEquivLeft_apply,term_symbols_relabel]
  exact old_term_symbols t s

private theorem old_formula_symbols {n : ℕ} (A : L[[α]].BoundedFormula β n) (s : L.Symbols) :
    s ∈ formulaSymbols (BoundedFormula.constantsVarsEquiv A) ↔
      originalSymbol α s ∈ formulaSymbols A := by
  induction A with
  | falsum => simp [BoundedFormula.constantsVarsEquiv,BoundedFormula.mapTermRelEquiv,
    BoundedFormula.mapTermRel,formulaSymbols]
  | equal t₁ t₂ =>
    simp only [BoundedFormula.constantsVarsEquiv,BoundedFormula.mapTermRelEquiv,
      Equiv.coe_fn_mk,BoundedFormula.mapTermRel,formulaSymbols,Finset.mem_union]
    exact or_congr (old_term_left_symbols t₁ s) (old_term_left_symbols t₂ s)
  | rel R ts =>
    cases R with
    | inl R =>
      simp only [BoundedFormula.constantsVarsEquiv,BoundedFormula.mapTermRelEquiv,
        Equiv.coe_fn_mk,BoundedFormula.mapTermRel,formulaSymbols,
        Finset.mem_insert,Finset.mem_biUnion,Finset.mem_univ,true_and]
      constructor
      · rintro (h | ⟨i,hi⟩)
        · exact Or.inl (congrArg (originalSymbol α) h)
        · exact Or.inr ⟨i,(old_term_left_symbols (ts i) s).mp hi⟩
      · rintro (h | ⟨i,hi⟩)
        · exact Or.inl (old_symbol_injective h)
        · exact Or.inr ⟨i,(old_term_left_symbols (ts i) s).mpr hi⟩
    | inr R => exact isEmptyElim R
  | imp A B ihA ihB =>
    simp only [BoundedFormula.constantsVarsEquiv,BoundedFormula.mapTermRelEquiv,
      Equiv.coe_fn_mk,BoundedFormula.mapTermRel,formulaSymbols,Finset.mem_union] at *
    exact or_congr ihA ihB
  | all A ih => exact ih
theorem unname_symbols (A : L[[α]].Sentence) (s : L.Symbols) :
    s ∈ formulaSymbols (Formula.equivSentence.symm A) ↔
      originalSymbol α s ∈ formulaSymbols A := by
  change s ∈ formulaSymbols (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty)
    (BoundedFormula.constantsVarsEquiv A)) ↔ _
  rw [formula_symbols_relabelEquiv]
  exact old_formula_symbols A s

theorem name_symbols (A : L.Formula α) (s : L.Symbols) :
    originalSymbol α s ∈ formulaSymbols (Formula.equivSentence A) ↔
      s ∈ formulaSymbols A := by
  simpa only [Equiv.symm_apply_apply] using (unname_symbols (Formula.equivSentence A) s).symm

theorem names_consequence_iff {n : ℕ} (φ ψ : L.Formula (Fin n)) :
    (({Formula.equivSentence φ} : L[[Fin n]].Theory) ⊨ᵇ Formula.equivSentence ψ) ↔
      (∀ (M : Type (max u v)) [L.Structure M] [Nonempty M] (a : Fin n → M),
        φ.Realize a → ψ.Realize a) := by
  constructor
  · intro h M _ _ a hφ
    let := constantsOn.structure a
    have hp := ChangingLanguages.deductive_completeness h
    have hnamed : M ⊨ Formula.equivSentence φ :=
      (Formula.realize_equivSentence_symm M (Formula.equivSentence φ) a).mp
        (by simpa using hφ)
    have hψ := Lemmatheca.MathematicalLogic.FirstOrderProofs.derives_sound hp
      (default : Empty → M) (by
        intro A hA
        rw [Set.mem_singleton_iff.mp hA]
        exact hnamed)
    simpa using (Formula.realize_equivSentence_symm M (Formula.equivSentence ψ) a).mpr hψ
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    let : L.Structure M := (L.lhomWithConstants (Fin n)).reduct M
    rw [Formula.realize_equivSentence]
    apply h M (fun i => (L.con i : M))
    exact (Formula.realize_equivSentence M φ).mp
      (Theory.realize_sentence_of_mem ({Formula.equivSentence φ} : L[[Fin n]].Theory) (by simp))

theorem formula_interpolation {n : ℕ} (φ ψ : L.Formula (Fin n))
    (h : ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M] (a : Fin n → M),
      φ.Realize a → ψ.Realize a) :
    ∃ θ : L.Formula (Fin n),
      (formulaSymbols θ ⊆ formulaSymbols φ ∩ formulaSymbols ψ) ∧
      (∀ (M : Type (max u v)) [L.Structure M] [Nonempty M] (a : Fin n → M),
        φ.Realize a → θ.Realize a) ∧
      (∀ (M : Type (max u v)) [L.Structure M] [Nonempty M] (a : Fin n → M),
        θ.Realize a → ψ.Realize a) := by
  obtain ⟨η,hfirst,hsecond,hs⟩ := sentence_interpolation
    (Formula.equivSentence φ) (Formula.equivSentence ψ) ((names_consequence_iff φ ψ).mpr h)
  let B := (supportInclusion
    (formulaSymbols (Formula.equivSentence φ) ∩ formulaSymbols (Formula.equivSentence ψ))).onSentence η
  let θ := Formula.equivSentence.symm B
  refine ⟨θ,?_,?_,?_⟩
  · intro s hsθ
    have hsB := (unname_symbols B s).mp hsθ
    have hboth := Finset.mem_inter.mp (hs hsB)
    exact Finset.mem_inter.mpr ⟨(name_symbols φ s).mp hboth.1,(name_symbols ψ s).mp hboth.2⟩
  · apply (names_consequence_iff φ θ).mp
    simpa only [θ,Equiv.apply_symm_apply] using hfirst
  · apply (names_consequence_iff θ ψ).mp
    simpa only [θ,Equiv.apply_symm_apply] using hsecond

end
end Lemmatheca.MathematicalLogic.CraigInterpolation
