import Lemmatheca.IsolatedTypes.IsolatedTypes
import Lemmatheca.HenkinCompleteness.HenkinBasic
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics

/-! Native new-name support, constant lifting, and finite avoidance. -/
namespace Lemmatheca.ModelTheory.OmittingTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes
open Lemmatheca.MathematicalLogic.HenkinCompleteness

universe u v w
variable {L : Language.{u, v}} {T : L.Theory} {n : ℕ}

noncomputable section
local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

/-- The actual added constants occurring in an expanded term with any free context. -/
def termNameSupport {α : Type*} [DecidableEq α] (t : L[[ℕ]].Term α) : Finset ℕ :=
  t.constantsToVars.varFinset.toLeft

/-- The actual added constants occurring in an expanded scoped formula. -/
def formulaNameSupport {α : Type*} [DecidableEq α] {k : ℕ}
    (φ : L[[ℕ]].BoundedFormula α k) : Finset ℕ :=
  (BoundedFormula.constantsVarsEquiv φ).freeVarFinset.toLeft

/-- A finite added condition uses the union of its members' new-name supports. -/
def conditionSupport (Γ : Finset (L.Formula ℕ)) : Finset ℕ :=
  Γ.biUnion BoundedFormula.freeVarFinset

/-- Changing unused new names preserves the value of a term under any free assignment. -/
theorem term_support_locality {α : Type*} [DecidableEq α]
    {M : Type w} [L.Structure M] (t : L[[ℕ]].Term α)
    (a b : ℕ → M) (v : α → M)
    (h : ∀ k ∈ termNameSupport t, a k = b k) :
    letI := Diagrams.namedExpansion (L := L) a
    let value := t.realize v
    letI := Diagrams.namedExpansion (L := L) b
    value = t.realize v := by
  have lift (g : ℕ → M) :
      (letI := Diagrams.namedExpansion (L := L) g; t.realize v) =
        t.constantsToVars.realize (Sum.elim g v) := by
    let := Diagrams.namedExpansion (L := L) g
    let := Diagrams.namedExpansion_isExpansion (L := L) g
    exact Term.realize_constantsToVars.symm
  change (letI := Diagrams.namedExpansion (L := L) a; t.realize v) =
    (letI := Diagrams.namedExpansion (L := L) b; t.realize v)
  rw [lift a, lift b]
  apply Lemmatheca.MathematicalLogic.FirstOrderSemantics.term_realize_agree
  intro c hc
  cases c with
  | inl c => exact h c (Finset.mem_toLeft.mpr hc)
  | inr c => rfl

/-- Changing unused new names preserves the formula's truth at every scoped assignment. -/
theorem named_support_locality {α : Type*} [DecidableEq α] {k : ℕ}
    {M : Type w} [L.Structure M] (φ : L[[ℕ]].BoundedFormula α k)
    (a b : ℕ → M) (v : α → M) (xs : Fin k → M)
    (h : ∀ c ∈ formulaNameSupport φ, a c = b c) :
    letI := Diagrams.namedExpansion (L := L) a
    let h₁ : Prop := φ.Realize v xs
    letI := Diagrams.namedExpansion (L := L) b
    h₁ ↔ φ.Realize v xs := by
  have lift (g : ℕ → M) :
      (letI := Diagrams.namedExpansion (L := L) g; φ.Realize v xs) ↔
        (BoundedFormula.constantsVarsEquiv φ).Realize (Sum.elim g v) xs := by
    let := Diagrams.namedExpansion (L := L) g
    let := Diagrams.namedExpansion_isExpansion (L := L) g
    exact BoundedFormula.realize_constantsVarsEquiv.symm
  change (letI := Diagrams.namedExpansion (L := L) a; φ.Realize v xs) ↔
    (letI := Diagrams.namedExpansion (L := L) b; φ.Realize v xs)
  refine (lift a).trans (Iff.trans ?_ (lift b).symm)
  apply Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
  intro c hc
  cases c with
  | inl c => exact h c (Finset.mem_toLeft.mpr hc)
  | inr c => rfl

/-- The finite support includes every name appearing in the condition or tuple. -/
def tupleSupport (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) : Finset ℕ :=
  conditionSupport Γ ∪ Finset.univ.image t

/-- Restrict a conjunction to the finite list of all names that matter. -/
def conditionMatrix (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) :
    L.Formula (tupleSupport Γ t) :=
  Formula.iInf fun φ : Γ =>
    φ.val.restrictFreeVar fun k =>
      ⟨k.val, Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨φ.val, φ.property, k.property⟩)⟩

/-- The indicated tuple's coordinates equal the matching support variables. -/
def tupleEqualities (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) :
    L.Formula (Fin n ⊕ tupleSupport Γ t) :=
  Formula.iInf fun i : Fin n =>
    (Term.var (Sum.inl i) : L.Term (Fin n ⊕ tupleSupport Γ t)).equal
      (.var (Sum.inr ⟨t i, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩))

/-- Existentially bind only the finite support, retaining the indicated tuple free. -/
def finiteConditionFormula (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) :
    L.Formula (Fin n) :=
  ((Formula.relabel Sum.inr (conditionMatrix Γ t)) ⊓ tupleEqualities Γ t).iExs
    (tupleSupport Γ t)

/-- Native constant lifting followed by support restriction has the stated truth identity. -/
theorem conditionMatrix_realize {M : Type w} [L.Structure M]
    (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) (g : ℕ → M) :
    (conditionMatrix Γ t).Realize (g ∘ Subtype.val) ↔
      Realizes (↑Γ : Set (L.Formula ℕ)) g := by
  simp only [conditionMatrix, Formula.realize_iInf]
  have truth (φ : Γ) :
      Formula.Realize (φ.val.restrictFreeVar (fun k =>
        (⟨k.val, Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨φ.val, φ.property, k.property⟩)⟩ : tupleSupport Γ t)))
          (g ∘ Subtype.val) ↔ φ.val.Realize g :=
    BoundedFormula.realize_restrictFreeVar g (fun _ => rfl)
  dsimp only [tupleSupport] at *
  simp_rw [truth]
  exact Subtype.forall

/-- The concrete support formula recovers exactly all expansions with the indicated tuple. -/
theorem finiteConditionFormula_realize {M : Type w} [L.Structure M] [Nonempty M]
    (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) (a : Fin n → M) :
    (finiteConditionFormula Γ t).Realize a ↔
      ∃ g : ℕ → M, Realizes (↑Γ : Set (L.Formula ℕ)) g ∧ g ∘ t = a := by
  classical
  simp only [finiteConditionFormula, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_relabel, Sum.elim_comp_inr, tupleEqualities,
    Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨b, hb, heq⟩
    let g : ℕ → M := fun c => if h : c ∈ tupleSupport Γ t then b ⟨c, h⟩
      else Classical.choice (inferInstance : Nonempty M)
    have hgb : g ∘ Subtype.val = b := by
      funext c
      exact dite_eq_left c.property
    refine ⟨g, (conditionMatrix_realize Γ t g).mp (hgb.symm ▸ hb), ?_⟩
    funext i
    exact (dite_eq_left (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))).trans (heq i).symm
  · rintro ⟨g, hg, heq⟩
    refine ⟨g ∘ Subtype.val, (conditionMatrix_realize Γ t g).mpr hg, ?_⟩
    intro i
    exact (congrFun heq i).symm

/-- Equality constraints explicitly account for repeated tuple names. -/
theorem finiteConditionFormula_repeated {M : Type w} [L.Structure M] [Nonempty M]
    (Γ : Finset (L.Formula ℕ)) (t : Fin n → ℕ) (a : Fin n → M)
    (ha : (finiteConditionFormula Γ t).Realize a) (i j : Fin n) (h : t i = t j) :
    a i = a j := by
  obtain ⟨g, _, hga⟩ := (finiteConditionFormula_realize Γ t a).mp ha
  exact (congrFun hga i).symm.trans ((congrArg g h).trans (congrFun hga j))

/-- Some consistent formula in the same context forces every original condition. -/
def Principal (T : L.Theory) (p : Set (L.Formula (Fin n))) : Prop :=
  ∃ θ : L.Formula (Fin n), IsPartial T {θ} ∧ ∀ φ ∈ p, T ⊨ᵇ θ.imp φ

/-- No T-consistent formula forces the whole partial condition set. -/
def Nonprincipal (T : L.Theory) (p : Set (L.Formula (Fin n))) : Prop :=
  ¬Principal T p

theorem principal_complete_iff (p : T.CompleteType (Fin n)) :
    Principal T (formulas p) ↔ Isolated T p := by
  constructor
  · rintro ⟨θ, hθ, force⟩
    obtain ⟨q, hq⟩ := exists_complete_extension ({θ} : Set (L.Formula (Fin n))) hθ
    have unique (r : T.CompleteType (Fin n)) (hr : θ ∈ formulas r) : r = p := by
      obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in r
      have hra : Realizes (formulas r) a := (realizes_complete_iff r a).mpr ha.symm
      have hpa : Realizes (formulas p) a := by
        intro φ hφ
        exact (force φ hφ).realize_formula N (hra θ hr)
      exact ((realizes_complete_iff r a).mp hra).trans
        ((realizes_complete_iff p a).mp hpa).symm
    have hqθ := hq (Set.mem_singleton θ)
    exact ⟨θ, (isolates_iff_unique p θ).mpr ⟨unique q hqθ ▸ hqθ, unique⟩⟩
  · rintro ⟨θ, hθ, force⟩
    obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
    have hpa : Realizes (formulas p) a := (realizes_complete_iff p a).mpr ha.symm
    refine ⟨θ, (partial_iff_model _ _).mpr ⟨N, a, ?_⟩, force⟩
    intro φ hφ
    obtain rfl := Set.mem_singleton_iff.mp hφ
    exact hpa φ hθ

/-- Arbitrary finite named conditions can force failure of an original nonprincipal condition. -/
theorem partial_finite_avoidance (p : Set (L.Formula (Fin n))) (hp : Nonprincipal T p)
    (Γ : Finset (L.Formula ℕ)) (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ)))
    (t : Fin n → ℕ) :
    ∃ φ ∈ p,
      IsPartial T (↑(insert (Formula.relabel t φ).not Γ) : Set (L.Formula ℕ)) := by
  classical
  by_contra h
  push Not at h
  let χ := finiteConditionFormula Γ t
  have force (φ : L.Formula (Fin n)) (hφ : φ ∈ p) : T ⊨ᵇ χ.imp φ := by
    apply Theory.models_formula_iff.mpr
    intro N a
    change χ.Realize a → φ.Realize a
    intro hχ
    obtain ⟨g, hg, hgt⟩ := (finiteConditionFormula_realize Γ t a).mp hχ
    by_contra hnφ
    apply h φ hφ
    apply (partial_iff_model _ _).mpr
    refine ⟨N, g, fun ψ hψ => ?_⟩
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · apply Formula.realize_not.mpr
      simpa only [Formula.realize_relabel, hgt] using hnφ
    · exact hg ψ hψ
  have hχ : IsPartial T ({χ} : Set (L.Formula (Fin n))) := by
    obtain ⟨N, g, hg⟩ := (partial_iff_model T (↑Γ : Set (L.Formula ℕ))).mp hΓ
    apply (partial_iff_model _ _).mpr
    refine ⟨N, g ∘ t, fun φ hφ => ?_⟩
    obtain rfl := Set.mem_singleton_iff.mp hφ
    exact (finiteConditionFormula_realize Γ t (g ∘ t)).mpr ⟨g, hg, rfl⟩
  exact hp ⟨χ, hχ, force⟩


/-- A finite satisfiable condition can force any named tuple to fail a nonisolated type. -/
theorem finite_avoidance (p : T.CompleteType (Fin n)) (hp : ¬Isolated T p)
    (Γ : Finset (L.Formula ℕ)) (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ)))
    (t : Fin n → ℕ) :
    ∃ φ ∈ formulas p,
      IsPartial T (↑(insert (Formula.relabel t φ).not Γ) : Set (L.Formula ℕ)) := by
  exact partial_finite_avoidance (formulas p)
    (fun h => hp ((principal_complete_iff p).mp h)) Γ hΓ t

/-- One of a sentence and its negation preserves the current finite consistency condition. -/
theorem decision_preserves (Γ : Finset (L.Formula ℕ))
    (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ))) (σ : L.Formula ℕ) :
    IsPartial T (↑(insert σ Γ) : Set (L.Formula ℕ)) ∨
      IsPartial T (↑(insert σ.not Γ) : Set (L.Formula ℕ)) := by
  obtain ⟨N, a, ha⟩ := (partial_iff_model T (↑Γ : Set (L.Formula ℕ))).mp hΓ
  by_cases hσ : σ.Realize a
  · left
    apply (partial_iff_model _ _).mpr
    refine ⟨N, a, fun φ hφ => ?_⟩
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · exact hσ
    · exact ha φ hφ
  · right
    apply (partial_iff_model _ _).mpr
    refine ⟨N, a, fun φ hφ => ?_⟩
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · exact Formula.realize_not.mpr hσ
    · exact ha φ hφ

/-- A genuinely fresh conditional witness preserves satisfiability of the whole background theory. -/
theorem witness_preserves (Γ : Finset (L.Formula ℕ))
    (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ))) (η : L.BoundedFormula ℕ 1) :
    ∃ c : ℕ, c ∉ conditionSupport Γ ∪ η.freeVarFinset ∧
      IsPartial T (↑(insert (witnessAxiom η c) Γ) : Set (L.Formula ℕ)) := by
  classical
  obtain ⟨c, hc⟩ := (conditionSupport Γ ∪ η.freeVarFinset).exists_notMem
  obtain ⟨N, a, ha⟩ := (partial_iff_model T (↑Γ : Set (L.Formula ℕ))).mp hΓ
  let b : N := if h : ∃ b : N, η.Realize a (fun _ => b) then Classical.choose h
    else Classical.choice (inferInstance : Nonempty N)
  let a' := Function.update a c b
  have agrees (φ : L.BoundedFormula ℕ 1) (hf : c ∉ φ.freeVarFinset) (xs : Fin 1 → N) :
      φ.Realize a' xs ↔ φ.Realize a xs := by
    apply Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
    intro k hk
    exact Function.update_of_ne (show k ≠ c from fun hkc => hf (hkc ▸ hk)) _ _
  have hw : (witnessAxiom η c).Realize a' := by
    rw [witnessAxiom, Formula.realize_imp,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate_realize]
    intro hex
    have hη : c ∉ η.freeVarFinset := fun h => hc (Finset.mem_union_right _ h)
    have hb : ∃ b : N, η.Realize a (fun _ => b) := by
      obtain ⟨d, hd⟩ := BoundedFormula.realize_ex.mp hex
      exact ⟨d, (agrees η hη _).mp hd⟩
    have hbη : η.Realize a (fun _ => b) := by
      dsimp only [b]
      rw [dite_eq_left hb]
      exact Classical.choose_spec hb
    have hbη' := (agrees η hη (fun _ => b)).mpr hbη
    simpa only [Term.realize_var, a', Function.update_self] using hbη'
  refine ⟨c, hc, (partial_iff_model _ _).mpr ⟨N, a', fun φ hφ => ?_⟩⟩
  rcases Finset.mem_insert.mp hφ with rfl | hφ
  · exact hw
  · apply (Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
      φ a' a default ?_).mpr (ha φ hφ)
    intro k hk
    apply Function.update_of_ne
    intro hkc
    apply hc
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨φ, hφ, hkc ▸ hk⟩)

end
end Lemmatheca.ModelTheory.OmittingTypes
