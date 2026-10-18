import Lemmatheca.MathematicalLogic.FirstOrderNormalForms

/-! The one-existential criterion for arbitrary first-order languages, including
the reduction from quantifier-free bodies to finite conjunctions of literals. -/
namespace Lemmatheca.MathematicalLogic.QuantifierElimination

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms

universe u v w

variable {L : Language.{u, v}} {α : Type w}

theorem qe_of_qf_existential (T : L.Theory)
    (h : ∀ (n : ℕ) (φ : L.BoundedFormula α (n + 1)), φ.IsQF →
      ∃ ψ, ψ.IsQF ∧ φ.ex ⇔[T] ψ) :
    ∀ (n : ℕ) (φ : L.BoundedFormula α n), ∃ ψ, ψ.IsQF ∧ φ ⇔[T] ψ := by
  intro n φ
  induction φ with
  | falsum => exact ⟨⊥, BoundedFormula.isQF_bot, Theory.Iff.refl _⟩
  | equal t s => exact ⟨_, (BoundedFormula.IsAtomic.equal _ _).isQF, Theory.Iff.refl _⟩
  | rel r ts => exact ⟨_, (BoundedFormula.IsAtomic.rel _ _).isQF, Theory.Iff.refl _⟩
  | imp φ ψ ihφ ihψ =>
    obtain ⟨φ', hφ', heφ⟩ := ihφ
    obtain ⟨ψ', hψ', heψ⟩ := ihψ
    exact ⟨φ'.imp ψ', hφ'.imp hψ', heφ.imp heψ⟩
  | @all n φ ih =>
    obtain ⟨ψ, hψ, he⟩ := ih
    obtain ⟨χ, hχ, heχ⟩ := h n ψ.not hψ.not
    exact ⟨χ.not, hχ.not, he.all.trans ((ψ.all_iff_not_ex_not).trans heχ.not)⟩

private def literalProduct {n : ℕ}
    (a b : List (List (L.BoundedFormula α n))) : List (List (L.BoundedFormula α n)) :=
  a.flatMap fun x => b.map fun y => x ++ y

/-- A finite literal-list disjunctive normal form, computed by paired polarity. -/
def literalDnf : {n : ℕ} → L.BoundedFormula α n → Bool →
    List (List (L.BoundedFormula α n))
  | _, .falsum, true => []
  | _, .falsum, false => [ [] ]
  | _, φ@(.equal _ _), true => [ [φ] ]
  | _, φ@(.equal _ _), false => [ [φ.not] ]
  | _, φ@(.rel _ _), true => [ [φ] ]
  | _, φ@(.rel _ _), false => [ [φ.not] ]
  | _, .imp φ ψ, true => literalDnf φ false ++ literalDnf ψ true
  | _, .imp φ ψ, false => literalProduct (literalDnf φ true) (literalDnf ψ false)
  | _, .all _, _ => []

/-- Empty conjunctions and disjunctions have their usual constant meanings. -/
def conjunction {n : ℕ} (l : List (L.BoundedFormula α n)) : L.BoundedFormula α n :=
  l.foldr (· ⊓ ·) ⊤

def disjunction {n : ℕ} (l : List (List (L.BoundedFormula α n))) :
    L.BoundedFormula α n := (l.map conjunction).foldr (· ⊔ ·) ⊥

theorem literalDnf_literals {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : φ.IsQF) (positive : Bool) :
    ∀ row ∈ literalDnf φ positive, ∀ θ ∈ row, IsLiteral θ := by
  induction hφ generalizing positive with
  | falsum => cases positive <;> simp [literalDnf]
  | of_isAtomic ha =>
    cases ha with
    | equal t s =>
      cases positive
      · simpa [literalDnf, Term.bdEqual, Relations.boundedFormula] using
          (show IsLiteral (BoundedFormula.equal t s).not from
            Or.inr ⟨_, .equal _ _, rfl⟩)
      · simpa [literalDnf, Term.bdEqual, Relations.boundedFormula] using
          (show IsLiteral (BoundedFormula.equal t s) from Or.inl (.equal _ _))
    | rel r ts =>
      cases positive
      · simpa [literalDnf, Term.bdEqual, Relations.boundedFormula] using
          (show IsLiteral (BoundedFormula.rel r ts).not from Or.inr ⟨_, .rel _ _, rfl⟩)
      · simpa [literalDnf, Term.bdEqual, Relations.boundedFormula] using
          (show IsLiteral (BoundedFormula.rel r ts) from Or.inl (.rel _ _))
  | imp hφ hψ ihφ ihψ =>
    cases positive
    · intro row hrow θ hθ
      simp only [literalDnf, literalProduct, List.mem_flatMap] at hrow
      obtain ⟨a, ha, hrow⟩ := hrow
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
      rcases List.mem_append.mp hθ with hθ | hθ
      · exact ihφ true a ha θ hθ
      · exact ihψ false b hb θ hθ
    · intro row hrow θ hθ
      rcases List.mem_append.mp hrow with ha | hb
      · exact ihφ false row ha θ hθ
      · exact ihψ true row hb θ hθ

theorem literalDnf_realize {M : Type*} [L.Structure M] {n : ℕ}
    {φ : L.BoundedFormula α n} (hφ : φ.IsQF) (positive : Bool)
    (a : α → M) (xs : Fin n → M) :
    (disjunction (literalDnf φ positive)).Realize a xs ↔
      if positive then φ.Realize a xs else ¬φ.Realize a xs := by
  have rows (l : List (List (L.BoundedFormula α n))) :
      (disjunction l).Realize a xs ↔ ∃ row ∈ l, ∀ θ ∈ row, θ.Realize a xs := by
    simp [disjunction, conjunction, BoundedFormula.realize_foldr_sup,
      BoundedFormula.realize_foldr_inf]
  have app (l r : List (List (L.BoundedFormula α n))) :
      (disjunction (l ++ r)).Realize a xs ↔
        (disjunction l).Realize a xs ∨ (disjunction r).Realize a xs := by
    simp only [rows, List.mem_append, or_and_right, exists_or]
  have prod (l r : List (List (L.BoundedFormula α n))) :
      (disjunction (literalProduct l r)).Realize a xs ↔
        (disjunction l).Realize a xs ∧ (disjunction r).Realize a xs := by
    simp only [rows]
    constructor
    · rintro ⟨row, hrow, hθ⟩
      obtain ⟨l', hl', hr⟩ := List.mem_flatMap.mp hrow
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      exact ⟨⟨l', hl', fun θ h => hθ θ (List.mem_append_left _ h)⟩,
        ⟨r', hr', fun θ h => hθ θ (List.mem_append_right _ h)⟩⟩
    · rintro ⟨⟨l', hl', hθl⟩, ⟨r', hr', hθr⟩⟩
      refine ⟨l' ++ r', List.mem_flatMap.mpr ⟨l', hl',
        List.mem_map.mpr ⟨r', hr', rfl⟩⟩, ?_⟩
      intro θ hθ
      exact (List.mem_append.mp hθ).elim (hθl θ) (hθr θ)
  induction hφ generalizing positive with
  | falsum => cases positive <;> simp [literalDnf, rows, BoundedFormula.Realize]
  | of_isAtomic ha =>
    cases ha with
    | equal t s => cases positive <;> simp [literalDnf, rows, Term.bdEqual]
    | rel r ts => cases positive <;> simp [literalDnf, rows, Relations.boundedFormula]
  | imp hφ hψ ihφ ihψ =>
    cases positive
    · simp only [literalDnf, prod]
      simpa [BoundedFormula.realize_imp] using and_congr (ihφ true) (ihψ false)
    · simp only [literalDnf, app]
      simpa [BoundedFormula.realize_imp, imp_iff_not_or] using
        or_congr (ihφ false) (ihψ true)

private theorem disjunction_exists_qf (T : L.Theory)
    (h : ∀ (n : ℕ) (row : List (L.BoundedFormula α (n + 1))),
      (∀ θ ∈ row, IsLiteral θ) → ∃ ψ, ψ.IsQF ∧ (conjunction row).ex ⇔[T] ψ)
    {n : ℕ} (rows : List (List (L.BoundedFormula α (n + 1))))
    (hrows : ∀ row ∈ rows, ∀ θ ∈ row, IsLiteral θ) :
    ∃ ψ, ψ.IsQF ∧ (disjunction rows).ex ⇔[T] ψ := by
  induction rows with
  | nil =>
    refine ⟨⊥, BoundedFormula.isQF_bot, ?_⟩
    intro M a xs
    simp [disjunction]
  | cons row rows ih =>
    obtain ⟨ψ, hψ, heψ⟩ := h n row (hrows row (by simp))
    obtain ⟨χ, hχ, heχ⟩ := ih (fun r hr => hrows r (by simp [hr]))
    refine ⟨ψ ⊔ χ, hψ.sup hχ, ?_⟩
    intro M a xs
    rw [BoundedFormula.realize_iff, BoundedFormula.realize_sup]
    have hψ' := heψ.realize_bd_iff (M := M) (v := a) (xs := xs)
    have hχ' := heχ.realize_bd_iff (M := M) (v := a) (xs := xs)
    rw [BoundedFormula.realize_ex] at hψ' hχ' ⊢
    change (∃ y, ((conjunction row) ⊔ (disjunction rows)).Realize a (Fin.snoc xs y)) ↔ _
    simp only [BoundedFormula.realize_sup]
    rw [exists_or]
    exact or_congr hψ' hχ'

/-- It suffices to eliminate one existential quantifier from finite conjunctions
of literals. This applies to arbitrary function and relation signatures. -/
theorem qe_of_literal_conjunctions (T : L.Theory)
    (h : ∀ (n : ℕ) (row : List (L.BoundedFormula α (n + 1))),
      (∀ θ ∈ row, IsLiteral θ) → ∃ ψ, ψ.IsQF ∧ (conjunction row).ex ⇔[T] ψ) :
    ∀ (n : ℕ) (φ : L.BoundedFormula α n), ∃ ψ, ψ.IsQF ∧ φ ⇔[T] ψ := by
  apply qe_of_qf_existential T
  intro n φ hφ
  obtain ⟨ψ, hψ, heψ⟩ := disjunction_exists_qf T h (literalDnf φ true)
    (literalDnf_literals hφ true)
  have he : φ ⇔[T] disjunction (literalDnf φ true) := by
    intro M a xs
    rw [BoundedFormula.realize_iff]
    exact (literalDnf_realize hφ true a xs).symm
  exact ⟨ψ, hψ, he.ex.trans heψ⟩

end Lemmatheca.MathematicalLogic.QuantifierElimination
