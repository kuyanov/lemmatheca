import Mathlib.ModelTheory.Complexity
import Lemmatheca.MathematicalLogic.Theories
import Lemmatheca.MathematicalLogic.Diagrams

/-! Preservation properties and the corresponding shared-syntax fragments. -/
namespace Lemmatheca.MathematicalLogic.Preservation

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Theories

universe u v w u'
variable {L : Language.{u, v}}

/-- Closure under embeddings into a model expresses closure under nonempty substructures,
with isomorphic copies included. The universe is the language's model universe. -/
def SubstructurePreserved (T : L.Theory) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory)),
    N ⊨ T → (M ↪[L] N) → M ⊨ T

/-- Truth is carried along every embedding between nonempty models of the theory. -/
def ExtensionPreserved (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N) (a : Fin n → M),
    φ.Realize a → φ.Realize (f ∘ a)

/-- The dual preservation property, at tuples from the smaller model. -/
def DownwardPreserved (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N) (a : Fin n → M),
    φ.Realize (f ∘ a) → φ.Realize a

/-- The literal inclusion form: every nonempty substructure of a nonempty
model of the theory is a model of the same theory. -/
def SubstructureInclusionPreserved (T : L.Theory) : Prop :=
  ∀ (N : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory)),
    N ⊨ T → ∀ S : L.Substructure N, Nonempty S → S ⊨ T

/-- The literal inclusion form of upward preservation, with both structures
satisfying the background theory and with the displayed subtype map. -/
def ExtensionInclusionPreserved (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∀ (N : Theory.ModelType.{u, v, max u v w} T) (S : L.Substructure N),
    Nonempty S → S ⊨ T → ∀ a : Fin n → S,
      φ.Realize a → φ.Realize (Subtype.val ∘ a)

/-- The literal inclusion form of downward preservation. -/
def DownwardInclusionPreserved (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∀ (N : Theory.ModelType.{u, v, max u v w} T) (S : L.Substructure N),
    Nonempty S → S ⊨ T → ∀ a : Fin n → S,
      φ.Realize (Subtype.val ∘ a) → φ.Realize a

/-- Isomorphism onto the actual image turns embedding preservation into the
literal nonempty-substructure formulation, in both directions. -/
theorem substructure_preserved_iff_inclusions (T : L.Theory) :
    SubstructurePreserved.{u, v, w} T ↔ SubstructureInclusionPreserved.{u, v, w} T := by
  constructor
  · intro h N hN S hne
    let := hne
    exact h (Theory.ModelType.of (∅ : L.Theory) S) N hN S.subtype
  · intro h M N hN f
    let e := f.equivRange
    have hne : Nonempty f.toHom.range := Nonempty.map e inferInstance
    let := hne
    let : f.toHom.range ⊨ T := h N hN f.toHom.range hne
    exact StrongHomClass.theory_model e.symm

/-- The image factorization identifies the tuple maps as well as the models. -/
theorem extension_preserved_iff_inclusions (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n)) :
    ExtensionPreserved.{u, v, w} T φ ↔ ExtensionInclusionPreserved.{u, v, w} T φ := by
  constructor
  · intro h N S hne hS a ha
    let := hne
    let := hS
    exact h (Theory.ModelType.of T S) N S.subtype a ha
  · intro h M N f a ha
    let e := f.equivRange
    have hne : Nonempty f.toHom.range := Nonempty.map e inferInstance
    let := hne
    let hS : f.toHom.range ⊨ T := StrongHomClass.theory_model e
    have hs : φ.Realize (e ∘ a) := (StrongHomClass.realize_formula e φ).mpr ha
    have he : Subtype.val ∘ (e ∘ a) = f ∘ a := rfl
    simpa only [he] using h N f.toHom.range hne hS (e ∘ a) hs

theorem downward_preserved_iff_inclusions (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n)) :
    DownwardPreserved.{u, v, w} T φ ↔ DownwardInclusionPreserved.{u, v, w} T φ := by
  constructor
  · intro h N S hne hS a ha
    let := hne
    let := hS
    exact h (Theory.ModelType.of T S) N S.subtype a ha
  · intro h M N f a ha
    let e := f.equivRange
    have hne : Nonempty f.toHom.range := Nonempty.map e inferInstance
    let := hne
    let hS : f.toHom.range ⊨ T := StrongHomClass.theory_model e
    have he : Subtype.val ∘ (e ∘ a) = f ∘ a := rfl
    have hs : φ.Realize (e ∘ a) := h N f.toHom.range hne hS (e ∘ a) (by
      simpa only [he] using ha)
    exact (StrongHomClass.realize_formula e φ).mp hs

/-- An equivalent theory whose actual shared-syntax sentences are all universal. -/
def HasUniversalAxiomatization (T : L.Theory) : Prop :=
  ∃ U : L.Theory, U.IsUniversal ∧ Theories.Equivalent T U

/-- All universal semantic consequences of a theory. -/
def universalPart (T : L.Theory) : L.Theory :=
  {σ | σ.IsUniversal ∧ T ⊨ᵇ σ}

/-- All existential formulas true at the specified finite tuple. -/
def existentialInformation {M : Type w} [L.Structure M] {n : ℕ} (a : Fin n → M) :
    Set (L.Formula (Fin n)) := {ψ | ψ.IsExistential ∧ ψ.Realize a}

/-- The existential consequences of one formula, relative to the given theory. -/
def existentialConsequences (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) :
    Set (L.Formula (Fin n)) := {ψ | ψ.IsExistential ∧ T ⊨ᵇ (φ.imp ψ)}

/-- The syntactic and semantic duality, allowing arbitrary free names and bound slots. -/
theorem exists_universal_not {ι : Type u'} {m : ℕ} {φ : L.BoundedFormula ι m}
    (hφ : φ.IsExistential) :
    ∃ ψ : L.BoundedFormula ι m, ψ.IsUniversal ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : ι → M) (xs : Fin m → M),
        ψ.Realize v xs ↔ ¬ φ.Realize v xs := by
  induction hφ with
  | @of_isQF m φ hq =>
    refine ⟨φ.not, hq.not.isUniversal, ?_⟩
    intro M _ _ v xs
    exact BoundedFormula.realize_not
  | @ex m φ he ih =>
    obtain ⟨ψ, hu, hs⟩ := ih
    refine ⟨ψ.all, hu.all, ?_⟩
    intro M _ _ v xs
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_ex, not_exists]
    exact forall_congr' fun x => hs M v (Fin.snoc xs x)

/-- The converse duality in the same shared syntax. -/
theorem exists_existential_not {ι : Type u'} {m : ℕ} {φ : L.BoundedFormula ι m}
    (hφ : φ.IsUniversal) :
    ∃ ψ : L.BoundedFormula ι m, ψ.IsExistential ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : ι → M) (xs : Fin m → M),
        ψ.Realize v xs ↔ ¬ φ.Realize v xs := by
  induction hφ with
  | @of_isQF m φ hq =>
    refine ⟨φ.not, hq.not.isExistential, ?_⟩
    intro M _ _ v xs
    exact BoundedFormula.realize_not
  | @all m φ he ih =>
    obtain ⟨ψ, hu, hs⟩ := ih
    refine ⟨ψ.ex, hu.ex, ?_⟩
    intro M _ _ v xs
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_ex, not_forall]
    exact exists_congr fun x => hs M v (Fin.snoc xs x)

private theorem existential_castLE {ι : Type u'} {m : ℕ} {φ : L.BoundedFormula ι m}
    (hφ : φ.IsExistential) : ∀ {n} {h : m ≤ n}, (φ.castLE h).IsExistential :=
  BoundedFormula.IsExistential.recOn
    (motive := @fun m φ _ => ∀ (n : ℕ) (h : m ≤ n), (φ.castLE h).IsExistential) hφ
    (@fun _ _ hq _ _ => hq.castLE.isExistential)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

private theorem existential_liftAt {ι : Type u'} {m : ℕ} {φ : L.BoundedFormula ι m}
    (hφ : φ.IsExistential) {k n : ℕ} : (φ.liftAt k n).IsExistential :=
  BoundedFormula.IsExistential.recOn hφ
    (fun hq => hq.liftAt.isExistential)
    (fun _ ih => (existential_castLE ih).ex)

private theorem exists_existential_binary {ι : Type u'} {m : ℕ}
    {φ ψ : L.BoundedFormula ι m} (hφ : φ.IsExistential) (hψ : ψ.IsExistential)
    (b : Bool) :
    ∃ χ : L.BoundedFormula ι m, χ.IsExistential ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : ι → M) (xs : Fin m → M),
        χ.Realize v xs ↔
          if b then φ.Realize v xs ∧ ψ.Realize v xs else φ.Realize v xs ∨ ψ.Realize v xs := by
  induction hφ with
  | @of_isQF m φ hq =>
    induction hψ with
    | @of_isQF m ψ hp =>
      refine ⟨if b then φ ⊓ ψ else φ ⊔ ψ, ?_, ?_⟩
      · cases b
        · exact (hq.sup hp).isExistential
        · exact (hq.inf hp).isExistential
      · intro M _ _ v xs
        cases b <;> simp
    | @ex m ψ he ih =>
      obtain ⟨χ, hc, ht⟩ := ih (φ := φ.liftAt 1 m) hq.liftAt
      refine ⟨χ.ex, hc.ex, ?_⟩
      intro M _ _ v xs
      rw [BoundedFormula.realize_ex]
      refine (exists_congr fun x => ht M v (Fin.snoc xs x)).trans ?_
      cases b <;> simp [BoundedFormula.realize_ex, exists_or]
  | @ex m φ he ih =>
    obtain ⟨χ, hc, ht⟩ := ih (ψ := ψ.liftAt 1 m) (existential_liftAt hψ)
    refine ⟨χ.ex, hc.ex, ?_⟩
    intro M _ _ v xs
    rw [BoundedFormula.realize_ex]
    refine (exists_congr fun x => ht M v (Fin.snoc xs x)).trans ?_
    cases b <;> simp [BoundedFormula.realize_ex, exists_or]

/-- A finite conjunction of existential formulas has a shared-syntax existential equivalent. -/
theorem existential_finite_conjunction {n : ℕ} (s : List (L.Formula (Fin n)))
    (hs : ∀ ψ ∈ s, ψ.IsExistential) :
    ∃ χ : L.Formula (Fin n), χ.IsExistential ∧
      (∅ : L.Theory) ⊨ᵇ (χ.iff (s.foldr (· ⊓ ·) ⊤)) := by
  induction s with
  | nil =>
    refine ⟨⊤, BoundedFormula.IsQF.top.isExistential, ?_⟩
    intro M v xs
    simp
  | cons φ rest ih =>
    obtain ⟨ψ, hψ, he⟩ := ih (fun θ hθ => hs θ (by simp [hθ]))
    obtain ⟨χ, hχ, hc⟩ := exists_existential_binary
      (hs φ (by simp)) hψ true
    refine ⟨χ, hχ, ?_⟩
    intro M v xs
    have hr := he M v xs
    simp only [BoundedFormula.realize_iff] at hr ⊢
    simpa [hr] using hc M v xs

/-- The corresponding finite disjunction result, including the empty disjunction. -/
theorem existential_finite_disjunction {n : ℕ} (s : List (L.Formula (Fin n)))
    (hs : ∀ ψ ∈ s, ψ.IsExistential) :
    ∃ χ : L.Formula (Fin n), χ.IsExistential ∧
      (∅ : L.Theory) ⊨ᵇ (χ.iff (s.foldr (· ⊔ ·) ⊥)) := by
  induction s with
  | nil =>
    refine ⟨⊥, BoundedFormula.isQF_bot.isExistential, ?_⟩
    intro M v xs
    simp
  | cons φ rest ih =>
    obtain ⟨ψ, hψ, he⟩ := ih (fun θ hθ => hs θ (by simp [hθ]))
    obtain ⟨χ, hχ, hc⟩ := exists_existential_binary
      (hs φ (by simp)) hψ false
    refine ⟨χ, hχ, ?_⟩
    intro M v xs
    have hr := he M v xs
    simp only [BoundedFormula.realize_iff] at hr ⊢
    simpa [hr] using hc M v xs

/-- Negating an existential formula has a shared-syntax universal equivalent. -/
theorem existential_negation_universal {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : φ.IsExistential) :
    ∃ ψ : L.Formula (Fin n), ψ.IsUniversal ∧
      (∅ : L.Theory) ⊨ᵇ (ψ.iff φ.not) := by
  obtain ⟨ψ, hψ, he⟩ := exists_universal_not hφ
  refine ⟨ψ, hψ, ?_⟩
  intro M v xs
  simpa using he M v xs

/-- The reverse duality is also needed for the formula preservation converse. -/
theorem universal_negation_existential {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : φ.IsUniversal) :
    ∃ ψ : L.Formula (Fin n), ψ.IsExistential ∧
      (∅ : L.Theory) ⊨ᵇ (ψ.iff φ.not) := by
  obtain ⟨ψ, hψ, he⟩ := exists_existential_not hφ
  refine ⟨ψ, hψ, ?_⟩
  intro M v xs
  simpa using he M v xs

end Lemmatheca.MathematicalLogic.Preservation
