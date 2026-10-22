import Lemmatheca.InductiveTheories.Diagrams
import Lemmatheca.ModelCompanions.ModelCompanions
import Mathlib.ModelTheory.Encoding
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! Existential requests, specified-map passes and set-sized model codes. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language
open Cardinal
open Lemmatheca.ModelTheory
open ModelCompleteness InductiveTheories
universe u v w
variable {L : Language.{u, v}}

/-- The class includes the original theory's model condition. -/
def IsEC (T : L.Theory) (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory)) : Prop :=
  M ⊨ T ∧ ∀ (N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N),
    ExistentiallyClosedEmbedding f

/-- The same earlier existential-closure definition, with model status already supplied. -/
theorem isEC_iff_existing (T : L.Theory) (M : Theory.ModelType.{u, v, max u v w} T) :
    IsEC T (Theory.ModelType.of ∅ M) ↔ ExistentiallyClosedModel.{u, v, w} T M := by
  change (M ⊨ T ∧ ExistentiallyClosedModel T M) ↔ ExistentiallyClosedModel T M
  exact ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

/-- Reflection of a fixed composite reflects witnesses from its middle object. -/
theorem reflection_of_composite {M N P : Type (max u v w)}
    [L.Structure M] [L.Structure N] [L.Structure P]
    (f : M ↪[L] N) (g : N ↪[L] P) (h : ExistentiallyClosedEmbedding (g.comp f)) :
    ExistentiallyClosedEmbedding f := by
  intro n φ hφ a hN
  apply h n φ hφ a
  have hpres := hφ.realize_embedding g hN
  have he : g ∘ (default : Fin 0 → N) = (default : Fin 0 → P) := Subsingleton.elim _ _
  have hc : (g.comp f) ∘ a = g ∘ (f ∘ a) := by
    funext i
    rfl
  simpa only [FirstOrder.Language.Formula.Realize, he, hc] using hpres

/-- Model completeness implies the actual union-closure property and a native axiomatization. -/
theorem modelComplete_inductive (T : L.Theory) (h : ModelComplete.{u, v, w} T) :
    IsInductive.{u, v, w} T ∧ HasUniversalExistentialAxiomatization T := by
  have hω : OmegaChainClosed.{u, v, w} T := by
    apply (omega_closed_iff_literal T).mpr
    intro M C hm
    have hc : C.IsElementary := by
      intro i j hij
      let : C.stage i ⊨ T := hm i
      let : C.stage j ⊨ T := hm j
      exact h (Theory.ModelType.of T (C.stage i)) (Theory.ModelType.of T (C.stage j))
        (C.inclusion i j hij)
    obtain ⟨e, _⟩ := C.elementary_union hc 0
    exact (e.theory_model_iff T).mp (hm 0)
  obtain ⟨h₁, h₂, h₃, _⟩ := inductive_characterization.{u, v, w} T
  exact ⟨h₁.mpr hω, h₃.mp (h₂.mp hω)⟩

/-- This conclusion does not assume that the source already models the theory. -/
theorem reflecting_model_status (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (M : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
    (N : Theory.ModelType.{u, v, max u v w} T) (f : M ↪[L] N)
    (hf : ExistentiallyClosedEmbedding f) : M ⊨ T := by
  have hp : M ⊨ universalExistentialPart T :=
    (model_part_iff_reflecting_embedding T M).mpr
      ⟨N, inferInstance, inferInstance, inferInstance, f, hf⟩
  let := hp
  exact model_part_of_omega_closed T (inductive_implies_omega T hT)
    (Theory.ModelType.of (universalExistentialPart T) M)

/-- A shared existential formula together with its original finite parameter tuple. -/
structure Request (L : Language.{u, v}) (M : Type w) where
  arity : ℕ
  formula : L.Formula (Fin arity)
  existential : formula.IsExistential
  parameters : Fin arity → M

namespace Request
variable {M N : Type (max u v w)} [L.Structure M] [L.Structure N]

def Realized (r : Request L M) (f : M ↪[L] N) : Prop := r.formula.Realize (f ∘ r.parameters)

def Possible (T : L.Theory) (r : Request L M) (f : M ↪[L] N) : Prop :=
  ∃ (P : Theory.ModelType.{u, v, max u v w} T) (g : N ↪[L] P), r.Realized (g.comp f)

/-- A rejected request cannot become possible after adjoining further elements. -/
theorem impossible_persists (T : L.Theory) (r : Request L M) (f : M ↪[L] N)
    (P : Type (max u v w)) [L.Structure P] (g : N ↪[L] P)
    (h : ¬ r.Possible T f) : ¬ r.Possible T (g.comp f) := by
  rintro ⟨Q, k, hQ⟩
  exact h ⟨Q, k.comp g, hQ⟩
end Request

/-- Only the parameters in the supplied domain are handled by this pass. -/
def IsCompletedPass (T : L.Theory) {M N : Type (max u v w)}
    [L.Structure M] [L.Structure N] (f : M ↪[L] N) : Prop :=
  ∀ r : Request L M, r.Possible T f → r.Realized f

/-- A single fixed cardinal bound for syntax, original parameters and all construction stages. -/
noncomputable def sizeBound (L : Language.{u, v}) (M : Type w) : Cardinal.{max u v w} :=
  max Cardinal.aleph0 (max (Cardinal.lift (#L.Symbols)) (Cardinal.lift (#M)))

/-- The whole family of structures and embeddings on these carriers is set-sized. -/
structure CodedModel (T : L.Theory) (κ : Cardinal.{max u v w}) where
  carrier : Set κ.out
  nonempty : carrier.Nonempty
  struc : L.Structure carrier
  models : @Theory.Model L carrier struc T

@[instance_reducible]
def CodedModel.asModel {T : L.Theory} {κ : Cardinal.{max u v w}} (C : CodedModel T κ) :
    Theory.ModelType.{u, v, max u v w} T where
  Carrier := C.carrier
  struc := C.struc
  is_model := C.models
  nonempty' := C.nonempty.to_subtype

theorem codedModel_card_le (T : L.Theory) (κ : Cardinal.{max u v w}) (C : CodedModel T κ) :
    #C.asModel ≤ κ := by
  exact (Cardinal.mk_subtype_le C.carrier).trans_eq (Cardinal.mk_out κ)

/-- The isomorphism retains the supplied model when its carrier is first coded. -/
theorem code_model (T : L.Theory) (κ : Cardinal.{max u v w})
    (M : Theory.ModelType.{u, v, max u v w} T) (hM : #M ≤ κ) :
    ∃ C : CodedModel T κ, Nonempty (M ≃[L] C.asModel) := by
  classical
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp (hM.trans_eq (Cardinal.mk_out κ).symm)
  let e : M ≃ Set.range f := Equiv.ofInjective f f.injective
  let S := e.inducedStructure (L := L)
  let := S
  let iso : M ≃[L] Set.range f := e.inducedStructureEquiv
  have hm : Set.range f ⊨ T := StrongHomClass.theory_model iso
  let C : CodedModel T κ :=
    { carrier := Set.range f
      nonempty := Set.range_nonempty f
      struc := S
      models := hm }
  exact ⟨C, ⟨iso⟩⟩

theorem requests_card_le (M : Type (max u v w)) : #(Request L M) ≤ sizeBound L M := by
  classical
  let κ : Cardinal.{max u v w} := sizeBound L M
  have hω : ℵ₀ ≤ κ := le_max_left _ _
  have hL : Cardinal.lift.{max u v w} L.card ≤ κ := by
    dsimp [κ, sizeBound, Language.card]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hM : #M ≤ κ := by
    dsimp [κ, sizeBound]
    rw [Cardinal.lift_id'.{max u v, w}]
    exact (le_max_right _ _).trans (le_max_right _ _)
  let enc : Request L M → Σ n : ℕ, L.Formula (Fin n) × (Fin n → M) :=
    fun r => ⟨r.arity, r.formula, r.parameters⟩
  have hi : Function.Injective enc := by
    rintro ⟨n, φ, hφ, a⟩ ⟨m, ψ, hψ, b⟩ h
    cases h
    rfl
  apply (Cardinal.mk_le_of_injective hi).trans
  rw [Cardinal.mk_sigma]
  have hf (n : ℕ) : Cardinal.lift.{max u v w} (#(L.Formula (Fin n))) ≤ κ := by
    have h₀ : #(L.Formula (Fin n)) ≤ max ℵ₀ ((n : Cardinal) + L.card) := by
      have hj : Function.Injective (fun φ : L.Formula (Fin n) =>
          (⟨0, φ⟩ : Σ k, L.BoundedFormula (Fin n) k)) := by
        intro φ ψ h
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      apply (Cardinal.mk_le_of_injective hj).trans
      simpa using (BoundedFormula.card_le (L := L) (α := Fin n))
    calc
      Cardinal.lift.{max u v w} (#(L.Formula (Fin n))) ≤
          max ℵ₀ ((n : Cardinal) + Cardinal.lift.{max u v w} L.card) := by
        simpa using (Cardinal.lift_le.mpr h₀)
      _ ≤ κ := max_le hω (Cardinal.add_le_of_le hω
        ((Cardinal.natCast_lt_aleph0 (n := n)).le.trans hω) hL)
  have hb (n : ℕ) : #(L.Formula (Fin n) × (Fin n → M)) ≤ κ := by
    rw [Cardinal.mk_prod, Cardinal.mk_arrow]
    simp only [Cardinal.mk_fin, Cardinal.lift_natCast,
      Cardinal.lift_id'.{0, max u v w}]
    rw [Cardinal.lift_id'.{max u v, w}]
    exact Cardinal.mul_le_of_le hω (hf n)
      ((Cardinal.power_le_power_right hM).trans (Cardinal.power_nat_le hω))
  calc
    Cardinal.sum (fun n : ℕ => #(L.Formula (Fin n) × (Fin n → M))) ≤
        Cardinal.sum (fun _ : ℕ => κ) := Cardinal.sum_le_sum _ _ hb
    _ = ℵ₀ * κ := by simp [Cardinal.sum_const]
    _ ≤ κ := Cardinal.mul_le_of_le hω hω le_rfl


/-- Löwenheim–Skolem shrinks an actual witness extension while retaining the source map. -/
theorem small_possible_extension (T : L.Theory) (κ : Cardinal.{max u v w})
    (hω : Cardinal.aleph0 ≤ κ) (hL : Cardinal.lift (#L.Symbols) ≤ κ)
    (M : Theory.ModelType.{u, v, max u v w} T) (hM : #M ≤ κ)
    (r : Request L M) (hr : r.Possible T (Embedding.refl L M)) :
    ∃ (C : CodedModel T κ) (f : M ↪[L] C.asModel), r.Realized f := by
  classical
  obtain ⟨P, g, hg⟩ := hr
  change r.formula.Realize (g ∘ r.parameters) at hg
  have hs : ∃ (Q : Theory.ModelType.{u, v, max u v w} T) (hQ : #Q ≤ κ)
      (f : M ↪[L] Q), r.Realized f := by
    by_cases hP : #P ≤ κ
    · exact ⟨P, hP, g, hg⟩
    · have hrange : #(Set.range g) ≤ κ := by
        have he : #(Set.range g) = #M :=
          (Cardinal.mk_congr (Equiv.ofInjective g g.injective)).symm
        exact he.trans_le hM
      obtain ⟨S, hS, hcard⟩ := L.exists_elementarySubstructure_card_eq (Set.range g) κ hω
        (by simpa only [Cardinal.lift_id] using hrange)
        (by
          rw [Cardinal.lift_umax.{max u v, w}, Cardinal.lift_id'.{max u v, w}]
          exact hL)
        (by simpa only [Cardinal.lift_id] using (le_of_lt (lt_of_not_ge hP)))
      let f : M ↪[L] S := Embedding.codRestrict S.toSubstructure g
        (fun x => hS (Set.mem_range_self x))
      let : Nonempty S := Nonempty.map f inferInstance
      have hsc : #S ≤ κ := by
        simpa only [Cardinal.lift_id] using hcard.le
      refine ⟨Theory.ModelType.of T S, hsc, f, ?_⟩
      have hc : S.subtype ∘ (f ∘ r.parameters) = g ∘ r.parameters := rfl
      change r.formula.Realize (f ∘ r.parameters)
      exact (S.subtype.map_formula r.formula (f ∘ r.parameters)).mp (hc ▸ hg)
  obtain ⟨Q, hQ, f, hf⟩ := hs
  obtain ⟨C, ⟨e⟩⟩ := code_model T κ Q hQ
  refine ⟨C, e.toEmbedding.comp f, ?_⟩
  change r.formula.Realize ((e.toEmbedding.comp f) ∘ r.parameters)
  have hc : (e.toEmbedding.comp f) ∘ r.parameters = e ∘ (f ∘ r.parameters) := rfl
  rw [hc]
  exact (e.toElementaryEmbedding.map_formula r.formula (f ∘ r.parameters)).mpr hf


end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
