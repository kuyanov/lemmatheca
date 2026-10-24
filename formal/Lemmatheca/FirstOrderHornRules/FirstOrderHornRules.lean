import Lemmatheca.HornClauses.HornClauses
import Lemmatheca.HerbrandModels.HerbrandModels
import Mathlib.Data.Fintype.Card

/-! Definite rules over actual first-order terms, their grounding, and least models. -/
namespace Lemmatheca.MathematicalLogic.FirstOrderHornRules

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.HerbrandModels

universe u v w z

/-- A definite rule has a finite body and exactly one positive head. -/
structure DefiniteRule (α : Type w) where
  body : Finset α
  head : α
  deriving DecidableEq

namespace DefiniteRule
variable {α : Type w} {β : Type z}

def Holds (r : DefiniteRule α) (I : Set α) : Prop :=
  (∀ a ∈ r.body, a ∈ I) → r.head ∈ I

def toHorn (r : DefiniteRule α) : HornClauses.Rule α := ⟨r.body, some r.head⟩

def map [DecidableEq β] (f : α → β) (r : DefiniteRule α) : DefiniteRule β :=
  ⟨r.body.image f, f r.head⟩
end DefiniteRule

section Closure
variable {α : Type w}

def Models (Γ : Set (DefiniteRule α)) (I : Set α) : Prop :=
  ∀ r ∈ Γ, r.Holds I

def least (Γ : Set (DefiniteRule α)) : Set α := ⋂₀ {I | Models Γ I}

def step (Γ : Set (DefiniteRule α)) (X : Set α) : Set α :=
  X ∪ {a | ∃ r ∈ Γ, r.head = a ∧ ∀ b ∈ r.body, b ∈ X}

def stage (Γ : Set (DefiniteRule α)) : ℕ → Set α
  | 0 => ∅
  | n + 1 => step Γ (stage Γ n)

def omegaStage (Γ : Set (DefiniteRule α)) : Set α := ⋃ n, stage Γ n

theorem toHorn_models (Γ : Set (DefiniteRule α)) (I : Set α) :
    HornClauses.TheoryModels (DefiniteRule.toHorn '' Γ) I ↔ Models Γ I := by
  simp [HornClauses.TheoryModels, Models, DefiniteRule.toHorn,
    HornClauses.Holds, DefiniteRule.Holds]

theorem universe_model (Γ : Set (DefiniteRule α)) : Models Γ Set.univ := by
  intro r _ _
  exact Set.mem_univ _

theorem model_intersection (Γ : Set (DefiniteRule α)) {𝓜 : Set (Set α)}
    (h𝓜 : 𝓜.Nonempty) (hm : ∀ I ∈ 𝓜, Models Γ I) : Models Γ (⋂₀ 𝓜) := by
  apply (toHorn_models Γ _).mp
  exact HornClauses.model_intersection _ h𝓜 (fun I hI => (toHorn_models Γ I).mpr (hm I hI))

theorem least_model (Γ : Set (DefiniteRule α)) :
    Models Γ (least Γ) ∧ ∀ I, Models Γ I → least Γ ⊆ I := by
  have hm : Models Γ (least Γ) :=
    model_intersection Γ ⟨Set.univ, universe_model Γ⟩ (fun _ h => h)
  exact ⟨hm, fun I hI a ha => Set.mem_sInter.mp ha I hI⟩

theorem step_inflation (Γ : Set (DefiniteRule α)) (X : Set α) : X ⊆ step Γ X := by
  exact Set.subset_union_left

theorem step_monotone (Γ : Set (DefiniteRule α)) : Monotone (step Γ) := by
  intro X Y h a ha
  rcases ha with ha | ⟨r, hr, he, hb⟩
  · exact Or.inl (h ha)
  · exact Or.inr ⟨r, hr, he, fun b hb' => h (hb b hb')⟩

theorem stage_increasing (Γ : Set (DefiniteRule α)) (n : ℕ) :
    stage Γ n ⊆ stage Γ (n + 1) := by
  exact step_inflation Γ _

theorem stage_le_model (Γ : Set (DefiniteRule α)) {I : Set α}
    (hI : Models Γ I) (n : ℕ) : stage Γ n ⊆ I := by
  induction n with
  | zero => exact Set.empty_subset _
  | succ n ih =>
    intro a ha
    rcases ha with ha | ⟨r, hr, rfl, hb⟩
    · exact ih ha
    · exact hI r hr (fun b hb' => ih (hb b hb'))

theorem stationary (Γ : Set (DefiniteRule α)) {n : ℕ}
    (h : stage Γ (n + 1) = stage Γ n) (k : ℕ) :
    stage Γ (n + k) = stage Γ n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, stage, ih]
    exact h

theorem fixed_iff_model (Γ : Set (DefiniteRule α)) (I : Set α) :
    step Γ I = I ↔ Models Γ I := by
  constructor
  · intro h r hr hb
    rw [← h]
    exact Or.inr ⟨r, hr, rfl, hb⟩
  · intro h
    apply Set.Subset.antisymm
    · rintro a (ha | ⟨r, hr, rfl, hb⟩)
      · exact ha
      · exact h r hr hb
    · exact step_inflation Γ I

theorem finite_body_stage (Γ : Set (DefiniteRule α)) (B : Finset α)
    (hB : ∀ b ∈ B, b ∈ omegaStage Γ) :
    ∃ n, ∀ b ∈ B, b ∈ stage Γ n := by
  classical
  have mono : Monotone (stage Γ) := monotone_nat_of_le_succ (stage_increasing Γ)
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a B ha ih =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hB a (Finset.mem_insert_self _ _))
    obtain ⟨m, hm⟩ := ih (fun b hb => hB b (Finset.mem_insert_of_mem hb))
    refine ⟨max n m, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact mono (le_max_left _ _) hn
    · exact mono (le_max_right _ _) (hm b hb)

theorem omega_is_model (Γ : Set (DefiniteRule α)) :
    Models Γ (omegaStage Γ) := by
  intro r hr hb
  obtain ⟨n, hn⟩ := finite_body_stage Γ r.body hb
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨r, hr, rfl, hn⟩⟩

theorem omega_fixed (Γ : Set (DefiniteRule α)) :
    step Γ (omegaStage Γ) = omegaStage Γ := by
  exact (fixed_iff_model Γ _).mpr (omega_is_model Γ)

theorem omega_eq_least (Γ : Set (DefiniteRule α)) : omegaStage Γ = least Γ := by
  apply Set.Subset.antisymm
  · rintro a ha
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    exact stage_le_model Γ (least_model Γ).1 n hn
  · exact (least_model Γ).2 _ (omega_is_model Γ)

theorem least_mem_iff_stage (Γ : Set (DefiniteRule α)) (a : α) :
    a ∈ least Γ ↔ ∃ n, a ∈ stage Γ n := by
  rw [← omega_eq_least]
  exact Set.mem_iUnion
end Closure

section FiniteClosure
variable {α : Type w} [DecidableEq α]

/-- A finite, simultaneous update with finite membership tests. -/
def finiteStep (Γ : Finset (DefiniteRule α)) (X : Finset α) : Finset α :=
  X ∪ Γ.biUnion (fun r => if r.body ⊆ X then {r.head} else ∅)

def finiteStage (Γ : Finset (DefiniteRule α)) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => finiteStep Γ (finiteStage Γ n)

def finiteAnswer [Fintype α] (Γ : Finset (DefiniteRule α)) (a : α) : Bool :=
  decide (a ∈ finiteStage Γ (Fintype.card α))

theorem finiteStep_bridge (Γ : Finset (DefiniteRule α)) (X : Finset α) :
    (↑(finiteStep Γ X) : Set α) = step (↑Γ) (↑X) := by
  ext a
  simp only [finiteStep, Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion,
    step, Set.mem_union, Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  apply exists_congr
  intro r
  have hbody : (∀ b ∈ r.body, b ∈ X) ↔ r.body ⊆ X := Iff.rfl
  rw [hbody]
  by_cases hb : r.body ⊆ X <;> simp [hb, eq_comm]

theorem finiteStep_toHorn (Γ : Finset (DefiniteRule α)) (X : Finset α) :
    HornClauses.step (Γ.image DefiniteRule.toHorn) X = finiteStep Γ X := by
  ext a
  simp [HornClauses.step, finiteStep, DefiniteRule.toHorn]

theorem finiteStage_bridge (Γ : Finset (DefiniteRule α)) (n : ℕ) :
    (↑(finiteStage Γ n) : Set α) = stage (↑Γ) n := by
  induction n with
  | zero => simp [finiteStage, stage]
  | succ n ih =>
    change (↑(finiteStep Γ (finiteStage Γ n)) : Set α) = step (↑Γ) (stage (↑Γ) n)
    rw [finiteStep_bridge, ih]

theorem finite_stabilization [Fintype α] (Γ : Finset (DefiniteRule α)) :
    finiteStep Γ (finiteStage Γ (Fintype.card α)) = finiteStage Γ (Fintype.card α) ∧
    (↑(finiteStage Γ (Fintype.card α)) : Set α) = least (↑Γ) := by
  classical
  have inc (n : ℕ) : finiteStage Γ n ⊆ finiteStage Γ (n + 1) :=
    Finset.subset_union_left
  have persistent {n : ℕ} (h : finiteStage Γ (n + 1) = finiteStage Γ n) (k : ℕ) :
      finiteStage Γ (n + k) = finiteStage Γ n := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.add_succ, finiteStage, ih]; exact h
  have fixed_or_card (n : ℕ) :
      finiteStage Γ (n + 1) = finiteStage Γ n ∨ n ≤ (finiteStage Γ n).card := by
    induction n with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      rcases ih with hf | hc
      · exact Or.inl (by change finiteStep Γ (finiteStage Γ (n + 1)) = _; rw [hf]; exact hf)
      · by_cases hf : finiteStage Γ (n + 1) = finiteStage Γ n
        · exact Or.inl (by change finiteStep Γ (finiteStage Γ (n + 1)) = _; rw [hf]; exact hf)
        · have hlt := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨inc n, Ne.symm hf⟩)
          exact Or.inr (by omega)
  have hf : finiteStep Γ (finiteStage Γ (Fintype.card α)) = finiteStage Γ (Fintype.card α) := by
    rcases fixed_or_card (Fintype.card α) with h | h
    · exact h
    · have he : finiteStage Γ (Fintype.card α) = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using h)
      simp [he, finiteStep]
  refine ⟨hf, ?_⟩
  have hm : Models (↑Γ) (↑(finiteStage Γ (Fintype.card α)) : Set α) := by
    apply (fixed_iff_model (↑Γ : Set (DefiniteRule α))
      (↑(finiteStage Γ (Fintype.card α)) : Set α)).mp
    rw [← finiteStep_bridge, hf]
  apply Set.Subset.antisymm
  · rw [finiteStage_bridge]
    exact stage_le_model (↑Γ : Set (DefiniteRule α))
      (least_model (↑Γ : Set (DefiniteRule α))).1 _
  · exact (least_model (↑Γ : Set (DefiniteRule α))).2 _ hm

theorem finiteAnswer_correct [Fintype α] (Γ : Finset (DefiniteRule α)) (a : α) :
    finiteAnswer Γ a = true ↔ a ∈ least (↑Γ) := by
  simp only [finiteAnswer, decide_eq_true_eq]
  change a ∈ (↑(finiteStage Γ (Fintype.card α)) : Set α) ↔ _
  rw [(finite_stabilization Γ).2]
end FiniteClosure

variable {L : Language.{u,v}}

/-- Each rule carries a finite variable context, permitting rules of different arities. -/
structure Rule (L : Language.{u,v}) where
  arity : ℕ
  body : Finset (Atom L (Fin arity))
  head : Atom L (Fin arity)

namespace Rule

noncomputable def formula (r : Rule L) : L.Formula (Fin r.arity) :=
  ((r.body.toList.map Atom.toFormula).foldr (· ⊓ ·) ⊤).imp r.head.toFormula

/-- The actual shared universally closed first-order sentence. -/
noncomputable def sentence (r : Rule L) : L.Sentence :=
  (BoundedFormula.relabel (Sum.inr : Fin r.arity → Empty ⊕ Fin r.arity) r.formula).alls

def Realize {M : Type z} [L.Structure M] (r : Rule L) (vs : Fin r.arity → M) : Prop :=
  (∀ a ∈ r.body, a.Realize vs) → r.head.Realize vs

def ground [DecidableEq (GroundAtom L)] (r : Rule L)
    (σ : Fin r.arity → GroundTerm L) : DefiniteRule (GroundAtom L) :=
  ⟨r.body.image (Atom.subst σ), r.head.subst σ⟩

theorem formula_realize {M : Type z} [L.Structure M] (r : Rule L)
    (vs : Fin r.arity → M) : r.formula.Realize vs ↔ r.Realize vs := by
  change BoundedFormula.Realize _ vs default ↔ _
  simp only [formula, BoundedFormula.realize_imp, BoundedFormula.realize_foldr_inf,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Finset.mem_toList]
  simp only [← Atom.realize_toFormula, Realize, Formula.Realize]

theorem sentence_realize {M : Type z} [L.Structure M] (r : Rule L) :
    M ⊨ r.sentence ↔ ∀ vs : Fin r.arity → M, r.Realize vs := by
  simp only [sentence, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_relabel, Function.comp_def, Sum.elim_inr,
    Fin.castAdd_zero, Nat.add_zero, Fin.cast_eq_self]
  apply forall_congr'
  intro a
  have he : (fun x : Fin 0 => a (Fin.natAdd r.arity x)) = default := Subsingleton.elim _ _
  rw [he]
  exact formula_realize r a

theorem ground_realize {M : Type z} [L.Structure M] (r : Rule L)
    (σ : Fin r.arity → GroundTerm L) :
    (r.ground σ).Holds {a | a.Realize (Empty.elim : Empty → M)} ↔
      r.Realize (fun i => (σ i).realize (Empty.elim : Empty → M)) := by
  classical
  simp only [ground, DefiniteRule.Holds, Finset.mem_image, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq, Atom.subst_realize]
  rfl
end Rule

noncomputable def theory (P : Set (Rule L)) : L.Theory := Rule.sentence '' P

def grounding (P : Set (Rule L)) : Set (DefiniteRule (GroundAtom L)) :=
  {g | ∃ r ∈ P, ∃ σ : Fin r.arity → GroundTerm L, r.ground σ = g}

/-- The specified term structure uses the supplied set for all ground relations. -/
@[instance_reducible]
noncomputable def interpretation (I : Set (GroundAtom L)) : L.Structure (GroundTerm L) :=
  termStructure (fun a => @decide (a ∈ I) (Classical.propDecidable _))

def induced {M : Type z} [L.Structure M] : Set (GroundAtom L) :=
  {a | a.Realize (Empty.elim : Empty → M)}

theorem theory_models_iff {M : Type z} [L.Structure M] (P : Set (Rule L)) :
    M ⊨ theory P ↔ ∀ r ∈ P, ∀ vs : Fin r.arity → M, r.Realize vs := by
  rw [Theory.model_iff]
  constructor
  · intro h r hr
    exact (Rule.sentence_realize r).mp (h _ ⟨r, hr, rfl⟩)
  · rintro h _ ⟨r, hr, rfl⟩
    exact (Rule.sentence_realize r).mpr (h r hr)

theorem interpretation_atom (I : Set (GroundAtom L)) (a : GroundAtom L) :
    @Atom.Realize L Empty (GroundTerm L) (interpretation I) a Empty.elim ↔ a ∈ I := by
  classical
  cases a with
  | mk n r ts =>
    change decide ((⟨n, r, fun i =>
      @Term.realize L (GroundTerm L) (interpretation I) Empty Empty.elim (ts i)⟩ :
        GroundAtom L) ∈ I) = true ↔ _
    simp only [ground_term_self, decide_eq_true_eq]

theorem interpretation_models [Nonempty (GroundTerm L)] (P : Set (Rule L))
    (I : Set (GroundAtom L)) :
    @Theory.Model L (GroundTerm L) (interpretation I) (theory P) ↔
      Models (grounding P) I := by
  classical
  let := interpretation I
  have hi : induced (M := GroundTerm L) = I := by
    ext a
    exact interpretation_atom I a
  rw [theory_models_iff]
  constructor
  · intro h g hg
    obtain ⟨r, hr, σ, he⟩ := hg
    subst g
    rw [← hi]
    apply (r.ground_realize σ).mpr
    simpa only [interpretation, ground_term_self] using h r hr σ
  · intro h r hr σ
    have hg := h (r.ground σ) ⟨r, hr, σ, rfl⟩
    rw [← hi] at hg
    have hh := (r.ground_realize σ).mp hg
    simpa only [interpretation, ground_term_self] using hh

theorem induced_model {M : Type z} [L.Structure M] (P : Set (Rule L))
    (hM : M ⊨ theory P) : Models (grounding P) (induced (M := M)) := by
  intro g hg
  obtain ⟨r, hr, σ, he⟩ := hg
  subst g
  exact (r.ground_realize σ).mpr ((theory_models_iff P).mp hM r hr _)

theorem ground_consequence [Nonempty (GroundTerm L)] (P : Set (Rule L))
    (a : GroundAtom L) :
    a ∈ least (grounding P) ↔ theory P ⊨ᵇ a.toFormula := by
  classical
  constructor
  · intro ha
    apply Theory.models_sentence_iff.mpr
    intro M
    have hm := induced_model P M.is_model
    have ht := (least_model (grounding P)).2 _ hm ha
    have hh := (Atom.realize_toFormula a Empty.elim).mpr ht
    simpa only [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim] using hh
  · intro h
    let := interpretation (least (grounding P))
    let : GroundTerm L ⊨ theory P :=
      (interpretation_models P _).mpr (least_model (grounding P)).1
    have ht := h.realize_sentence (GroundTerm L)
    have hh : a.toFormula.Realize (M := GroundTerm L) Empty.elim := by
      simpa only [Sentence.Realize, Subsingleton.elim (default : Empty → GroundTerm L) Empty.elim] using ht
    exact (interpretation_atom _ a).mp ((Atom.realize_toFormula a Empty.elim).mp hh)

/-- Adding a fresh constant preserves every old-language sentence consequence. -/
theorem fresh_constant_consequence (T : L.Theory) (A : L.Sentence) :
    T ⊨ᵇ A ↔ (freshInclusion L).onTheory T ⊨ᵇ (freshInclusion L).onSentence A := by
  classical
  let j := freshInclusion L
  have hn : j.onSentence A.not = (j.onSentence A).not := rfl
  have hu : j.onTheory (T ∪ {A.not}) = j.onTheory T ∪ {(j.onSentence A).not} := by
    simp only [LHom.onTheory, Set.image_union, Set.image_singleton, hn]
  rw [Theory.models_iff_not_satisfiable, Theory.models_iff_not_satisfiable, ← hu]
  exact not_congr (Theory.isSatisfiable_onTheory_iff LHom.sumInl_injective).symm

/-- All positive-arity function-symbol types are empty. -/
def FunctionFree (L : Language.{u,v}) : Prop := ∀ n, 0 < n → IsEmpty (L.Functions n)

theorem constantTerm_bijective (hL : FunctionFree L) :
    Function.Bijective (Constants.term : L.Constants → GroundTerm L) := by
  constructor
  · intro c d h
    exact (by simpa [Constants.term, Term.func.injEq] using h : c = d)
  · intro t
    cases t with
    | var x => exact x.elim
    | @func n f ts =>
      cases n with
      | zero => exact ⟨f, congrArg (Term.func f) (Subsingleton.elim _ _)⟩
      | succ n => exact False.elim ((hL (n + 1) (Nat.succ_pos _)).false f)

noncomputable def constantEquiv (hL : FunctionFree L) : L.Constants ≃ GroundTerm L :=
  Equiv.ofBijective Constants.term (constantTerm_bijective hL)

@[instance_reducible]
noncomputable def constantTermFintype (hL : FunctionFree L) [Fintype L.Constants] :
    Fintype (GroundTerm L) := Fintype.ofEquiv _ (constantEquiv hL)

/-- The base is the disjoint union of argument tuples, indexed by relation symbols. -/
def atomTuplesEquiv : GroundAtom L ≃ (Σ r : (Σ n, L.Relations n), Fin r.1 → GroundTerm L) where
  toFun a := ⟨⟨a.arity, a.relation⟩, a.terms⟩
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable instance groundAtomFintype [Fintype (Σ n, L.Relations n)]
    [Fintype (GroundTerm L)] : Fintype (GroundAtom L) :=
  Fintype.ofEquiv _ atomTuplesEquiv.symm

theorem groundAtom_card [Fintype (Σ n, L.Relations n)] [Fintype (GroundTerm L)] :
    Fintype.card (GroundAtom L) =
      ∑ r : (Σ n, L.Relations n), (Fintype.card (GroundTerm L)) ^ r.1 := by
  rw [Fintype.card_congr atomTuplesEquiv, Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem groundAtom_card_constants (hL : FunctionFree L)
    [Fintype L.Constants] [Fintype (GroundTerm L)] [Fintype (Σ n, L.Relations n)] :
    Fintype.card (GroundAtom L) =
      ∑ r : (Σ n, L.Relations n), (Fintype.card L.Constants) ^ r.1 := by
  rw [groundAtom_card]
  simp only [← Fintype.card_congr (constantEquiv hL)]

/-- Enumerate each finite rule's finite set of ground substitutions. -/
def finiteGrounding [DecidableEq (GroundAtom L)] [Fintype (GroundTerm L)]
    (P : Finset (Rule L)) : Finset (DefiniteRule (GroundAtom L)) :=
  P.biUnion fun r => Finset.univ.image r.ground

theorem finiteGrounding_bridge [Fintype (GroundTerm L)] (P : Finset (Rule L)) :
    (↑(finiteGrounding P) : Set (DefiniteRule (GroundAtom L))) = grounding (↑P) := by
  ext g
  simp [finiteGrounding, grounding]

theorem ground_substitution_count (hL : FunctionFree L)
    [Fintype L.Constants] [Fintype (GroundTerm L)] (r : Rule L) :
    Fintype.card (Fin r.arity → GroundTerm L) =
      (Fintype.card L.Constants) ^ r.arity := by
  rw [Fintype.card_fun, Fintype.card_fin, ← Fintype.card_congr (constantEquiv hL)]

def answer [DecidableEq (GroundAtom L)] [Fintype (GroundAtom L)] [Fintype (GroundTerm L)]
    (P : Finset (Rule L)) (a : GroundAtom L) : Bool :=
  finiteAnswer (finiteGrounding P) a

private theorem finiteGrounding_bridge_any (d : DecidableEq (GroundAtom L))
    [Fintype (GroundTerm L)] (P : Finset (Rule L)) :
    (↑(@finiteGrounding L d inferInstance P) : Set (DefiniteRule (GroundAtom L))) = grounding (↑P) := by
  have he : d = HerbrandModels.atomDecidableEq := Subsingleton.elim _ _
  subst d
  exact finiteGrounding_bridge P

theorem finite_ground_answer [Nonempty (GroundTerm L)] [DecidableEq (GroundAtom L)]
    [Fintype (GroundAtom L)] [Fintype (GroundTerm L)] (P : Finset (Rule L)) (a : GroundAtom L) :
    answer P a = true ↔ theory (↑P) ⊨ᵇ a.toFormula := by
  unfold answer
  rw [finiteAnswer_correct, finiteGrounding_bridge_any, ground_consequence]

theorem finite_ground_stabilization [DecidableEq (GroundAtom L)]
    [Fintype (GroundAtom L)] [Fintype (GroundTerm L)] (P : Finset (Rule L)) :
    let Γ := finiteGrounding P
    let N := Fintype.card (GroundAtom L)
    finiteStep Γ (finiteStage Γ N) = finiteStage Γ N ∧
      (↑(finiteStage Γ N) : Set (GroundAtom L)) = least (grounding (↑P)) := by
  dsimp only
  have h := finite_stabilization (finiteGrounding P)
  rw [finiteGrounding_bridge_any] at h
  exact h

end Lemmatheca.MathematicalLogic.FirstOrderHornRules
