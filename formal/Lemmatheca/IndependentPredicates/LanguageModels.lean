import Lemmatheca.QuantifierElimination.QuantifierEliminationCriterion
import Lemmatheca.QuantifierElimination.QuantifierElimination
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-! The countably infinite unary language and its exact finite-cell axiom scheme. -/
namespace Lemmatheca.ModelTheory.IndependentPredicates

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms

inductive Predicate : ℕ → Type
  | pred (index : ℕ) : Predicate 1
  deriving DecidableEq

def Lang : Language := ⟨fun _ => Empty, Predicate⟩

instance : Lang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance countableSymbols : Countable Lang.Symbols := by
  let f : (Σ n, Predicate n) → ℕ := fun ⟨_, .pred n⟩ => n
  have hf : Function.Injective f := by
    rintro ⟨_, r⟩ ⟨_, t⟩ h
    cases r with
    | pred n =>
      cases t with
      | pred m =>
        change n = m at h
        cases h
        rfl
  let : Countable (Σ n, Predicate n) := hf.countable
  change Countable ((Σ _ : ℕ, Empty) ⊕ (Σ n, Predicate n))
  infer_instance

def predicate {M : Type*} [Lang.Structure M] (n : ℕ) (a : M) : Prop :=
  Structure.RelMap (L := Lang) (.pred n) (fun _ => a)

@[instance_reducible]
def structureOfPredicates {M : Type*} (P : ℕ → M → Prop) : Lang.Structure M where
  funMap := fun f _ => f.elim
  RelMap := fun r a => match r with | .pred n => P n (a 0)

def cell (M : Type*) [Lang.Structure M] (F G : Finset ℕ) : Set M :=
  {a | (∀ n ∈ F, predicate n a) ∧ ∀ n ∈ G, ¬ predicate n a}

def predicateFormula {α : Type*} {k : ℕ} (n : ℕ) (x : Lang.Term (α ⊕ Fin k)) :
    Lang.BoundedFormula α k := .rel (.pred n) (fun _ => x)

noncomputable def cellFormula {α : Type*} {k : ℕ} (F G : Finset ℕ)
    (x : Lang.Term (α ⊕ Fin k)) : Lang.BoundedFormula α k :=
  QuantifierElimination.conjunction
    ((F.toList.map fun n => predicateFormula n x) ++
      G.toList.map fun n => (predicateFormula n x).not)

noncomputable def cellSentence (F G : Finset ℕ) (k : ℕ) : Lang.Sentence :=
  (QuantifierElimination.conjunction
    ((List.ofFn fun i : Fin k => cellFormula F G (.var (.inr i))) ++
      (((Finset.univ : Finset (Fin k × Fin k)).toList.filter fun p => p.1 < p.2).map
        fun p => (BoundedFormula.equal (.var (.inr p.1)) (.var (.inr p.2))).not))).exs

def independentTheory : Lang.Theory :=
  {σ | ∃ F G : Finset ℕ, Disjoint F G ∧ ∃ k : ℕ, σ = cellSentence F G k}

theorem theory_countable : independentTheory.Countable := by
  exact Set.to_countable independentTheory

theorem cellFormula_realize {M : Type*} [Lang.Structure M] {α : Type*} {k : ℕ}
    (F G : Finset ℕ) (x : Lang.Term (α ⊕ Fin k)) (a : α → M) (v : Fin k → M) :
    (cellFormula F G x).Realize a v ↔ x.realize (Sum.elim a v) ∈ cell M F G := by
  rw [cellFormula, QuantifierElimination.conjunction, BoundedFormula.realize_foldr_inf]
  constructor
  · intro h
    constructor
    · intro n hn
      exact h _ (List.mem_append_left _ (List.mem_map.mpr ⟨n, Finset.mem_toList.mpr hn, rfl⟩))
    · intro n hn
      exact h _ (List.mem_append_right _ (List.mem_map.mpr ⟨n, Finset.mem_toList.mpr hn, rfl⟩))
  · rintro ⟨hF, hG⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hφ
      exact hF n (Finset.mem_toList.mp hn)
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hφ
      exact hG n (Finset.mem_toList.mp hn)

theorem cellSentence_realize {M : Type*} [Lang.Structure M] (F G : Finset ℕ) (k : ℕ) :
    M ⊨ cellSentence F G k ↔
      ∃ a : Fin k → M, Function.Injective a ∧ ∀ i, a i ∈ cell M F G := by
  classical
  rw [cellSentence, Sentence.Realize, BoundedFormula.realize_exs]
  apply exists_congr
  intro a
  rw [QuantifierElimination.conjunction, BoundedFormula.realize_foldr_inf]
  constructor
  · intro h
    have hcell (i : Fin k) : a i ∈ cell M F G := by
      apply (cellFormula_realize (M := M) (α := Empty) F G (.var (.inr i)) default a).mp
      exact h _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    have hne (i j : Fin k) (hij : i < j) : a i ≠ a j := by
      exact h _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨(i,j), List.mem_filter.mpr ⟨Finset.mem_toList.mpr (Finset.mem_univ _), by simpa using hij⟩, rfl⟩))
    refine ⟨?_, hcell⟩
    intro i j hij
    by_contra hneij
    rcases lt_or_gt_of_ne hneij with hlt | hgt
    · exact hne i j hlt hij
    · exact hne j i hgt hij.symm
  · rintro ⟨hinj, hcell⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hφ
      exact (cellFormula_realize (M := M) (α := Empty) F G (.var (.inr i)) default a).mpr (hcell i)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      have hlt : p.1 < p.2 := of_decide_eq_true (List.mem_filter.mp hp).2
      change a p.1 ≠ a p.2
      exact fun he => (ne_of_lt hlt) (hinj he)

theorem model_iff_cells {M : Type*} [Lang.Structure M] :
    M ⊨ independentTheory ↔
      ∀ F G : Finset ℕ, Disjoint F G → (cell M F G).Infinite := by
  classical
  constructor
  · intro h F G hd hfin
    let : M ⊨ independentTheory := h
    let := hfin.fintype
    let k := Fintype.card (cell M F G) + 1
    have hσ : cellSentence F G k ∈ independentTheory := ⟨F, G, hd, k, rfl⟩
    obtain ⟨a, ha, hcell⟩ := (cellSentence_realize (M := M) F G k).mp
      (Theory.realize_sentence_of_mem independentTheory hσ)
    let g : Fin k → cell M F G := fun i => ⟨a i, hcell i⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact ha (congrArg Subtype.val hij)
    have hcard : k ≤ Fintype.card (cell M F G) := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hg
    exact Nat.not_succ_le_self _ hcard
  · intro h
    constructor
    rintro σ ⟨F, G, hd, k, rfl⟩
    let e := Set.Infinite.natEmbedding (cell M F G) (h F G hd)
    refine (cellSentence_realize (M := M) F G k).mpr ⟨fun i => (e i.val).val, ?_, ?_⟩
    · intro i j hij
      exact Fin.ext (e.injective (Subtype.ext hij))
    · intro i
      exact (e i.val).property

instance finiteSubsetStructure : Lang.Structure (Finset ℕ) :=
  structureOfPredicates fun n A => n ∈ A

instance subsetStructure : Lang.Structure (Set ℕ) :=
  structureOfPredicates fun n A => n ∈ A

def finiteWitness (F G : Finset ℕ) (r : ℕ) : Finset ℕ :=
  F ∪ {(if F ∪ G = ∅ then 0 else (F ∪ G).sup id + 1) + r}

private theorem marker_gt (F G : Finset ℕ) (r n : ℕ) (hn : n ∈ F ∪ G) :
    n < (if F ∪ G = ∅ then 0 else (F ∪ G).sup id + 1) + r := by
  have hne : F ∪ G ≠ ∅ := Finset.ne_empty_of_mem hn
  rw [ite_eq_right_iff.mpr (fun he => False.elim (hne he))]
  have h := Finset.le_sup (f := id) hn
  dsimp at h
  omega

theorem finiteWitness_mem (F G : Finset ℕ) (h : Disjoint F G) (r : ℕ) :
    finiteWitness F G r ∈ cell (Finset ℕ) F G := by
  constructor
  · intro n hn
    change n ∈ finiteWitness F G r
    exact Finset.mem_union_left _ hn
  · intro n hn hmem
    change n ∈ finiteWitness F G r at hmem
    rcases Finset.mem_union.mp hmem with hF | hm
    · exact Finset.disjoint_left.mp h hF hn
    · have he := Finset.mem_singleton.mp hm
      have hl := marker_gt F G r n (Finset.mem_union_right F hn)
      omega

theorem finiteWitness_injective (F G : Finset ℕ) :
    Function.Injective (finiteWitness F G) := by
  intro r s h
  let a := (if F ∪ G = ∅ then 0 else (F ∪ G).sup id + 1) + r
  have ha : a ∈ finiteWitness F G r := Finset.mem_union_right F (Finset.mem_singleton_self _)
  rw [h] at ha
  rcases Finset.mem_union.mp ha with hF | hs
  · have hl := marker_gt F G r a (Finset.mem_union_left G hF)
    exact False.elim ((lt_irrefl a) hl)
  · have he := Finset.mem_singleton.mp hs
    exact Nat.add_left_cancel he

theorem finiteSubset_model : Finset ℕ ⊨ independentTheory := by
  apply model_iff_cells.mpr
  intro F G hd
  exact Set.infinite_of_injective_forall_mem (finiteWitness_injective F G)
    (finiteWitness_mem F G hd)

theorem finiteSubset_countably_infinite : Countable (Finset ℕ) ∧ Infinite (Finset ℕ) := by
  exact ⟨inferInstance, inferInstance⟩

theorem subset_model : Set ℕ ⊨ independentTheory := by
  apply model_iff_cells.mpr
  intro F G hd
  let f : ℕ → Set ℕ := fun r => (finiteWitness F G r : Set ℕ)
  have hf : Function.Injective f := Finset.coe_injective.comp (finiteWitness_injective F G)
  apply Set.infinite_of_injective_forall_mem hf
  intro r
  exact finiteWitness_mem F G hd r

theorem models_infinite {M : Type*} [Lang.Structure M] [M ⊨ independentTheory] :
    Infinite M := by
  have h := model_iff_cells.mp (inferInstance : M ⊨ independentTheory)
    ∅ ∅ (Finset.disjoint_empty_left _)
  have he : cell M ∅ ∅ = Set.univ := by ext a; simp [cell]
  rw [he] at h
  exact Set.infinite_univ_iff.mp h

theorem fresh_cell_witness {M : Type*} [Lang.Structure M] [M ⊨ independentTheory]
    (F G : Finset ℕ) (hd : Disjoint F G) (A : Finset M) :
    ∃ b : M, b ∈ cell M F G ∧ b ∉ A := by
  exact (model_iff_cells.mp (inferInstance : M ⊨ independentTheory) F G hd).exists_notMem_finset A

def predicateSupport {α : Type*} : {k : ℕ} → Lang.BoundedFormula α k → Finset ℕ
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel (.pred n) _ => {n}
  | _, .imp φ ψ => predicateSupport φ ∪ predicateSupport ψ
  | _, .all φ => predicateSupport φ

end Lemmatheca.ModelTheory.IndependentPredicates
