import Lemmatheca.DefinableAndAlgebraicClosure.Closures
import Lemmatheca.DiagramsAndExtensions.Diagrams
import Mathlib.Data.Set.Card

/-! Unary finite/cofinite behavior and its native uniform-bound construction. -/
namespace Lemmatheca.ModelTheory.StronglyMinimalSets
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Closures
open Lemmatheca.ModelTheory.Diagrams
universe u v w w' z
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

def Cofinite (s : Set M) : Prop := sᶜ.Finite

def Minimal (L : Language.{u,v}) (M : Type w) [L.Structure M] : Prop :=
  Infinite M ∧ ∀ s : Set M, (Set.univ : Set M).Definable₁ L s → s.Finite ∨ Cofinite s

/-- The elementary diagram keeps the specified original structure as named data. -/
def StronglyMinimalStructure (L : Language.{u,v}) (M : Type w) [L.Structure M] : Prop :=
  Minimal L M ∧ ∀ P : Theory.ModelType.{max u w,v,max u v w} (L.elementaryDiagram M),
    letI : L.Structure P := (L.lhomWithConstants M).reduct P
    Minimal L P

def StronglyMinimalTheory (T : L.Theory) : Prop :=
  ∀ P : Theory.ModelType.{u,v,max u v} T, Minimal L P

def fiber {α : Type z} (φ : L.Formula (α ⊕ Fin 1)) (b : α → M) : Set M :=
  {x | φ.Realize (Sum.elim b (fun _ => x))}

def Small (s : Set M) (N : ℕ) : Prop := s.Finite ∧ s.ncard ≤ N

theorem fiberBound_iff_small [Nonempty M] {α : Type z}
    (φ : L.Formula (α ⊕ Fin 1)) (N : ℕ) (b : α → M) :
    (fiberBound φ N).Realize b ↔ Small (fiber φ b) N := by
  classical
  rw [fiberBound_iff_finite_card]
  constructor
  · rintro ⟨s,hs,hφ⟩
    have he : fiber φ b = (s : Set M) := Set.ext hφ
    rw [he]
    exact ⟨s.finite_toSet,by simpa using hs⟩
  · rintro ⟨hf,hn⟩
    refine ⟨hf.toFinset,?_,?_⟩
    · rwa [←Set.ncard_eq_toFinset_card _ hf]
    · intro x
      exact hf.mem_toFinset.symm

theorem not_small_iff_embedding (s : Set M) (k : ℕ) (hk : 0 < k) :
    ¬Small s (k-1) ↔ ∃ a : Fin k ↪ M, ∀ i, a i ∈ s := by
  classical
  constructor
  · intro hn
    obtain ⟨t,ht,hkcard⟩ : ∃ t : Finset M, (t : Set M) ⊆ s ∧ k ≤ t.card := by
      by_cases hf : s.Finite
      · refine ⟨hf.toFinset,fun _ hx => hf.mem_toFinset.mp hx,?_⟩
        rw [←Set.ncard_eq_toFinset_card _ hf]
        have : ¬s.ncard ≤ k-1 := fun h => hn ⟨hf,h⟩
        omega
      · obtain ⟨t,ht,he⟩ := (show s.Infinite from hf).exists_subset_card_eq k
        exact ⟨t,ht,he.ge⟩
    let a : Fin k ↪ M := ((Fin.castLEEmb hkcard).trans t.equivFin.symm.toEmbedding).trans
      (Function.Embedding.subtype (fun x : M => x ∈ t))
    exact ⟨a,fun i => ht (t.equivFin.symm (Fin.castLEEmb hkcard i)).property⟩
  · rintro ⟨a,ha⟩ ⟨hf,hn⟩
    let t : Finset M := Finset.univ.image a
    have ht : t.card = k := by simp [t,Finset.card_image_of_injective, a.injective]
    have hsub : (t : Set M) ⊆ s := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ha i
    have hcard : k ≤ s.ncard := by
      rw [←ht]
      simpa using Set.ncard_le_ncard hsub hf
    omega


theorem minimal_iff_fibers :
    Minimal L M ↔ Infinite M ∧ ∀ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (b : Fin n → M),
      (fiber φ b).Finite ∨ Cofinite (fiber φ b) := by
  classical
  constructor
  · rintro ⟨hinf,h⟩
    refine ⟨hinf,?_⟩
    intro n φ b
    apply h
    apply Set.definable_iff_exists_formula_sum.mpr
    let ψ : L.Formula ((Set.univ : Set M) ⊕ Fin 1) :=
      φ.relabel (Sum.map (fun i => (⟨b i,Set.mem_univ _⟩ : (Set.univ : Set M))) id)
    refine ⟨ψ,?_⟩
    ext x
    simp only [ψ,Formula.realize_relabel]
    change φ.Realize (Sum.elim b (fun _ : Fin 1 => x 0)) ↔ φ.Realize _
    apply Iff.of_eq
    congr 1
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  · rintro ⟨hinf,h⟩
    refine ⟨hinf,?_⟩
    intro s hs
    obtain ⟨A₀,hA₀,hdef⟩ := Set.definable_iff_finitely_definable.mp hs
    obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hdef
    let e := Fintype.equivFin (A₀ : Set M)
    let b : Fin (Fintype.card (A₀ : Set M)) → M := fun i => (e.symm i).val
    let ψ := φ.relabel (Sum.map e id)
    have he : fiber ψ b = s := by
      ext x
      simp only [fiber,Set.mem_ofPred_eq,ψ,Formula.realize_relabel]
      have hv : Sum.elim b (fun _ : Fin 1 => x) ∘ Sum.map e id =
          Sum.elim (fun a : (A₀ : Set M) => a.val) (fun _ : Fin 1 => x) := by
        funext i
        cases i <;> simp [b,Function.comp_apply]
      rw [hv]
      change (fun _ : Fin 1 => x) ∈ {v | φ.Realize (Sum.elim (↑) v)} ↔ x ∈ s
      rw [←hφ]
      rfl
    simpa only [he] using h _ ψ b




def FiniteSideBound (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (N : ℕ) : Prop :=
  ∀ P : Theory.ModelType.{u,v,max u v} T, ∀ b : Fin n → P,
    Small (fiber φ b) N ∨ Small (fiber φ b)ᶜ N

theorem finiteSideBound_model (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (N : ℕ) (h : FiniteSideBound T φ N)
    [Nonempty M] [M ⊨ T] (b : Fin n → M) :
    Small (fiber φ b) N ∨ Small (fiber φ b)ᶜ N := by
  have hs : T ⊨ᵇ ((fiberBound φ N) ⊔ (fiberBound φ.not N)) := by
    apply Theory.models_formula_iff.mpr
    intro P a
    rw [Formula.realize_sup]
    rcases h P a with hp | hp
    · exact Or.inl ((fiberBound_iff_small φ N a).mpr hp)
    · right
      apply (fiberBound_iff_small φ.not N a).mpr
      simpa only [fiber,Formula.realize_not,Set.compl_ofPred] using hp
  have hM := hs.realize_formula M (v := b)
  rw [Formula.realize_sup] at hM
  rcases hM with hM | hM
  · exact Or.inl ((fiberBound_iff_small φ N b).mp hM)
  · right
    simpa only [fiber,Formula.realize_not,Set.compl_ofPred] using (fiberBound_iff_small φ.not N b).mp hM

/-- For positive k this native sentence requires k distinct points on one side. -/
def sideSentence {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1))
    (negative : Bool) (k : ℕ) : L[[Fin n]].Sentence :=
  Formula.equivSentence ((fiberBound (if negative then φ.not else φ) (k-1)).not)

inductive SideRequest (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1))
  | background (σ : L.Sentence) (hσ : σ ∈ T)
  | side (negative : Bool) (k : ℕ) (hk : 0 < k)

def sideRequestSentence (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) :
    SideRequest T φ → L[[Fin n]].Sentence
  | .background σ _ => (L.lhomWithConstants (Fin n)).onSentence σ
  | .side negative k _ => sideSentence φ negative k

def sideTheory (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) :
    L[[Fin n]].Theory := Set.range (sideRequestSentence T φ)

theorem sideSentence_realize [Nonempty M] {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (b : Fin n → M) (negative : Bool) (k : ℕ)
    (hk : 0 < k) :
    letI := namedExpansion (L := L) b
    M ⊨ sideSentence φ negative k ↔
      ∃ a : Fin k ↪ M, ∀ i, if negative then a i ∉ fiber φ b else a i ∈ fiber φ b := by
  let := namedExpansion (L := L) b
  change (M ⊨ sideSentence φ negative k) ↔ _
  rw [sideSentence,Formula.realize_equivSentence,Formula.realize_not]
  change (¬(fiberBound (if negative then φ.not else φ) (k-1)).Realize b) ↔ _
  rw [fiberBound_iff_small,not_small_iff_embedding _ k hk]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    fiber,Formula.realize_not,Set.mem_ofPred_eq]

theorem sideTheory_finite_realization (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (h : ¬∃ N, FiniteSideBound T φ N)
    (Γ : Finset (L[[Fin n]].Sentence)) (hΓ : (Γ : Set _) ⊆ sideTheory T φ) :
    ∃ P : Theory.ModelType.{u,v,max u v} T, ∃ b : Fin n → P,
      letI := namedExpansion (L := L) b
      P ⊨ (Γ : L[[Fin n]].Theory) := by
  classical
  let pick (γ : Γ) : SideRequest T φ := (hΓ γ.property).choose
  have hpick (γ : Γ) : sideRequestSentence T φ (pick γ) = γ.val :=
    (hΓ γ.property).choose_spec
  let requestCount : SideRequest T φ → ℕ
    | .background _ _ => 0
    | .side _ k _ => k
  let N := Finset.univ.sup (fun γ : Γ => requestCount (pick γ))
  have hex : ∃ P : Theory.ModelType.{u,v,max u v} T, ∃ b : Fin n → P,
      ¬Small (fiber φ b) N ∧ ¬Small (fiber φ b)ᶜ N := by
    have hn := not_exists.mp h N
    change ¬∀ P : Theory.ModelType.{u,v,max u v} T, ∀ b : Fin n → P,
      Small (fiber φ b) N ∨ Small (fiber φ b)ᶜ N at hn
    push Not at hn
    exact hn
  obtain ⟨P,b,hp,hc⟩ := hex
  let := namedExpansion (L := L) b
  refine ⟨P,b,⟨?_⟩⟩
  intro γ hγ
  let d : Γ := ⟨γ,hγ⟩
  change P ⊨ d.val
  rw [←hpick d]
  cases hd : pick d with
  | background σ hσ =>
    exact (LHom.realize_onSentence P (L.lhomWithConstants _) σ).mpr
      (P.is_model.realize_of_mem σ hσ)
  | side negative k hk =>
    have hkle : k ≤ N := by
      have hs := Finset.le_sup (f := fun γ : Γ => requestCount (pick γ)) (Finset.mem_univ d)
      simpa only [requestCount,hd] using hs
    rw [sideRequestSentence,sideSentence,Formula.realize_equivSentence,Formula.realize_not]
    change ¬(fiberBound (if negative then φ.not else φ) (k-1)).Realize b
    intro hb
    have hs := (fiberBound_iff_small _ _ _).mp hb
    cases negative
    · simp only [Bool.false_eq_true,ite_false] at hs
      exact hp ⟨hs.1,hs.2.trans ((Nat.sub_le k 1).trans hkle)⟩
    · simp only [ite_true] at hs
      have hs' : Small (fiber φ b)ᶜ (k-1) := by
        simpa only [fiber,Formula.realize_not,Set.compl_ofPred] using hs
      exact hc ⟨hs'.1,hs'.2.trans ((Nat.sub_le k 1).trans hkle)⟩

theorem sideTheory_satisfiable (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (h : ¬∃ N, FiniteSideBound T φ N) :
    (sideTheory T φ).IsSatisfiable := by
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  obtain ⟨P,b,hP⟩ := sideTheory_finite_realization T φ h Γ hΓ
  let := namedExpansion (L := L) b
  let : P ⊨ (Γ : L[[Fin n]].Theory) := hP
  exact Theory.Model.isSatisfiable P

def sideParameters (L : Language.{u,v}) (n : ℕ)
    (P : Type w) [L[[Fin n]].Structure P] : Fin n → P :=
  fun i => (L.con i : P)

theorem side_model_spec (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1))
    (P : Theory.ModelType.{max u 0,v,max u v} (sideTheory T φ)) :
    letI : L.Structure P := (L.lhomWithConstants (Fin n)).reduct P
    P ⊨ T ∧ (fiber φ (sideParameters L n P)).Infinite ∧
      (fiber φ (sideParameters L n P))ᶜ.Infinite := by
  let : L.Structure P := (L.lhomWithConstants (Fin n)).reduct P
  let : (L.lhomWithConstants (Fin n)).IsExpansionOn P := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have hr (r : SideRequest T φ) : P ⊨ sideRequestSentence T φ r :=
    P.is_model.realize_of_mem _ ⟨r,rfl⟩
  have hnot (neg : Bool) (K : ℕ) :
      ¬(fiberBound (if neg then φ.not else φ) K).Realize (sideParameters L n P) := by
    have h := hr (.side neg (K+1) (Nat.succ_pos _))
    change P ⊨ sideSentence φ neg (K+1) at h
    rw [sideSentence,Formula.realize_equivSentence,Formula.realize_not] at h
    change ¬(fiberBound (if neg then φ.not else φ) K).Realize (fun i => (L.con i : P))
    simpa only [Nat.add_sub_cancel] using h
  change P ⊨ T ∧ _
  refine ⟨?_,?_,?_⟩
  · constructor
    intro σ hσ
    exact (LHom.realize_onSentence P (L.lhomWithConstants _) σ).mp (hr (.background σ hσ))
  · intro hf
    have hb := hnot false (fiber φ (sideParameters L n P)).ncard
    simp only [Bool.false_eq_true,ite_false] at hb
    exact hb ((fiberBound_iff_small _ _ _).mpr ⟨hf,le_rfl⟩)
  · intro hc
    have hb := hnot true (fiber φ (sideParameters L n P))ᶜ.ncard
    simp only [ite_true] at hb
    apply hb
    apply (fiberBound_iff_small _ _ _).mpr
    simpa only [fiber,Formula.realize_not,Set.compl_ofPred] using
      (show Small (fiber φ (sideParameters L n P))ᶜ
        (fiber φ (sideParameters L n P))ᶜ.ncard from ⟨hc,le_rfl⟩)

private theorem uniform_of_finite_or_cofinite (T : L.Theory) {n : ℕ}
    (φ : L.Formula (Fin n ⊕ Fin 1))
    (hφ : ∀ P : Theory.ModelType.{u,v,max u v} T, ∀ b : Fin n → P,
      (fiber φ b).Finite ∨ Cofinite (fiber φ b)) :
    ∃ N, FiniteSideBound T φ N := by
  classical
  by_contra h
  let P := (sideTheory_satisfiable T φ h).some
  have hp := side_model_spec T φ P
  let : L.Structure P := (L.lhomWithConstants (Fin n)).reduct P
  let : P ⊨ T := hp.1
  rcases hφ (Theory.ModelType.of T P) (sideParameters L n P) with hf | hc
  · exact hp.2.1 hf
  · exact hp.2.2 hc


theorem uniform_finite_side (T : L.Theory) (hT : StronglyMinimalTheory T)
    {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) :
    ∃ N, FiniteSideBound T φ N := by
  classical
  by_contra h
  let P := (sideTheory_satisfiable T φ h).some
  have hp := side_model_spec T φ P
  let : L.Structure P := (L.lhomWithConstants (Fin n)).reduct P
  let : P ⊨ T := hp.1
  have hm := hT (Theory.ModelType.of T P)
  rcases (minimal_iff_fibers.mp hm).2 n φ (sideParameters L n P) with hf | hc
  · exact hp.2.1 hf
  · exact hp.2.2 hc

theorem theory_model_minimal (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] : Minimal L M := by
  have hInf : M ⊨ L.infiniteTheory := by
    constructor
    intro σ hσ
    have hs : T ⊨ᵇ σ := Theory.models_sentence_iff.mpr fun P => by
      let : Infinite P := (hT P).1
      exact Theory.realize_sentence_of_mem L.infiniteTheory hσ
    exact hs.realize_sentence M
  refine minimal_iff_fibers.mpr ⟨(L.model_infiniteTheory_iff).mp hInf,?_⟩
  intro n φ b
  obtain ⟨N,hN⟩ := uniform_finite_side T hT φ
  rcases finiteSideBound_model T φ N hN b with hf | hc
  · exact Or.inl hf.1
  · exact Or.inr hc.1

theorem structure_extension_minimal (hM : StronglyMinimalStructure L M)
    {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N) : Minimal L N := by
  let : Infinite M := hM.1.1
  let : Infinite N := Infinite.of_injective f f.injective
  refine minimal_iff_fibers.mpr ⟨inferInstance,?_⟩
  intro n φ b
  have hφ : ∀ P : Theory.ModelType.{max u w,v,max u v w} (L.elementaryDiagram M),
      ∀ a : Fin n → P,
      (fiber ((L.lhomWithConstants M).onFormula φ) a).Finite ∨
        Cofinite (fiber ((L.lhomWithConstants M).onFormula φ) a) := by
    intro P a
    let : L.Structure P := (L.lhomWithConstants M).reduct P
    let : (L.lhomWithConstants M).IsExpansionOn P := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
    have hp := (minimal_iff_fibers.mp (hM.2 P)).2 n φ a
    simpa only [fiber,LHom.realize_onFormula,Cofinite] using hp
  obtain ⟨K,hK⟩ := uniform_of_finite_or_cofinite (L.elementaryDiagram M)
    ((L.lhomWithConstants M).onFormula φ) hφ
  let := namedExpansion (L := L) (f : M → N)
  let : N ⊨ L.elementaryDiagram M := elementary_namedExpansion_models_diagram f
  rcases finiteSideBound_model (L.elementaryDiagram M)
      ((L.lhomWithConstants M).onFormula φ) K hK b with hf | hc
  · left
    simpa only [fiber,LHom.realize_onFormula,Cofinite] using hf.1
  · right
    simpa only [fiber,LHom.realize_onFormula,Cofinite] using hc.1

theorem theory_model_stronglyMinimal (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] : StronglyMinimalStructure L M := by
  refine ⟨theory_model_minimal T hT,?_⟩
  intro P
  let : L.Structure P := (L.lhomWithConstants M).reduct P
  let : (L.lhomWithConstants M).IsExpansionOn P := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  let f : M ↪ₑ[L] P := ElementaryEmbedding.ofModelsElementaryDiagram L M P
  let : P ⊨ T := (f.theory_model_iff T).mp inferInstance
  exact theory_model_minimal T hT

theorem finite_sides_bounded (T : L.Theory) (hT : StronglyMinimalTheory T)
    {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) (N : ℕ) (hN : FiniteSideBound T φ N)
    [Nonempty M] [M ⊨ T] (b : Fin n → M) :
    ((fiber φ b).Finite → Small (fiber φ b) N) ∧
      ((fiber φ b)ᶜ.Finite → Small (fiber φ b)ᶜ N) := by
  let : Infinite M := (theory_model_minimal T hT (M := M)).1
  have hbad : ¬((fiber φ b).Finite ∧ (fiber φ b)ᶜ.Finite) := by
    rintro ⟨hf,hc⟩
    exact Set.infinite_univ (by simpa only [Set.union_compl_self] using hf.union hc)
  rcases finiteSideBound_model T φ N hN b with hf | hc
  · exact ⟨fun _ => hf,fun h => (hbad ⟨hf.1,h⟩).elim⟩
  · exact ⟨fun h => (hbad ⟨h,hc.1⟩).elim,fun _ => hc⟩

def cofiniteFormula {α : Type z} (φ : L.Formula (α ⊕ Fin 1)) (N : ℕ) : L.Formula α :=
  (fiberBound φ N).not

theorem cofiniteFormula_realize (T : L.Theory) (hT : StronglyMinimalTheory T)
    {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) (N : ℕ) (hN : FiniteSideBound T φ N)
    [Nonempty M] [M ⊨ T] (b : Fin n → M) :
    (cofiniteFormula φ N).Realize b ↔ Cofinite (fiber φ b) := by
  let : Infinite M := (theory_model_minimal T hT (M := M)).1
  rw [cofiniteFormula,Formula.realize_not,fiberBound_iff_small]
  constructor
  · intro hn
    rcases (minimal_iff_fibers.mp (theory_model_minimal T hT (M := M))).2 n φ b with hf | hc
    · exact (hn ((finite_sides_bounded T hT φ N hN b).1 hf)).elim
    · exact hc
  · intro hc hf
    exact Set.infinite_univ (by simpa only [Set.union_compl_self] using hf.1.union hc)

theorem cofinite_iff_many_solutions (T : L.Theory) (hT : StronglyMinimalTheory T)
    {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) (N : ℕ) (hN : FiniteSideBound T φ N)
    [Nonempty M] [M ⊨ T] (b : Fin n → M) :
    Cofinite (fiber φ b) ↔ ∃ a : Fin (N+1) ↪ M, ∀ i, a i ∈ fiber φ b := by
  let := namedExpansion (L := L) b
  have h := sideSentence_realize φ b false (N+1) (Nat.succ_pos _)
  change (M ⊨ sideSentence φ false (N+1)) ↔ _ at h
  rw [sideSentence,Formula.realize_equivSentence] at h
  simp only [Bool.false_eq_true,ite_false,Nat.add_sub_cancel,Formula.realize_not] at h
  change (¬(fiberBound φ N).Realize b) ↔ _ at h
  exact (cofiniteFormula_realize T hT φ N hN b).symm.trans h

end
end Lemmatheca.ModelTheory.StronglyMinimalSets
