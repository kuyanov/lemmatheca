import Lemmatheca.EhrenfeuchtMostowskiModels.SkolemExpansion
import Mathlib.Data.Finset.Sort

/-! One fixed, realized coherent template and its exact stretching theory. -/
namespace Lemmatheca.ModelTheory.EhrenfeuchtMostowski
open FirstOrder FirstOrder.Language
universe u v w z
variable {K : Language.{u,v}} (T : K.Theory)

/-- A realized template is chosen once, before any target order is specified. -/
structure Template where
  source : Theory.ModelType.{u,v,max u v w} T
  sequence : ℕ → source
  distinct : Function.Injective sequence
  indiscernible :
    IndiscernibleSequences.OrderIndiscernible (L := K) (∅ : Set source)
      (fun i (_ : Fin 1) => sequence i)

noncomputable def templateType (p : Template.{u,v,w} T) (n : ℕ) :
    T.CompleteType (Fin n) :=
  T.typeOf (fun i : Fin n => p.sequence i)

private def singletonIndex (n : ℕ) : Fin (n*1) ≃o Fin n := Fin.castOrderIso (Nat.mul_one n)

private theorem singleton_assignment {I : Type*} {N : Type*} (b : I → N) {n}
    (s : Fin n → I) :
    IndiscernibleSequences.tupleAssignment (fun i (_ : Fin 1) => b i) s =
      b ∘ s ∘ singletonIndex n := by
  funext k
  change b (s (finProdFinEquiv.symm k).1) = b (s (singletonIndex n k))
  congr 2
  apply Fin.ext
  simp [finProdFinEquiv,singletonIndex,Fin.divNat]

private theorem template_formula_selection (p : Template.{u,v,w} T) {n}
    (φ : K.Formula (Fin n)) (s t : Fin n ↪o ℕ) :
    φ.Realize (p.sequence ∘ s) ↔ φ.Realize (p.sequence ∘ t) := by
  by_cases hn : 0 < n
  · let ψ : K[[(∅ : Set p.source)]].Formula (Fin (n*1)) :=
      (K.lhomWithConstants (∅ : Set p.source)).onFormula (φ.relabel (singletonIndex n).symm)
    have h := p.indiscernible n hn ψ s t
    simp only [ψ,LHom.realize_onFormula,Formula.realize_relabel,singleton_assignment] at h
    simpa only [Function.comp_def,OrderIso.apply_symm_apply] using h
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have he : p.sequence ∘ s = p.sequence ∘ t := Subsingleton.elim _ _
    rw [he]

theorem template_any_selection (p : Template.{u,v,w} T) (n : ℕ)
    (s : Fin n ↪o ℕ) :
    T.typeOf (p.sequence ∘ s) = templateType T p n := by
  apply SetLike.ext
  intro γ
  change γ ∈ T.typeOf (p.sequence ∘ s) ↔ γ ∈ T.typeOf (fun i : Fin n => p.sequence i)
  simp only [Theory.CompleteType.mem_typeOf]
  exact template_formula_selection T p (Formula.equivSentence.symm γ) s (Fin.valOrderEmb n)

theorem template_coherence (p : Template.{u,v,w} T) {r n : ℕ}
    (e : Fin r ↪o Fin n) (φ : K.Formula (Fin r)) :
    φ.relabel e ∈ Types.formulas (templateType T p n) ↔
      φ ∈ Types.formulas (templateType T p r) := by
  have he := template_any_selection T p r (e.trans (Fin.valOrderEmb n))
  have hm := congrArg (fun q => Formula.equivSentence φ ∈ q) he
  change (Formula.equivSentence φ ∈ T.typeOf (p.sequence ∘ (e.trans (Fin.valOrderEmb n)))) =
    (Formula.equivSentence φ ∈ T.typeOf (fun i : Fin r => p.sequence i)) at hm
  rw [Theory.CompleteType.formula_mem_typeOf,Theory.CompleteType.formula_mem_typeOf] at hm
  change Formula.equivSentence (φ.relabel e) ∈ T.typeOf (fun i : Fin n => p.sequence i) ↔
    Formula.equivSentence φ ∈ T.typeOf (fun i : Fin r => p.sequence i)
  rw [Theory.CompleteType.formula_mem_typeOf,Theory.CompleteType.formula_mem_typeOf,
    Formula.realize_relabel]
  exact Iff.of_eq hm

theorem template_zero (p : Template.{u,v,w} T) (φ : K.Sentence) :
    φ.relabel (Empty.elim : Empty → Fin 0) ∈ Types.formulas (templateType T p 0) ↔ p.source ⊨ φ := by
  change Formula.equivSentence (φ.relabel (Empty.elim : Empty → Fin 0)) ∈
    T.typeOf (fun i : Fin 0 => p.sequence i) ↔ _
  rw [Theory.CompleteType.formula_mem_typeOf,Formula.realize_relabel]
  change Formula.Realize φ ((fun i : Fin 0 => p.sequence i) ∘ Empty.elim) ↔ Formula.Realize φ default
  rw [show ((fun i : Fin 0 => p.sequence i) ∘ Empty.elim) = (default : Empty → p.source) from Subsingleton.elim _ _]

theorem template_distinct (p : Template.{u,v,w} T) :
    ((Term.var (0 : Fin 2)).equal (Term.var 1)).not ∈
      Types.formulas (templateType T p 2) := by
  apply Theory.CompleteType.formula_mem_typeOf.mpr
  change ¬p.sequence 0 = p.sequence 1
  exact fun he => (by decide : (0 : ℕ) ≠ 1) (p.distinct he)

/-- Exact agreement includes the empty selection, hence the sentence theory. -/
def RealizesTemplate (p : Template.{u,v,w} T) {I : Type z} [LinearOrder I]
    {N : Type*} [K.Structure N] (b : I → N) : Prop :=
  ∀ n (s : Fin n ↪o I) (φ : K.Formula (Fin n)),
    φ.Realize (b ∘ s) ↔ φ ∈ Types.formulas (templateType T p n)

/-- This labelled origin keeps positions even when its formula ignores them. -/
inductive StretchRequest (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I]
  | background (σ : K.Sentence) (hσ : σ ∈ T)
  | selection (n : ℕ) (φ : K.Formula (Fin n))
      (hφ : φ ∈ Types.formulas (templateType T p n)) (s : Fin n ↪o I)

def stretchInstance {I : Type z} {n : ℕ} (φ : K.Formula (Fin n)) (s : Fin n → I) :
    K[[I]].Sentence :=
  Formula.equivSentence (φ.relabel s)

def stretchSentence (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I] :
    StretchRequest T p I → K[[I]].Sentence
  | .background σ _ => (K.lhomWithConstants I).onSentence σ
  | .selection _ φ _ s => stretchInstance φ s

def stretchTheory (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I] : K[[I]].Theory :=
  Set.range (stretchSentence T p I)

private theorem stretch_instance_truth {I : Type z} {n : ℕ}
    (φ : K.Formula (Fin n)) (s : Fin n → I) {N : Type*} [K[[I]].Structure N] :
    letI : K.Structure N := (K.lhomWithConstants I).reduct N
    N ⊨ stretchInstance φ s ↔ φ.Realize ((fun i : I => (K.con i : N)) ∘ s) := by
  let : K.Structure N := (K.lhomWithConstants I).reduct N
  let : (K.lhomWithConstants I).IsExpansionOn N := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  rw [stretchInstance,Formula.realize_equivSentence,Formula.realize_relabel]

private def pairSelection {I : Type z} [LinearOrder I] (i j : I) (h : i < j) : Fin 2 ↪o I where
  toFun := ![i,j]
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [ne_of_lt h,ne_of_gt h]
  map_rel_iff' := by
    intro a b
    change (![i,j] a ≤ ![i,j] b ↔ a ≤ b)
    fin_cases a <;> fin_cases b <;> simp [le_of_lt h,not_le_of_gt h]

theorem stretch_finite_realization (p : Template.{u,v,w} T)
    (I : Type z) [LinearOrder I] (Γ : Finset K[[I]].Sentence)
    (hΓ : (↑Γ : K[[I]].Theory) ⊆ stretchTheory T p I) :
    ∃ b : I → p.source,
      letI := Diagrams.namedExpansion (L := K) b
      p.source ⊨ (↑Γ : K[[I]].Theory) := by
  classical
  let pick (γ : Γ) : StretchRequest T p I := (hΓ γ.property).choose
  have hpick (γ : Γ) : stretchSentence T p I (pick γ) = γ.val :=
    (hΓ γ.property).choose_spec
  let labels : StretchRequest T p I → Finset I
    | .background _ _ => ∅
    | .selection n _ _ s => Finset.univ.image s
  let S : Finset I := Finset.univ.biUnion (fun γ : Γ => labels (pick γ))
  let rank (i : I) : ℕ := if hi : i ∈ S then ((S.orderIsoOfFin rfl).symm ⟨i,hi⟩).val else 0
  have hrank (i j : I) (hi : i ∈ S) (hj : j ∈ S) : rank i < rank j ↔ i < j := by
    simp only [rank,dite_eq_left hi,dite_eq_left hj]
    exact (S.orderIsoOfFin rfl).symm.lt_iff_lt
  let b : I → p.source := fun i => p.sequence (rank i)
  let := Diagrams.namedExpansion (L := K) b
  refine ⟨b,⟨?_⟩⟩
  intro γ hγ
  let d : Γ := ⟨γ,hγ⟩
  change p.source ⊨ d.val
  rw [← hpick d]
  cases hd : pick d with
  | background σ hσ =>
    exact (LHom.realize_onSentence p.source (K.lhomWithConstants _) σ).mpr
      (p.source.is_model.realize_of_mem σ hσ)
  | selection n φ hφ e =>
    have heS (i : Fin n) : e i ∈ S :=
      Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,by simp only [labels,hd]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    let e' : Fin n ↪o ℕ := OrderEmbedding.ofStrictMono (fun i => rank (e i))
      (fun i j hij => (hrank _ _ (heS i) (heS j)).mpr (e.strictMono hij))
    have ht : φ ∈ Types.formulas (T.typeOf (p.sequence ∘ e')) := by
      rw [template_any_selection T p n e']
      exact hφ
    have ht' := Theory.CompleteType.formula_mem_typeOf.mp ht
    exact (stretch_instance_truth φ e).mpr ht'

theorem stretch_satisfiable (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I] :
    (stretchTheory T p I).IsSatisfiable := by
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  obtain ⟨b,hb⟩ := stretch_finite_realization T p I Γ hΓ
  let := Diagrams.namedExpansion (L := K) b
  let : p.source ⊨ (Γ : K[[I]].Theory) := hb
  exact Theory.Model.isSatisfiable p.source

def namedSkeleton (K : Language.{u,v}) (I : Type z) (N : Type*)
    [K[[I]].Structure N] : I → N :=
  fun i => (K.con i : N)

/-- The skeleton is exactly the interpretation of this model's added constants. -/
theorem stretch_model_spec (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I]
    {N : Type*} [K[[I]].Structure N] [Nonempty N]
    (h : N ⊨ stretchTheory T p I) :
    letI : K.Structure N := (K.lhomWithConstants I).reduct N
    N ⊨ T ∧ RealizesTemplate T p (namedSkeleton K I N) ∧
      Function.Injective (namedSkeleton K I N) := by
  classical
  let : K.Structure N := (K.lhomWithConstants I).reduct N
  let : (K.lhomWithConstants I).IsExpansionOn N := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have hreq (r : StretchRequest T p I) : N ⊨ stretchSentence T p I r :=
    h.realize_of_mem _ ⟨r,rfl⟩
  change N ⊨ T ∧ _
  have hr : RealizesTemplate T p (namedSkeleton K I N) := by
    intro n e φ
    constructor
    · intro ht
      by_contra hn
      have hneg : φ.not ∈ Types.formulas (templateType T p n) :=
        ((templateType T p n).not_mem_iff (Formula.equivSentence φ)).mpr hn
      have htneg := (stretch_instance_truth φ.not e).mp (hreq (.selection n φ.not hneg e))
      exact (Formula.realize_not.mp htneg) ht
    · intro hφ
      exact (stretch_instance_truth φ e).mp (hreq (.selection n φ hφ e))
  refine ⟨⟨fun σ hσ => (LHom.realize_onSentence N (K.lhomWithConstants _) σ).mp
    (hreq (.background σ hσ))⟩,hr,?_⟩
  have hne (i j : I) (hij : i < j) : namedSkeleton K I N i ≠ namedSkeleton K I N j := by
    have hn := (hr 2 (pairSelection i j hij)
      (((Term.var (0 : Fin 2)).equal (Term.var 1)).not)).mpr (template_distinct T p)
    exact hn
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (hne i j hlt hij).elim
  · exact heq
  · exact (hne j i hgt hij.symm).elim

theorem exists_stretch (p : Template.{u,v,w} T) (I : Type z) [LinearOrder I] [Infinite I] :
    ∃ N : Theory.ModelType.{u,v,max u v w z} T,
      ∃ b : I → N, Function.Injective b ∧ RealizesTemplate T p b := by
  let S : Theory.ModelType.{max u z,v,max u v w z} (stretchTheory T p I) :=
    Theory.ModelType.ulift.{max u z,v,max u v z,w} (stretch_satisfiable T p I).some
  let : K.Structure S := (K.lhomWithConstants I).reduct S
  have hs := stretch_model_spec T p I S.is_model
  let : S ⊨ T := hs.1
  exact ⟨Theory.ModelType.of T S,namedSkeleton K I S,hs.2.2,hs.2.1⟩

theorem realizesTemplate_indiscernible (p : Template.{u,v,w} T)
    {I : Type z} [LinearOrder I] {N : Type*} [K.Structure N] (b : I → N)
    (h : RealizesTemplate T p b) :
    IndiscernibleSequences.OrderIndiscernible (L := K) (∅ : Set N)
      (fun i (_ : Fin 1) => b i) := by
  intro n hn φ s t
  let ψ : K.Formula (Fin (n*1)) :=
    (LEquiv.addEmptyConstants K (∅ : Set N)).symm.toLHom.onFormula φ
  have hs := h (n*1) ((singletonIndex n).toOrderEmbedding.trans s) ψ
  have ht := h (n*1) ((singletonIndex n).toOrderEmbedding.trans t) ψ
  have bridge (r : Fin n ↪o I) :
      φ.Realize (IndiscernibleSequences.tupleAssignment (fun i (_ : Fin 1) => b i) r) ↔
        ψ.Realize (b ∘ ((singletonIndex n).toOrderEmbedding.trans r)) := by
    rw [singleton_assignment]
    exact (LHom.realize_onFormula _ φ).symm
  exact (bridge s).trans (hs.trans (ht.symm.trans (bridge t).symm))

theorem exists_template {M : Type w} [K.Structure M] [Infinite M] [M ⊨ T] :
    Nonempty (Template.{u,v,w} T) := by
  let e : ℕ ↪ M := Infinite.natEmbedding M
  let a : ℕ → Fin 1 → M := fun i _ => e i
  have ha : Function.Injective a := fun i j h => e.injective (congrFun h 0)
  obtain ⟨N,SN,hN,f,b,hb,hl,hd⟩ :=
    IndiscernibleSequences.exists_indiscernible_extension (L := K) (I := ℕ)
      (by decide : 0 < 1) (∅ : Set M) a ha
  let := SN
  let := hN
  let : N ⊨ T := (f.theory_model_iff T).mp inferInstance
  let P : Theory.ModelType.{u,v,max u v w} T := Theory.ModelType.of T N
  refine ⟨⟨P,fun i => b i 0,?_,?_⟩⟩
  · change Function.Injective (fun i : ℕ => b i 0)
    intro i j hij
    apply hd
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    simpa only [hk] using hij
  · change IndiscernibleSequences.OrderIndiscernible (L := K) (∅ : Set N)
      (fun i (_ : Fin 1) => b i 0)
    have he : (fun i (_ : Fin 1) => b i 0) = b := by
      funext i k
      congr 1
      exact Subsingleton.elim _ _
    rw [he]
    simpa only [Set.image_empty] using hb

end Lemmatheca.ModelTheory.EhrenfeuchtMostowski
