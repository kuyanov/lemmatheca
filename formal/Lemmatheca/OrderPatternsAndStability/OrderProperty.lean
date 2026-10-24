import Lemmatheca.TypesAndRealization.Types
import Mathlib.Data.Finset.Sort

/-! Partitioned native formulas, finite order patterns, and their specified compactness models. -/
namespace Lemmatheca.ModelTheory.OrderPatternsAndStability
open FirstOrder FirstOrder.Language
universe u v w z
variable {L : Language.{u,v}} (T : L.Theory) {m n : ℕ}

/-- The first block is varied as objects; the second supplies parameter values. -/
def pairAssignment {M : Type w} (a : Fin m → M) (b : Fin n → M) : Fin (m+n) → M :=
  Fin.addCases a b

def OrderPattern {M : Type w} [L.Structure M] {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) (a : I → Fin m → M) (b : I → Fin n → M) : Prop :=
  ∀ i j, φ.Realize (pairAssignment (a i) (b j)) ↔ i < j

/-- Native models are bundled; their size is harmless for finite configurations. -/
def HasFinitePattern (φ : L.Formula (Fin (m+n))) (k : ℕ) : Prop :=
  ∃ M : Theory.ModelType.{u,v,max u v} T,
    ∃ a : Fin k → Fin m → M, ∃ b : Fin k → Fin n → M, OrderPattern φ a b


def HasOrderProperty (φ : L.Formula (Fin (m+n))) : Prop :=
  ∀ k, 0 < k → HasFinitePattern T φ k

def StableFormula (φ : L.Formula (Fin (m+n))) : Prop :=
  ¬HasOrderProperty T φ

def StableTheory : Prop :=
  ∀ m n, 0 < m → 0 < n → ∀ φ : L.Formula (Fin (m+n)), StableFormula T φ

theorem stableFormula_iff_finite_obstruction (φ : L.Formula (Fin (m+n))) :
    StableFormula T φ ↔ ∃ k, 0 < k ∧ ¬HasFinitePattern T φ k := by
  classical
  simp only [StableFormula,HasOrderProperty,not_forall,exists_prop]

theorem no_two_pattern_empty_object {M : Type w} [L.Structure M]
    (φ : L.Formula (Fin (0+n))) (a : Fin 2 → Fin 0 → M) (b : Fin 2 → Fin n → M) :
    ¬OrderPattern φ a b := by
  intro h
  have h01 := (h 0 1).mpr (by decide)
  have ha : a 0 = a 1 := Subsingleton.elim _ _
  rw [ha] at h01
  exact (lt_irrefl (1 : Fin 2)) ((h 1 1).mp h01)

theorem no_two_pattern_empty_parameter {M : Type w} [L.Structure M]
    (φ : L.Formula (Fin (m+0))) (a : Fin 2 → Fin m → M) (b : Fin 2 → Fin 0 → M) :
    ¬OrderPattern φ a b := by
  intro h
  have h01 := (h 0 1).mpr (by decide)
  have hb : b 1 = b 0 := Subsingleton.elim _ _
  rw [hb] at h01
  exact (lt_irrefl (0 : Fin 2)) ((h 0 0).mp h01)

def patternSentence {I : Type z} (φ : L.Formula (Fin (m+n))) (i j : I) :
    L[[I × (Fin m ⊕ Fin n)]].Sentence :=
  Formula.equivSentence (φ.relabel
    (Fin.addCases (fun x => (i,Sum.inl x)) (fun y => (j,Sum.inr y))))

inductive PatternRequest (φ : L.Formula (Fin (m+n))) (I : Type z) [LinearOrder I]
  | background (σ : L.Sentence) (hσ : σ ∈ T)
  | comparison (i j : I)

noncomputable def patternRequestSentence {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) :
    PatternRequest T φ I → L[[I × (Fin m ⊕ Fin n)]].Sentence := by
  classical
  exact fun r => match r with
    | .background σ _ => (L.lhomWithConstants _).onSentence σ
    | .comparison i j => if i < j then patternSentence φ i j else (patternSentence φ i j).not

noncomputable def patternTheory {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) : L[[I × (Fin m ⊕ Fin n)]].Theory :=
  Set.range (patternRequestSentence T (I := I) φ)

theorem patternSentence_realize {I : Type z} (φ : L.Formula (Fin (m+n)))
    {M : Type w} [L.Structure M] (a : I → Fin m → M) (b : I → Fin n → M) (i j : I) :
    letI := Diagrams.namedExpansion (L := L)
      (fun c : I × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
    M ⊨ patternSentence φ i j ↔ φ.Realize (pairAssignment (a i) (b j)) := by
  let := Diagrams.namedExpansion (L := L)
      (fun c : I × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
  change (M ⊨ patternSentence φ i j) ↔ φ.Realize (pairAssignment (a i) (b j))
  rw [patternSentence,Formula.realize_equivSentence,Formula.realize_relabel]
  apply Iff.of_eq
  congr 1
  funext k
  refine Fin.addCases (fun x => ?_) (fun y => ?_) k <;> simp only [pairAssignment,Function.comp_apply,Fin.addCases_left,Fin.addCases_right] <;> rfl

theorem patternTheory_finite_realization {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) (h : HasOrderProperty T φ)
    (Γ : Finset L[[I × (Fin m ⊕ Fin n)]].Sentence)
    (hΓ : (↑Γ : L[[I × (Fin m ⊕ Fin n)]].Theory) ⊆ patternTheory T (I := I) φ) :
    ∃ M : Theory.ModelType.{u,v,max u v} T,
      ∃ a : I → Fin m → M, ∃ b : I → Fin n → M,
        letI := Diagrams.namedExpansion (L := L)
          (fun c : I × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
        M ⊨ (↑Γ : L[[I × (Fin m ⊕ Fin n)]].Theory) := by
  classical
  let pick (γ : Γ) : PatternRequest T φ I := (hΓ γ.property).choose
  have hpick (γ : Γ) : patternRequestSentence T φ (pick γ) = γ.val :=
    (hΓ γ.property).choose_spec
  let labels : PatternRequest T φ I → Finset I
    | .background _ _ => ∅
    | .comparison i j => {i,j}
  let S : Finset I := Finset.univ.biUnion (fun γ : Γ => labels (pick γ))
  let rank (i : I) : Fin (S.card+1) :=
    if hi : i ∈ S then ((S.orderIsoOfFin rfl).symm ⟨i,hi⟩).castSucc else Fin.last _
  have hrank (i j : I) (hi : i ∈ S) (hj : j ∈ S) : rank i < rank j ↔ i < j := by
    simp only [rank,dite_eq_left hi,dite_eq_left hj,Fin.castSucc_lt_castSucc_iff]
    exact (S.orderIsoOfFin rfl).symm.lt_iff_lt
  obtain ⟨M,a₀,b₀,hp⟩ := h (S.card+1) (Nat.succ_pos _)
  let a (i : I) := a₀ (rank i)
  let b (i : I) := b₀ (rank i)
  let := Diagrams.namedExpansion (L := L)
    (fun c : I × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
  refine ⟨M,a,b,⟨?_⟩⟩
  intro γ hγ
  let d : Γ := ⟨γ,hγ⟩
  change M ⊨ d.val
  rw [←hpick d]
  cases hd : pick d with
  | background σ hσ =>
    exact (LHom.realize_onSentence M (L.lhomWithConstants _) σ).mpr
      (M.is_model.realize_of_mem σ hσ)
  | comparison i j =>
    have hi : i ∈ S := Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,by simp [labels,hd]⟩
    have hj : j ∈ S := Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,by simp [labels,hd]⟩
    have htruth : φ.Realize (pairAssignment (a i) (b j)) ↔ i < j :=
      (hp (rank i) (rank j)).trans (hrank i j hi hj)
    have he := patternSentence_realize φ a b i j
    by_cases hij : i < j
    · simp only [patternRequestSentence,ite_eq_left hij]
      exact he.mpr (htruth.mpr hij)
    · simp only [patternRequestSentence,ite_eq_right hij,Sentence.realize_not]
      exact fun ht => hij (htruth.mp (he.mp ht))

theorem patternTheory_satisfiable {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) (h : HasOrderProperty T φ) :
    (patternTheory T (I := I) φ).IsSatisfiable := by
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  obtain ⟨M,a,b,hm⟩ := patternTheory_finite_realization T φ h Γ hΓ
  let := Diagrams.namedExpansion (L := L)
    (fun c : I × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
  let : M ⊨ (Γ : L[[I × (Fin m ⊕ Fin n)]].Theory) := hm
  exact Theory.Model.isSatisfiable M

def canonicalObjects (L : Language.{u,v}) (I : Type z) (m n : ℕ)
    (M : Type w) [L[[I × (Fin m ⊕ Fin n)]].Structure M] : I → Fin m → M :=
  fun i k => (L.con ((i,Sum.inl k) : I × (Fin m ⊕ Fin n)) : M)

def canonicalParameters (L : Language.{u,v}) (I : Type z) (m n : ℕ)
    (M : Type w) [L[[I × (Fin m ⊕ Fin n)]].Structure M] : I → Fin n → M :=
  fun i k => (L.con ((i,Sum.inr k) : I × (Fin m ⊕ Fin n)) : M)

theorem pattern_model_spec {I : Type z} [LinearOrder I]
    (φ : L.Formula (Fin (m+n))) {M : Type w}
    [L[[I × (Fin m ⊕ Fin n)]].Structure M]
    (h : M ⊨ patternTheory T (I := I) φ) :
    letI : L.Structure M := (L.lhomWithConstants (I × (Fin m ⊕ Fin n))).reduct M
    M ⊨ T ∧ OrderPattern φ (canonicalObjects L I m n M) (canonicalParameters L I m n M) := by
  classical
  let : L.Structure M := (L.lhomWithConstants (I × (Fin m ⊕ Fin n))).reduct M
  let : (L.lhomWithConstants (I × (Fin m ⊕ Fin n))).IsExpansionOn M := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have hreq (r : PatternRequest T φ I) :
      M ⊨ patternRequestSentence T φ r := h.realize_of_mem _ ⟨r,rfl⟩
  change M ⊨ T ∧ _
  constructor
  · constructor
    intro σ hσ
    exact (LHom.realize_onSentence M (L.lhomWithConstants _) σ).mp (hreq (.background σ hσ))
  · intro i j
    have he :
        M ⊨ patternSentence φ i j ↔
          φ.Realize (pairAssignment (canonicalObjects L I m n M i) (canonicalParameters L I m n M j)) := by
      rw [patternSentence,Formula.realize_equivSentence,Formula.realize_relabel]
      apply Iff.of_eq
      congr 1
      funext k
      refine Fin.addCases (fun x => ?_) (fun y => ?_) k <;>
        simp only [pairAssignment,Function.comp_apply,Fin.addCases_left,Fin.addCases_right] <;> rfl
    have hc := hreq (.comparison i j)
    by_cases hij : i < j
    · have hp : M ⊨ patternSentence φ i j := by
        simpa only [patternRequestSentence,ite_eq_left hij] using hc
      exact iff_of_true (he.mp hp) hij
    · have hn : ¬M ⊨ patternSentence φ i j := by
        simpa only [patternRequestSentence,ite_eq_right hij,Sentence.realize_not] using hc
      exact iff_of_false (fun ht => hn (he.mpr ht)) hij

theorem hasFinitePattern_of_model {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    (φ : L.Formula (Fin (m+n))) (k : ℕ)
    (a : Fin k → Fin m → M) (b : Fin k → Fin n → M) (h : OrderPattern φ a b) :
    HasFinitePattern T φ k := by
  classical
  let := Diagrams.namedExpansion (L := L)
    (fun c : Fin k × (Fin m ⊕ Fin n) => Sum.elim (a c.1) (b c.1) c.2)
  have hs : M ⊨ patternTheory T (I := Fin k) φ := by
    constructor
    rintro γ ⟨r,rfl⟩
    cases r with
    | background σ hσ =>
      exact (LHom.realize_onSentence M (L.lhomWithConstants _) σ).mpr
        (Theory.realize_sentence_of_mem T hσ)
    | comparison i j =>
      have he := patternSentence_realize φ a b i j
      by_cases hij : i < j
      · simp only [patternRequestSentence,ite_eq_left hij]
        exact he.mpr ((h i j).mpr hij)
      · simp only [patternRequestSentence,ite_eq_right hij,Sentence.realize_not]
        exact fun ht => hij ((h i j).mp (he.mp ht))
  let : M ⊨ patternTheory T (I := Fin k) φ := hs
  let C : Theory.ModelType.{u,v,max u v} (patternTheory T (I := Fin k) φ) :=
    (Theory.Model.isSatisfiable M).some
  let : L.Structure C := (L.lhomWithConstants (Fin k × (Fin m ⊕ Fin n))).reduct C
  have hC : C ⊨ patternTheory T (I := Fin k) φ := C.is_model
  have hc := pattern_model_spec T (I := Fin k) φ (M := C) hC
  let : C ⊨ T := hc.1
  exact ⟨Theory.ModelType.of T C,canonicalObjects L (Fin k) m n C,
    canonicalParameters L (Fin k) m n C,hc.2⟩

theorem exists_order_pattern (φ : L.Formula (Fin (m+n))) (h : HasOrderProperty T φ)
    (I : Type z) [LinearOrder I] [Infinite I] :
    ∃ M : Theory.ModelType.{u,v,max u v z} T,
      ∃ a : I → Fin m → M, ∃ b : I → Fin n → M, OrderPattern φ a b := by
  classical
  let C : Theory.ModelType.{max u z,v,max u v z} (patternTheory T (I := I) φ) :=
    (patternTheory_satisfiable T (I := I) φ h).some
  let : L.Structure C := (L.lhomWithConstants (I × (Fin m ⊕ Fin n))).reduct C
  have hC : C ⊨ patternTheory T (I := I) φ := C.is_model
  have hs := pattern_model_spec T (I := I) φ (M := C) hC
  let : C ⊨ T := hs.1
  exact ⟨Theory.ModelType.of T C,canonicalObjects L I m n C,canonicalParameters L I m n C,hs.2⟩

end Lemmatheca.ModelTheory.OrderPatternsAndStability
