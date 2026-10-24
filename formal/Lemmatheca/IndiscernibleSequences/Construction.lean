import Lemmatheca.IndiscernibleSequences.Indiscernibles

/-! The actual named compactness theory and its specified elementary and tuple maps. -/
namespace Lemmatheca.ModelTheory.IndiscernibleSequences
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory

universe u v w w' z
variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable {I : Type z} [LinearOrder I] {m n : ℕ}
variable [L.Structure M] [L.Structure N]

/-- Replace old parameters by old names and each tuple position by its tagged new name. -/
def instantiate (A : Set M) (φ : L[[A]].Formula (Fin (n * m))) (s : Fin n → I) :
    L[[M ⊕ (I × Fin m)]].Sentence :=
  Formula.equivSentence ((Types.parameterFormula A φ).relabel
    (Sum.elim (Sum.inl : M → M ⊕ (I × Fin m)) fun x =>
      let p : Fin n × Fin m := finProdFinEquiv.symm x
      Sum.inr (s p.1, p.2)))

/-- Different entries means at least one coordinate differs. -/
def tupleInequality (L : Language.{u, v}) (M : Type w) {I : Type z} (m : ℕ)
    (i j : I) : L[[M ⊕ (I × Fin m)]].Sentence :=
  (List.ofFn fun k : Fin m =>
    ((Constants.term (L.con (Sum.inr (i, k) : M ⊕ (I × Fin m)))).equal
      (Constants.term (L.con (Sum.inr (j, k) : M ⊕ (I × Fin m))))).not).foldr (· ⊔ ·) ⊥

/-- These are exactly the tuple values supplied by a model's actual new constants. -/
def canonicalTuples (L : Language.{u, v}) (M : Type w) (I : Type z) (m : ℕ)
    (N : Type w') [L[[M ⊕ (I × Fin m)]].Structure N] : I → Fin m → N :=
  fun i k => (L.con (Sum.inr (i, k) : M ⊕ (I × Fin m)) : N)

omit [LinearOrder I] in
theorem instantiate_realize [_indexOrder : LinearOrder I] (A : Set M) (f : M ↪ₑ[L] N)
    (b : I → Fin m → N) (φ : L[[A]].Formula (Fin (n * m))) (s : Fin n → I) :
    letI := Diagrams.namedExpansion (L := L)
      (Sum.elim f (fun p : I × Fin m => b p.1 p.2) : M ⊕ (I × Fin m) → N)
    N ⊨ instantiate A φ s ↔
      @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (tupleAssignment b s) := by
  let names : M ⊕ (I × Fin m) → N :=
    Sum.elim f (fun p => b p.1 p.2)
  let : L[[M ⊕ (I × Fin m)]].Structure N := Diagrams.namedExpansion names
  rw [instantiate, Formula.realize_equivSentence, Formula.realize_relabel]
  convert Types.parameterFormula_realize f A φ (tupleAssignment b s) using 1
  apply Iff.of_eq
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr k => rfl
  all_goals rfl

omit [L.Structure M] [L.Structure N] [LinearOrder I] in
theorem tupleInequality_realize [_indexOrder : LinearOrder I] [L[[M ⊕ (I × Fin m)]].Structure N] (i j : I) :
    N ⊨ tupleInequality L M m i j ↔
      canonicalTuples L M I m N i ≠ canonicalTuples L M I m N j := by
  classical
  simp only [tupleInequality, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_foldr_sup, List.mem_ofFn]
  constructor
  · rintro ⟨φ, ⟨k, rfl⟩, hk⟩ he
    have hk' : (L.con (Sum.inr (i,k) : M ⊕ (I × Fin m)) : N) ≠
        (L.con (Sum.inr (j,k) : M ⊕ (I × Fin m)) : N) := by
      change Formula.Realize _ (default : Empty → N) at hk
      simpa only [Formula.realize_not, Formula.realize_equal, Term.realize_constants, canonicalTuples] using hk
    exact hk' (congrFun he k)
  · intro he
    obtain ⟨k,hk⟩ := not_forall.mp (fun h => he (funext h))
    refine ⟨_, ⟨k,rfl⟩, ?_⟩
    change Formula.Realize _ (default : Empty → N)
    simpa only [Formula.realize_not, Formula.realize_equal, Term.realize_constants, canonicalTuples] using hk

/-- Each occurrence retains its origin labels, even if unused variables erase a written name. -/
inductive ConstructionRequest (L : Language.{u, v}) (M : Type w) [L.Structure M]
    (A : Set M) (I : Type z) [LinearOrder I] (m : ℕ) (distinct : Bool)
  | old (γ : L[[M]].Sentence) (hγ : γ ∈ L.elementaryDiagram M)
  | different (i j : I) (hij : i ≠ j) (enabled : distinct = true)
  | equivalence (n : ℕ) (positive : 0 < n)
      (φ : L[[A]].Formula (Fin (n * m))) (s t : Fin n ↪o I)
  | pattern (n : ℕ) (positive : 0 < n)
      (Δ : Finset (L[[A]].Formula (Fin (n * m)))) (s : Fin n ↪o I)

noncomputable def requestSentence (A : Set M) (source : ℕ → Fin m → M) (distinct : Bool) :
    ConstructionRequest L M A I m distinct → L[[M ⊕ (I × Fin m)]].Sentence
  | .old γ _ => (L.lhomWithConstantsMap (Sum.inl : M → M ⊕ (I × Fin m))).onSentence γ
  | .different i j _ _ => tupleInequality L M m i j
  | .equivalence _ _ φ s t => (instantiate A φ s).iff (instantiate A φ t)
  | .pattern _ _ Δ s => instantiate A (patternFormula A source Δ) s

noncomputable def constructionTheory (A : Set M) (source : ℕ → Fin m → M) (distinct : Bool) :
    L[[M ⊕ (I × Fin m)]].Theory :=
  Set.range (requestSentence (L := L) (I := I) A source distinct)

private noncomputable def reqLabels {A : Set M} {distinct : Bool} :
    ConstructionRequest L M A I m distinct → Finset I
  | .old _ _ => ∅
  | .different i j _ _ => {i,j}
  | .equivalence _ _ _ s t => Finset.univ.image s ∪ Finset.univ.image t
  | .pattern _ _ _ s => Finset.univ.image s

private noncomputable def reqTest {A : Set M} {distinct : Bool} :
    ConstructionRequest L M A I m distinct →
      Σ n, PLift (0<n) × Finset (L[[A]].Formula (Fin (n*m)))
  | .old _ _ => ⟨1,⟨by omega⟩,∅⟩
  | .different _ _ _ _ => ⟨1,⟨by omega⟩,∅⟩
  | .equivalence n hn φ _ _ => ⟨n,⟨hn⟩,{φ}⟩
  | .pattern n hn Δ _ => ⟨n,⟨hn⟩,Δ⟩

theorem constructionTheory_finite_realization [Nonempty M] (hm : 0 < m)
    (A : Set M) (source : ℕ → Fin m → M) (distinct : Bool)
    (hd : distinct = true → Function.Injective source)
    (Γ : Finset L[[M ⊕ (I × Fin m)]].Sentence)
    (hΓ : (↑Γ : L[[M ⊕ (I × Fin m)]].Theory) ⊆
      constructionTheory (L := L) (I := I) A source distinct) :
    ∃ b : I → Fin m → M,
      letI := Diagrams.namedExpansion (L := L)
        (Sum.elim id (fun p : I × Fin m => b p.1 p.2) : M ⊕ (I × Fin m) → M)
      M ⊨ (↑Γ : L[[M ⊕ (I × Fin m)]].Theory) := by
  classical
  have _hm := hm
  choose req hreq using fun γ : Γ => hΓ γ.property
  let ei := (Fintype.equivFin Γ).symm
  let data := fun j : Fin (Fintype.card Γ) => reqTest (req (ei j))
  obtain ⟨H,hH,hh⟩ := finite_formula_homogeneity A source (Fintype.card Γ)
    (fun j => (data j).1) (fun j => (data j).2.1.down) (fun j => (data j).2.2)
  let S : Finset I := Γ.attach.biUnion (fun γ => reqLabels (req γ))
  let : Infinite H := hH.to_subtype
  let e : S ↪o H := Classical.choice (nonempty_orderEmbedding_of_finite_infinite S H)
  let b : I → Fin m → M := fun i => if hi : i ∈ S then source (e ⟨i,hi⟩).val else source 0
  have hlabels (γ : Γ) : reqLabels (req γ) ⊆ S := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨γ,Finset.mem_attach _ _,hi⟩
  let liftSel {n : ℕ} (s : Fin n ↪o I) (hs : ∀ x, s x ∈ S) : Fin n ↪o ℕ :=
    { toFun := fun x => (e ⟨s x,hs x⟩).val
      inj' := fun x y he => s.injective (congrArg Subtype.val (e.injective (Subtype.ext he)))
      map_rel_iff' := by
        intro x y
        exact (e.map_rel_iff).trans s.map_rel_iff }
  have htup {n : ℕ} (s : Fin n ↪o I) (hs : ∀ x, s x ∈ S) :
      tupleAssignment b s = tupleAssignment source (liftSel s hs) := by
    funext x
    simp only [tupleAssignment,b,dite_eq_left (hs _)]
    rfl
  have hHsel {n : ℕ} (s : Fin n ↪o I) (hs : ∀ x, s x ∈ S) :
      Set.range (liftSel s hs) ⊆ H := by
    rintro _ ⟨i,rfl⟩
    exact (e ⟨s i,hs i⟩).property
  have hraw (γ : Γ) :
      ∀ (s t : Fin (reqTest (req γ)).1 ↪o ℕ),
        Set.range s ⊆ H → Set.range t ⊆ H →
        ∀ φ ∈ (reqTest (req γ)).2.2,
          φ.Realize (tupleAssignment source s) ↔ φ.Realize (tupleAssignment source t) := by
    obtain ⟨j,rfl⟩ := ei.surjective γ
    exact hh j
  have hhom (γ : Γ) :
      ∀ (s t : Fin (reqTest (req γ)).1 ↪o I)
        (hs : ∀ x, s x ∈ S) (ht : ∀ x, t x ∈ S),
        ∀ φ ∈ (reqTest (req γ)).2.2,
          φ.Realize (tupleAssignment b s) ↔ φ.Realize (tupleAssignment b t) := by
    intro s t hs ht φ hφ
    rw [htup s hs,htup t ht]
    exact hraw γ _ _ (hHsel s hs) (hHsel t ht) φ hφ
  refine ⟨b,?_⟩
  let : L[[M ⊕ (I × Fin m)]].Structure M := Diagrams.namedExpansion
    (Sum.elim id (fun p : I × Fin m => b p.1 p.2) : M ⊕ (I × Fin m) → M)
  let : (L.lhomWithConstants (M ⊕ (I × Fin m))).IsExpansionOn M :=
    Diagrams.namedExpansion_isExpansion _
  have hinst {n : ℕ} (φ : L[[A]].Formula (Fin (n*m))) (s : Fin n → I) :
      M ⊨ instantiate A φ s ↔ φ.Realize (tupleAssignment b s) := by
    rw [instantiate,Formula.realize_equivSentence,Formula.realize_relabel]
    convert Types.parameterFormula_realize (ElementaryEmbedding.refl L M) A φ
      (tupleAssignment b s) using 1
    apply Iff.of_eq
    congr 1
    funext x
    cases x <;> rfl
    all_goals rfl
  constructor
  intro γ hγ
  let g : Γ := ⟨γ,hγ⟩
  have hg := hreq g
  change requestSentence A source distinct (req g) = γ at hg
  rw [←hg]
  have hsup := hlabels g
  have hhom' := hhom g
  cases hr : req g with
  | old θ hθ =>
    let : (constantsOn (M ⊕ (I × Fin m))).Structure M := constantsOn.structure
      (Sum.elim id (fun p : I × Fin m => b p.1 p.2))
    let : (LHom.constantsOnMap (Sum.inl : M → M ⊕ (I × Fin m))).IsExpansionOn M :=
      constantsOnMap_isExpansionOn (fα := id) (by rfl)
    let : (L.lhomWithConstantsMap (Sum.inl : M → M ⊕ (I × Fin m))).IsExpansionOn M :=
      LHom.sumMap_isExpansionOn _ _ M
    exact (LHom.realize_onSentence M _ θ).mpr hθ
  | different i j hij he =>
    apply (tupleInequality_realize i j).mpr
    have hi : i ∈ S := hsup (by simp [hr,reqLabels])
    have hj : j ∈ S := hsup (by simp [hr,reqLabels])
    change b i ≠ b j
    simp only [b,dite_eq_left hi,dite_eq_left hj]
    intro h
    have hev := hd he h
    exact hij (congrArg Subtype.val (e.injective (Subtype.ext hev)))
  | equivalence n hn φ s t =>
    have hs (x : Fin n) : s x ∈ S := hsup (by simp [hr,reqLabels])
    have ht (x : Fin n) : t x ∈ S := hsup (by simp [hr,reqLabels])
    rw [requestSentence,Sentence.realize_iff,
      hinst φ s, hinst φ t]
    have h := hhom'
    change ∀ (s t : Fin (reqTest (req g)).1 ↪o I),
      (∀ x, s x ∈ S) → (∀ x, t x ∈ S) →
      ∀ φ ∈ (reqTest (req g)).2.2,
        φ.Realize (tupleAssignment b s) ↔ φ.Realize (tupleAssignment b t) at h
    rw [hr] at h
    simp only [reqTest] at h
    exact h s t hs ht φ (Finset.mem_singleton_self φ)
  | pattern n hn Δ s =>
    have hs (x : Fin n) : s x ∈ S := hsup (by simp [hr,reqLabels])
    rw [requestSentence,hinst]
    apply (patternFormula_realize A source Δ (ElementaryEmbedding.refl L M) _).mpr
    refine ⟨liftSel s hs,?_⟩
    intro φ hφ
    rw [htup s hs]
    rfl

theorem constructionTheory_satisfiable [Nonempty M] (hm : 0 < m)
    (A : Set M) (source : ℕ → Fin m → M) (distinct : Bool)
    (hd : distinct = true → Function.Injective source) :
    (constructionTheory (L := L) (I := I) A source distinct).IsSatisfiable := by
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  obtain ⟨b, hb⟩ := constructionTheory_finite_realization hm A source distinct hd Γ hΓ
  let : L[[M ⊕ (I × Fin m)]].Structure M := Diagrams.namedExpansion
    (Sum.elim id (fun p : I × Fin m => b p.1 p.2) : M ⊕ (I × Fin m) → M)
  let : M ⊨ (↑Γ : L[[M ⊕ (I × Fin m)]].Theory) := hb
  exact Theory.Model.isSatisfiable M

theorem construction_model_spec [Nonempty M] (hm : 0 < m)
    (A : Set M) (source : ℕ → Fin m → M) (distinct : Bool)
    {C : Type w'} [L[[M ⊕ (I × Fin m)]].Structure C] [Nonempty C] :
    letI : L.Structure C := (L.lhomWithConstants (M ⊕ (I × Fin m))).reduct C
    C ⊨ constructionTheory (L := L) (I := I) A source distinct →
      ∃ f : M ↪ₑ[L] C,
        (∀ a : M, f a = (L.con (Sum.inl a : M ⊕ (I × Fin m)) : C)) ∧
        OrderIndiscernible (L := L) (f '' A) (canonicalTuples L M I m C) ∧
        LocallyBased A f source (canonicalTuples L M I m C) ∧
        (distinct = true → Function.Injective (canonicalTuples L M I m C)) := by
  have _hm := hm
  let : L.Structure C := (L.lhomWithConstants (M ⊕ (I × Fin m))).reduct C
  let : (L.lhomWithConstants (M ⊕ (I × Fin m))).IsExpansionOn C := LHom.isExpansionOn_reduct _ _
  intro hC
  let k := L.lhomWithConstantsMap (Sum.inl : M → M ⊕ (I × Fin m))
  let : L[[M]].Structure C := k.reduct C
  let : (L.lhomWithConstants M).IsExpansionOn C :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hold : C ⊨ L.elementaryDiagram M := by
    constructor
    intro γ hγ
    apply (k.realize_onSentence C γ).mp
    exact hC.realize_of_mem _ ⟨.old γ hγ,rfl⟩
  obtain ⟨f,hf⟩ := Diagrams.model_elementary_iff_canonical_elementary.mp hold
  have hf' (a : M) : f a = (L.con (Sum.inl a : M ⊕ (I × Fin m)) : C) := congrFun hf a
  have hi {n : ℕ} (φ : L[[A]].Formula (Fin (n*m))) (s : Fin n → I) :
      C ⊨ instantiate A φ s ↔
        @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ
          (tupleAssignment (canonicalTuples L M I m C) s) := by
    rw [instantiate, Formula.realize_equivSentence, Formula.realize_relabel]
    convert Types.parameterFormula_realize f A φ
      (tupleAssignment (canonicalTuples L M I m C) s) using 1
    apply Iff.of_eq
    congr 1
    funext x
    cases x with
    | inl a => exact (hf' a).symm
    | inr x => rfl
    all_goals rfl
  refine ⟨f,hf',?_,?_,?_⟩
  · apply (image_parameters_indiscernible A f _).mpr
    intro n hn φ s t
    have h := hC.realize_of_mem _ ⟨.equivalence n hn φ s t,rfl⟩
    rw [requestSentence, Sentence.realize_iff,hi,hi] at h
    exact h
  · intro n hn Δ s
    have h := hC.realize_of_mem _ ⟨.pattern n hn Δ s,rfl⟩
    have hp := (hi (patternFormula A source Δ) s).mp h
    exact (patternFormula_realize A source Δ f _).mp hp
  · intro hd i j he
    by_contra hij
    have h := hC.realize_of_mem _ ⟨.different i j hij hd,rfl⟩
    exact (tupleInequality_realize i j).mp h he

theorem exists_indiscernible_extension [Nonempty M] [Infinite I] (hm : 0 < m)
    (A : Set M) (source : ℕ → Fin m → M) (hs : Function.Injective source) :
    ∃ (N : Type (max u v w z)) (_ : L.Structure N), Nonempty N ∧
      ∃ (f : M ↪ₑ[L] N) (b : I → Fin m → N),
        OrderIndiscernible (L := L) (f '' A) b ∧
        LocallyBased A f source b ∧ Function.Injective b := by
  let C := (constructionTheory_satisfiable (L := L) (I := I) hm A source true (fun _ => hs)).some
  let : L.Structure C := (L.lhomWithConstants (M ⊕ (I × Fin m))).reduct C
  obtain ⟨f, hf, hi, hl, hd⟩ := construction_model_spec (L := L) (I := I) hm A source true C.is_model
  exact ⟨C, inferInstance, inferInstance, f, canonicalTuples L M I m C, hi, hl, hd rfl⟩

theorem exists_locally_based_extension [Nonempty M] [Infinite I] (hm : 0 < m)
    (A : Set M) (source : ℕ → Fin m → M) :
    ∃ (N : Type (max u v w z)) (_ : L.Structure N), Nonempty N ∧
      ∃ (f : M ↪ₑ[L] N) (b : I → Fin m → N),
        OrderIndiscernible (L := L) (f '' A) b ∧ LocallyBased A f source b := by
  let C := (constructionTheory_satisfiable (L := L) (I := I) hm A source false (by simp)).some
  let : L.Structure C := (L.lhomWithConstants (M ⊕ (I × Fin m))).reduct C
  obtain ⟨f, hf, hi, hl, hd⟩ := construction_model_spec (L := L) (I := I) hm A source false C.is_model
  exact ⟨C, inferInstance, inferInstance, f, canonicalTuples L M I m C, hi, hl⟩

theorem locallyBased_constant [Infinite I] (A : Set M) (f : M ↪ₑ[L] N)
    (a : Fin m → M) (b : I → Fin m → N)
    (h : LocallyBased A f (fun _ : ℕ => a) b) :
    (∀ i j, b i = b j) ∧ ¬Function.Injective b := by

  classical
  have hlt : ∀ i j : I, i < j → b i = b j := by
    intro i j hij
    let s : Fin 2 ↪o I := OrderEmbedding.ofStrictMono ![i,j] (by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all)
    funext k
    let φ : L[[A]].Formula (Fin (2*m)) :=
      Term.equal (Term.var (finProdFinEquiv ((0 : Fin 2),k)))
        (Term.var (finProdFinEquiv ((1 : Fin 2),k)))
    have hφ : ∀ t : Fin 2 ↪o ℕ,
        φ.Realize (tupleAssignment (fun _ : ℕ => a) t) ↔ true = true := by
      intro t
      simp [φ,Formula.realize_equal,Term.realize_var,tupleAssignment]
    have hb := locallyBased_preserves_uniform_test h (by decide : 0 < 2) φ true hφ s
    have ht := hb.mpr rfl
    have hs0 : s 0 = i := rfl
    have hs1 : s 1 = j := rfl
    simpa only [φ,Formula.realize_equal,Term.realize_var,tupleAssignment,
      Equiv.symm_apply_apply,hs0,hs1] using! ht
  have hall : ∀ i j : I, b i = b j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hlt i j hij
    · rfl
    · exact (hlt j i hji).symm
  refine ⟨hall,?_⟩
  intro hinj
  have hsub : Subsingleton I := ⟨fun i j => hinj (hall i j)⟩
  have := hsub
  exact not_finite I

end Lemmatheca.ModelTheory.IndiscernibleSequences
