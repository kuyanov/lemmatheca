import Lemmatheca.OrderPatternsAndStability.TypesAndCuts
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared

/-! Exact named-point classification and finite equality-pattern bounds. -/
namespace Lemmatheca.ModelTheory.OrderPatternsAndStability.Equality
open FirstOrder FirstOrder.Language Cardinal
universe w v z
open Lemmatheca.ModelTheory.QuantifierElimination
variable {M : Type w} [Language.empty.Structure M] [Infinite M] (A : Set M)

omit [Infinite M] in
private theorem formulas_injective {r : ℕ} :
    Function.Injective (fun q : TypesOver (L := Language.empty) A r => Types.formulas q) := by
  intro p q hp
  apply SetLike.ext'
  change p.toTheory = q.toTheory
  apply Set.ext
  intro γ
  have h := Set.ext_iff.mp hp (Formula.equivSentence.symm γ)
  change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory ↔
    Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory at h
  simpa only [Equiv.apply_symm_apply] using h

private theorem empty_formula_pattern {D : Type v} {E : Type z}
    [Language.empty.Structure D] [Language.empty.Structure E] [Infinite D] [Infinite E]
    {α : Type*} (φ : Language.empty.Formula α) (a : α → D) (b : α → E)
    (he : ∀ i j, a i = a j ↔ b i = b j) : φ.Realize a ↔ φ.Realize b := by
  classical
  let e := Fintype.equivFin φ.freeVarFinset
  let ψ := φ.restrictFreeVar e
  let da : Fin (Fintype.card φ.freeVarFinset) → D := fun i => a (e.symm i).val
  let eb : Fin (Fintype.card φ.freeVarFinset) → E := fun i => b (e.symm i).val
  have hD : FirstOrder.Language.Formula.Realize ψ da ↔ φ.Realize a := by
    simpa only [FirstOrder.Language.Formula.Realize,ψ] using (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := e) (v := da) a (by intro i; simp only [da,e.symm_apply_apply]))
  have hE : FirstOrder.Language.Formula.Realize ψ eb ↔ φ.Realize b := by
    simpa only [FirstOrder.Language.Formula.Realize,ψ] using (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := e) (v := eb) b (by intro i; simp only [eb,e.symm_apply_apply]))
  have hs : Similar (o := false) noRelation noRelation da eb := by
    intro atom
    rcases atom with ⟨i,j⟩ | ⟨c,i,j⟩
    · exact he (e.symm i).val (e.symm j).val
    · exact c.elim
  have hq := realize_of_patterns equality_extends equality_extends (Shared.fromShared (Shared.pack ψ)) hs
  have hd := (Shared.fromEquality_realize (Shared.pack ψ) da).trans (Shared.pack_realize ψ da)
  have hb := (Shared.fromEquality_realize (Shared.pack ψ) eb).trans (Shared.pack_realize ψ eb)
  exact hD.symm.trans (hd.symm.trans (hq.trans (hb.trans hE)))

private theorem realize_type (r : ℕ) (q : TypesOver (L := Language.empty) A r) :
    ∃ (D : Type w) (_SD : Language.empty.Structure D) (_ : Infinite D),
      ∃ (f : M ↪ₑ[Language.empty] D) (a : Fin r → D),
        ∀ φ : Language.empty[[A]].Formula (Fin r),
          φ ∈ Types.formulas q ↔ @FirstOrder.Language.Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ a := by
  have hp := (Types.partial_iff_finitelyRealized_completeTheory (M := M) (Types.formulas q)).mp (Types.partial_formulas q)
  obtain ⟨D,SD,hD,f,a,ha⟩ := (Types.parameter_realization A (Types.formulas q)).mp hp
  let := SD
  let := hD
  let hi : Infinite D := Infinite.of_injective f f.injective
  let : Nonempty (f.toEmbedding.withConstants A) := hD
  let : Language.empty[[A]].Structure D := inferInstanceAs (Language.empty[[A]].Structure (f.toEmbedding.withConstants A))
  let : f.toEmbedding.withConstants A ⊨ (Language.empty[[A]].completeTheory M) :=
    ((f.liftWithConstants A).theory_model_iff _).mp inferInstance
  have he : q = (Language.empty[[A]].completeTheory M).typeOf (M := f.toEmbedding.withConstants A) a :=
    (Types.realizes_complete_iff (M := f.toEmbedding.withConstants A) q a).mp ha
  exact ⟨D,SD,hi,f,a,fun φ => he ▸ Theory.CompleteType.formula_mem_typeOf⟩

def coordinateNamed (r : ℕ) (i : Fin r) (a : A) :
    Language.empty[[A]].Formula (Fin r) :=
  (Term.var i).equal (Constants.term (Language.empty.con a))

private theorem type_eq_of_atoms (r : ℕ) (q t : TypesOver (L := Language.empty) A r)
    (heq : ∀ i j : Fin r,
      (Term.var i).equal (Term.var j) ∈ Types.formulas q ↔
      (Term.var i).equal (Term.var j) ∈ Types.formulas t)
    (hnamed : ∀ (i : Fin r) (c : A),
      coordinateNamed A r i c ∈ Types.formulas q ↔ coordinateNamed A r i c ∈ Types.formulas t) : q = t := by
  obtain ⟨D,SD,hD,f,a,ha⟩ := realize_type A r q
  obtain ⟨E,SE,hE,g,b,hb⟩ := realize_type A r t
  let := SD
  let := SE
  let := hD
  let := hE
  have hae (i j : Fin r) : (Term.var i).equal (Term.var j) ∈ Types.formulas q ↔ a i = a j := ha _
  have hbe (i j : Fin r) : (Term.var i).equal (Term.var j) ∈ Types.formulas t ↔ b i = b j := hb _
  have han (i : Fin r) (c : A) : coordinateNamed A r i c ∈ Types.formulas q ↔ a i = f c := ha _
  have hbn (i : Fin r) (c : A) : coordinateNamed A r i c ∈ Types.formulas t ↔ b i = g c := hb _
  have hsame (i j : A ⊕ Fin r) : Sum.elim (fun c : A => f c) a i = Sum.elim (fun c : A => f c) a j ↔
      Sum.elim (fun c : A => g c) b i = Sum.elim (fun c : A => g c) b j := by
    rcases i with c | i <;> rcases j with d | j
    · exact f.injective.eq_iff.trans g.injective.eq_iff.symm
    · change f c = a j ↔ g c = b j
      exact eq_comm.trans (((han j c).symm.trans ((hnamed j c).trans (hbn j c))).trans eq_comm)
    · exact (han i d).symm.trans ((hnamed i d).trans (hbn i d))
    · exact (hae i j).symm.trans ((heq i j).trans (hbe i j))
  apply formulas_injective A
  apply Set.ext
  intro φ
  have hp := empty_formula_pattern (BoundedFormula.constantsVarsEquiv φ)
    (Sum.elim (fun c : A => f c) a) (Sum.elim (fun c : A => g c) b) hsame
  have had := BoundedFormula.realize_constantsVarsEquiv (M := f.toEmbedding.withConstants A)
    (φ := φ) (v := a) (xs := Fin.elim0)
  have hbd := BoundedFormula.realize_constantsVarsEquiv (M := g.toEmbedding.withConstants A)
    (φ := φ) (v := b) (xs := Fin.elim0)
  exact (ha φ).trans (had.symm.trans (hp.trans (hbd.trans (hb φ).symm)))

private theorem coordinate_unique (r : ℕ) (q : TypesOver (L := Language.empty) A r)
    (i : Fin r) (a b : A) (ha : coordinateNamed A r i a ∈ Types.formulas q)
    (hb : coordinateNamed A r i b ∈ Types.formulas q) : a = b := by
  obtain ⟨D,SD,hD,f,x,hx⟩ := realize_type A r q
  let := SD
  let := hD
  have ha' : x i = f a := (hx _).mp ha
  have hb' : x i = f b := (hx _).mp hb
  exact Subtype.ext (f.injective (ha'.symm.trans hb'))

private theorem equality_reflexive (r : ℕ) (q : TypesOver (L := Language.empty) A r) (i j : Fin r)
    (hij : i = j) : (Term.var i).equal (Term.var j) ∈ Types.formulas q := by
  obtain ⟨D,SD,hD,f,x,hx⟩ := realize_type A r q
  let := SD
  let := hD
  exact (hx _).mpr (by subst j; rfl)

omit [Infinite M] in
private theorem formula_not_both (r : ℕ) (q : TypesOver (L := Language.empty) A r)
    (φ : Language.empty[[A]].Formula (Fin r)) (hp : φ ∈ Types.formulas q)
    (hn : φ.not ∈ Types.formulas q) : False := by
  change FirstOrder.Language.Formula.equivSentence φ.not ∈ q.toTheory at hn
  rw [FirstOrder.Language.Formula.equivSentence_not] at hn
  exact (q.not_mem_iff _).mp hn hp

def exclusions : Set (Language.empty[[A]].Formula (Fin 1)) :=
  Set.range fun a : A => (coordinateNamed A 1 0 a).not

theorem exclusions_finitely_realized :
    Types.FinitelyRealized M (exclusions A) := by
  classical
  intro s hs
  choose c hc using fun φ : s => (hs φ.property : ∃ a : A, (coordinateNamed A 1 0 a).not = φ.val)
  let bad := Finset.univ.image (fun φ : s => (c φ).val)
  obtain ⟨b,hb⟩ := bad.finite_toSet.exists_notMem
  refine ⟨fun _ => b,?_⟩
  intro φ hφ
  have hφeq : (coordinateNamed A 1 0 (c ⟨φ,hφ⟩)).not = φ := hc ⟨φ,hφ⟩
  rw [← hφeq]
  have hne : b ≠ (c ⟨φ,hφ⟩).val := by
    intro he
    exact hb (Finset.mem_image.mpr ⟨⟨φ,hφ⟩,Finset.mem_univ _,he.symm⟩)
  exact hne

theorem exclusions_partial :
    Types.IsPartial (Language.empty[[A]].completeTheory M) (exclusions A) := by
  exact (Types.partial_iff_finitelyRealized_completeTheory (M := M) (exclusions A)).mpr
    (exclusions_finitely_realized A)

def pointType (a : A) : TypesOver (L := Language.empty) A 1 :=
  (Language.empty[[A]].completeTheory M).typeOf (fun _ => a.val)

noncomputable def freshType : TypesOver (L := Language.empty) A 1 :=
  (Types.exists_complete_extension (exclusions A) (exclusions_partial A)).choose

theorem freshType_excludes :
    exclusions A ⊆ Types.formulas (freshType A) := by
  exact (Types.exists_complete_extension (exclusions A) (exclusions_partial A)).choose_spec

noncomputable def typeFromChoice : A ⊕ PUnit → TypesOver (L := Language.empty) A 1 :=
  Sum.elim (pointType A) (fun _ => freshType A)

theorem typeFromChoice_bijective : Function.Bijective (typeFromChoice A) := by
  classical
  have point_named (a : A) : coordinateNamed A 1 0 a ∈ Types.formulas (pointType A a) :=
    Theory.CompleteType.formula_mem_typeOf.mpr rfl
  have fresh_not_named (a : A) : coordinateNamed A 1 0 a ∉ Types.formulas (freshType A) := by
    intro h
    exact formula_not_both A 1 (freshType A) _ h (freshType_excludes A ⟨a,rfl⟩)
  constructor
  · rintro (a | a) (b | b) hab
    · change pointType A a = pointType A b at hab
      have hm : coordinateNamed A 1 0 a ∈ Types.formulas (pointType A b) := hab ▸ point_named a
      have he : b.val = a.val := Theory.CompleteType.formula_mem_typeOf.mp hm
      exact congrArg Sum.inl (Subtype.ext he.symm)
    · change pointType A a = freshType A at hab
      exact (fresh_not_named a (hab ▸ point_named a)).elim
    · change freshType A = pointType A b at hab
      exact (fresh_not_named b (hab.symm ▸ point_named b)).elim
    · exact congrArg Sum.inr (Subsingleton.elim a b)
  · intro q
    by_cases hn : ∃ a : A, coordinateNamed A 1 0 a ∈ Types.formulas q
    · obtain ⟨a,ha⟩ := hn
      refine ⟨Sum.inl a,?_⟩
      change pointType A a = q
      symm
      apply type_eq_of_atoms A 1 q (pointType A a)
      · intro i j
        exact iff_of_true (equality_reflexive A 1 q i j (Subsingleton.elim _ _))
          (equality_reflexive A 1 (pointType A a) i j (Subsingleton.elim _ _))
      · intro i b
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        constructor
        · intro hb
          have he := coordinate_unique A 1 q 0 a b ha hb
          subst b
          exact point_named a
        · intro hb
          have he : a.val = b.val := Theory.CompleteType.formula_mem_typeOf.mp hb
          exact (Subtype.ext he : a = b) ▸ ha
    · refine ⟨Sum.inr PUnit.unit,?_⟩
      change freshType A = q
      symm
      apply type_eq_of_atoms A 1 q (freshType A)
      · intro i j
        exact iff_of_true (equality_reflexive A 1 q i j (Subsingleton.elim _ _))
          (equality_reflexive A 1 (freshType A) i j (Subsingleton.elim _ _))
      · intro i a
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact iff_of_false (fun h => hn ⟨a,h⟩) (fresh_not_named a)

noncomputable def typeEquiv : (A ⊕ PUnit) ≃ TypesOver (L := Language.empty) A 1 :=
  Equiv.ofBijective (typeFromChoice A) (typeFromChoice_bijective A)

theorem one_type_cardinality :
    #(TypesOver (L := Language.empty) A 1) = #A + 1 := by
  have he := Cardinal.mk_congr (typeEquiv A : (A ⊕ PUnit.{w+1}) ≃ TypesOver (L := Language.empty) A 1)
  simpa only [Cardinal.mk_sum,Cardinal.mk_punit,Cardinal.lift_id] using he.symm

/-- Inconsistent codes are permitted; every true type still has its exact equality data. -/
structure TuplePattern (r : ℕ) where
  same : Fin r → Fin r → Bool
  named : Fin r → Option A

noncomputable def tuplePattern (r : ℕ) (q : TypesOver (L := Language.empty) A r) :
    TuplePattern A r := by
  classical
  exact {
    same := fun i j => decide ((Term.var i).equal (Term.var j) ∈ Types.formulas q)
    named := fun i => if h : ∃ a : A, coordinateNamed A r i a ∈ Types.formulas q
      then some h.choose else none }

theorem tuplePattern_same_equivalence (r : ℕ)
    (q : TypesOver (L := Language.empty) A r) :
    Equivalence (fun i j => (tuplePattern A r q).same i j = true) := by
  classical
  obtain ⟨D,SD,hD,f,a,ha⟩ := realize_type A r q
  let := SD
  let := hD
  have he (i j : Fin r) : (tuplePattern A r q).same i j = true ↔ a i = a j := by
    have hφ : (Term.var i).equal (Term.var j) ∈ Types.formulas q ↔ a i = a j := ha _
    simpa only [tuplePattern,decide_eq_true_eq] using hφ
  exact ⟨fun i => (he i i).mpr rfl,
    fun {i j} h => (he j i).mpr ((he i j).mp h).symm,
    fun {i j k} hij hjk => (he i k).mpr (((he i j).mp hij).trans ((he j k).mp hjk))⟩

theorem tuplePattern_named (r : ℕ) (q : TypesOver (L := Language.empty) A r)
    (i : Fin r) (a : A) :
    (tuplePattern A r q).named i = some a ↔ coordinateNamed A r i a ∈ Types.formulas q := by
  classical
  by_cases h : ∃ c : A, coordinateNamed A r i c ∈ Types.formulas q
  · simp only [tuplePattern,dite_eq_left h]
    constructor
    · intro he
      exact (Option.some.inj he) ▸ h.choose_spec
    · intro ha
      exact congrArg some (coordinate_unique A r q i h.choose a h.choose_spec ha)
  · simp only [tuplePattern,dite_eq_right h]
    exact iff_of_false (by intro he; cases he) (fun ha => h ⟨a,ha⟩)

theorem tuplePattern_injective (r : ℕ) : Function.Injective (tuplePattern A r) := by
  classical
  intro q t he
  apply type_eq_of_atoms A r q t
  · intro i j
    have hh := congrArg (fun p : TuplePattern A r => p.same i j) he
    change decide ((Term.var i).equal (Term.var j) ∈ Types.formulas q) =
      decide ((Term.var i).equal (Term.var j) ∈ Types.formulas t) at hh
    have hiff := (congrArg (fun b : Bool => b = true) hh).to_iff
    simpa only [decide_eq_true_eq] using hiff
  · intro i a
    rw [← tuplePattern_named A r q i a,← tuplePattern_named A r t i a,he]

theorem tuple_pattern_card (r : ℕ) :
    #(TuplePattern A r) ≤ (2 : Cardinal.{w}) ^ (r*r) * (#A+1)^r := by
  let label : Option A ≃ TypesOver (L := Language.empty) A 1 :=
    (Equiv.optionEquivSumPUnit.{w,w} A).trans (typeEquiv A)
  let raw : TuplePattern A r ≃ (Fin r → Fin r → Bool) × (Fin r → Option A) :=
    { toFun := fun p => (p.same,p.named)
      invFun := fun p => ⟨p.1,p.2⟩
      left_inv := by rintro ⟨a,b⟩; rfl
      right_inv := by rintro ⟨a,b⟩; rfl }
  let e := raw.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ : Fin r => label))
  have he := (Cardinal.mk_congr e).le
  simp only [Cardinal.mk_prod,Cardinal.mk_arrow,Cardinal.mk_bool,Cardinal.mk_fin,
    one_type_cardinality A,Cardinal.lift_power,Cardinal.lift_id,Cardinal.lift_uzero,
    Cardinal.lift_ofNat,Cardinal.lift_natCast,← Cardinal.power_mul,← Nat.cast_mul] at he
  simpa only [Cardinal.power_natCast] using he

theorem finite_tuple_type_bound (r : ℕ) (κ : Cardinal.{w})
    (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    #(TypesOver (L := Language.empty) A r) ≤ κ := by
  have hb := (Cardinal.mk_le_of_injective (tuplePattern_injective A r)).trans (tuple_pattern_card A r)
  have htwo : (2 : Cardinal.{w}) ≤ κ := (Cardinal.natCast_le_aleph0 (n := 2)).trans hκ
  have hone : (1 : Cardinal.{w}) ≤ κ := Cardinal.one_le_aleph0.trans hκ
  have hleft : (2 : Cardinal.{w}) ^ (r*r) ≤ κ :=
    (Cardinal.power_le_power_right htwo).trans (Cardinal.power_nat_le hκ)
  have hright : (#A+1) ^ r ≤ κ :=
    (Cardinal.power_le_power_right (Cardinal.add_le_of_le hκ hA hone)).trans (Cardinal.power_nat_le hκ)
  exact hb.trans (Cardinal.mul_le_of_le hκ hleft hright)

theorem kappa_stable (κ : Cardinal.{w}) (hκ : ℵ₀ ≤ κ) :
    KappaStable.{0,0,w} Language.empty.infiniteTheory κ := by
  refine ⟨hκ,?_⟩
  intro P A hA
  let : Infinite P := Language.empty.model_infiniteTheory_iff.mp P.is_model
  rw [one_type_cardinality A]
  exact Cardinal.add_le_of_le hκ hA (Cardinal.one_le_aleph0.trans hκ)

theorem stable : StableTheory Language.empty.infiniteTheory := by
  intro m n hm hn φ h
  obtain ⟨P,A,hA,hlower⟩ := orderProperty_many_types.{0,0,0} Language.empty.infiniteTheory φ h
  let : Infinite P := Language.empty.model_infiniteTheory_iff.mp P.is_model
  have hupper := finite_tuple_type_bound A m ℵ₀ le_rfl (Cardinal.mk_le_aleph0_iff.mpr hA.to_subtype)
  exact (not_le_of_gt (Cardinal.cantor ℵ₀)) (hlower.trans hupper)

theorem infinitely_many_one_types (hA : A.Infinite) :
    Infinite (TypesOver (L := Language.empty) A 1) := by
  let : Infinite A := hA.to_subtype
  exact Infinite.of_injective (fun a : A => typeFromChoice A (Sum.inl a : A ⊕ PUnit.{w+1}))
    ((typeFromChoice_bijective A).1.comp Sum.inl_injective)

end Lemmatheca.ModelTheory.OrderPatternsAndStability.Equality
