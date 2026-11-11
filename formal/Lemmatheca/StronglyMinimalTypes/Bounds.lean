import Lemmatheca.StronglyMinimalTypes.Generic

/-! Counts in the same universe as the actual native parameter type space. -/
namespace Lemmatheca.ModelTheory.StronglyMinimalTypes
open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.ModelTheory
open StronglyMinimalSets Closures OrderPatternsAndStability
universe u v w w'
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- Formula-count bound, with lifts to the common language/parameter universe. -/
def syntaxBound (A : Set M) : Cardinal.{max u v w} :=
  max (Cardinal.lift.{w} L.card) (max ℵ₀ (Cardinal.lift.{max u v} #A))

/-- A union of finite solution sets over the actual parameter formulas bounds acl. -/
theorem acl_cardinal_bound (A : Set M) :
    Cardinal.lift.{max u v} #(acl L A) ≤ syntaxBound (L := L) A := by
  classical
  let F := {φ : L[[A]].Formula (Fin 1) // (solutions A φ).Finite}
  have hInf : ℵ₀ ≤ syntaxBound (L := L) A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hF : #F ≤ syntaxBound (L := L) A :=
    (Cardinal.mk_subtype_le _).trans (parameter_formula_count A 1)
  have hcover : acl L A = ⋃ φ : F, solutions A φ.val := by
    ext b
    rw [mem_acl_iff_formula]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨φ, hfin, hb⟩
      exact ⟨⟨φ, hfin⟩, hb⟩
    · rintro ⟨φ, hb⟩
      exact ⟨φ.val, φ.property, hb⟩
  let : Nonempty F := ⟨⟨⊥, by simp [solutions]⟩⟩
  have hs : (⨆ φ : F, Cardinal.lift.{max u v w} #(solutions A φ.val)) ≤ ℵ₀ := by
    apply ciSup_le
    intro φ
    let : Finite (solutions A φ.val) := φ.property.to_subtype
    exact Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0
  have hu := Cardinal.mk_iUnion_le_lift (fun φ : F => solutions A φ.val)
  rw [← hcover] at hu
  have hm : Cardinal.lift.{w} #F *
      (⨆ φ : F, Cardinal.lift.{max u v w} #(solutions A φ.val)) ≤
      syntaxBound (L := L) A * ℵ₀ :=
    mul_le_mul' (by rw [Cardinal.lift_id'.{w, max u v}]; exact hF) hs
  have h := hu.trans hm
  rw [Cardinal.lift_umax.{w, max u v}] at h
  simpa only [Cardinal.mul_aleph0_eq hInf] using h

/-- Surjectivity of the specified map bounds the algebraic-type subtype. -/
theorem algebraic_type_cardinal_bound (A : Set M) :
    #({q : TypesOver (L := L) A 1 // Algebraic A q}) ≤ syntaxBound (L := L) A := by
  have hs : Function.Surjective
      (fun b : ULift.{max u v} (acl L A) => algebraicPointType A b.down) := by
    intro q
    obtain ⟨b, hb⟩ := algebraicPointType_surjective A q
    exact ⟨⟨b⟩, hb⟩
  have hc := Cardinal.mk_le_of_surjective hs
  have hcard : #({q : TypesOver (L := L) A 1 // Algebraic A q}) ≤
      Cardinal.lift.{max u v} #(acl L A) := by
    simpa only [Cardinal.mk_uLift] using hc
  exact hcard.trans (acl_cardinal_bound A)

/-- Every algebraic type can be assigned a distinct finite-solution isolating formula. -/
theorem algebraic_formula_injection (A : Set M) :
    ∃ f : {q : TypesOver (L := L) A 1 // Algebraic A q} → L[[A]].Formula (Fin 1),
      Function.Injective f ∧ ∀ q,
        (solutions A (f q)).Finite ∧
          IsolatedTypes.Isolates (L[[A]].completeTheory M) q.val (f q) := by
  classical
  choose f hfin hiso using
    (fun q : {q : TypesOver (L := L) A 1 // Algebraic A q} =>
      algebraic_isolated A q.val q.property)
  refine ⟨f, ?_, fun q => ⟨hfin q, hiso q⟩⟩
  intro q r he
  apply Subtype.ext
  have hr := ((IsolatedTypes.isolates_iff_unique r.val (f r)).mp (hiso r)).1
  have hr' : f q ∈ Types.formulas r.val := by simpa only [he] using hr
  exact (((IsolatedTypes.isolates_iff_unique q.val (f q)).mp (hiso q)).2 r.val hr').symm

/-- The complete one-type space is the union of algebraic types and its one generic member. -/
theorem one_type_bound (A : Set M) (hM : Minimal L M) :
    #(TypesOver (L := L) A 1) ≤ syntaxBound (L := L) A := by
  classical
  let F : TypesOver (L := L) A 1 → Option {q : TypesOver (L := L) A 1 // Algebraic A q} :=
    fun q => if h : Algebraic A q then some ⟨q, h⟩ else none
  have hi : Function.Injective F := by
    intro q r he
    by_cases hq : Algebraic A q
    · by_cases hr : Algebraic A r
      · have he' : (⟨q, hq⟩ : {q : TypesOver (L := L) A 1 // Algebraic A q}) = ⟨r, hr⟩ :=
          Option.some.inj (by simpa only [F, dite_eq_left hq, dite_eq_left hr] using he)
        exact congrArg Subtype.val he'
      · simp only [F, dite_eq_left hq, dite_eq_right hr, reduceCtorEq] at he
    · by_cases hr : Algebraic A r
      · simp only [F, dite_eq_right hq, dite_eq_left hr, reduceCtorEq] at he
      · exact (unique_nonalgebraic A hM q hq).trans
          (unique_nonalgebraic A hM r hr).symm
  have hInf : ℵ₀ ≤ syntaxBound (L := L) A :=
    (le_max_left _ _).trans (le_max_right _ _)
  calc
    #(TypesOver (L := L) A 1) ≤ #(Option {q : TypesOver (L := L) A 1 // Algebraic A q}) :=
      Cardinal.mk_le_of_injective hi
    _ = #({q : TypesOver (L := L) A 1 // Algebraic A q}) + 1 := Cardinal.mk_option
    _ ≤ syntaxBound (L := L) A := Cardinal.add_le_of_le hInf
      (algebraic_type_cardinal_bound A) (Cardinal.one_le_aleph0.trans hInf)

/-- Omega-stability is the existing cardinal stability predicate at aleph zero, in one variable. -/
def OmegaStable (T : L.Theory) : Prop :=
  KappaStable.{u,v,w} T ℵ₀

/-- Strongly minimal complete theories satisfy the one-variable cardinal stability bound. -/
theorem stronglyMinimal_kappaStable (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalTheory T) (κ : Cardinal.{max u v w})
    (hκ : ℵ₀ ≤ κ) (hL : Cardinal.lift.{w} L.card ≤ κ) :
    KappaStable T κ := by
  have _hSatisfiable := hT.1
  refine ⟨hκ, ?_⟩
  intro P A hA
  apply (one_type_bound A (theory_model_minimal T hSM)).trans
  apply max_le
  · change Cardinal.lift.{max u v w} L.card ≤ κ
    rw [Cardinal.lift_umax.{max u v, w}]
    exact hL
  · apply max_le hκ
    rw [Cardinal.lift_id'.{max u v, w}]
    exact hA

/-- In a countable language the one-variable stability bound is countable. -/
theorem stronglyMinimal_omegaStable (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalTheory T) [Countable L.Symbols] :
    OmegaStable.{u,v,w} T := by
  apply stronglyMinimal_kappaStable T hT hSM ℵ₀ le_rfl
  exact Cardinal.lift_le_aleph0.mpr (Cardinal.mk_le_aleph0 (α := L.Symbols))

/-- A model larger than its syntax bound already contains a generic point over A. -/
theorem old_generic_of_large_model (A : Set M) (hM : Minimal L M)
    (hlarge : syntaxBound (L := L) A < Cardinal.lift.{max u v} #M) :
    ∃ b : M, (L[[A]].completeTheory M).typeOf (fun _ => b) = genericType A hM := by
  classical
  by_contra hn
  have hall : ∀ b : M, b ∈ acl L A := by
    intro b
    by_contra hb
    exact hn ⟨b, (generic_old_realization A hM b).mpr hb⟩
  have he : acl L A = Set.univ := Set.eq_univ_of_forall hall
  have hc := acl_cardinal_bound (L := L) A
  rw [he, Cardinal.mk_univ] at hc
  exact (not_lt_of_ge hc) hlarge

/-- When all old elements are parameters, no old point realizes the generic type. -/
theorem generic_over_model_omitted (hM : Minimal L M) (b : M) :
    (L[[(Set.univ : Set M)]].completeTheory M).typeOf (fun _ => b) ≠
      genericType (Set.univ : Set M) hM := by
  intro he
  have hn := (generic_old_realization (Set.univ : Set M) hM b).mp he
  exact hn (dcl_subset_acl _ (subset_dcl _ (Set.mem_univ b)))

/-- A generic realization over the whole old model cannot belong to the elementary image. -/
theorem generic_over_model_new {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (hM : Minimal L M) (b : N)
    (hb : extensionType f (Set.univ : Set M) b = genericType (Set.univ : Set M) hM) :
    b ∉ Set.range f := by
  rintro ⟨a, rfl⟩
  apply generic_over_model_omitted hM a
  rw [← extensionType_old_point f (Set.univ : Set M) a]
  exact hb

end
end Lemmatheca.ModelTheory.StronglyMinimalTypes
