import Lemmatheca.OrderPatternsAndStability.OrderProperty
import Mathlib.ModelTheory.Encoding
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality

/-! Native parameter types and complete types distinguished by external real cuts. -/
namespace Lemmatheca.ModelTheory.OrderPatternsAndStability
open FirstOrder FirstOrder.Language Cardinal
universe u v w w'
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N] {m n : ℕ}

abbrev TypesOver (A : Set M) (r : ℕ) :=
  (L[[A]].completeTheory M).CompleteType (Fin r)

/-- The common ambient universe contains the language, parameter sets, and their type spaces. -/
def KappaStable (T : L.Theory) (κ : Cardinal.{max u v w}) : Prop :=
  ℵ₀ ≤ κ ∧ ∀ P : Theory.ModelType.{u,v,max u v w} T,
    ∀ A : Set P, #A ≤ κ → #(TypesOver (L := L) A 1) ≤ κ

theorem parameter_formula_count (A : Set M) (r : ℕ) :
    #(L[[A]].Formula (Fin r)) ≤
      max (Cardinal.lift.{w} L.card) (max ℵ₀ (Cardinal.lift.{max u v} #A)) := by
  let _ : L.Structure M := inferInstance
  let K := L.withConstants A
  let c : Cardinal.{max u v w} :=
    max (Cardinal.lift.{w} L.card) (max ℵ₀ (Cardinal.lift.{max u v} #A))
  have hc : ℵ₀ ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hK : K.card ≤ c := by
    rw [Language.card_withConstants]
    exact Cardinal.add_le_of_le hc (le_max_left _ _)
      ((le_max_right _ _).trans (le_max_right _ _))
  calc
    #(K.Formula (Fin r)) ≤ #(Σ n, K.BoundedFormula (Fin r) n) :=
      Cardinal.mk_le_of_injective (f := fun p : K.Formula (Fin r) => (⟨0,p⟩ : Σ n, K.BoundedFormula (Fin r) n))
        (fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    _ ≤ max ℵ₀ (Cardinal.lift.{max u v w} #(Fin r) + K.card) := by
      simpa only [Cardinal.lift_uzero] using (BoundedFormula.card_le (L := K) (α := Fin r))
    _ ≤ c := max_le hc (Cardinal.add_le_of_le hc
      ((Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hc) hK)

theorem parameter_type_count (A : Set M) (r : ℕ) :
    #(TypesOver (L := L) A r) ≤
      2 ^ max (Cardinal.lift.{w} L.card) (max ℵ₀ (Cardinal.lift.{max u v} #A)) := by
  have hi : Function.Injective
      (fun q : TypesOver (L := L) A r => Types.formulas q) := by
    intro p q hp
    apply SetLike.ext'
    change p.toTheory = q.toTheory
    apply Set.ext
    intro γ
    have h := Set.ext_iff.mp hp (Formula.equivSentence.symm γ)
    change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory ↔
      Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory at h
    simpa only [Equiv.apply_symm_apply] using h
  calc
    #(TypesOver (L := L) A r) ≤ #(Set (L[[A]].Formula (Fin r))) := Cardinal.mk_le_of_injective hi
    _ = 2 ^ #(L[[A]].Formula (Fin r)) := Cardinal.mk_set
    _ ≤ _ := Cardinal.power_le_power_left (by simp) (parameter_formula_count A r)

/-- Substitute the actual named parameter tuple into the parameter block. -/
def parameterInstance (A : Set M) (φ : L.Formula (Fin (m+n)))
    (b : Fin n → M) (hb : ∀ k, b k ∈ A) : L[[A]].Formula (Fin m) :=
  ((L.lhomWithConstants A).onFormula φ).subst
    (Fin.addCases Term.var (fun k => Constants.term (L.con (⟨b k,hb k⟩ : A))))

theorem parameterInstance_realize (A : Set M) (φ : L.Formula (Fin (m+n)))
    (b : Fin n → M) (hb : ∀ k, b k ∈ A) (f : M ↪ₑ[L] N) (a : Fin m → N) :
    @Formula.Realize _ (f.toEmbedding.withConstants A) _ _
        (parameterInstance A φ b hb) a ↔
      φ.Realize (pairAssignment a (f ∘ b)) := by
  let : L[[A]].Structure N := inferInstanceAs (L[[A]].Structure (f.toEmbedding.withConstants A))
  let : (L.lhomWithConstants A).IsExpansionOn N :=
    ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  let tf : Fin (m+n) → L[[A]].Term (Fin m) :=
    Fin.addCases Term.var (fun k => Constants.term (L.con (⟨b k,hb k⟩ : A)))
  change (((L.lhomWithConstants A).onFormula φ).subst tf).Realize a default ↔ _
  simp only [Formula.Realize,BoundedFormula.realize_subst]
  change ((L.lhomWithConstants A).onFormula φ).Realize (fun i => (tf i).realize a) ↔ _
  rw [LHom.realize_onFormula]
  have hv : (fun i => (tf i).realize a) = pairAssignment a (f ∘ b) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [tf,Fin.addCases_left,Term.realize_var,pairAssignment]
    · intro j
      simp only [tf,Fin.addCases_right,Term.realize_constants,pairAssignment,Function.comp_apply]
      rfl
  rw [hv]
  rfl

def parameterSet (b : ℚ → Fin n → M) : Set M :=
  Set.range (fun p : ℚ × Fin n => b p.1 p.2)

theorem parameterSet_countable (b : ℚ → Fin n → M) : (parameterSet b).Countable := by
  exact Set.countable_range _

def rationalTest (φ : L.Formula (Fin (m+n))) (b : ℚ → Fin n → M) (q : ℚ) :
    L[[parameterSet b]].Formula (Fin m) :=
  parameterInstance (parameterSet b) φ (b q) (fun k => ⟨(q,k),rfl⟩)

/-- The real cut selects formulas; no real is added to the model's named parameter set. -/
noncomputable def cutConditions (φ : L.Formula (Fin (m+n)))
    (b : ℚ → Fin n → M) (r : ℝ) : Set (L[[parameterSet b]].Formula (Fin m)) := by
  classical
  exact Set.range fun q : ℚ =>
    if (q : ℝ) ≤ r then (rationalTest φ b q).not else rationalTest φ b q

private theorem finite_rational_separator (S : Finset ℚ) (r : ℝ) :
    ∃ t : ℚ, ∀ q ∈ S, t < q ↔ r < (q : ℝ) := by
  classical
  let U : Finset ℚ := S.filter (fun q : ℚ => r < (q : ℝ))
  by_cases hU : U.Nonempty
  · have hmin := (Finset.mem_filter.mp (Finset.min'_mem U hU)).2
    obtain ⟨t,hrt,htu⟩ := exists_rat_btwn hmin
    refine ⟨t,fun q hq => ?_⟩
    by_cases hqr : r < (q : ℝ)
    · have huq : U.min' hU ≤ q := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hq,hqr⟩)
      have htq : t < q := by exact_mod_cast (htu.trans_le (Rat.cast_le.mpr huq))
      exact iff_of_true htq hqr
    · have hqt : (q : ℝ) < (t : ℝ) := (le_of_not_gt hqr).trans_lt hrt
      have hqt' : q < t := by exact_mod_cast hqt
      exact iff_of_false (not_lt_of_ge hqt'.le) hqr
  · obtain ⟨t,hrt⟩ := exists_rat_gt r
    refine ⟨t,fun q hq => ?_⟩
    have hqr : ¬r < (q : ℝ) := fun h => hU ⟨q,Finset.mem_filter.mpr ⟨hq,h⟩⟩
    have hqt : (q : ℝ) < (t : ℝ) := (le_of_not_gt hqr).trans_lt hrt
    have hqt' : q < t := by exact_mod_cast hqt
    exact iff_of_false (not_lt_of_ge hqt'.le) hqr

theorem cut_finite_indexed_witness (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b)
    (r : ℝ) (Γ : Finset (L[[parameterSet b]].Formula (Fin m)))
    (hΓ : (↑Γ : Set _) ⊆ cutConditions φ b r) :
    ∃ t : ℚ, Types.Realizes (↑Γ : Set (L[[parameterSet b]].Formula (Fin m))) (a t) := by
  classical
  let origin : Γ → ℚ := fun ψ => (hΓ ψ.property).choose
  have hOrigin (ψ : Γ) :
      (if ((origin ψ : ℚ) : ℝ) ≤ r then (rationalTest φ b (origin ψ)).not
       else rationalTest φ b (origin ψ)) = ψ.val :=
    (hΓ ψ.property).choose_spec
  let S := Γ.attach.image origin
  obtain ⟨t,ht⟩ := finite_rational_separator S r
  refine ⟨t,fun ψ hψ => ?_⟩
  let q := origin ⟨ψ,hψ⟩
  have hqS : q ∈ S := Finset.mem_image.mpr ⟨⟨ψ,hψ⟩,Finset.mem_attach _ _,rfl⟩
  have htest : (rationalTest φ b q).Realize (a t) ↔ t < q :=
    (parameterInstance_realize (parameterSet b) φ (b q) (fun k => ⟨(q,k),rfl⟩)
      (ElementaryEmbedding.refl L M) (a t)).trans (h t q)
  have hψeq : (if (q : ℝ) ≤ r then (rationalTest φ b q).not else rationalTest φ b q) = ψ :=
    hOrigin ⟨ψ,hψ⟩
  rw [← hψeq]
  by_cases hqr : ((q : ℚ) : ℝ) ≤ r
  · rw [ite_eq_left hqr,Formula.realize_not,htest]
    exact fun hpos => (not_lt_of_ge hqr) ((ht q hqS).mp hpos)
  · rw [ite_eq_right hqr,htest]
    exact (ht q hqS).mpr (lt_of_not_ge hqr)

theorem cut_finitely_realized (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) (r : ℝ) :
    Types.FinitelyRealized M (cutConditions φ b r) := by
  intro Γ hΓ
  obtain ⟨t,ht⟩ := cut_finite_indexed_witness φ a b h r Γ hΓ
  exact ⟨a t,ht⟩

theorem cut_partial [Nonempty M] (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) (r : ℝ) :
    Types.IsPartial (L[[parameterSet b]].completeTheory M) (cutConditions φ b r) := by
  exact (Types.partial_iff_finitelyRealized_completeTheory _).mpr (cut_finitely_realized φ a b h r)

/-- Choose a completion for each cut, always in this same parameter-type space. -/
noncomputable def cutCompletion [Nonempty M] (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) (r : ℝ) :
    TypesOver (L := L) (parameterSet b) m :=
  (Types.exists_complete_extension (cutConditions φ b r) (cut_partial φ a b h r)).choose

theorem cutCompletion_contains [Nonempty M] (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) (r : ℝ) :
    cutConditions φ b r ⊆ Types.formulas (cutCompletion φ a b h r) := by
  exact (Types.exists_complete_extension _ (cut_partial φ a b h r)).choose_spec

theorem cutCompletion_injective [Nonempty M] (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) :
    Function.Injective (cutCompletion φ a b h) := by
  classical
  have hle (r s : ℝ) (he : cutCompletion φ a b h r = cutCompletion φ a b h s) : s ≤ r := by
    by_contra hn
    obtain ⟨q,hrq,hqs⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have hrmem : rationalTest φ b q ∈ cutConditions φ b r :=
      ⟨q,by simp only [not_le.mpr hrq, ↓reduceIte]⟩
    have hsmem : (rationalTest φ b q).not ∈ cutConditions φ b s :=
      ⟨q,by simp only [le_of_lt hqs, ↓reduceIte]⟩
    have hpos := cutCompletion_contains φ a b h r hrmem
    have hneg := cutCompletion_contains φ a b h s hsmem
    rw [he] at hpos
    have hn := (cutCompletion φ a b h s).not_mem_iff (Formula.equivSentence (rationalTest φ b q))
    exact (hn.mp hneg) hpos
  intro r s he
  exact le_antisymm (hle s r he.symm) (hle r s he)

theorem rational_pattern_many_types [Nonempty M] (φ : L.Formula (Fin (m+n)))
    (a : ℚ → Fin m → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) :
    2 ^ (ℵ₀ : Cardinal.{max u v w}) ≤ #(TypesOver (L := L) (parameterSet b) m) := by
  have hc := Cardinal.lift_mk_le_lift_mk_of_injective (cutCompletion_injective φ a b h)
  simpa only [Cardinal.mk_real,Cardinal.lift_continuum,Cardinal.two_power_aleph0,
    Cardinal.lift_id'] using hc

theorem orderProperty_many_types (T : L.Theory)
    (φ : L.Formula (Fin (m+n))) (h : HasOrderProperty T φ) :
    ∃ P : Theory.ModelType.{u,v,max u v w} T, ∃ A : Set P,
      A.Countable ∧ 2 ^ (ℵ₀ : Cardinal.{max u v w}) ≤ #(TypesOver (L := L) A m) := by
  obtain ⟨P,a,b,hp⟩ := exists_order_pattern T φ h ℚ
  let Q : Theory.ModelType.{u,v,max u v w} T := P.ulift
  let e : P ≃[L] Q := (Equiv.ulift.symm : P ≃ Q).inducedStructureEquiv
  have hQ : OrderPattern φ (fun q => e ∘ a q) (fun q => e ∘ b q) := by
    intro i j
    have hv : pairAssignment (e ∘ a i) (e ∘ b j) = e ∘ pairAssignment (a i) (b j) := by
      funext k
      refine Fin.addCases ?_ ?_ k <;> intro j <;>
        simp only [pairAssignment,Fin.addCases_left,Fin.addCases_right,Function.comp_apply]
    rw [hv,StrongHomClass.realize_formula]
    exact hp i j
  exact ⟨Q,parameterSet (fun q => e ∘ b q),parameterSet_countable _,
    rational_pattern_many_types φ (fun q => e ∘ a q) (fun q => e ∘ b q) hQ⟩

theorem orderProperty_not_countably_stable (T : L.Theory)
    (φ : L.Formula (Fin (1+n))) (h : HasOrderProperty T φ) :
    ¬KappaStable.{u,v,w} T ℵ₀ := by
  intro hs
  obtain ⟨P,A,hA,hbound⟩ := orderProperty_many_types.{u,v,w} T φ h
  have hA' : #A ≤ (ℵ₀ : Cardinal.{max u v w}) := Cardinal.mk_le_aleph0_iff.mpr hA.to_subtype
  have hf := hs.2 P A hA'
  exact (not_le_of_gt (Cardinal.cantor ℵ₀)) (hbound.trans hf)

end Lemmatheca.ModelTheory.OrderPatternsAndStability
