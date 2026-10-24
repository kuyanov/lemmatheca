import Lemmatheca.EhrenfeuchtMostowskiModels.Hulls

/-! Chosen realizing models, actual hulls, and size estimates for one fixed template. -/
namespace Lemmatheca.ModelTheory.EhrenfeuchtMostowski
open FirstOrder FirstOrder.Language Cardinal
universe u v w z w'
variable {K : Language.{u,v}} (T : K.Theory) (p : Template.{u,v,w} T)

/-- A choice for one index order, always for the already fixed template. -/
structure EMRealization (I : Type z) [LinearOrder I] where
  ambient : Theory.ModelType.{u,v,max u v w z} T
  skeleton : I → ambient
  distinct : Function.Injective skeleton
  realizes : RealizesTemplate T p skeleton

def realizedHull {I : Type z} [LinearOrder I] (R : EMRealization T p I) :=
  hull K R.skeleton

theorem exists_realization (I : Type z) [LinearOrder I] [Infinite I] :
    Nonempty (EMRealization T p I) := by
  obtain ⟨N,b,hb,hp⟩ := exists_stretch T p I
  exact ⟨⟨N,b,hb,hp⟩⟩

theorem realizedHull_indiscernible {I : Type z} [LinearOrder I]
    (R : EMRealization T p I) (he : (hull K R.skeleton).IsElementary) :
    IndiscernibleSequences.OrderIndiscernible (L := K)
      (∅ : Set (hull K R.skeleton)) (fun i (_ : Fin 1) => hullGenerator K R.skeleton i) := by
  intro n hn φ s t
  let H := hull K R.skeleton
  let f : H ↪ₑ[K] R.ambient := (⟨H,he⟩ : K.ElementarySubstructure R.ambient).subtype
  let ψ : K.Formula (Fin (n*1)) :=
    (LEquiv.addEmptyConstants K (∅ : Set H)).symm.toLHom.onFormula φ
  have bridge (e : Fin n ↪o I) :
      φ.Realize (IndiscernibleSequences.tupleAssignment (fun i (_ : Fin 1) => hullGenerator K R.skeleton i) e) ↔
      ψ.Realize (IndiscernibleSequences.tupleAssignment (fun i (_ : Fin 1) => R.skeleton i) e) := by
    exact (LHom.realize_onFormula _ φ).symm.trans
      ((f.map_formula ψ _).symm)
  let θ : K[[(∅ : Set R.ambient)]].Formula (Fin (n*1)) :=
    (K.lhomWithConstants (∅ : Set R.ambient)).onFormula ψ
  have h := realizesTemplate_indiscernible T p R.skeleton R.realizes n hn θ s t
  simp only [θ, LHom.realize_onFormula] at h
  exact (bridge s).trans (h.trans (bridge t).symm)

theorem hull_card_lower {I : Type z} [LinearOrder I]
    {N : Type w'} [K.Structure N] (b : I → N) (hb : Function.Injective b) :
    Cardinal.lift.{max u v w'} #I ≤
      Cardinal.lift.{max u v z} #(hull K b) := by
  apply Cardinal.lift_mk_le.mpr
  exact ⟨⟨hullGenerator K b,fun i j h => hb (congrArg Subtype.val h)⟩⟩

theorem hull_card_upper {I : Type z} {N : Type w'} [K.Structure N] (b : I → N) :
    Cardinal.lift.{max u v z} #(hull K b) ≤
      max (Cardinal.lift.{max w' z} K.card)
        (max ℵ₀ (Cardinal.lift.{max u v w'} #I)) := by
  let c : Cardinal.{max u v w' z} :=
    max (Cardinal.lift.{max w' z} K.card)
      (max ℵ₀ (Cardinal.lift.{max u v w'} #I))
  have hc : ℵ₀ ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hs : Cardinal.lift.{max u v z} #(Set.range b) ≤ c := by
    have h := Cardinal.lift_mk_le_lift_mk_of_surjective (Set.rangeFactorization_surjective (f := b))
    have hh := Cardinal.lift_le.{max u v}.mpr h
    have hh' : Cardinal.lift.{max u v z} #(Set.range b) ≤
        Cardinal.lift.{max u v w'} #I := by
      simpa only [Cardinal.lift_lift] using hh
    exact hh'.trans ((le_max_right _ _).trans (le_max_right _ _))
  have hf : Cardinal.lift.{max v w' z} #(Σ n, K.Functions n) ≤ c := by
    have h : Cardinal.lift.{v} #(Σ n, K.Functions n) ≤ K.card :=
      by
        change Cardinal.lift.{v} #(Σ n, K.Functions n) ≤
          #((Σ n, K.Functions n) ⊕ (Σ n, K.Relations n))
        rw [Cardinal.mk_sum]
        exact le_add_right le_rfl
    have hh := Cardinal.lift_le.{max w' z}.mpr h
    have hh' : Cardinal.lift.{max v w' z} #(Σ n, K.Functions n) ≤
        Cardinal.lift.{max w' z} K.card := by
      simpa only [Cardinal.lift_lift] using hh
    exact hh'.trans (le_max_left _ _)
  have h := Cardinal.lift_le.{max v z}.mpr (Substructure.lift_card_closure_le (L := K) (s := Set.range b))
  have h' : Cardinal.lift.{max u v z} #(hull K b) ≤
      max ℵ₀ (Cardinal.lift.{max u v z} #(Set.range b) +
        Cardinal.lift.{max v w' z} #(Σ n, K.Functions n)) := by
    simpa only [hull,Cardinal.lift_lift,Cardinal.lift_max,Cardinal.lift_aleph0,Cardinal.lift_add] using h
  exact h'.trans (max_le hc (Cardinal.add_le_of_le hc hs hf))

variable (L : Language.{u,v}) {M : Type w} [L.Structure M] (m₀ : M)

theorem full_template_zero
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    (φ : (fullySkolemizedLanguage L).Sentence) :
    φ.relabel (Empty.elim : Empty → Fin 0) ∈
        Types.formulas (templateType (expansionTheory L m₀) p 0) ↔
      φ ∈ expansionTheory L m₀ := by
  let := fullExpansion L m₀
  rw [template_zero]
  let : p.source ⊨ (fullySkolemizedLanguage L).completeTheory M := p.source.is_model
  exact realize_iff_of_model_completeTheory M p.source φ

theorem full_realizedHull_elementary
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I] [Nonempty I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    (hull (fullySkolemizedLanguage L) R.skeleton).IsElementary := by
  exact full_hull_elementary L m₀ (Set.range R.skeleton) (Set.range_nonempty _)

/-- The original language keeps the actual hull carrier and forgets added symbols. -/
@[instance_reducible]
def hullReductStructure
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    L.Structure (hull (fullySkolemizedLanguage L) R.skeleton) :=
  (originalInclusion L).reduct _

theorem full_realizedHull_models [Nonempty M] (T : L.Theory) [M ⊨ T]
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I] [Nonempty I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    letI := hullReductStructure L m₀ p R
    (hull (fullySkolemizedLanguage L) R.skeleton) ⊨ T := by
  exact full_hull_models L m₀ T (Set.range R.skeleton) (Set.range_nonempty _)

theorem full_realizedHull_size
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I] [Infinite I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    Cardinal.lift.{max u v w} #I ≤ #(hull (fullySkolemizedLanguage L) R.skeleton) ∧
    #(hull (fullySkolemizedLanguage L) R.skeleton) ≤
      max (Cardinal.lift.{max u v w} #I)
        (max ℵ₀ (Cardinal.lift.{max w z} L.card)) := by
  have hHl : Cardinal.lift.{max u v z} #(hull (fullySkolemizedLanguage L) R.skeleton) =
      #(hull (fullySkolemizedLanguage L) R.skeleton) :=
    Cardinal.lift_id'.{max u v z,w} _
  have hIl : Cardinal.lift.{max u v w z} #I = Cardinal.lift.{max u v w} #I :=
    congrArg (fun f => f #I) Cardinal.lift_umax.{z,max u v w}
  have hKl : Cardinal.lift.{max u v w z} (fullySkolemizedLanguage L).card =
      Cardinal.lift.{max w z} (fullySkolemizedLanguage L).card :=
    congrArg (fun f => f (fullySkolemizedLanguage L).card) Cardinal.lift_umax.{max u v,max w z}
  constructor
  · have h := hull_card_lower (K := fullySkolemizedLanguage L) R.skeleton R.distinct
    rw [hHl,hIl] at h
    exact h
  · have h := hull_card_upper (K := fullySkolemizedLanguage L) R.skeleton
    rw [hHl,hIl,hKl] at h
    apply h.trans
    have hk : Cardinal.lift.{max w z} (fullySkolemizedLanguage L).card ≤
        max ℵ₀ (Cardinal.lift.{max w z} L.card) := by
      simpa only [Cardinal.lift_max,Cardinal.lift_aleph0] using
        Cardinal.lift_le.{max w z}.mpr (full_language_card L)
    exact max_le (hk.trans (le_max_right _ _))
      (max_le ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))

theorem countable_language_exact_size [Countable L.Symbols]
    (p : Template.{max u v,max u v,w} (expansionTheory L m₀))
    {I : Type z} [LinearOrder I] [Infinite I]
    (R : EMRealization (expansionTheory L m₀) p I) :
    #(hull (fullySkolemizedLanguage L) R.skeleton) = Cardinal.lift.{max u v w} #I := by
  apply le_antisymm
  · apply (full_realizedHull_size L m₀ p R).2.trans
    have hl : L.card ≤ ℵ₀ := Cardinal.mk_le_aleph0
    have hl' : Cardinal.lift.{max w z} L.card ≤ ℵ₀ := by
      simpa only [Cardinal.lift_aleph0] using Cardinal.lift_le.{max w z}.mpr hl
    have hi : ℵ₀ ≤ Cardinal.lift.{max u v w} #I := by
      simpa only [Cardinal.lift_aleph0] using
        Cardinal.lift_le.{max u v w}.mpr (Cardinal.aleph0_le_mk I)
    exact max_le le_rfl (max_le hi (hl'.trans hi))
  · exact (full_realizedHull_size L m₀ p R).1

/-- The template is quantified before every choice of the target linear order. -/
theorem em_existence [Infinite M] (T : L.Theory) [M ⊨ T] :
    ∃ p : Template.{max u v,max u v,w} (expansionTheory L m₀),
      ∀ (I : Type z) (_ : LinearOrder I) (_ : Infinite I),
        ∃ R : EMRealization (expansionTheory L m₀) p I,
          letI := hullReductStructure L m₀ p R
          (hull (fullySkolemizedLanguage L) R.skeleton) ⊨ T ∧
          Cardinal.lift.{max u v w} #I ≤ #(hull (fullySkolemizedLanguage L) R.skeleton) ∧
          #(hull (fullySkolemizedLanguage L) R.skeleton) ≤
            max (Cardinal.lift.{max u v w} #I)
              (max ℵ₀ (Cardinal.lift.{max w z} L.card)) := by
  let := fullExpansion L m₀
  let : M ⊨ expansionTheory L m₀ := inferInstanceAs
    (M ⊨ (fullySkolemizedLanguage L).completeTheory M)
  obtain ⟨p⟩ := exists_template (expansionTheory L m₀) (M := M)
  refine ⟨p,fun I _ _ => ?_⟩
  obtain ⟨R⟩ := exists_realization (expansionTheory L m₀) p I
  exact ⟨R,full_realizedHull_models L m₀ T p R,full_realizedHull_size L m₀ p R⟩

end Lemmatheca.ModelTheory.EhrenfeuchtMostowski
