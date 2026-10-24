import Lemmatheca.IndiscernibleSequences.Construction
import Lemmatheca.Skolemization.Skolemization
import Lemmatheca.ElementarySubmodels.GeneratedCarriers
import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Mathlib.ModelTheory.Skolem

/-! An actual countable iteration of witness languages and its union expansion. -/
namespace Lemmatheca.ModelTheory.EhrenfeuchtMostowski
open FirstOrder FirstOrder.Language Cardinal
universe u v w
variable (L : Language.{u,v})

/-- Put both sorts of symbols in one universe before the recursive construction. -/
def normalizedLanguage : Language.{max u v,max u v} where
  Functions n := ULift.{v} (L.Functions n)
  Relations n := ULift.{u} (L.Relations n)

def normalizationMap : L →ᴸ normalizedLanguage L where
  onFunction := fun {_} => ULift.up
  onRelation := fun {_} => ULift.up

@[instance_reducible]
def normalizedStructure {M : Type w} [L.Structure M] :
    (normalizedLanguage L).Structure M where
  funMap f xs := Structure.funMap f.down xs
  RelMap R xs := Structure.RelMap R.down xs

section Iteration
variable (K : Language.{u,u})

/-- A stage adds functions for every formula in the preceding stage. -/
def stageLanguage : ℕ → Language.{u,u}
  | 0 => K
  | n + 1 => (stageLanguage n).sum (stageLanguage n).skolem₁

/-- A union symbol remembers the stage at which its witness function was added. -/
def unionLanguage : Language.{u,u} where
  Functions r := K.Functions r ⊕ (Σ n, (stageLanguage K n).BoundedFormula Empty (r + 1))
  Relations := K.Relations

def stageFunction : (n : ℕ) → {r : ℕ} →
    (stageLanguage K n).Functions r → (unionLanguage K).Functions r
  | 0, _, f => .inl f
  | n + 1, _, .inl f => stageFunction n f
  | n + 1, _, .inr φ => .inr ⟨n, φ⟩

def stageRelation : (n : ℕ) → {r : ℕ} →
    (stageLanguage K n).Relations r → K.Relations r
  | 0, _, R => R
  | n + 1, _, .inl R => stageRelation n R
  | _ + 1, _, .inr e => e.elim

def stageInclusion (n : ℕ) : stageLanguage K n →ᴸ unionLanguage K where
  onFunction := fun {_} => stageFunction K n
  onRelation := fun {_} => stageRelation K n

@[instance_reducible]
noncomputable def nextWitnessStructure {M : Type w} [K.Structure M] (m₀ : M) :
    K.skolem₁.Structure M where
  funMap φ xs := ElementarySubmodels.selectedWitness (L := K) m₀ φ xs
  RelMap e _ := e.elim

@[instance_reducible]
noncomputable def stageStructure {M : Type w} [K.Structure M] (m₀ : M) :
    (n : ℕ) → (stageLanguage K n).Structure M
  | 0 => by change K.Structure M; infer_instance
  | n + 1 => by
      letI := stageStructure m₀ n
      letI := nextWitnessStructure (stageLanguage K n) m₀
      change ((stageLanguage K n).sum (stageLanguage K n).skolem₁).Structure M
      exact Language.sumStructure (stageLanguage K n) (stageLanguage K n).skolem₁ M

@[instance_reducible]
noncomputable def unionStructure {M : Type w} [K.Structure M] (m₀ : M) :
    (unionLanguage K).Structure M where
  funMap f xs := match f with
    | .inl g => @Structure.funMap K M _ _ g xs
    | .inr ⟨n, φ⟩ =>
        @ElementarySubmodels.selectedWitness (stageLanguage K n) M (stageStructure K m₀ n) m₀ _ φ xs
  RelMap R xs := @Structure.RelMap K M _ _ R xs

private theorem stageFunction_tag_lt (n : ℕ) {r : ℕ}
    (f : (stageLanguage K n).Functions r) (k : ℕ)
    (φ : (stageLanguage K k).BoundedFormula Empty (r+1))
    (h : stageFunction K n f = Sum.inr ⟨k,φ⟩) : k < n := by
  induction n with
  | zero => cases h
  | succ n ih =>
    cases f with
    | inl f => exact (ih f h).trans (Nat.lt_succ_self _)
    | inr ψ =>
      have hk : n = k := congrArg Sigma.fst (Sum.inr.inj h)
      subst k
      exact Nat.lt_succ_self _

private theorem stage_fun_compatible {M : Type w} [K.Structure M]
    (m₀ : M) (n : ℕ) {r : ℕ} (f : (stageLanguage K n).Functions r) (xs : Fin r → M) :
    @Structure.funMap (unionLanguage K) M (unionStructure K m₀) r (stageFunction K n f) xs =
      @Structure.funMap (stageLanguage K n) M (stageStructure K m₀ n) r f xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases f with
    | inl f => exact ih f
    | inr φ => rfl

private theorem stage_rel_compatible {M : Type w} [K.Structure M]
    (m₀ : M) (n : ℕ) {r : ℕ} (R : (stageLanguage K n).Relations r) (xs : Fin r → M) :
    @Structure.RelMap (unionLanguage K) M (unionStructure K m₀) r (stageRelation K n R) xs =
      @Structure.RelMap (stageLanguage K n) M (stageStructure K m₀ n) r R xs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases R with
    | inl R => exact ih R
    | inr e => exact Empty.elim e

private def stageAdvance (n : ℕ) : (k : ℕ) → stageLanguage K n →ᴸ stageLanguage K (n+k)
  | 0 => LHom.id _
  | k+1 => LHom.sumInl.comp (stageAdvance n k)

private theorem stageAdvance_union (n k : ℕ) :
    (stageInclusion K (n+k)).comp (stageAdvance K n k) = stageInclusion K n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((stageInclusion K (n+k+1)).comp LHom.sumInl).comp
      (stageAdvance K n k) = stageInclusion K n
    have he : (stageInclusion K (n+k+1)).comp LHom.sumInl = stageInclusion K (n+k) := rfl
    rw [he]
    exact ih

private theorem function_at_stage {r : ℕ} (f : (unionLanguage K).Functions r) :
    ∃ n, ∀ N, n ≤ N → ∃ g : (stageLanguage K N).Functions r,
      (stageInclusion K N).onFunction g = f := by
  classical
  have hf : ∃ n, ∃ g : (stageLanguage K n).Functions r, (stageInclusion K n).onFunction g = f := by
    cases f with
    | inl f => exact ⟨0,f,rfl⟩
    | inr f =>
      rcases f with ⟨n,φ⟩
      exact ⟨n+1,Sum.inr φ,rfl⟩
  obtain ⟨n,g,hg⟩ := hf
  refine ⟨n,?_⟩
  intro N hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨(stageAdvance K n k).onFunction g,?_⟩
  change ((stageInclusion K (n+k)).comp (stageAdvance K n k)).onFunction g = f
  rw [stageAdvance_union]
  exact hg

private theorem relation_at_stage {r : ℕ} (R : (unionLanguage K).Relations r) (N : ℕ) :
    ∃ S : (stageLanguage K N).Relations r, (stageInclusion K N).onRelation S = R := by
  induction N with
  | zero => exact ⟨R,rfl⟩
  | succ N ih =>
    obtain ⟨S,hS⟩ := ih
    exact ⟨Sum.inl S,hS⟩

private theorem term_at_stage {α : Type w} (t : (unionLanguage K).Term α) :
    ∃ n, ∀ N, n ≤ N → ∃ s : (stageLanguage K N).Term α,
      (stageInclusion K N).onTerm s = t := by
  classical
  induction t with
  | var a =>
    exact ⟨0,fun N _ => ⟨.var a,rfl⟩⟩
  | @func r f ts ih =>
    choose ns hs using ih
    obtain ⟨nf,hf⟩ := function_at_stage K f
    refine ⟨max nf (Finset.univ.sup ns),?_⟩
    intro N hN
    obtain ⟨g,hg⟩ := hf N ((le_max_left _ _).trans hN)
    have hge (i : Fin r) : ns i ≤ N :=
      (Finset.le_sup (f := ns) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hN)
    choose ys hys using fun i => hs i N (hge i)
    refine ⟨.func g ys,?_⟩
    change Term.func ((stageInclusion K N).onFunction g)
      (fun i => (stageInclusion K N).onTerm (ys i)) = Term.func f ts
    rw [hg]
    congr 1
    funext i
    exact hys i

private theorem bounded_at_stage {α : Type w} {r : ℕ}
    (φ : (unionLanguage K).BoundedFormula α r) :
    ∃ n, ∀ N, n ≤ N → ∃ ψ : (stageLanguage K N).BoundedFormula α r,
      (stageInclusion K N).onBoundedFormula ψ = φ := by
  classical
  induction φ with
  | falsum => exact ⟨0,fun _ _ => ⟨.falsum,rfl⟩⟩
  | equal t s =>
    obtain ⟨nt,ht⟩ := term_at_stage K t
    obtain ⟨ns,hs⟩ := term_at_stage K s
    refine ⟨max nt ns,?_⟩
    intro N hN
    obtain ⟨t',ht'⟩ := ht N ((le_max_left _ _).trans hN)
    obtain ⟨s',hs'⟩ := hs N ((le_max_right _ _).trans hN)
    exact ⟨.equal t' s',by simp only [LHom.onBoundedFormula,Term.bdEqual,ht',hs']⟩
  | @rel r l R ts =>
    choose ns hs using fun i => term_at_stage K (ts i)
    refine ⟨Finset.univ.sup ns,?_⟩
    intro N hN
    obtain ⟨R',hR⟩ := relation_at_stage K R N
    have hge (i : Fin l) : ns i ≤ N :=
      (Finset.le_sup (f := ns) (Finset.mem_univ i)).trans hN
    choose ys hys using fun i => hs i N (hge i)
    refine ⟨.rel R' ys,?_⟩
    change BoundedFormula.rel ((stageInclusion K N).onRelation R')
      (fun i => (stageInclusion K N).onTerm (ys i)) = BoundedFormula.rel R ts
    rw [hR]
    congr 1
    funext i
    exact hys i
  | imp φ ψ ihφ ihψ =>
    obtain ⟨nφ,hφ⟩ := ihφ
    obtain ⟨nψ,hψ⟩ := ihψ
    refine ⟨max nφ nψ,?_⟩
    intro N hN
    obtain ⟨φ',hφ'⟩ := hφ N ((le_max_left _ _).trans hN)
    obtain ⟨ψ',hψ'⟩ := hψ N ((le_max_right _ _).trans hN)
    exact ⟨φ'.imp ψ',by simp only [LHom.onBoundedFormula,hφ',hψ']⟩
  | all φ ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n,?_⟩
    intro N hN
    obtain ⟨ψ,hψ⟩ := hn N hN
    exact ⟨ψ.all,by simp only [LHom.onBoundedFormula,hψ]⟩

theorem stageInclusion_injective (n : ℕ) : (stageInclusion K n).Injective := by
  constructor
  · intro r f g h
    change stageFunction K n f = stageFunction K n g at h
    induction n with
    | zero => exact Sum.inl.inj h
    | succ n ih =>
      cases f with
      | inl f =>
        cases g with
        | inl g => exact congrArg Sum.inl (ih h)
        | inr ψ =>
          exact False.elim ((Nat.lt_irrefl n) (stageFunction_tag_lt K n f n ψ h))
      | inr φ =>
        cases g with
        | inl g =>
          exact False.elim ((Nat.lt_irrefl n) (stageFunction_tag_lt K n g n φ h.symm))
        | inr ψ =>
          have hp : φ = ψ := eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
          exact congrArg Sum.inr hp
  · intro r R S h
    change stageRelation K n R = stageRelation K n S at h
    induction n with
    | zero => exact h
    | succ n ih =>
      cases R with
      | inl R =>
        cases S with
        | inl S => exact congrArg Sum.inl (ih h)
        | inr e => exact Empty.elim e
      | inr e => exact Empty.elim e

theorem stageStructure_compatible {M : Type w} [K.Structure M] (m₀ : M) (n : ℕ) :
    letI := stageStructure K m₀ n
    letI := unionStructure K m₀
    (stageInclusion K n).IsExpansionOn M := by
  let : (stageLanguage K n).Structure M := stageStructure K m₀ n
  let : (unionLanguage K).Structure M := unionStructure K m₀
  change (stageInclusion K n).IsExpansionOn M
  constructor
  · intro r f xs
    exact stage_fun_compatible K m₀ n f xs
  · intro r R xs
    exact stage_rel_compatible K m₀ n R xs

/-- Every native formula in the union comes from one actual finite stage. -/
theorem formula_at_finite_stage {α : Type w} {r : ℕ}
    (φ : (unionLanguage K).BoundedFormula α r) :
    ∃ n, ∃ ψ : (stageLanguage K n).BoundedFormula α r,
      (stageInclusion K n).onBoundedFormula ψ = φ := by
  obtain ⟨n,hn⟩ := bounded_at_stage K φ
  obtain ⟨ψ,hψ⟩ := hn n le_rfl
  exact ⟨n,ψ,hψ⟩

/-- Choose the stage presentation, not a new unrelated formula or interpretation. -/
noncomputable def witnessPresentation {r : ℕ}
    (φ : (unionLanguage K).BoundedFormula Empty (r + 1)) :
    Σ n, {ψ : (stageLanguage K n).BoundedFormula Empty (r + 1) //
      (stageInclusion K n).onBoundedFormula ψ = φ} :=
  let n := (formula_at_finite_stage K φ).choose
  ⟨n, ⟨(formula_at_finite_stage K φ).choose_spec.choose,
    (formula_at_finite_stage K φ).choose_spec.choose_spec⟩⟩

noncomputable def witnessSymbol {r : ℕ}
    (φ : (unionLanguage K).BoundedFormula Empty (r + 1)) : (unionLanguage K).Functions r :=
  .inr ⟨(witnessPresentation K φ).1, (witnessPresentation K φ).2.val⟩

/-- The actual sentence universally closes the original formula's witness implication. -/
noncomputable def witnessAxiom {r : ℕ}
    (φ : (unionLanguage K).BoundedFormula Empty (r + 1)) :
    (unionLanguage K).Sentence :=
  let ts : Fin r → (unionLanguage K).Term (Empty ⊕ Fin r) := fun i => .var (.inr i)
  let t := Term.func (witnessSymbol K φ) ts
  (φ.ex.imp (Lemmatheca.MathematicalLogic.Skolemization.Prenex.fill φ (Fin.snoc ts t))).alls

theorem witnessAxiom_realize {N : Type w} [(unionLanguage K).Structure N]
    {r : ℕ} (φ : (unionLanguage K).BoundedFormula Empty (r + 1)) :
    N ⊨ witnessAxiom K φ ↔ ∀ xs : Fin r → N,
      (∃ y, φ.Realize Empty.elim (Fin.snoc xs y)) →
        φ.Realize Empty.elim (Fin.snoc xs (Structure.funMap (witnessSymbol K φ) xs)) := by
  rw [witnessAxiom, Sentence.Realize, BoundedFormula.realize_alls]
  have he : (default : Empty → N) = Empty.elim := Subsingleton.elim _ _
  rw [he]
  apply forall_congr'
  intro xs
  rw [BoundedFormula.realize_imp,BoundedFormula.realize_ex,
    Lemmatheca.MathematicalLogic.Skolemization.Prenex.fill_realize]
  let ts : Fin r → (unionLanguage K).Term (Empty ⊕ Fin r) := fun i => .var (.inr i)
  let t : (unionLanguage K).Term (Empty ⊕ Fin r) := .func (witnessSymbol K φ) ts
  have ha : (fun i : Fin (r+1) =>
      Term.realize (Sum.elim Empty.elim xs) ((Fin.snoc ts t : Fin (r+1) → (unionLanguage K).Term (Empty ⊕ Fin r)) i)) =
      Fin.snoc xs (Structure.funMap (witnessSymbol K φ) xs) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [ts, t, Term.realize]
  rw [ha]

theorem union_witness_axioms {M : Type w} [K.Structure M] (m₀ : M)
    {r : ℕ} (φ : (unionLanguage K).BoundedFormula Empty (r + 1)) :
    letI := unionStructure K m₀
    M ⊨ witnessAxiom K φ := by
  let : (unionLanguage K).Structure M := unionStructure K m₀
  change M ⊨ witnessAxiom K φ
  apply (witnessAxiom_realize K φ).mpr
  intro xs hx
  let p := witnessPresentation K φ
  let : (stageLanguage K p.1).Structure M := stageStructure K m₀ p.1
  let : (stageInclusion K p.1).IsExpansionOn M := stageStructure_compatible K m₀ p.1
  have he (ys : Fin (r+1) → M) :
      φ.Realize Empty.elim ys ↔ p.2.val.Realize Empty.elim ys := by
    have h := (stageInclusion K p.1).realize_onBoundedFormula (M := M) p.2.val (v := Empty.elim) (xs := ys)
    simpa only [p.2.property] using h
  have he0 : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  have hex : ∃ y, p.2.val.Realize default (Fin.snoc xs y) := by
    simpa only [he0] using (hx.imp fun y hy => (he _).mp hy)
  have hw := ElementarySubmodels.selectedWitness_spec m₀ p.2.val xs hex
  apply (he _).mpr
  change p.2.val.Realize Empty.elim (Fin.snoc xs (ElementarySubmodels.selectedWitness m₀ p.2.val xs))
  simpa only [he0] using hw

private theorem closed_formula_count (A : Language.{u,u}) :
    #(Σ r, A.BoundedFormula Empty r) ≤ max ℵ₀ A.card := by
  simpa only [Cardinal.mk_empty,Cardinal.lift_zero,zero_add,Cardinal.lift_uzero,
    Cardinal.lift_id] using (BoundedFormula.card_le (L := A) (α := Empty))

private theorem successor_formula_count (A : Language.{u,u}) :
    #(Σ r, A.BoundedFormula Empty (r+1)) ≤ max ℵ₀ A.card := by
  refine (Cardinal.mk_le_of_injective
    (f := Sigma.map Nat.succ (fun _ => id))
    (Nat.succ_injective.sigma_map (fun _ => Function.injective_id))).trans (closed_formula_count A)

private theorem witness_language_count (A : Language.{u,u}) :
    A.skolem₁.card ≤ max ℵ₀ A.card := by
  have he : A.skolem₁.card = #(Σ r, A.BoundedFormula Empty (r+1)) := by
    simp only [Language.card,Language.Symbols,skolem₁,Cardinal.mk_sum,
      Cardinal.lift_id,Cardinal.mk_sigma,Cardinal.mk_empty,Cardinal.sum_const,
      Cardinal.lift_zero,Cardinal.lift_uzero,mul_zero,add_zero]
  rw [he]
  exact successor_formula_count A

private theorem stage_language_count (n : ℕ) :
    (stageLanguage K n).card ≤ max ℵ₀ K.card := by
  induction n with
  | zero => exact le_max_right _ _
  | succ n ih =>
    change ((stageLanguage K n).sum (stageLanguage K n).skolem₁).card ≤ _
    rw [Language.card_sum]
    simp only [Cardinal.lift_id]
    apply Cardinal.add_le_of_le (le_max_left _ _) ih
    exact (witness_language_count _).trans (max_le (le_max_left _ _) ih)

private def unionSymbolCode : (unionLanguage K).Symbols →
    K.Symbols ⊕ (Σ n, Σ r, (stageLanguage K n).BoundedFormula Empty (r+1))
  | .inl ⟨r,.inl f⟩ => .inl (.inl ⟨r,f⟩)
  | .inl ⟨r,.inr ⟨n,φ⟩⟩ => .inr ⟨n,r,φ⟩
  | .inr ⟨r,R⟩ => .inl (.inr ⟨r,R⟩)

private theorem unionSymbolCode_injective : Function.Injective (unionSymbolCode K) := by
  rintro (⟨r,f | ⟨n,φ⟩⟩ | ⟨r,R⟩) (⟨s,g | ⟨m,ψ⟩⟩ | ⟨s,S⟩) h <;>
    simp only [unionSymbolCode,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at h
  all_goals cases h; rfl


theorem union_language_card :
    (unionLanguage K).card ≤ max ℵ₀ K.card := by
  let κ := max ℵ₀ K.card
  have hκ : ℵ₀ ≤ κ := le_max_left _ _
  have hforms : #(Σ n, Σ r, (stageLanguage K n).BoundedFormula Empty (r+1)) ≤ κ := by
    rw [Cardinal.mk_sigma]
    have h := Cardinal.sum_le_sum
      (fun n => #(Σ r, (stageLanguage K n).BoundedFormula Empty (r+1))) (fun _ : ℕ => κ)
      (fun n => (successor_formula_count _).trans (max_le hκ (stage_language_count K n)))
    simpa only [Cardinal.sum_const,Cardinal.mk_nat,Cardinal.lift_aleph0,
      Cardinal.lift_id,Cardinal.lift_uzero,Cardinal.aleph0_mul_eq hκ] using h
  have h := Cardinal.mk_le_of_injective (unionSymbolCode_injective K)
  change (unionLanguage K).card ≤ κ
  exact h.trans (by
    rw [Cardinal.mk_sum]
    simp only [Cardinal.lift_id]
    exact Cardinal.add_le_of_le hκ (le_max_right _ _) hforms)

theorem union_formula_card :
    #(Σ n, (unionLanguage K).BoundedFormula Empty n) ≤ max ℵ₀ K.card := by
  exact (closed_formula_count _).trans
    (max_le (le_max_left _ _) (union_language_card K))

end Iteration

abbrev fullySkolemizedLanguage := unionLanguage (normalizedLanguage L)

def originalInclusion : L →ᴸ fullySkolemizedLanguage L :=
  (stageInclusion (normalizedLanguage L) 0).comp (normalizationMap L)

@[instance_reducible]
noncomputable def fullExpansion {M : Type w} [L.Structure M] (m₀ : M) :
    (fullySkolemizedLanguage L).Structure M :=
  @unionStructure (normalizedLanguage L) M (normalizedStructure L) m₀

theorem fullExpansion_compatible {M : Type w} [L.Structure M] (m₀ : M) :
    letI := fullExpansion L m₀
    (originalInclusion L).IsExpansionOn M := by
  let : (fullySkolemizedLanguage L).Structure M := fullExpansion L m₀
  change (originalInclusion L).IsExpansionOn M
  constructor
  · intro r f xs
    rfl
  · intro r R xs
    rfl

/-- This is the complete theory of the chosen compatible expansion on the old carrier. -/
noncomputable def expansionTheory {M : Type w} [L.Structure M] (m₀ : M) :
    (fullySkolemizedLanguage L).Theory :=
  letI := fullExpansion L m₀
  (fullySkolemizedLanguage L).completeTheory M

theorem expansionTheory_contains {M : Type w} [L.Structure M] [Nonempty M]
    (m₀ : M) (T : L.Theory) [M ⊨ T] :
    (originalInclusion L).onTheory T ⊆ expansionTheory L m₀ := by
  let : (fullySkolemizedLanguage L).Structure M := fullExpansion L m₀
  let : (originalInclusion L).IsExpansionOn M := fullExpansion_compatible L m₀
  rintro σ ⟨τ,hτ,rfl⟩
  exact (LHom.realize_onSentence M (originalInclusion L) τ).mpr (Theory.realize_sentence_of_mem T hτ)

theorem witness_mem_expansionTheory {M : Type w} [L.Structure M] (m₀ : M)
    {r : ℕ} (φ : (fullySkolemizedLanguage L).BoundedFormula Empty (r + 1)) :
    witnessAxiom (normalizedLanguage L) φ ∈ expansionTheory L m₀ := by
  exact @union_witness_axioms (normalizedLanguage L) M (normalizedStructure L) m₀ r φ

private theorem normalized_language_card : (normalizedLanguage L).card = L.card := by
  simp only [Language.card,Language.Symbols,normalizedLanguage,Cardinal.mk_sum,
    Cardinal.mk_sigma,Cardinal.lift_sum,Cardinal.mk_uLift,Cardinal.lift_lift]
  rw [Cardinal.lift_umax.{u,v},Cardinal.lift_umax.{v,u}]


theorem full_language_card :
    (fullySkolemizedLanguage L).card ≤ max ℵ₀ L.card := by
  have h := union_language_card (normalizedLanguage L)
  simpa only [fullySkolemizedLanguage,normalized_language_card] using h

theorem full_formula_card :
    #(Σ n, (fullySkolemizedLanguage L).BoundedFormula Empty n) ≤ max ℵ₀ L.card := by
  have h := union_formula_card (normalizedLanguage L)
  simpa only [fullySkolemizedLanguage,normalized_language_card] using h

theorem originalInclusion_injective : (originalInclusion L).Injective := by
  constructor
  · intro r f g h
    exact ULift.up_injective (Sum.inl.inj h)
  · intro r R S h
    exact ULift.up_injective h

end Lemmatheca.ModelTheory.EhrenfeuchtMostowski
