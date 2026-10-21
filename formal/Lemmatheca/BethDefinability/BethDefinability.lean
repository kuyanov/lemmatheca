import Lemmatheca.CraigInterpolation.Formula
import Lemmatheca.DefinitionalExtensions.DefinitionalExtensions

/-! Beth definability for one added relation, including arity zero, in the
actual shared scoped syntax and native first-order proof calculus. -/
namespace Lemmatheca.MathematicalLogic.BethDefinability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.ChangingLanguages
open Lemmatheca.MathematicalLogic.DefinitionalExtensions
universe u v w z z'
variable {L : Language.{u,v}} {n : ℕ} {α : Type z} {β : Type z'}
noncomputable section
local instance {β : Type*} : DecidableEq β := Classical.decEq _

/-- Exactly one fresh relation, at the prescribed arity. -/
inductive AddedRelation (n : ℕ) : ℕ → Type
  | fresh : AddedRelation n n

/-- The old function symbols are unchanged; a disjoint tag adds the relation. -/
def extended (L : Language.{u,v}) (n : ℕ) : Language.{u,v} where
  Functions := L.Functions
  Relations m := L.Relations m ⊕ AddedRelation n m

/-- Two distinct copies of the fresh relation, indexed by false and true. -/
def doubled (L : Language.{u,v}) (n : ℕ) : Language.{u,v} where
  Functions := L.Functions
  Relations m := L.Relations m ⊕ (AddedRelation n m × Bool)

def oldInclusion : L →ᴸ extended L n where
  onFunction := fun {_} => id
  onRelation := fun {_} => Sum.inl

def side (b : Bool) : extended L n →ᴸ doubled L n where
  onFunction := fun {_} => id
  onRelation := fun {_} => Sum.elim Sum.inl (fun r => Sum.inr (r,b))

def doubleOld : L →ᴸ doubled L n where
  onFunction := fun {_} => id
  onRelation := fun {_} => Sum.inl

/-- Every subset of the tuple space gives a genuine expansion on this domain. -/
@[instance_reducible] def expansion {M : Type w} [L.Structure M] (r : (Fin n → M) → Prop) :
    (extended L n).Structure M where
  funMap := @Structure.funMap L M _
  RelMap := fun R => match R with
    | .inl R => @Structure.RelMap L M _ _ R
    | .inr .fresh => r

/-- The two new interpretations are independent on the same old structure. -/
@[instance_reducible] def doubleExpansion {M : Type w} [L.Structure M]
    (r s : (Fin n → M) → Prop) : (doubled L n).Structure M where
  funMap := @Structure.funMap L M _
  RelMap := fun R => match R with
    | .inl R => @Structure.RelMap L M _ _ R
    | .inr (.fresh,b) => if b then s else r

instance expansion_isExpansion {M : Type w} [L.Structure M]
    (r : (Fin n → M) → Prop) :
    @LHom.IsExpansionOn L (extended L n) oldInclusion M inferInstance (expansion r) := by
  let := expansion (L := L) r
  exact { map_onFunction := fun _ _ => rfl, map_onRelation := fun _ _ => rfl }

instance doubleExpansion_isExpansion {M : Type w} [L.Structure M]
    (r s : (Fin n → M) → Prop) :
    @LHom.IsExpansionOn L (doubled L n) doubleOld M inferInstance (doubleExpansion r s) := by
  let := doubleExpansion (L := L) r s
  exact { map_onFunction := fun _ _ => rfl, map_onRelation := fun _ _ => rfl }

/-- The added relation applied to its entire permitted free context. -/
def relationAtom : (extended L n).Formula (Fin n) :=
  Relations.formula (.inr .fresh) Term.var

def sideAtom (b : Bool) : (doubled L n).Formula (Fin n) :=
  (side (L := L) (n := n) b).onFormula relationAtom

/-- The uniform explicit-definition sentence. -/
def definingAxiom (ρ : L.Formula (Fin n)) : (extended L n).Sentence :=
  close (relationAtom.iff (oldInclusion.onFormula ρ))

def DefinedBy (T : (extended L n).Theory) (ρ : L.Formula (Fin n)) : Prop :=
  T ⊨ᵇ definingAxiom ρ

def Explicit (T : (extended L n).Theory) : Prop :=
  ∃ ρ : L.Formula (Fin n), DefinedBy T ρ

/-- At most one interpretation on each identical old structure, not existence. -/
def Implicit (T : (extended L n).Theory) : Prop :=
  ∀ (M : Type (max u v)) [L.Structure M] [Nonempty M]
    (r s : (Fin n → M) → Prop),
    (letI := expansion (L := L) r; M ⊨ T) → (letI := expansion (L := L) s; M ⊨ T) → r = s

/-- Agreement of the two actually distinct fresh relation interpretations. -/
def agreement : (doubled L n).Sentence := close ((sideAtom false).iff (sideAtom true))

/-- Recover the original structure, not just an isomorphic one, by expansion. -/
theorem expansion_recovers {M : Type w} (S : (extended L n).Structure M) :
    letI := S
    letI : L.Structure M := (oldInclusion (L := L) (n := n)).reduct M
    expansion (L := L) (fun a => @Structure.RelMap (extended L n) M S n (.inr .fresh) a) = S := by
  ext k R x
  · rfl
  · cases R with
    | inl R => rfl
    | inr R => cases R; rfl

theorem realize_definingAxiom {M : Type w} [L.Structure M]
    [(extended L n).Structure M] [(oldInclusion (L := L) (n := n)).IsExpansionOn M]
    (ρ : L.Formula (Fin n)) :
    M ⊨ definingAxiom ρ ↔ ∀ a : Fin n → M,
      (relationAtom (L := L) (n := n)).Realize a ↔ ρ.Realize a := by
  rw [definingAxiom, realize_close]
  simp only [Formula.realize_iff, LHom.realize_onFormula]

theorem explicit_implies_implicit {T : (extended L n).Theory}
    (h : Explicit T) : Implicit T := by
  obtain ⟨ρ, hρ⟩ := h
  intro M _ _ r s hr hs
  have hreal (t : (Fin n → M) → Prop) (ht : letI := expansion (L := L) t; M ⊨ T) :
      ∀ a, t a ↔ ρ.Realize a := by
    let := expansion (L := L) t
    let : M ⊨ T := ht
    have hD := (realize_definingAxiom ρ).mp (hρ.realize_sentence M)
    exact hD
  funext a
  exact propext ((hreal r hr a).trans (hreal s hs a).symm)

/-- The two reducts are exactly the two independently selected expansions. -/
theorem double_models_iff {M : Type w} [L.Structure M]
    (r s : (Fin n → M) → Prop) (T : (extended L n).Theory) :
    (letI := doubleExpansion (L := L) r s;
      M ⊨ (side (L := L) (n := n) false).onTheory T ∪ (side (L := L) (n := n) true).onTheory T) ↔
    (letI := expansion (L := L) r; M ⊨ T) ∧ (letI := expansion (L := L) s; M ⊨ T) := by
  let := doubleExpansion (L := L) r s
  have hside (b : Bool) :
      M ⊨ (side (L := L) (n := n) b).onTheory T ↔
        (letI := expansion (L := L) (if b then s else r); M ⊨ T) := by
    let := expansion (L := L) (if b then s else r)
    have : (side (L := L) (n := n) b).IsExpansionOn M := by
      constructor
      · intro k f x
        rfl
      · intro k R x
        cases R with
        | inl R => rfl
        | inr R => cases R; rfl
    exact LHom.onTheory_model _ _
  rw [Theory.model_union_iff, hside false, hside true]

theorem implicit_iff_two_copies (T : (extended L n).Theory) :
    Implicit T ↔ ((side (L := L) (n := n) false).onTheory T ∪ (side (L := L) (n := n) true).onTheory T) ⊨ᵇ agreement := by
  constructor
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    let : L.Structure M := (doubleOld (L := L) (n := n)).reduct M
    let r (b : Bool) (a : Fin n → M) :=
      @Structure.RelMap (doubled L n) M _ n (.inr (.fresh,b)) a
    have hside (b : Bool) : letI := expansion (L := L) (r b); M ⊨ T := by
      let := expansion (L := L) (r b)
      have : (side (L := L) (n := n) b).IsExpansionOn M := by
        constructor
        · intro k f x
          rfl
        · intro k R x
          cases R with
          | inl R => rfl
          | inr R => cases R; rfl
      apply (LHom.onTheory_model (side (L := L) (n := n) b) T).mp
      apply M.is_model.mono
      cases b
      · exact Set.subset_union_left
      · exact Set.subset_union_right
    have he := h M (r false) (r true) (hside false) (hside true)
    rw [agreement, realize_close]
    intro a
    rw [Formula.realize_iff]
    change r false a ↔ r true a
    rw [he]
  · intro h M _ _ r s hr hs
    let := doubleExpansion (L := L) r s
    let : M ⊨ (side (L := L) (n := n) false).onTheory T ∪
        (side (L := L) (n := n) true).onTheory T :=
      (double_models_iff r s T).mpr ⟨hr,hs⟩
    have he := (realize_close _).mp (h.realize_sentence M)
    funext a
    apply propext
    have ha := he a
    rw [Formula.realize_iff] at ha
    exact ha

/-- The actual finite conjunction of translated sentences, with no free names. -/
def finiteConj (b : Bool) (Γ : Finset (extended L n).Sentence) :
    (doubled L n).Formula (Fin n) :=
  Formula.iInf (fun A : Γ => ((side (L := L) (n := n) b).onSentence A.val).relabel Empty.elim)

theorem realize_finiteConj {M : Type w} [(doubled L n).Structure M]
    (b : Bool) (Γ : Finset (extended L n).Sentence) (a : Fin n → M) :
    (finiteConj b Γ).Realize a ↔ M ⊨ (side (L := L) (n := n) b).onTheory (↑Γ : (extended L n).Theory) := by
  have hs (A : (doubled L n).Sentence) :
      (A.relabel (Empty.elim : Empty → Fin n)).Realize a ↔ M ⊨ A := by
    rw [Formula.realize_relabel]
    change Formula.Realize A (a ∘ Empty.elim) ↔ Formula.Realize A (default : Empty → M)
    rw [Subsingleton.elim (a ∘ Empty.elim) (default : Empty → M)]
  rw [finiteConj, Formula.realize_iInf]
  constructor
  · intro h
    constructor
    rintro A ⟨B, hB, rfl⟩
    exact (hs _).mp (h ⟨B, hB⟩)
  · intro h A
    let : M ⊨ (side (L := L) (n := n) b).onTheory (↑Γ : (extended L n).Theory) := h
    exact (hs _).mpr (Theory.realize_sentence_of_mem
      ((side (L := L) (n := n) b).onTheory (↑Γ : (extended L n).Theory))
      (M := M) ⟨A.val, A.property, rfl⟩)

/-- Finite preimages of the two sides, rather than imaginary conjunction axioms. -/
theorem finite_witnesses {T : (extended L n).Theory} (h : Implicit T) :
    ∃ Γ Δ : Finset (extended L n).Sentence,
      (↑Γ : Set _) ⊆ T ∧ (↑Δ : Set _) ⊆ T ∧
      ((side (L := L) (n := n) false).onTheory (↑Γ : (extended L n).Theory) ∪ (side (L := L) (n := n) true).onTheory (↑Δ : (extended L n).Theory)) ⊨ᵇ agreement := by
  obtain ⟨F, hF, hp⟩ := consequence_finite_support ((implicit_iff_two_copies T).mp h)
  have pick_exists (A : F) : ∃ p : Bool × (extended L n).Sentence,
      p.2 ∈ T ∧ (side (L := L) (n := n) p.1).onSentence p.2 = A.val := by
    rcases hF A.property with (⟨B,hB,he⟩ | ⟨B,hB,he⟩)
    · exact ⟨(false,B),hB,he⟩
    · exact ⟨(true,B),hB,he⟩
  choose pick hpick using pick_exists
  let Γ : Finset (extended L n).Sentence :=
    (Finset.univ.filter (fun A : F => (pick A).1 = false)).image (fun A => (pick A).2)
  let Δ : Finset (extended L n).Sentence :=
    (Finset.univ.filter (fun A : F => (pick A).1 = true)).image (fun A => (pick A).2)
  have hΓ : (↑Γ : Set _) ⊆ T := by
    intro B hB
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hB
    exact (hpick A).1
  have hΔ : (↑Δ : Set _) ⊆ T := by
    intro B hB
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hB
    exact (hpick A).1
  refine ⟨Γ,Δ,hΓ,hΔ,consequence_iff_derives.mpr (derives_mono hp ?_)⟩
  intro B hB
  let A : F := ⟨B,hB⟩
  have he := (hpick A).2
  cases hb : (pick A).1
  · apply Or.inl
    refine ⟨(pick A).2,?_,?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
    · simpa only [hb] using he
  · apply Or.inr
    refine ⟨(pick A).2,?_,?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
    · simpa only [hb] using he

/-- A support condition on actual tagged symbol occurrences. -/
def OldOnly (S : Finset (doubled L n).Symbols) : Prop :=
  ∀ s ∈ S, match s with
    | .inl _ => True
    | .inr ⟨_,.inl _⟩ => True
    | .inr ⟨_,.inr _⟩ => False

/-- Functions were not extended, so erasing their language wrapper is total. -/
def oldTerm : (doubled L n).Term α → L.Term α
  | .var x => .var x
  | .func f ts => .func f (fun i => oldTerm (ts i))

/-- Strip the actual formula using its proof that no new relation occurs. -/
def stripFormula : {k : ℕ} → (A : (doubled L n).BoundedFormula α k) →
    OldOnly (formulaSymbols A) → L.BoundedFormula α k
  | _, .falsum, _ => .falsum
  | _, .equal s t, _ => .equal (oldTerm s) (oldTerm t)
  | _, .rel (.inl R) ts, _ => .rel R (fun i => oldTerm (ts i))
  | _, .rel (.inr R) ts, h => False.elim (h (.inr ⟨_,.inr R⟩) (by simp [formulaSymbols]))
  | _, .imp A B, h => .imp
      (stripFormula A (by intro s hs; apply h s; simp only [formulaSymbols, Finset.mem_union]; exact Or.inl hs))
      (stripFormula B (by intro s hs; apply h s; simp only [formulaSymbols, Finset.mem_union]; exact Or.inr hs))
  | _, .all A, h => .all (stripFormula A h)

private theorem include_oldTerm (t : (doubled L n).Term α) :
    (doubleOld (L := L) (n := n)).onTerm (oldTerm t) = t := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    change Term.func f (fun i => (doubleOld (L := L) (n := n)).onTerm
      (oldTerm (ts i))) = Term.func f ts
    congr 1
    funext i
    exact ih i


/-- Re-inclusion recovers exactly the original formula syntax. -/
theorem include_stripFormula {k : ℕ} (A : (doubled L n).BoundedFormula α k)
    (h : OldOnly (formulaSymbols A)) :
    (doubleOld (L := L) (n := n)).onBoundedFormula (stripFormula A h) = A := by
  induction A with
  | falsum => rfl
  | equal s t => simp [stripFormula, Term.bdEqual, include_oldTerm]
  | rel R ts =>
    cases R with
    | inl R =>
      change BoundedFormula.rel (L := doubled L n) (Sum.inl R) (fun i =>
        (doubleOld (L := L) (n := n)).onTerm (oldTerm (ts i))) =
          BoundedFormula.rel (L := doubled L n) (Sum.inl R) ts
      congr 1
      funext i
      exact include_oldTerm (ts i)
    | inr R => exact False.elim (h (.inr ⟨_,.inr R⟩) (by simp [formulaSymbols]))
  | imp A B ihA ihB =>
    change ((doubleOld (L := L) (n := n)).onBoundedFormula (stripFormula A _)).imp
      ((doubleOld (L := L) (n := n)).onBoundedFormula (stripFormula B _)) = A.imp B
    exact congrArg₂ BoundedFormula.imp (ihA _) (ihB _)
  | all A ih =>
    change ((doubleOld (L := L) (n := n)).onBoundedFormula (stripFormula A _)).all = A.all
    exact congrArg BoundedFormula.all (ih _)

private def freshSymbol (b : Bool) : (doubled L n).Symbols :=
  .inr ⟨n, .inr (.fresh, b)⟩

private def freshTag : (doubled L n).Symbols → Option Bool
  | .inl _ => none
  | .inr ⟨_, .inl _⟩ => none
  | .inr ⟨_, .inr (_, b)⟩ => some b

private theorem fresh_not_term (b : Bool) (t : (doubled L n).Term α) :
    freshSymbol b ∉ termSymbols t := by
  induction t with
  | var => simp [termSymbols]
  | func f ts ih =>
    intro h
    simp only [termSymbols, Finset.mem_insert, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at h
    rcases h with he | ⟨i, hi⟩
    · have hh := congrArg freshTag he
      change some b = none at hh
      cases hh
    · exact ih i hi

private theorem symbols_relabel_term {K : Language} (t : K.Term α) (f : α → β) :
    termSymbols (t.relabel f) = termSymbols t := by
  induction t with
  | var => rfl
  | func F ts ih => simp only [Term.relabel, termSymbols, ih]

private theorem symbols_relabel_formula {K : Language} {k m : ℕ}
    (A : K.BoundedFormula α k) (f : α → β ⊕ Fin m) :
    formulaSymbols (A.relabel f) = formulaSymbols A := by
  induction A with
  | falsum => rfl
  | equal s t =>
    simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, formulaSymbols,
      symbols_relabel_term]
  | rel R ts =>
    simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, formulaSymbols,
      symbols_relabel_term]
  | imp A B ihA ihB => simp only [BoundedFormula.relabel_imp, formulaSymbols, ihA, ihB]
  | all A ih => simpa only [BoundedFormula.relabel_all, formulaSymbols] using ih

private theorem symbols_inf {K : Language} {k : ℕ} (A B : K.BoundedFormula α k) :
    formulaSymbols (A ⊓ B) = formulaSymbols A ∪ formulaSymbols B := by
  change formulaSymbols ((A.imp B.not).not) = _
  ext s
  simp [formulaSymbols]

private theorem symbols_top {K : Language} {k : ℕ} :
    formulaSymbols (⊤ : K.BoundedFormula α k) = ∅ := by
  change formulaSymbols ((BoundedFormula.falsum : K.BoundedFormula α k).imp .falsum) = _
  simp [formulaSymbols]

private theorem fresh_not_fold (c : Bool) (as : List ((doubled L n).Formula α))
    (h : ∀ A ∈ as, freshSymbol c ∉ formulaSymbols A) :
    freshSymbol c ∉ formulaSymbols (as.foldr (· ⊓ ·) ⊤) := by
  induction as with
  | nil => simp [symbols_top]
  | cons A as ih =>
    rw [List.foldr_cons, symbols_inf]
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact h A (by simp) hx
    · exact ih (fun B hB => h B (by simp [hB])) hx

private theorem fresh_not_iInf {ι : Type*} [Finite ι] (c : Bool)
    (f : ι → (doubled L n).Formula α)
    (h : ∀ i, freshSymbol c ∉ formulaSymbols (f i)) :
    freshSymbol c ∉ formulaSymbols (Formula.iInf f) := by
  unfold Formula.iInf BoundedFormula.iInf
  apply fresh_not_fold
  intro A hA
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hA
  exact h i

private theorem side_avoids (b c : Bool) (hcb : c ≠ b) {k : ℕ}
    (A : (extended L n).BoundedFormula α k) :
    freshSymbol c ∉ formulaSymbols ((side b).onBoundedFormula A) := by
  induction A with
  | falsum => simp [formulaSymbols]
  | equal s t =>
    simp [LHom.onBoundedFormula, Term.bdEqual, formulaSymbols, fresh_not_term]
  | rel R ts =>
    intro hs
    simp only [LHom.onBoundedFormula, Relations.boundedFormula, formulaSymbols,
      Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and] at hs
    rcases hs with he | ⟨i, hi⟩
    · have hh := congrArg freshTag he
      cases R with
      | inl R =>
        change some c = none at hh
        cases hh
      | inr R =>
        change some c = some b at hh
        exact hcb (Option.some.inj hh)
    · exact fresh_not_term c _ hi
  | imp A B ihA ihB => simp only [LHom.onBoundedFormula, formulaSymbols,
      Finset.mem_union, not_or]; exact ⟨ihA, ihB⟩
  | all A ih => exact ih

private theorem finiteConj_avoids (b c : Bool) (hcb : c ≠ b)
    (Γ : Finset (extended L n).Sentence) :
    freshSymbol c ∉ formulaSymbols (finiteConj b Γ) := by
  unfold finiteConj
  apply fresh_not_iInf
  intro A
  simpa only [Formula.relabel, symbols_relabel_formula, LHom.onSentence,
    LHom.onFormula] using (side_avoids b c hcb A.val)


/-- Vocabulary control really excludes both private relation symbols. -/
theorem interpolant_oldOnly (Γ Δ : Finset (extended L n).Sentence)
    (θ : (doubled L n).Formula (Fin n))
    (h : formulaSymbols θ ⊆
      formulaSymbols (finiteConj false Γ ⊓ sideAtom false) ∩
      formulaSymbols ((finiteConj true Δ).imp (sideAtom true))) :
    OldOnly (formulaSymbols θ) := by
  have hleft : freshSymbol true ∉ formulaSymbols (finiteConj false Γ ⊓ sideAtom false) := by
    rw [symbols_inf]
    intro hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact finiteConj_avoids false true (by decide) Γ hs
    · exact side_avoids false true (by decide) relationAtom hs
  have hright : freshSymbol false ∉ formulaSymbols ((finiteConj true Δ).imp (sideAtom true)) := by
    intro hs
    simp only [formulaSymbols, Finset.mem_union] at hs
    rcases hs with hs | hs
    · exact finiteConj_avoids true false (by decide) Δ hs
    · exact side_avoids true false (by decide) relationAtom hs
  intro s hs
  rcases s with ⟨m, f⟩ | ⟨m, R⟩
  · trivial
  · cases R with
    | inl R => trivial
    | inr R =>
      rcases R with ⟨R, b⟩
      cases R
      cases b
      · exact hright (Finset.mem_inter.mp (h hs)).2
      · exact hleft (Finset.mem_inter.mp (h hs)).1


/-- The uniform old-language separator obtained from actual formula Craig. -/
theorem separation (Γ Δ : Finset (extended L n).Sentence)
    (h : ((side (L := L) (n := n) false).onTheory (↑Γ : (extended L n).Theory) ∪ (side (L := L) (n := n) true).onTheory (↑Δ : (extended L n).Theory)) ⊨ᵇ agreement) :
    ∃ ρ : L.Formula (Fin n),
      (∀ (M : Type (max u v)) [(doubled L n).Structure M] [Nonempty M]
        (a : Fin n → M),
        (finiteConj false Γ ⊓ sideAtom false).Realize a →
          ((doubleOld (L := L) (n := n)).onFormula ρ).Realize a) ∧
      (∀ (M : Type (max u v)) [(doubled L n).Structure M] [Nonempty M]
        (a : Fin n → M),
        ((doubleOld (L := L) (n := n)).onFormula ρ).Realize a →
          ((finiteConj true Δ).imp (sideAtom true)).Realize a) := by
  have hc : ∀ (M : Type (max u v)) [(doubled L n).Structure M] [Nonempty M]
      (a : Fin n → M),
      (finiteConj false Γ ⊓ sideAtom false).Realize a →
        ((finiteConj true Δ).imp (sideAtom true)).Realize a := by
    intro M _ _ a hp hB
    have hp' := Formula.realize_inf.mp hp
    let : M ⊨ (side (L := L) (n := n) false).onTheory (↑Γ : (extended L n).Theory) ∪
        (side (L := L) (n := n) true).onTheory (↑Δ : (extended L n).Theory) :=
      ((realize_finiteConj false Γ a).mp hp'.1).union
        ((realize_finiteConj true Δ a).mp hB)
    have he := (realize_close _).mp (h.realize_sentence M) a
    rw [Formula.realize_iff] at he
    exact he.mp hp'.2
  obtain ⟨θ,hs,hleft,hright⟩ := CraigInterpolation.formula_interpolation
    (finiteConj false Γ ⊓ sideAtom false) ((finiteConj true Δ).imp (sideAtom true)) hc
  let hOld := interpolant_oldOnly Γ Δ θ hs
  let ρ : L.Formula (Fin n) := stripFormula θ hOld
  have he : (doubleOld (L := L) (n := n)).onFormula ρ = θ := include_stripFormula θ hOld
  refine ⟨ρ,?_,?_⟩
  · simpa only [he] using hleft
  · simpa only [he] using hright

/-- The quantified definition is chosen before all models and assignments. -/
theorem beth (T : (extended L n).Theory) : Implicit T ↔ Explicit T := by
  constructor
  · intro h
    obtain ⟨Γ,Δ,hΓ,hΔ,hfinite⟩ := finite_witnesses h
    obtain ⟨ρ,hleft,hright⟩ := separation Γ Δ hfinite
    refine ⟨ρ, Theory.models_sentence_iff.mpr ?_⟩
    intro M
    let : L.Structure M := (oldInclusion (L := L) (n := n)).reduct M
    apply (realize_definingAxiom ρ).mpr
    intro a
    let r (x : Fin n → M) :=
      @Structure.RelMap (extended L n) M _ n (.inr .fresh) x
    change r a ↔ ρ.Realize a
    constructor
    · intro hR
      let := doubleExpansion (L := L) r (fun _ => False)
      have : (side (L := L) (n := n) false).IsExpansionOn M := by
        constructor
        · intro k f x
          rfl
        · intro k R x
          cases R with
          | inl R => rfl
          | inr R => cases R; rfl
      have hA : (finiteConj false Γ).Realize a :=
        (realize_finiteConj false Γ a).mpr
          ((LHom.onTheory_model (side (L := L) (n := n) false) _).mpr
            (M.is_model.mono hΓ))
      have hi := hleft M a (Formula.realize_inf.mpr ⟨hA,hR⟩)
      exact (LHom.realize_onFormula (doubleOld (L := L) (n := n)) ρ (v := a)).mp hi
    · intro hρ
      let := doubleExpansion (L := L) (fun _ => False) r
      have : (side (L := L) (n := n) true).IsExpansionOn M := by
        constructor
        · intro k f x
          rfl
        · intro k R x
          cases R with
          | inl R => rfl
          | inr R => cases R; rfl
      have hB : (finiteConj true Δ).Realize a :=
        (realize_finiteConj true Δ a).mpr
          ((LHom.onTheory_model (side (L := L) (n := n) true) _).mpr
            (M.is_model.mono hΔ))
      exact hright M a
        ((LHom.realize_onFormula (doubleOld (L := L) (n := n)) ρ (v := a)).mpr hρ) hB
  · exact explicit_implies_implicit

/-- Beth's conclusion in the existing nineteen-rule proof calculus. -/
theorem beth_derives (T : (extended L n).Theory) :
    Implicit T ↔ ∃ ρ : L.Formula (Fin n), Derives T (definingAxiom ρ) := by
  rw [beth]
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ, deductive_completeness hρ⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ, consequence_iff_derives.mpr hρ⟩

end
end Lemmatheca.MathematicalLogic.BethDefinability
