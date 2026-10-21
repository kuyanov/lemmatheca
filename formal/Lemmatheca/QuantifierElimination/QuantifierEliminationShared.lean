import Lemmatheca.QuantifierElimination.QuantifierElimination
import Lemmatheca.DefinabilityAndAutomorphisms.Definability
import Lemmatheca.QuantifierElimination.QuantifierEliminationCells
import Mathlib.Tactic.FinCases

open Lemmatheca.MathematicalLogic

/-! Bridges from the finite-pattern calculation to the shared first-order syntax.
The translations retain every scoped slot, preserve realization and preserve
quantifier-freeness. All public theory conclusions below concern actual theories
and formulas in the shared syntax.
-/

namespace Lemmatheca.ModelTheory.QuantifierElimination
namespace Shared

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

universe u v

abbrev Lang : Bool → Language
  | false => Language.empty
  | true => binaryRelLanguage

def relation {o : Bool} {M : Type u} [S : (Lang o).Structure M] : M → M → Prop := by
  cases o with
  | false => exact noRelation
  | true => exact fun a b => Structure.RelMap (L := binaryRelLanguage) .rel ![a, b]

def termIndex {o n} : (Lang o).Term (Empty ⊕ Fin n) → Fin n
  | .var (.inl a) => a.elim
  | .var (.inr i) => i
  | .func f _ => by cases o <;> exact f.elim

theorem termIndex_realize {o n} {M : Type u} [(Lang o).Structure M]
    (t : (Lang o).Term (Empty ⊕ Fin n)) (x : Fin n → M) :
    t.realize (Sum.elim Empty.elim x) = x (termIndex t) := by
  cases t with
  | var i => cases i with
    | inl a => exact a.elim
    | inr i => rfl
  | func f ts => cases o <;> exact f.elim

def atomToShared {o n} (a : Atom o n) : (Lang o).BoundedFormula Empty n := by
  cases a with
  | inl p => exact .equal (.var (.inr p.1)) (.var (.inr p.2))
  | inr p =>
    cases o with
    | false => exact isEmptyElim p.1
    | true => exact .rel .rel ![.var (.inr p.2.1), .var (.inr p.2.2)]

def toShared {o} : {n : ℕ} → Formula o n → (Lang o).BoundedFormula Empty n
  | _, .bot => ⊥
  | _, .atom a => atomToShared a
  | _, .imp φ ψ => (toShared φ).imp (toShared ψ)
  | _, .ex φ => (toShared φ).ex

def fromShared {o} : {n : ℕ} → (Lang o).BoundedFormula Empty n → Formula o n
  | _, .falsum => .bot
  | _, .equal t s => .atom (.inl (termIndex t, termIndex s))
  | _, .rel R ts => by
      cases o with
      | false => exact R.elim
      | true =>
        cases R
        exact .atom (.inr ((), termIndex (ts 0), termIndex (ts 1)))
  | _, .imp φ ψ => (fromShared φ).imp (fromShared ψ)
  | _, .all φ => (fromShared φ).all

theorem atomToShared_realize {o n} {M : Type u} [(Lang o).Structure M]
    (a : Atom o n) (x : Fin n → M) :
    (atomToShared a).Realize Empty.elim x ↔ Formula.realizeAtom (relation (o := o)) a x := by
  cases a with
  | inl p => rfl
  | inr p =>
    cases o with
    | false => exact isEmptyElim p.1
    | true =>
      change Structure.RelMap (L := binaryRelLanguage) .rel
        (fun i => (![.var (.inr p.2.1), .var (.inr p.2.2)] i :
          binaryRelLanguage.Term (Empty ⊕ Fin n)).realize (Sum.elim Empty.elim x)) ↔ _
      have h : (fun i => (![.var (.inr p.2.1), .var (.inr p.2.2)] i :
          binaryRelLanguage.Term (Empty ⊕ Fin n)).realize (Sum.elim Empty.elim x)) =
          ![x p.2.1, x p.2.2] := by funext i; fin_cases i <;> rfl
      rw [h]
      rfl

theorem toShared_realize {o n} {M : Type u} [(Lang o).Structure M]
    (φ : Formula o n) (x : Fin n → M) :
    (toShared φ).Realize Empty.elim x ↔ φ.Realize (relation (o := o)) x := by
  induction φ with
  | bot => rfl
  | atom a => exact atomToShared_realize a x
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ x) (ihψ x)
  | ex φ ih =>
    rw [toShared, BoundedFormula.realize_ex]
    exact exists_congr fun a => ih (Fin.snoc x a)

theorem fromShared_realize {o n} {M : Type u} [(Lang o).Structure M]
    (φ : (Lang o).BoundedFormula Empty n) (x : Fin n → M) :
    (fromShared φ).Realize (relation (o := o)) x ↔ φ.Realize Empty.elim x := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    exact (congrArg₂ Eq (termIndex_realize t x) (termIndex_realize s x)).symm.to_iff
  | rel R ts =>
    cases o with
    | false => exact R.elim
    | true =>
      cases R
      simp only [fromShared, Formula.Realize, Formula.realizeAtom]
      change relation (o := true) (x (termIndex (ts 0))) (x (termIndex (ts 1))) ↔
        Structure.RelMap (L := binaryRelLanguage) .rel
          (fun i => (ts i).realize (Sum.elim Empty.elim x))
      have h : (fun i => (ts i).realize (Sum.elim Empty.elim x)) =
          ![x (termIndex (ts 0)), x (termIndex (ts 1))] := by
        funext i
        fin_cases i <;> exact termIndex_realize _ x
      rw [h]
      rfl
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ x) (ihψ x)
  | all φ ih =>
    change ¬(∃ a, ¬(fromShared φ).Realize relation (Fin.snoc x a)) ↔
      ∀ a, φ.Realize Empty.elim (Fin.snoc x a)
    simp only [ih, not_exists, Classical.not_not]

theorem atomToShared_isQF {o n} (a : Atom o n) : (atomToShared a).IsQF := by
  cases a with
  | inl p => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | inr p =>
    cases o with
    | false => exact isEmptyElim p.1
    | true => exact (BoundedFormula.IsAtomic.rel _ _).isQF

theorem toShared_isQF {o n} {φ : Formula o n} (h : φ.IsQF) : (toShared φ).IsQF := by
  induction h with
  | bot => exact BoundedFormula.isQF_bot
  | atom a => exact atomToShared_isQF a
  | imp _ _ ihφ ihψ => exact ihφ.imp ihψ

/-- A complete finite atomic pattern expressed in the shared first-order syntax. -/
noncomputable def atomicPatternFormula {o n} (p : Atom o n → Bool) :
    (Lang o).BoundedFormula Empty n :=
  toShared (patternFormula p)

theorem atomicPatternFormula_isQF {o n} (p : Atom o n → Bool) :
    (atomicPatternFormula p).IsQF :=
  toShared_isQF (patternFormula_isQF p)

theorem atomicPatternFormula_realize {o n} {M : Type u} [(Lang o).Structure M]
    (p : Atom o n → Bool) (x : Fin n → M) :
    (atomicPatternFormula p).Realize Empty.elim x ↔
      pattern (relation (o := o)) x = p :=
  (toShared_realize (patternFormula p) x).trans (realize_patternFormula _ p x)

theorem fromShared_isQF {o n} {φ : (Lang o).BoundedFormula Empty n}
    (h : φ.IsQF) : (fromShared φ).IsQF := by
  induction h with
  | falsum => exact .bot
  | @of_isAtomic φ h =>
    cases h with
    | equal t s => exact .atom _
    | rel R ts =>
      cases o with
      | false => exact R.elim
      | true => cases R; exact .atom _
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ

theorem fromEquality_realize {n} {M : Type u} [Language.empty.Structure M]
    (φ : Language.empty.BoundedFormula Empty n) (a : Fin n → M) :
    (fromShared (o := false) φ).Realize noRelation a ↔ φ.Realize Empty.elim a :=
  fromShared_realize (o := false) φ a

theorem fromStrict_realize {n} {M : Type u} [LT M]
    (φ : binaryRelLanguage.BoundedFormula Empty n) (a : Fin n → M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    (fromShared (o := true) φ).Realize (fun a b : M => a < b) a ↔ φ.Realize Empty.elim a := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  exact fromShared_realize (o := true) φ a

theorem equality_hasQuantifierElimination :
    HasQuantifierElimination Language.empty.infiniteTheory := by
  intro n φ
  let θ := equalityEliminate (fromShared (o := false) φ)
  refine ⟨toShared θ, toShared_isQF (equality_quantifier_elimination.{0} _).1, ?_⟩
  intro M v xs
  have : Infinite M := (Language.empty.model_infiniteTheory_iff).mp M.is_model
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff, toShared_realize (o := false) θ xs]
  exact (fromShared_realize (o := false) φ xs).symm.trans
    ((equality_quantifier_elimination (fromShared φ)).2 M xs).symm

def ltAtom {n} (i j : Fin n) : binaryRelLanguage.BoundedFormula Empty n :=
  .rel .rel ![.var (.inr i), .var (.inr j)]

def eqAtom {n} (i j : Fin n) : binaryRelLanguage.BoundedFormula Empty n :=
  .equal (.var (.inr i)) (.var (.inr j))

def strictIrreflexive : binaryRelLanguage.Sentence :=
  (ltAtom (n := 1) 0 0).not.all

def strictTransitive : binaryRelLanguage.Sentence :=
  ((ltAtom (n := 3) 0 1 ⊓ ltAtom 1 2).imp (ltAtom 0 2)).all.all.all

def strictTotal : binaryRelLanguage.Sentence :=
  (ltAtom (n := 2) 0 1 ⊔ eqAtom 0 1 ⊔ ltAtom 1 0).all.all

def strictDense : binaryRelLanguage.Sentence :=
  ((ltAtom (n := 2) 0 1).imp
    (ltAtom (n := 3) 0 2 ⊓ ltAtom 2 1).ex).all.all

def strictNoMinimum : binaryRelLanguage.Sentence :=
  (ltAtom (n := 2) 1 0).ex.all

def strictNoMaximum : binaryRelLanguage.Sentence :=
  (ltAtom (n := 2) 0 1).ex.all

/-- Actual strict-order sentences, rather than a metatheoretic model class. -/
def strictDloTheory : binaryRelLanguage.Theory :=
  {strictIrreflexive, strictTransitive, strictTotal, strictDense,
    strictNoMinimum, strictNoMaximum}

theorem ltAtom_realize {n} {M : Type u} [binaryRelLanguage.Structure M]
    (i j : Fin n) (x : Fin n → M) (v : Empty → M) :
    (ltAtom i j).Realize v x ↔ relation (o := true) (x i) (x j) := by
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  exact atomToShared_realize (o := true) (.inr ((), i, j)) x

theorem model_strictDloTheory_iff {M : Type u} [binaryRelLanguage.Structure M] :
    M ⊨ strictDloTheory ↔ DloAxioms (relation (o := true) (M := M)) := by
  have hirr : (M ⊨ strictIrreflexive) ↔ ∀ a : M, ¬ relation (o := true) a a := by
    simp [strictIrreflexive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_not, ltAtom_realize, Fin.snoc]
  have htrans : (M ⊨ strictTransitive) ↔ ∀ a b c : M,
      relation (o := true) a b → relation (o := true) b c → relation (o := true) a c := by
    simp [strictTransitive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
      ltAtom_realize, Fin.snoc]
  have htotal : (M ⊨ strictTotal) ↔ ∀ a b : M,
      relation (o := true) a b ∨ a = b ∨ relation (o := true) b a := by
    simp [strictTotal, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_sup, ltAtom_realize,
      eqAtom, BoundedFormula.Realize, Term.realize, or_assoc, Fin.snoc]
  have hdense : (M ⊨ strictDense) ↔ ∀ a b : M,
      relation (o := true) a b → ∃ c, relation (o := true) a c ∧ relation (o := true) c b := by
    simp [strictDense, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_ex,
      BoundedFormula.realize_inf, ltAtom_realize, Fin.snoc]
  have hmin : (M ⊨ strictNoMinimum) ↔ ∀ a : M, ∃ b, relation (o := true) b a := by
    simp [strictNoMinimum, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex, ltAtom_realize, Fin.snoc]
  have hmax : (M ⊨ strictNoMaximum) ↔ ∀ a : M, ∃ b, relation (o := true) a b := by
    simp [strictNoMaximum, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex, ltAtom_realize, Fin.snoc]
  simp only [strictDloTheory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, hirr, htrans, htotal, hdense, hmin, hmax]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.irrefl, h.trans, h.total, h.dense, h.noMin, h.noMax⟩⟩

theorem strictDlo_hasQuantifierElimination : HasQuantifierElimination strictDloTheory := by
  intro n φ
  let θ := dloEliminate (fromShared (o := true) φ)
  refine ⟨toShared θ, toShared_isQF (dlo_quantifier_elimination.{0} _).1, ?_⟩
  intro M v xs
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff, toShared_realize (o := true) θ xs]
  have h := (model_strictDloTheory_iff (M := M)).mp M.is_model
  exact (fromShared_realize (o := true) φ xs).symm.trans
    (dlo_axioms_quantifier_elimination _ h (fromShared φ) xs).2.symm

@[instance_reducible] noncomputable def orderOfAxioms {M : Type u} (r : M → M → Prop) (h : DloAxioms r) :
    LinearOrder M := by
  classical
  let : IsStrictTotalOrder M r :=
    { irrefl := h.irrefl, trans := h.trans,
      trichotomous := fun a b hab hba => ((h.total a b).resolve_left hab).resolve_right hba }
  exact linearOrderOfSTO r

theorem model_strictDloTheory {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    M ⊨ strictDloTheory := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  exact model_strictDloTheory_iff.mpr dlo_axioms_of_order

theorem qf_transport {o n} {M : Type u} {N : Type v}
    [(Lang o).Structure M] [(Lang o).Structure N]
    {φ : (Lang o).BoundedFormula Empty n} (hφ : φ.IsQF)
    {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) (relation (o := o)) (relation (o := o)) x y) :
    φ.Realize Empty.elim x ↔ φ.Realize Empty.elim y :=
  (fromShared_realize φ x).symm.trans
    ((qf_pattern_invariance (fromShared_isQF hφ) h).trans (fromShared_realize φ y))

theorem equality_sentence_agreement {M : Type u} {N : Type v}
    [Language.empty.Structure M] [Language.empty.Structure N] [Infinite M] [Infinite N]
    (φ : Language.empty.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  obtain ⟨ψ, hψ, he⟩ := equality_hasQuantifierElimination 0 φ
  have hs : Similar (o := false) (relation (o := false) (M := M))
      (relation (o := false) (M := N)) Fin.elim0 Fin.elim0 := by
    rintro (⟨i, _⟩ | ⟨_, i, _⟩) <;> exact Fin.elim0 i
  have h := qf_transport (o := false) hψ hs
  have h' : (M ⊨ ψ) ↔ (N ⊨ ψ) := by
    simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize, Unique.eq_default] using h
  exact (he.models_sentence_iff (M := M)).trans (h'.trans (he.models_sentence_iff (M := N)).symm)

theorem strictDlo_sentence_agreement {M : Type u} {N : Type v}
    [binaryRelLanguage.Structure M] [binaryRelLanguage.Structure N]
    [M ⊨ strictDloTheory] [N ⊨ strictDloTheory] [Nonempty M] [Nonempty N]
    (φ : binaryRelLanguage.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  obtain ⟨ψ, hψ, he⟩ := strictDlo_hasQuantifierElimination 0 φ
  have hs : Similar (o := true) (relation (o := true) (M := M))
      (relation (o := true) (M := N)) Fin.elim0 Fin.elim0 := by
    rintro (⟨i, _⟩ | ⟨_, i, _⟩) <;> exact Fin.elim0 i
  have h := qf_transport (o := true) hψ hs
  have h' : (M ⊨ ψ) ↔ (N ⊨ ψ) := by
    simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize, Unique.eq_default] using h
  exact (he.models_sentence_iff (M := M)).trans (h'.trans (he.models_sentence_iff (M := N)).symm)

theorem equality_satisfiable : Language.empty.infiniteTheory.IsSatisfiable := by
  let : Language.empty.Structure ℕ := Language.emptyStructure
  exact Theory.Model.isSatisfiable ℕ

theorem equality_isComplete : Language.empty.infiniteTheory.IsComplete := by
  apply (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent
    (T := Language.empty.infiniteTheory)).mpr
  refine ⟨equality_satisfiable, fun M N => ?_⟩
  have : Infinite M := Language.empty.model_infiniteTheory_iff.mp M.is_model
  have : Infinite N := Language.empty.model_infiniteTheory_iff.mp N.is_model
  exact elementarilyEquivalent_iff.mpr (equality_sentence_agreement (M := M) (N := N))

theorem strictDlo_satisfiable : strictDloTheory.IsSatisfiable := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
  let : ℚ ⊨ strictDloTheory := model_strictDloTheory
  exact Theory.Model.isSatisfiable ℚ

theorem strictDlo_isComplete : strictDloTheory.IsComplete := by
  apply (Theory.IsComplete.isComplete_iff_models_elementarily_equivalent (T := strictDloTheory)).mpr
  refine ⟨strictDlo_satisfiable, fun M N => ?_⟩
  exact elementarilyEquivalent_iff.mpr (strictDlo_sentence_agreement (M := M) (N := N))

/-- The shared syntax moves a finite free-variable list into exactly the same
number of scoped slots. This is the existing semantic relabeling operation. -/
def pack {L : Language} {n} (φ : L.Formula (Fin n)) : L.BoundedFormula Empty n :=
  BoundedFormula.relabel Sum.inr φ

theorem pack_realize {L : Language} {M : Type u} [L.Structure M] {n}
    (φ : L.Formula (Fin n)) (a : Fin n → M) :
    (pack φ).Realize Empty.elim a ↔ φ.Realize a :=
  FirstOrder.Language.Formula.realize_relabel_sumInr φ

def packUnary {L : Language} {n} (φ : L.Formula (Fin n ⊕ Fin 1)) :
    L.BoundedFormula Empty (n + 1) :=
  pack (φ.relabel finSumFinEquiv)

theorem packUnary_realize {L : Language} {M : Type u} [L.Structure M] {n}
    (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M) (x : M) :
    (packUnary φ).Realize Empty.elim (Fin.snoc a x) ↔
      φ.Realize (Sum.elim a (fun _ => x)) := by
  rw [packUnary, pack_realize, FirstOrder.Language.Formula.realize_relabel]
  have hv : Fin.snoc a x ∘ finSumFinEquiv = Sum.elim a (fun _ : Fin 1 => x) := by
    funext i
    cases i with
    | inl i => simp [Function.comp_apply, finSumFinEquiv_apply_left, Fin.snoc]
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [Function.comp_apply, finSumFinEquiv_apply_right, Fin.snoc]
  rw [hv]

def equality_elementaryEmbedding {M : Type u} {N : Type v}
    [Language.empty.Structure M] [Language.empty.Structure N] [Infinite M] [Infinite N]
    (f : M → N) (hf : Function.Injective f) : M ↪ₑ[Language.empty] N where
  toFun := f
  map_formula' := by
    intro n φ a
    obtain ⟨ψ, hψ, he⟩ := equality_hasQuantifierElimination n (pack φ)
    have hs : Similar (o := false) (relation (o := false) (M := M))
        (relation (o := false) (M := N)) a (f ∘ a) := by
      rintro (⟨i,j⟩ | ⟨r,_,_⟩)
      · exact hf.eq_iff.symm
      · exact isEmptyElim r
    have h := (he.realize_bd_iff (M := M)).trans
      ((qf_transport (o := false) hψ hs).trans (he.realize_bd_iff (M := N)).symm)
    rw [pack_realize, pack_realize] at h
    exact h.symm

def strictDlo_elementaryEmbedding {M : Type u} {N : Type v}
    [binaryRelLanguage.Structure M] [binaryRelLanguage.Structure N]
    [M ⊨ strictDloTheory] [N ⊨ strictDloTheory] [Nonempty M] [Nonempty N]
    (f : M ↪[binaryRelLanguage] N) : M ↪ₑ[binaryRelLanguage] N where
  toFun := f
  map_formula' := by
    intro n φ a
    obtain ⟨ψ, hψ, he⟩ := strictDlo_hasQuantifierElimination n (pack φ)
    have hs : Similar (o := true) (relation (o := true) (M := M))
        (relation (o := true) (M := N)) a (f ∘ a) := by
      rintro (⟨i,j⟩ | ⟨_,i,j⟩)
      · exact f.injective.eq_iff.symm
      · have hv : (f ∘ ![a i,a j]) = ![f (a i), f (a j)] := by
          funext k; fin_cases k <;> rfl
        simpa only [relation, hv, Function.comp_apply, Formula.realizeAtom] using
          (f.map_rel (r := BinaryRelationSymbol.rel) (x := ![a i,a j])).symm
    have h := (he.realize_bd_iff (M := M)).trans
      ((qf_transport (o := true) hψ hs).trans (he.realize_bd_iff (M := N)).symm)
    rw [pack_realize, pack_realize] at h
    exact h.symm

/-- The elementary map is the given injection, not an unspecified map with the
same domain and codomain. -/
theorem equality_injection_isElementary {M : Type u} {N : Type v}
    [Language.empty.Structure M] [Language.empty.Structure N] [Infinite M] [Infinite N]
    (f : M → N) (hf : Function.Injective f) :
    ∃ e : M ↪ₑ[Language.empty] N, (e : M → N) = f :=
  ⟨equality_elementaryEmbedding f hf, rfl⟩

/-- The elementary embedding has exactly the given structure embedding as its map. -/
theorem strictDlo_embedding_isElementary {M : Type u} {N : Type v}
    [binaryRelLanguage.Structure M] [binaryRelLanguage.Structure N]
    [M ⊨ strictDloTheory] [N ⊨ strictDloTheory] [Nonempty M] [Nonempty N]
    (f : M ↪[binaryRelLanguage] N) :
    ∃ e : M ↪ₑ[binaryRelLanguage] N, (e : M → N) = (f : M → N) :=
  ⟨strictDlo_elementaryEmbedding f, rfl⟩

private theorem qf_equality_unary_finite_or_cofinite {M : Type u} [Infinite M]
    {n : ℕ} (φ : Formula false (n + 1)) (hφ : φ.IsQF) (a : Fin n → M) :
    Set.Finite {x | φ.Realize noRelation (Fin.snoc a x)} ∨
      Set.Finite {x | ¬φ.Realize noRelation (Fin.snoc a x)} := by
  classical
  obtain ⟨b, hb⟩ := (Set.finite_range a).exists_notMem
  have agree (x : M) (hx : x ∉ Set.range a) :
      φ.Realize noRelation (Fin.snoc a x) ↔ φ.Realize noRelation (Fin.snoc a b) := by
    apply qf_pattern_invariance hφ
    apply similar_snoc (similar_refl noRelation a) x b
    · intro i
      exact iff_of_false (fun h => hx ⟨i, h⟩) (fun h => hb ⟨i, h⟩)
    all_goals intro q; exact isEmptyElim q
  by_cases h : φ.Realize noRelation (Fin.snoc a b)
  · right
    apply (Set.finite_range a).subset
    intro x hx
    by_contra hxa
    exact hx ((agree x hxa).mpr h)
  · left
    apply (Set.finite_range a).subset
    intro x hx
    by_contra hxa
    exact h ((agree x hxa).mp hx)


private theorem qf_dlo_unary_finite_union {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    {n : ℕ} (φ : Formula true (n + 1)) (hφ : φ.IsQF) (a : Fin n → M) :
    ∃ s : Finset (Cell M), (∀ c ∈ s, c.Supported (Set.range a)) ∧ {x | φ.Realize (fun a b : M => a < b) (Fin.snoc a x)} =
      {x | ∃ c ∈ s, x ∈ c.realize} := by
  classical
  let P := Atom true (n + 1) → Bool
  let good (p : P) := ∃ x, pattern (fun a b : M => a < b) (Fin.snoc a x) = p ∧
    φ.Realize (fun a b : M => a < b) (Fin.snoc a x)
  let representative (p : P) (hp : good p) := Classical.choose hp
  have rep_spec (p : P) (hp : good p) := Classical.choose_spec hp
  let cell (p : P) : Cell M := if hp : good p then
    Classical.choose (sameCell_is_interval a (representative p hp)) else .empty
  have cell_spec (p : P) (hp : good p) :
      (cell p).realize = {y | SameCell a (representative p hp) y} := by
    simp only [cell, dite_eq_left hp]
    exact (Classical.choose_spec (sameCell_is_interval a (representative p hp))).2
  refine ⟨Finset.univ.image cell, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    dsimp [cell]
    split
    · rename_i hp
      exact (Classical.choose_spec (sameCell_is_interval a (representative p hp))).1
    · trivial
  ext x
  constructor
  · intro hx
    let p : P := pattern (fun a b : M => a < b) (Fin.snoc a x)
    have hp : good p := ⟨x, rfl, hx⟩
    refine ⟨cell p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [cell_spec p hp]
    have hpat := congrFun (rep_spec p hp).1
    have hs : Similar (o := true) (fun a b : M => a < b) (fun a b : M => a < b)
        (Fin.snoc a (representative p hp)) (Fin.snoc a x) := by
      intro z
      exact decide_eq_decide.mp (hpat z)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · simpa [Formula.realizeAtom] using hs.eq i.castSucc (Fin.last n)
    · simpa [Formula.realizeAtom] using hs.lt i.castSucc (Fin.last n)
    · simpa [Formula.realizeAtom] using hs.lt (Fin.last n) i.castSucc
  · rintro ⟨c, hc, hxc⟩
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    by_cases hp : good p
    · rw [cell_spec p hp] at hxc
      exact (qf_pattern_invariance hφ (sameCell_similarity a hxc)).mp
        (rep_spec p hp).2
    · simp [cell, hp, Cell.realize] at hxc

theorem equality_unary_finite_or_cofinite {M : Type u} [Language.empty.Structure M]
    [Infinite M] {n} (φ : Language.empty.BoundedFormula Empty (n + 1)) (a : Fin n → M) :
    Set.Finite {x | φ.Realize Empty.elim (Fin.snoc a x)} ∨
      Set.Finite {x | ¬φ.Realize Empty.elim (Fin.snoc a x)} := by
  obtain ⟨ψ, hψ, he⟩ := equality_hasQuantifierElimination (n + 1) φ
  have h := qf_equality_unary_finite_or_cofinite
    (fromShared (o := false) ψ) (fromShared_isQF hψ) a
  simpa only [fromEquality_realize, ← he.realize_bd_iff (M := M)] using h

theorem strictDlo_unary_finite_union {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] {n}
    (φ : binaryRelLanguage.BoundedFormula Empty (n + 1)) (a : Fin n → M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    ∃ s : Finset (Cell M), (∀ c ∈ s, c.Supported (Set.range a)) ∧
      {x | φ.Realize Empty.elim (Fin.snoc a x)} = {x | ∃ c ∈ s, x ∈ c.realize} := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  let : M ⊨ strictDloTheory := model_strictDloTheory
  obtain ⟨ψ, hψ, he⟩ := strictDlo_hasQuantifierElimination (n + 1) φ
  have h := qf_dlo_unary_finite_union
    (fromShared (o := true) ψ) (fromShared_isQF hψ) a
  simpa only [fromStrict_realize, ← he.realize_bd_iff (M := M)] using h

theorem equality_parameterfree_unary {M : Type u} [Language.empty.Structure M]
    [Infinite M] (φ : Language.empty.BoundedFormula Empty 1) (x y : M) :
    φ.Realize Empty.elim ![x] ↔ φ.Realize Empty.elim ![y] := by
  obtain ⟨ψ, hψ, he⟩ := equality_hasQuantifierElimination 1 φ
  have hs : Similar (o := false) (relation (o := false) (M := M))
      (relation (o := false) (M := M)) ![x] ![y] := by
    rintro (⟨i,j⟩ | ⟨r,_,_⟩)
    · fin_cases i; fin_cases j; simp [Formula.realizeAtom]
    · exact isEmptyElim r
  exact (he.realize_bd_iff (M := M)).trans
    ((qf_transport (o := false) hψ hs).trans (he.realize_bd_iff (M := M)).symm)

theorem strictDlo_parameterfree_unary {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (φ : binaryRelLanguage.BoundedFormula Empty 1) (x y : M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    φ.Realize Empty.elim ![x] ↔ φ.Realize Empty.elim ![y] := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  let : M ⊨ strictDloTheory := model_strictDloTheory
  obtain ⟨ψ, hψ, he⟩ := strictDlo_hasQuantifierElimination 1 φ
  have hrel (a b : M) : relation (o := true) a b ↔ a < b := Iff.rfl
  have hs : Similar (o := true) (relation (o := true) (M := M))
      (relation (o := true) (M := M)) ![x] ![y] := by
    rintro (⟨i,j⟩ | ⟨_,i,j⟩) <;> fin_cases i <;> fin_cases j <;>
      simp [Formula.realizeAtom, hrel]
  exact (he.realize_bd_iff (M := M)).trans
    ((qf_transport (o := true) hψ hs).trans (he.realize_bd_iff (M := M)).symm)

/-- Every unary definition is represented by an actual shared formula with a
finite parameter tuple and one remaining argument slot. -/
theorem definable_unary_tuple {L : Language} {M : Type u} [L.Structure M]
    {A s : Set M} (hs : A.Definable₁ L s) :
    ∃ (n : ℕ) (a : Fin n → M) (φ : L.BoundedFormula Empty (n + 1)),
      (∀ i, a i ∈ A) ∧ ∀ x, φ.Realize Empty.elim (Fin.snoc a x) ↔ x ∈ s := by
  classical
  obtain ⟨A0, hA0, hdef⟩ := Set.definable_iff_finitely_definable.mp hs
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hdef
  let e := Fintype.equivFin (A0 : Set M)
  let a : Fin (Fintype.card (A0 : Set M)) → M := fun i => (e.symm i : M)
  let ψ := φ.relabel (Sum.map e id)
  refine ⟨_, a, packUnary ψ, fun i => hA0 (e.symm i).property, ?_⟩
  intro x
  rw [packUnary_realize, FirstOrder.Language.Formula.realize_relabel]
  have hv : Sum.elim a (fun _ : Fin 1 => x) ∘ Sum.map e id =
      Sum.elim (fun a : ↥(A0 : Set M) => (a : M)) (fun _ : Fin 1 => x) := by
    funext i
    cases i <;> simp [a, Function.comp_apply]
  rw [hv]
  change (fun _ : Fin 1 => x) ∈ {v | φ.Realize (Sum.elim (↑) v)} ↔ x ∈ s
  rw [← hφ]
  rfl

theorem equality_definable_iff_finite_cofinite {M : Type u} [Language.empty.Structure M]
    [Infinite M] (s : Set M) :
    (Set.univ : Set M).Definable₁ Language.empty s ↔ s.Finite ∨ sᶜ.Finite := by
  constructor
  · intro hs
    obtain ⟨n, a, φ, _, hφ⟩ := definable_unary_tuple hs
    have h := equality_unary_finite_or_cofinite φ a
    simpa only [hφ, Set.ofPred_mem_eq, ← Set.mem_compl_iff] using h
  · rintro (hs | hs)
    · exact Lemmatheca.ModelTheory.Definability.finite_definable₁ s hs
    · have h := (Lemmatheca.ModelTheory.Definability.finite_definable₁
        (L := Language.empty) sᶜ hs).compl
      simpa only [Set.Definable₁, Set.compl_ofPred, Set.mem_compl_iff, Classical.not_not] using h

theorem Cell.supported_mono {M : Type u} {A B : Set M} {c : Cell M}
    (h : c.Supported A) (hAB : A ⊆ B) : c.Supported B := by
  cases c with
  | empty => trivial
  | point a => exact hAB h
  | interval l u =>
    exact ⟨fun a ha => hAB (h.1 a ha), fun b hb => hAB (h.2 b hb)⟩

theorem strictDlo_definable_finite_union {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] (A s : Set M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    A.Definable₁ binaryRelLanguage s →
      ∃ t : Finset (Cell M), (∀ c ∈ t, c.Supported A) ∧
        s = {x | ∃ c ∈ t, x ∈ c.realize} := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  dsimp only
  intro hs
  obtain ⟨n, a, φ, ha, hφ⟩ := definable_unary_tuple hs
  obtain ⟨t, ht, he⟩ := strictDlo_unary_finite_union φ a
  refine ⟨t, fun c hc => Cell.supported_mono (ht c hc) ?_, ?_⟩
  · rintro b ⟨i, rfl⟩
    exact ha i
  · simpa only [hφ, Set.ofPred_mem_eq] using he

theorem strictDlo_definable_iff_finite_union {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] (A s : Set M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    A.Definable₁ binaryRelLanguage s ↔
      ∃ t : Finset (Cell M), (∀ c ∈ t, c.Supported A) ∧
        s = {x | ∃ c ∈ t, x ∈ c.realize} := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  dsimp only
  constructor
  · exact strictDlo_definable_finite_union A s
  · rintro ⟨t, ht, rfl⟩
    exact finite_cell_union_definable₁ t A ht

end Shared
end Lemmatheca.ModelTheory.QuantifierElimination
