import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-! Second-order formulas with shared first-order leaves and named binders. -/
namespace Lemmatheca.MathematicalLogic.SecondOrderLogic

open FirstOrder FirstOrder.Language
noncomputable section
universe u v w

inductive Formula (L : Language.{u, v})
  | firstOrder : L.Formula ℕ → Formula L
  | relation {n : ℕ} : ℕ → (Fin n → L.Term ℕ) → Formula L
  | falsum : Formula L
  | imp : Formula L → Formula L → Formula L
  | allIndividual : ℕ → Formula L → Formula L
  | allRelation : ℕ → ℕ → Formula L → Formula L

def Formula.not {L : Language} (φ : Formula L) : Formula L := .imp φ .falsum
def Formula.and {L : Language} (φ ψ : Formula L) : Formula L := (φ.imp ψ.not).not
def Formula.iff {L : Language} (φ ψ : Formula L) : Formula L := (φ.imp ψ).and (ψ.imp φ)
def Formula.exIndividual {L : Language} (x : ℕ) (φ : Formula L) : Formula L :=
  (Formula.allIndividual x φ.not).not
def Formula.exRelation {L : Language} (n X : ℕ) (φ : Formula L) : Formula L :=
  (Formula.allRelation n X φ.not).not

abbrev RelationAssignment (M : Type w) := (n : ℕ) → ℕ → (Fin n → M) → Prop
abbrev RelationDomains (M : Type w) := (n : ℕ) → Set ((Fin n → M) → Prop)

def updateRelation {M : Type w} (r : RelationAssignment M) (n X : ℕ)
    (R : (Fin n → M) → Prop) : RelationAssignment M :=
  Function.update r n (Function.update (r n) X R)

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

def realize (D : RelationDomains M) (a : ℕ → M) (r : RelationAssignment M) : Formula L → Prop
  | .firstOrder φ => φ.Realize a
  | .relation X ts => r _ X (fun i => (ts i).realize a)
  | .falsum => False
  | .imp φ ψ => realize D a r φ → realize D a r ψ
  | .allIndividual x φ => ∀ b : M, realize D (Function.update a x b) r φ
  | .allRelation n X φ => ∀ R, R ∈ D n → realize D a (updateRelation r n X R) φ

def fullRealize (a : ℕ → M) (r : RelationAssignment M) (φ : Formula L) : Prop :=
  realize (fun _ => Set.univ) a r φ

@[simp] theorem realize_not (D : RelationDomains M) (a : ℕ → M) (r : RelationAssignment M)
    (φ : Formula L) : realize D a r φ.not ↔ ¬ realize D a r φ := Iff.rfl

@[simp] theorem realize_and (D : RelationDomains M) (a : ℕ → M) (r : RelationAssignment M)
    (φ ψ : Formula L) : realize D a r (φ.and ψ) ↔ realize D a r φ ∧ realize D a r ψ := by
  simp [Formula.and, realize]

@[simp] theorem realize_iff (D : RelationDomains M) (a : ℕ → M) (r : RelationAssignment M)
    (φ ψ : Formula L) : realize D a r (φ.iff ψ) ↔ (realize D a r φ ↔ realize D a r ψ) := by
  simp [Formula.iff, realize, iff_def]

@[simp] theorem realize_exIndividual (D : RelationDomains M) (a : ℕ → M)
    (r : RelationAssignment M) (x : ℕ) (φ : Formula L) :
    realize D a r (.exIndividual x φ) ↔ ∃ b : M, realize D (Function.update a x b) r φ := by
  simp [Formula.exIndividual, realize]

@[simp] theorem realize_exRelation (D : RelationDomains M) (a : ℕ → M)
    (r : RelationAssignment M) (n X : ℕ) (φ : Formula L) :
    realize D a r (.exRelation n X φ) ↔
      ∃ R, R ∈ D n ∧ realize D a (updateRelation r n X R) φ := by
  simp [Formula.exRelation, realize]

@[simp] theorem updateRelation_same (r : RelationAssignment M) (n X : ℕ)
    (R : (Fin n → M) → Prop) : updateRelation r n X R n X = R := by
  simp [updateRelation]

theorem updateRelation_other (r : RelationAssignment M) (n X : ℕ)
    (R : (Fin n → M) → Prop) (m Y : ℕ) (h : (m, Y) ≠ (n, X)) :
    updateRelation r n X R m Y = r m Y := by
  by_cases hm : m = n
  · subst m
    have hy : Y ≠ X := fun hy => h (by simp [hy])
    simp [updateRelation, hy]
  · simp [updateRelation, hm]

theorem realize_tuple_one (a : ℕ → M) (t : L.Term ℕ) :
    (fun i : Fin 1 => (![t] i).realize a) = ![t.realize a] := by
  funext i
  fin_cases i
  rfl

theorem realize_tuple_two (a : ℕ → M) (t u : L.Term ℕ) :
    (fun i : Fin 2 => (![t, u] i).realize a) = ![t.realize a, u.realize a] := by
  funext i
  fin_cases i <;> rfl

def freeIndividual : Formula L → Finset ℕ
  | .firstOrder φ => φ.freeVarFinset
  | .relation _ ts => Finset.univ.biUnion (fun i => (ts i).varFinset)
  | .falsum => ∅
  | .imp φ ψ => freeIndividual φ ∪ freeIndividual ψ
  | .allIndividual x φ => (freeIndividual φ).erase x
  | .allRelation _ _ φ => freeIndividual φ

def freeRelation : Formula L → Finset (ℕ × ℕ)
  | .firstOrder _ => ∅
  | .relation (n := n) X _ => {(n, X)}
  | .falsum => ∅
  | .imp φ ψ => freeRelation φ ∪ freeRelation ψ
  | .allIndividual _ φ => freeRelation φ
  | .allRelation n X φ => (freeRelation φ).erase (n, X)

def IsSentence (φ : Formula L) : Prop := freeIndividual φ = ∅ ∧ freeRelation φ = ∅

theorem realize_agree (D : RelationDomains M) (φ : Formula L)
    (a b : ℕ → M) (r s : RelationAssignment M)
    (hi : ∀ x ∈ freeIndividual φ, a x = b x)
    (hr : ∀ p ∈ freeRelation φ, r p.1 p.2 = s p.1 p.2) :
    realize D a r φ ↔ realize D b s φ := by
  induction φ generalizing a b r s with
  | firstOrder φ =>
    exact FirstOrderSemantics.formula_realize_agree φ a b default hi
  | @relation n X ts =>
    have ht : (fun i => (ts i).realize a) = (fun i => (ts i).realize b) := by
      funext i
      apply FirstOrderSemantics.term_realize_agree
      intro x hx
      exact hi x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
    change r n X _ ↔ s n X _
    rw [ht, hr (n, X) (Finset.mem_singleton_self _)]
  | falsum => rfl
  | imp φ ψ ihφ ihψ =>
    apply imp_congr
    · exact ihφ a b r s (fun x hx => hi x (Finset.mem_union_left _ hx))
        (fun p hp => hr p (Finset.mem_union_left _ hp))
    · exact ihψ a b r s (fun x hx => hi x (Finset.mem_union_right _ hx))
        (fun p hp => hr p (Finset.mem_union_right _ hp))
  | allIndividual x φ ih =>
    apply forall_congr'
    intro c
    apply ih _ _ _ _ _ hr
    intro y hy
    by_cases h : y = x
    · subst y; simp
    · simp only [Function.update_of_ne h]
      exact hi y (Finset.mem_erase.mpr ⟨h, hy⟩)
  | allRelation n X φ ih =>
    apply forall_congr'
    intro R
    apply imp_congr_right
    intro _
    apply ih _ _ _ _ hi
    intro p hp
    by_cases h : p = (n, X)
    · subst p; simp
    · rw [updateRelation_other r n X R p.1 p.2 h,
        updateRelation_other s n X R p.1 p.2 h]
      exact hr p (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem sentence_assignment_independent (D : RelationDomains M) (φ : Formula L)
    (h : IsSentence φ) (a b : ℕ → M) (r s : RelationAssignment M) :
    realize D a r φ ↔ realize D b s φ := by
  apply realize_agree
  · simp [h.1]
  · simp [h.2]

def ofSentence (φ : L.Sentence) : Formula L := .firstOrder (φ.relabel Empty.elim)

private theorem empty_term_relabel_support {k : ℕ} (t : L.Term (Empty ⊕ Fin k))
    (g : Empty → ℕ ⊕ Fin 0) :
    (t.relabel (BoundedFormula.relabelAux g k)).varFinsetLeft = ∅ := by
  induction t with
  | var x =>
    cases x with
    | inl x => exact x.elim
    | inr i => simp [Term.relabel, BoundedFormula.relabelAux]
  | func f ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, ih]
    ext x; simp

private theorem empty_formula_relabel_support {k : ℕ} (φ : L.BoundedFormula Empty k)
    (g : Empty → ℕ ⊕ Fin 0) : (φ.relabel g).freeVarFinset = ∅ := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      empty_term_relabel_support]
  | rel R ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset,
      empty_term_relabel_support]
    ext x; simp
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

theorem ofSentence_isSentence (φ : L.Sentence) : IsSentence (ofSentence φ) := by
  constructor
  · exact empty_formula_relabel_support φ _
  · rfl

@[simp] theorem realize_ofSentence (D : RelationDomains M) (a : ℕ → M)
    (r : RelationAssignment M) (φ : L.Sentence) :
    realize D a r (ofSentence φ) ↔ M ⊨ φ := by
  simp only [ofSentence, realize, Formula.realize_relabel]
  change Formula.Realize φ (a ∘ Empty.elim) ↔ Formula.Realize φ (default : Empty → M)
  rw [Subsingleton.elim (a ∘ Empty.elim) (default : Empty → M)]

@[simp] theorem fullRealize_ofSentence (a : ℕ → M) (r : RelationAssignment M)
    (φ : L.Sentence) : fullRealize a r (ofSentence φ) ↔ M ⊨ φ :=
  realize_ofSentence _ a r φ

def allIndividuals : ℕ → Formula L → Formula L
  | 0, φ => φ
  | n + 1, φ => .allIndividual n (allIndividuals n φ)

def fill (n : ℕ) (a : ℕ → M) (b : Fin n → M) (x : ℕ) : M :=
  if h : x < n then b ⟨x, h⟩ else a x

private theorem fill_snoc (n : ℕ) (a : ℕ → M) (b : Fin n → M) (c : M) :
    fill n (Function.update a n c) b = fill (n + 1) a (Fin.snoc b c) := by
  funext x
  by_cases h : x < n
  · simp [fill, h, Nat.lt_succ_of_lt h, Fin.snoc]
  · by_cases he : x = n
    · subst x; simp [fill, Fin.snoc]
    · have hn : ¬ x < n + 1 := by omega
      simp [fill, h, hn, he]

theorem realize_allIndividuals (D : RelationDomains M) (n : ℕ)
    (a : ℕ → M) (r : RelationAssignment M) (φ : Formula L) :
    realize D a r (allIndividuals n φ) ↔ ∀ b : Fin n → M, realize D (fill n a b) r φ := by
  induction n generalizing a with
  | zero =>
    have hf (b : Fin 0 → M) : fill 0 a b = a := by funext x; simp [fill]
    simp [allIndividuals, hf]
  | succ n ih =>
    change (∀ c : M, realize D (Function.update a n c) r (allIndividuals n φ)) ↔ _
    simp_rw [ih, fill_snoc]
    constructor
    · intro h b
      simpa using h (b (Fin.last n)) (Fin.init b)
    · intro h c b
      exact h (Fin.snoc b c)

def relationEqual (n X Y : ℕ) : Formula L :=
  allIndividuals n ((Formula.relation X (fun i : Fin n => .var i.val)).iff
    (Formula.relation Y (fun i : Fin n => .var i.val)))

theorem fullRealize_relationEqual (n X Y : ℕ) (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (relationEqual n X Y : Formula L) ↔ r n X = r n Y := by
  simp only [fullRealize, relationEqual, realize_allIndividuals, realize_iff, realize,
    Term.realize_var]
  have hf (b : Fin n → M) : (fun i : Fin n => fill n a b i.val) = b := by
    funext i; simp [fill]
  simp_rw [hf]
  exact ⟨fun h => funext (fun b => propext (h b)), fun h b => by rw [h]⟩

def functionGraphFormula (F : ℕ) : Formula L :=
  .allIndividual 0 (.exIndividual 1
    ((Formula.relation F ![.var 0, .var 1]).and
      (.allIndividual 2 ((Formula.relation F ![.var 0, .var 2]).imp
        (.firstOrder (.equal (.var (.inl 2)) (.var (.inl 1))))))))

theorem fullRealize_functionGraphFormula (F : ℕ) (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (functionGraphFormula F : Formula L) ↔
      ∀ x : M, ∃! y : M, r 2 F ![x, y] := by
  simp only [fullRealize, functionGraphFormula, realize, realize_exIndividual, realize_and, realize_tuple_two,
    Formula.Realize, BoundedFormula.Realize, Term.realize_var,
    Sum.elim_inl, Function.update_self, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1),
    Function.update_of_ne (by decide : (0 : ℕ) ≠ 2),
    Function.update_of_ne (by decide : (1 : ℕ) ≠ 2)]
  simp [ExistsUnique]

theorem unique_function_iff {A : Type*} {B : Type*} (R : A → B → Prop) :
    (∀ x, ∃! y, R x y) ↔ ∃! f : A → B, ∀ x y, R x y ↔ y = f x := by
  constructor
  · intro h
    let f : A → B := fun x => Classical.choose (h x)
    have hf : ∀ x y, R x y ↔ y = f x := by
      intro x y
      exact ⟨fun hy => (Classical.choose_spec (h x)).2 y hy,
        fun hy => hy ▸ (Classical.choose_spec (h x)).1⟩
    refine ⟨f, hf, ?_⟩
    intro g hg
    funext x
    exact (hg x (f x)).mp ((hf x (f x)).mpr rfl) |>.symm
  · rintro ⟨f, hf, _⟩ x
    exact ⟨f x, (hf x (f x)).mpr rfl, fun y hy => (hf x y).mp hy⟩

theorem unique_finite_arity_graph_iff (n : ℕ) (R : (Fin (n + 1) → M) → Prop) :
    (∀ xs : Fin n → M, ∃! y : M, R (Fin.snoc xs y)) ↔
      ∃! f : (Fin n → M) → M, ∀ xs y, R (Fin.snoc xs y) ↔ y = f xs :=
  unique_function_iff (fun xs y => R (Fin.snoc xs y))

def wellOrderFormula (R : ℕ) : Formula L :=
  .allRelation 1 0 ((Formula.exIndividual 0 (.relation 0 ![.var 0])).imp
    (.exIndividual 0 ((Formula.relation 0 ![.var 0]).and
      (.allIndividual 1 ((Formula.relation 0 ![.var 1]).imp
        (Formula.relation R ![.var 1, .var 0]).not)))))

theorem fullRealize_wellOrderFormula (R : ℕ) (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (wellOrderFormula R : Formula L) ↔
      ∀ S : Set M, S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, ¬ r 2 R ![x, m] := by
  simp only [fullRealize, wellOrderFormula, realize, Set.mem_univ, forall_const,
    realize_exIndividual, realize_and, realize_not, realize_tuple_one, realize_tuple_two,
    Term.realize_var, updateRelation_same]
  simp only [updateRelation, Function.update_of_ne (by decide : (2 : ℕ) ≠ 1),
    Function.update_self, Function.update_of_ne (by decide : (0 : ℕ) ≠ 1)]
  constructor
  · intro h S hs
    exact h (fun xs => S (xs 0)) hs
  · intro h S hs
    exact h (fun x => S ![x]) hs

theorem fullRealize_wellOrder (R : ℕ) (a : ℕ → M) (r : RelationAssignment M)
    [IsStrictTotalOrder M (fun x y => r 2 R ![x, y])] :
    fullRealize a r (wellOrderFormula R : Formula L) ↔
      IsWellOrder M (fun x y => r 2 R ![x, y]) := by
  rw [fullRealize_wellOrderFormula, ← WellFounded.wellFounded_iff_has_min]
  exact ⟨fun h => { wf := h }, fun h => h.wf⟩

def inductionSentence (z : L.Functions 0) (s : L.Functions 1) : Formula L :=
  .allRelation 1 0 (((Formula.relation 0 ![.func z Fin.elim0]).and
    (.allIndividual 0 ((Formula.relation 0 ![.var 0]).imp
      (.relation 0 ![.func s (fun _ => .var 0)])))).imp
        (.allIndividual 0 (.relation 0 ![.var 0])))

@[simp] theorem fullRealize_inductionSentence (z : L.Functions 0) (s : L.Functions 1)
    (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (inductionSentence z s) ↔
      ∀ P : M → Prop, P (Structure.funMap z Fin.elim0) →
        (∀ x, P x → P (Structure.funMap s (fun _ => x))) → ∀ x, P x := by
  simp only [fullRealize, inductionSentence, realize, Set.mem_univ, forall_const,
    realize_and, realize_tuple_one, Term.realize_var, Term.realize_func,
    Function.update_self, updateRelation_same]
  have hz : (fun i : Fin 0 => (Fin.elim0 i : L.Term ℕ).realize a) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  constructor
  · intro h P h0 hs
    exact h (fun xs => P (xs 0)) ⟨h0, hs⟩
  · intro h P hp
    exact h (fun x => P ![x]) hp.1 hp.2

theorem inductionSentence_isSentence (z : L.Functions 0) (s : L.Functions 1) :
    IsSentence (inductionSentence z s) := by
  simp [IsSentence, inductionSentence, freeIndividual, freeRelation, Formula.and,
    Formula.not, Term.varFinset]

def fullSubsetExists : Formula L := .exRelation 1 0 (.allIndividual 0 (.relation 0 ![.var 0]))

theorem fullRealize_fullSubsetExists (a : ℕ → M) (r : RelationAssignment M) :
    fullRealize a r (fullSubsetExists : Formula L) := by
  simp only [fullRealize, fullSubsetExists, realize_exRelation, Set.mem_univ, true_and,
    realize, realize_tuple_one, Term.realize_var, Function.update_self, updateRelation_same]
  exact ⟨fun _ => True, fun _ => trivial⟩

end
end Lemmatheca.MathematicalLogic.SecondOrderLogic
