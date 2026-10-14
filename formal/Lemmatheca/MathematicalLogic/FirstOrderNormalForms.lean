import Mathlib.ModelTheory.Complexity
import Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-! First-order normal forms with exact free support and scoped quantifier movement. -/

namespace Lemmatheca.MathematicalLogic.FirstOrderNormalForms

open FirstOrder FirstOrder.Language

universe u v w u'

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}
variable {M : Type w} [L.Structure M]

/-- A literal is atomic or the negation of an atomic formula. -/
def IsLiteral (φ : L.BoundedFormula α n) : Prop :=
  φ.IsAtomic ∨ ∃ θ : L.BoundedFormula α n, θ.IsAtomic ∧ φ = θ.not

/-- The displayed negation-normal grammar, interpreted through the fixed abbreviations. -/
inductive IsNnf : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | falsum {n : ℕ} : IsNnf (⊥ : L.BoundedFormula α n)
  | truth {n : ℕ} : IsNnf (⊤ : L.BoundedFormula α n)
  | atom {n : ℕ} {φ : L.BoundedFormula α n} : φ.IsAtomic → IsNnf φ
  | negAtom {n : ℕ} {φ : L.BoundedFormula α n} : φ.IsAtomic → IsNnf φ.not
  | inf {n : ℕ} {φ ψ : L.BoundedFormula α n} : IsNnf φ → IsNnf ψ → IsNnf (φ ⊓ ψ)
  | sup {n : ℕ} {φ ψ : L.BoundedFormula α n} : IsNnf φ → IsNnf ψ → IsNnf (φ ⊔ ψ)
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsNnf φ → IsNnf φ.all
  | ex {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsNnf φ → IsNnf φ.ex

/-- Positive and negative normal forms by primitive recursion. -/
def nnf : ∀ {n : ℕ}, L.BoundedFormula α n → Bool → L.BoundedFormula α n
  | _, .falsum, true => ⊥
  | _, .falsum, false => ⊤
  | _, .equal t s, true => .equal t s
  | _, .equal t s, false => (BoundedFormula.equal t s).not
  | _, .rel R ts, true => .rel R ts
  | _, .rel R ts, false => (BoundedFormula.rel R ts).not
  | _, .imp φ ψ, true => nnf φ false ⊔ nnf ψ true
  | _, .imp φ ψ, false => nnf φ true ⊓ nnf ψ false
  | _, .all φ, true => (nnf φ true).all
  | _, .all φ, false => (nnf φ false).ex

/-- A prefix whose quantifier-free matrix is in negation normal form. -/
inductive IsPrenexNnf : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | matrix {n : ℕ} {φ : L.BoundedFormula α n} : φ.IsQF → IsNnf φ → IsPrenexNnf φ
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsPrenexNnf φ → IsPrenexNnf φ.all
  | ex {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsPrenexNnf φ → IsPrenexNnf φ.ex

/-- Abstract a chosen free name into the newest placeholder. -/
def bindVar [DecidableEq α] (φ : L.Formula α) (x : α) : L.BoundedFormula α 1 :=
  BoundedFormula.relabel (n := 1) (k := 0) (fun y => if y = x then Sum.inr 0 else Sum.inl y) φ

/-- Rename a free name in the body before abstracting its new name. -/
def renameVar [DecidableEq α] (φ : L.Formula α) (x y : α) : L.Formula α :=
  φ.subst (fun z => .var (if z = x then y else z))

private theorem bindVar_realize [DecidableEq α] (φ : L.Formula α) (x : α)
    (a : α → M) (b : Fin 0 → M) (m : M) :
    (bindVar φ x).Realize a (Fin.snoc b m) ↔ φ.Realize (Function.update a x m) := by
  rw [bindVar, BoundedFormula.realize_relabel]
  have hb : (Fin.snoc b m) ∘ Fin.natAdd 1 = (default : Fin 0 → M) :=
    Subsingleton.elim _ _
  rw [hb]
  have ha : (Sum.elim a (Fin.snoc b m ∘ Fin.castAdd 0) ∘
      fun z => if z = x then Sum.inr 0 else Sum.inl z) = Function.update a x m := by
    funext z
    by_cases hz : z = x
    · subst z
      simp [Function.comp_apply, Fin.snoc, Fin.castAdd]
    · simp [Function.comp_apply, hz]
  rw [ha]
  rfl

private theorem fresh_body_renaming [DecidableEq α] (φ : L.Formula α) (x y : α)
    (_hne : x ≠ y) (hy : y ∉ φ.freeVarFinset)
    (a : α → M) (b : Fin 0 → M) (m : M) :
    (bindVar φ x).Realize a (Fin.snoc b m) ↔
      (bindVar (renameVar φ x y) y).Realize a (Fin.snoc b m) := by
  rw [bindVar_realize, bindVar_realize]
  simp only [renameVar, Formula.Realize, BoundedFormula.realize_subst, Term.realize]
  apply Lemmatheca.MathematicalLogic.FirstOrderSemantics.formula_realize_agree
  intro z hz
  have hzy : z ≠ y := fun h => hy (h ▸ hz)
  by_cases hzx : z = x
  · subst z
    simp
  · simp [hzx, hzy]

theorem fresh_all_renaming [DecidableEq α] (φ : L.Formula α) (x y : α)
    (hne : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    (bindVar φ x).all ⇔[(∅ : L.Theory)] (bindVar (renameVar φ x y) y).all := by
  intro M a b
  rw [BoundedFormula.realize_iff]
  simp only [BoundedFormula.realize_all]
  exact forall_congr' fun m => fresh_body_renaming φ x y hne hy a b m

theorem fresh_ex_renaming [DecidableEq α] (φ : L.Formula α) (x y : α)
    (hne : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    (bindVar φ x).ex ⇔[(∅ : L.Theory)] (bindVar (renameVar φ x y) y).ex := by
  intro M a b
  rw [BoundedFormula.realize_iff]
  simp only [BoundedFormula.realize_ex]
  exact exists_congr fun m => fresh_body_renaming φ x y hne hy a b m

theorem fresh_labels (s : Finset ℕ) (k : ℕ) :
    ∃ f : Fin k → ℕ, Function.Injective f ∧ ∀ i, f i ∉ s := by
  refine ⟨fun i => s.sup id + 1 + i, ?_, ?_⟩
  · intro i j h
    exact Fin.ext (Nat.add_left_cancel h)
  · intro i hi
    have hbound := Finset.le_sup (f := id) hi
    have hlt : s.sup id < s.sup id + 1 + i := by omega
    exact (Nat.not_lt_of_ge hbound) hlt

theorem nnf_isNnf (φ : L.BoundedFormula α n) (positive : Bool) :
    IsNnf (nnf φ positive) := by
  induction φ generalizing positive with
  | falsum => cases positive <;> simp only [nnf] <;> constructor
  | equal t s =>
    cases positive
    · exact IsNnf.negAtom (.equal t s)
    · exact IsNnf.atom (.equal t s)
  | rel R ts =>
    cases positive
    · exact IsNnf.negAtom (.rel R ts)
    · exact IsNnf.atom (.rel R ts)
  | imp φ ψ ihφ ihψ =>
    cases positive
    · exact IsNnf.inf (ihφ true) (ihψ false)
    · exact IsNnf.sup (ihφ false) (ihψ true)
  | all φ ih =>
    cases positive
    · exact IsNnf.ex (ih false)
    · exact IsNnf.all (ih true)

theorem nnf_realize (φ : L.BoundedFormula α n) (positive : Bool)
    (a : α → M) (b : Fin n → M) :
    (nnf φ positive).Realize a b ↔ if positive then φ.Realize a b else ¬φ.Realize a b := by
  induction φ generalizing positive with
  | falsum => cases positive <;> simp [nnf, BoundedFormula.Realize]
  | equal t s => cases positive <;> simp [nnf]
  | rel R ts => cases positive <;> simp [nnf]
  | imp φ ψ ihφ ihψ =>
    cases positive <;> simp [nnf, ihφ, ihψ, imp_iff_not_or]
  | all φ ih =>
    cases positive <;> simp [nnf, ih, not_forall]

theorem nnf_freeVarFinset [DecidableEq α] (φ : L.BoundedFormula α n) (positive : Bool) :
    (nnf φ positive).freeVarFinset = φ.freeVarFinset := by
  induction φ generalizing positive with
  | falsum => cases positive <;> simp [nnf, Top.top, BoundedFormula.not]
  | equal t s => cases positive <;> simp [nnf, BoundedFormula.not]
  | rel R ts => cases positive <;> simp [nnf, BoundedFormula.not]
  | imp φ ψ ihφ ihψ =>
    cases positive <;> simp [nnf, Min.min, Max.max, BoundedFormula.not, ihφ, ihψ]
  | all φ ih =>
    cases positive <;> simp [nnf, BoundedFormula.ex, BoundedFormula.not, ih]

theorem negation_identities_support [DecidableEq α]
    (φ ψ : L.BoundedFormula α n) (θ : L.BoundedFormula α (n + 1)) :
    φ.not.not.freeVarFinset = φ.freeVarFinset ∧
    (φ ⊓ ψ).not.freeVarFinset = (φ.not ⊔ ψ.not).freeVarFinset ∧
    (φ ⊔ ψ).not.freeVarFinset = (φ.not ⊓ ψ.not).freeVarFinset ∧
    (φ.imp ψ).freeVarFinset = (φ.not ⊔ ψ).freeVarFinset ∧
    θ.all.not.freeVarFinset = θ.not.ex.freeVarFinset ∧
    θ.ex.not.freeVarFinset = θ.not.all.freeVarFinset ∧
    (⊥ : L.BoundedFormula α n).not.freeVarFinset = (⊤ : L.BoundedFormula α n).freeVarFinset ∧
    (⊤ : L.BoundedFormula α n).not.freeVarFinset = (⊥ : L.BoundedFormula α n).freeVarFinset := by
  simp [BoundedFormula.not, Min.min, Max.max]

theorem moving_quantifiers [Nonempty M] (θ : L.BoundedFormula α (n + 1))
    (χ : L.BoundedFormula α n) (a : α → M) (b : Fin n → M) :
    ((θ.all ⊓ χ).Realize a b ↔ (θ ⊓ χ.liftAt 1 n).all.Realize a b) ∧
    ((θ.ex ⊓ χ).Realize a b ↔ (θ ⊓ χ.liftAt 1 n).ex.Realize a b) ∧
    ((θ.all ⊔ χ).Realize a b ↔ (θ ⊔ χ.liftAt 1 n).all.Realize a b) ∧
    ((θ.ex ⊔ χ).Realize a b ↔ (θ ⊔ χ.liftAt 1 n).ex.Realize a b) ∧
    ((χ ⊓ θ.all).Realize a b ↔ (χ.liftAt 1 n ⊓ θ).all.Realize a b) ∧
    ((χ ⊓ θ.ex).Realize a b ↔ (χ.liftAt 1 n ⊓ θ).ex.Realize a b) ∧
    ((χ ⊔ θ.all).Realize a b ↔ (χ.liftAt 1 n ⊔ θ).all.Realize a b) ∧
    ((χ ⊔ θ.ex).Realize a b ↔ (χ.liftAt 1 n ⊔ θ).ex.Realize a b) := by
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_liftAt_one_self, Fin.snoc_comp_castSucc]
  by_cases hc : χ.Realize a b <;> simp [hc]

theorem moving_quantifiers_empty_allowed (θ : L.BoundedFormula α (n + 1))
    (χ : L.BoundedFormula α n) (a : α → M) (b : Fin n → M) :
    ((θ.ex ⊓ χ).Realize a b ↔ (θ ⊓ χ.liftAt 1 n).ex.Realize a b) ∧
    ((θ.all ⊔ χ).Realize a b ↔ (θ ⊔ χ.liftAt 1 n).all.Realize a b) := by
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_liftAt_one_self, Fin.snoc_comp_castSucc]
  constructor
  · exact exists_and_right.symm
  · exact forall_or_right.symm

section ExactSupport

variable [DecidableEq α]

private theorem term_bound_relabel_support {β γ : Type*} (f : β → γ)
    (t : L.Term (α ⊕ β)) :
    (t.relabel (Sum.map id f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> rfl
  | func F ts ih => simp [ih]

private theorem castLE_support {m n : ℕ} (φ : L.BoundedFormula α m) (h : m ≤ n) :
    (φ.castLE h).freeVarFinset = φ.freeVarFinset := by
  induction φ generalizing n with
  | falsum => rfl
  | equal t s => simp [term_bound_relabel_support]
  | rel R ts => simp [Function.comp_def, term_bound_relabel_support]
  | imp φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | all φ ih => simp [ih]

theorem liftAt_freeVarFinset {n : ℕ} (φ : L.BoundedFormula α n) (k m : ℕ) :
    (φ.liftAt k m).freeVarFinset = φ.freeVarFinset := by
  induction φ with
  | falsum => rfl
  | equal t s => simp [BoundedFormula.liftAt, BoundedFormula.mapTermRel,
      Term.liftAt, term_bound_relabel_support]
  | rel R ts => simp [BoundedFormula.liftAt, BoundedFormula.mapTermRel,
      Term.liftAt, term_bound_relabel_support]
  | imp φ ψ ihφ ihψ =>
    change (φ.liftAt k m).freeVarFinset ∪ (ψ.liftAt k m).freeVarFinset = _
    simp only [ihφ, ihψ, BoundedFormula.freeVarFinset]
  | all φ ih =>
    change ((φ.liftAt k m).castLE _).freeVarFinset = _
    rw [castLE_support, ih]
    rfl

private theorem neg_support {n : ℕ} (φ : L.BoundedFormula α n) :
    φ.not.freeVarFinset = φ.freeVarFinset := by
  simp

private theorem ex_support {n : ℕ} (φ : L.BoundedFormula α (n+1)) :
    φ.ex.freeVarFinset = φ.freeVarFinset := by
  simp

private theorem prenexRight_support {n : ℕ} {ψ : L.BoundedFormula α n}
    (hψ : ψ.IsPrenex) (φ : L.BoundedFormula α n) :
    (φ.toPrenexImpRight ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  revert φ
  induction hψ with
  | of_isQF h => intro φ; rw [h.toPrenexImpRight]; rfl
  | @all n ψ h ih =>
    intro φ
    change ((φ.liftAt 1 _).toPrenexImpRight ψ).freeVarFinset = _
    rw [ih, liftAt_freeVarFinset]
    rfl
  | @ex n ψ h ih =>
    intro φ
    change (((φ.liftAt 1 n).toPrenexImpRight ψ).ex).freeVarFinset = _
    rw [ex_support, ih, liftAt_freeVarFinset, ex_support]

private theorem prenexImp_support {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : φ.IsPrenex) (ψ : L.BoundedFormula α n) (hψ : ψ.IsPrenex) :
    (φ.toPrenexImp ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  revert ψ
  induction hφ with
  | @of_isQF n φ h =>
    intro ψ hψ
    rw [h.toPrenexImp]
    exact prenexRight_support hψ φ
  | @all n φ h ih =>
    intro ψ hψ
    rw [BoundedFormula.toPrenexImp, ex_support, ih _ hψ.liftAt, liftAt_freeVarFinset]
    rfl
  | @ex n φ h ih =>
    intro ψ hψ
    change (φ.toPrenexImp (ψ.liftAt 1 _)).freeVarFinset = _
    rw [ih _ hψ.liftAt, liftAt_freeVarFinset, ex_support]

theorem toPrenex_freeVarFinset {n : ℕ} (φ : L.BoundedFormula α n) :
    φ.toPrenex.freeVarFinset = φ.freeVarFinset := by
  induction φ with
  | falsum => rfl
  | equal t s => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    change (φ.toPrenex.toPrenexImp ψ.toPrenex).freeVarFinset = _
    rw [prenexImp_support φ.toPrenex_isPrenex _ ψ.toPrenex_isPrenex, ihφ, ihψ]
    rfl
  | all φ ih => exact ih


private theorem term_hide_support (x : α) (k : ℕ) (t : L.Term (α ⊕ Fin k)) :
    (t.relabel (BoundedFormula.relabelAux
      (fun a => if a = x then Sum.inr (0 : Fin 1) else Sum.inl a) k)).varFinsetLeft =
      t.varFinsetLeft.erase x := by
  induction t with
  | var a =>
    cases a with
    | inl a =>
      by_cases h : a = x
      · simp [BoundedFormula.relabelAux, h]
      · simp [BoundedFormula.relabelAux, h, Ne.symm h]
    | inr a => simp [BoundedFormula.relabelAux]
  | func F ts ih => simp [ih, Finset.erase_biUnion]

private theorem hide_free_support {k : ℕ} (φ : L.BoundedFormula α k) (x : α) :
    (φ.relabel (n := 1) (fun a => if a = x then Sum.inr (0 : Fin 1) else Sum.inl a)).freeVarFinset =
      φ.freeVarFinset.erase x := by
  induction φ with
  | falsum => rfl
  | equal t s => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      term_hide_support, Finset.erase_union_distrib]
  | rel R ts => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      term_hide_support, Finset.erase_biUnion]
  | imp φ ψ ihφ ihψ =>
    change (φ.relabel _).freeVarFinset ∪ (ψ.relabel _).freeVarFinset = _
    rw [ihφ, ihψ]
    exact (Finset.erase_union_distrib _ _ x).symm
  | all φ ih =>
    change ((φ.relabel (n := 1) _).castLE _).freeVarFinset = _
    rw [castLE_support, ih]
    rfl

end ExactSupport

theorem fresh_renaming_support [DecidableEq α] (φ : L.Formula α) (x y : α)
    (_hne : x ≠ y) (hy : y ∉ φ.freeVarFinset) :
    (bindVar (renameVar φ x y) y).freeVarFinset = (bindVar φ x).freeVarFinset := by
  rw [bindVar, hide_free_support, bindVar, hide_free_support, renameVar,
    Lemmatheca.MathematicalLogic.FirstOrderSyntax.formula_freeVarFinset_subst]
  ext z
  simp only [Finset.mem_erase, Finset.mem_biUnion, Term.varFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hzy, a, ha, hza⟩
    by_cases hax : a = x
    · simp only [ite_eq_left hax] at hza
      exact (hzy hza).elim
    · simp only [ite_eq_right hax] at hza
      subst z
      exact ⟨hax, ha⟩
  · rintro ⟨hzx, hz⟩
    have hzy : z ≠ y := fun h => hy (h ▸ hz)
    exact ⟨hzy, z, hz, by simp [hzx]⟩

private theorem nnf_isQF {φ : L.BoundedFormula α n} (hφ : φ.IsQF) (positive : Bool) :
    (nnf φ positive).IsQF := by
  induction hφ generalizing positive with
  | falsum =>
    cases positive
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal t s =>
      cases positive
      · exact (BoundedFormula.IsAtomic.equal t s).isQF.not
      · exact (BoundedFormula.IsAtomic.equal t s).isQF
    | rel R ts =>
      cases positive
      · exact (BoundedFormula.IsAtomic.rel R ts).isQF.not
      · exact (BoundedFormula.IsAtomic.rel R ts).isQF
  | imp hφ hψ ihφ ihψ =>
    cases positive
    · exact (ihφ true).inf (ihψ false)
    · exact (ihφ false).sup (ihψ true)

private theorem nnf_equivalent (φ : L.BoundedFormula α n) :
    φ ⇔[(∅ : L.Theory)] nnf φ true := by
  intro M a b
  rw [BoundedFormula.realize_iff]
  exact (nnf_realize φ true a b).symm

private theorem normalize_prenex_matrix [DecidableEq α] {φ : L.BoundedFormula α n}
    (hφ : φ.IsPrenex) :
    ∃ ψ : L.BoundedFormula α n, IsPrenexNnf ψ ∧
      ψ.freeVarFinset = φ.freeVarFinset ∧ φ ⇔[(∅ : L.Theory)] ψ := by
  induction hφ with
  | @of_isQF n φ hφ =>
    exact ⟨nnf φ true, .matrix (nnf_isQF hφ true) (nnf_isNnf φ true),
      nnf_freeVarFinset φ true, nnf_equivalent φ⟩
  | @all n φ hφ ih =>
    obtain ⟨ψ, hψ, hs, he⟩ := ih
    exact ⟨ψ.all, .all hψ, hs, he.all⟩
  | @ex n φ hφ ih =>
    obtain ⟨ψ, hψ, hs, he⟩ := ih
    exact ⟨ψ.ex, .ex hψ, by simpa using hs, he.ex⟩

theorem prenex_nnf_exists [DecidableEq α] (φ : L.BoundedFormula α n) :
    ∃ ψ : L.BoundedFormula α n, IsPrenexNnf ψ ∧
      ψ.freeVarFinset = φ.freeVarFinset ∧ φ ⇔[(∅ : L.Theory)] ψ := by
  obtain ⟨ψ, hψ, hs, he⟩ := normalize_prenex_matrix φ.toPrenex_isPrenex
  refine ⟨ψ, hψ, hs.trans (toPrenex_freeVarFinset φ), ?_⟩
  have hp : φ ⇔[(∅ : L.Theory)] φ.toPrenex := by
    intro M a b
    simp
  exact hp.trans he

theorem prenex_nonunique :
    (⊥ : L.BoundedFormula α n) ≠ (⊥ : L.BoundedFormula α (n + 1)).all ∧
    (⊥ : L.BoundedFormula α n).IsPrenex ∧
    (⊥ : L.BoundedFormula α (n + 1)).all.IsPrenex ∧
    (⊥ : L.BoundedFormula α n) ⇔[(∅ : L.Theory)] (⊥ : L.BoundedFormula α (n + 1)).all := by
  refine ⟨(by intro h; cases h), BoundedFormula.isQF_bot.isPrenex,
    BoundedFormula.IsPrenex.all BoundedFormula.isQF_bot.isPrenex, ?_⟩
  intro M a b
  simp

/-- Every object has an equal object, with the latter chosen afterwards. -/
def eachHasEqual (L : Language) : L.Sentence :=
  ((.var (.inr (0 : Fin 2)) : L.Term (Empty ⊕ Fin 2)).bdEqual
    (.var (.inr 1))).ex.all

/-- One object is equal to every object, with the witness chosen first. -/
def commonEqual (L : Language) : L.Sentence :=
  ((.var (.inr (0 : Fin 2)) : L.Term (Empty ⊕ Fin 2)).bdEqual
    (.var (.inr 1))).all.ex

theorem eachHasEqual_realize : M ⊨ eachHasEqual L := by
  simp only [eachHasEqual, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex]
  change ∀ m : M, ∃ m' : M, m = m'
  exact fun m => ⟨m, rfl⟩

theorem commonEqual_realize : M ⊨ commonEqual L ↔ Subsingleton M ∧ Nonempty M := by
  simp only [commonEqual, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_all]
  change (∃ m : M, ∀ m' : M, m = m') ↔ Subsingleton M ∧ Nonempty M
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨⟨fun x y => (hm x).symm.trans (hm y)⟩, ⟨m⟩⟩
  · rintro ⟨hsub, ⟨m⟩⟩
    exact ⟨m, fun m' => hsub.elim m m'⟩

end Lemmatheca.MathematicalLogic.FirstOrderNormalForms
