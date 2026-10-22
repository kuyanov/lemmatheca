import Lemmatheca.BackAndForth.BackAndForth

/-! Quantifier rank and finite atomic positions in the existing first-order syntax. -/

namespace Lemmatheca.ModelTheory.FiniteRoundComparison

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}}

/-- Quantifier nesting depth in the native formula representation. -/
def quantifierRank {α : Type} : {n : ℕ} → L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (quantifierRank φ) (quantifierRank ψ)
  | _, .all φ => quantifierRank φ + 1

theorem quantifierRank_not {α : Type} {n : ℕ} (φ : L.BoundedFormula α n) :
    quantifierRank φ.not = quantifierRank φ := by
  simp [quantifierRank]

theorem quantifierRank_inf {α : Type} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊓ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  change quantifierRank ((φ.imp ψ.not).not) = _
  rw [quantifierRank_not]
  change max (quantifierRank φ) (quantifierRank ψ.not) = _
  rw [quantifierRank_not]

theorem quantifierRank_sup {α : Type} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊔ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  change max (quantifierRank φ.not) (quantifierRank ψ) = _
  rw [quantifierRank_not]

theorem quantifierRank_ex {α : Type} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    quantifierRank φ.ex = quantifierRank φ + 1 := by
  change quantifierRank φ.not.all.not = _
  rw [quantifierRank_not]
  change quantifierRank φ.not + 1 = _
  rw [quantifierRank_not]

/-- Regard the in-scope tuple slots as ordinary free variables. -/
def tupleFormula {n : ℕ} (φ : L.BoundedFormula Empty n) : L.Formula (Fin n) :=
  φ.toFormula.relabel (Sum.elim Empty.elim id)

/-- Put a formula's free tuple variables into the native in-scope tuple slots. -/
def tupleBounded {n : ℕ} (φ : L.Formula (Fin n)) : L.BoundedFormula Empty n :=
  BoundedFormula.relabel (Sum.inr : Fin n → Empty ⊕ Fin n) φ

theorem tupleFormula_realize {M : Type} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) (a : Fin n → M) :
    (tupleFormula φ).Realize a ↔ φ.Realize default a := by
  rw [tupleFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hfree : ((a ∘ Sum.elim Empty.elim id) ∘ Sum.inl : Empty → M) = default :=
    Subsingleton.elim _ _
  have hbound : (a ∘ Sum.elim Empty.elim id) ∘ Sum.inr = a := rfl
  rw [hfree, hbound]

theorem tupleBounded_realize {M : Type} [L.Structure M] {n : ℕ}
    (φ : L.Formula (Fin n)) (a : Fin n → M) :
    (tupleBounded φ).Realize default a ↔ φ.Realize a := by
  exact Formula.realize_relabel_sumInr φ

theorem rank_relabel {α β : Type} {m n : ℕ}
    (φ : L.BoundedFormula α n) (f : α → β ⊕ Fin m) :
    quantifierRank (φ.relabel f) = quantifierRank φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => exact congrArg₂ max ihφ ihψ
  | all φ ih => simpa only [BoundedFormula.relabel_all, quantifierRank] using congrArg (· + 1) ih

theorem quantifierRank_tupleFormula {n : ℕ} (φ : L.BoundedFormula Empty n) :
    quantifierRank (tupleFormula φ) = quantifierRank φ := by
  rw [tupleFormula, Formula.relabel, rank_relabel]
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => exact congrArg₂ max ihφ ihψ
  | all φ ih => simpa only [BoundedFormula.toFormula, Formula.relabel, quantifierRank,
      rank_relabel] using congrArg (· + 1) ih

theorem quantifierRank_tupleBounded {n : ℕ} (φ : L.Formula (Fin n)) :
    quantifierRank (tupleBounded φ) = quantifierRank φ := by
  exact rank_relabel _ _

/-- Agreement on actual formulas in the specified finite free-variable context. -/
def RankAgreement {M N : Type} [L.Structure M] [L.Structure N]
    (k : ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ φ : L.Formula (Fin n), quantifierRank φ ≤ k → (φ.Realize a ↔ φ.Realize b)

/-- Finite index data for atomic formulas, not a replacement formula syntax. -/
abbrev AtomicIndex (L : Language.{0, 0}) (n : ℕ) :=
  (Fin n × Fin n) ⊕ (Σ r : ℕ, L.Relations r × (Fin r → Fin n))

/-- The actual equality or relation formula at an atomic index. -/
def atomicFormula (n : ℕ) : AtomicIndex L n → L.BoundedFormula Empty n
  | .inl ⟨i, j⟩ => .equal (.var (.inr i)) (.var (.inr j))
  | .inr ⟨_, R, v⟩ => .rel R (fun i => .var (.inr (v i)))

/-- Equality and every relation agree on the displayed tuples, including nullary relations. -/
def AtomicMatch {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ i : AtomicIndex L n,
    (atomicFormula n i).Realize default a ↔ (atomicFormula n i).Realize default b

private theorem relational_term_var [L.IsRelational] {α : Type} (t : L.Term α) :
    ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f _ => exact isEmptyElim f

/-- Every atomic native formula in a relational language occurs in the indexed list. -/
theorem atomicFormula_complete [L.IsRelational] {n : ℕ}
    (φ : L.BoundedFormula Empty n) (hφ : φ.IsAtomic) :
    ∃ i : AtomicIndex L n, atomicFormula n i = φ := by
  cases hφ with
  | equal t u =>
    obtain ⟨i, rfl⟩ := relational_term_var t
    obtain ⟨j, rfl⟩ := relational_term_var u
    cases i with
    | inl i => exact i.elim
    | inr i =>
      cases j with
      | inl j => exact j.elim
      | inr j => exact ⟨.inl (i, j), rfl⟩
  | rel R ts =>
    choose v hv using fun i => relational_term_var (ts i)
    let f := fun i => (v i).elim Empty.elim id
    have ht : ts = fun i => Term.var (Sum.inr (f i)) := by
      funext i
      rw [hv i]
      dsimp only [f]
      cases v i with
      | inl x => exact x.elim
      | inr x => rfl
    exact ⟨.inr ⟨_, R, f⟩, by rw [ht]; rfl⟩

theorem atomicMatch_iff {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    AtomicMatch (L := L) a b ↔
      (∀ i j, a i = a j ↔ b i = b j) ∧
      ∀ r (R : L.Relations r) (v : Fin r → Fin n),
        Structure.RelMap R (a ∘ v) ↔ Structure.RelMap R (b ∘ v) := by
  constructor
  · intro h
    refine ⟨fun i j => h (.inl (i, j)), fun r R v => ?_⟩
    exact h (.inr ⟨r, R, v⟩)
  · rintro ⟨heq, hrel⟩ (⟨i, j⟩ | ⟨r, R, v⟩)
    · exact heq i j
    · exact hrel r R v

private theorem atomic_agreement [L.IsRelational]
    {M N : Type} [L.Structure M] [L.Structure N] {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (h : AtomicMatch (L := L) a b)
    (φ : L.Formula (Fin n)) (hφ : φ.IsAtomic) : φ.Realize a ↔ φ.Realize b := by
  obtain ⟨i, hi⟩ := atomicFormula_complete (tupleBounded φ) (hφ.relabel Sum.inr)
  have hh := h i
  rw [hi] at hh
  exact (tupleBounded_realize φ a).symm.trans (hh.trans (tupleBounded_realize φ b))

private theorem rank_zero_qf {α : Type} {n : ℕ} (φ : L.BoundedFormula α n)
    (h : quantifierRank φ = 0) : φ.IsQF := by
  induction φ with
  | falsum => exact .falsum
  | equal t u => exact (BoundedFormula.IsAtomic.equal t u).isQF
  | rel R ts => exact (BoundedFormula.IsAtomic.rel R ts).isQF
  | imp φ ψ ihφ ihψ =>
    have hm : max (quantifierRank φ) (quantifierRank ψ) ≤ 0 := Nat.le_of_eq h
    exact (ihφ (Nat.eq_zero_of_le_zero (max_le_iff.mp hm).1)).imp
      (ihψ (Nat.eq_zero_of_le_zero (max_le_iff.mp hm).2))
  | all φ _ => simp [quantifierRank] at h

theorem atomicMatch_iff_partialIso [L.IsRelational]
    {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    AtomicMatch (L := L) a b ↔
      ∃ p : BackAndForth.FinitePartialIso L M N,
        p.dom = Set.range a ∧ Set.range p.toFun = Set.range b ∧
        ∀ i, ∃ hi : a i ∈ p.dom, p.toFun ⟨a i, hi⟩ = b i := by
  classical
  constructor
  · intro h
    have heq := (atomicMatch_iff a b).mp h |>.1
    let f : Set.range a → N := fun x => b (Classical.choose x.property)
    have hcoord (i : Fin n) : f ⟨a i, Set.mem_range_self i⟩ = b i := by
      exact (heq _ i).mp (Classical.choose_spec (Set.mem_range_self i))
    let p : BackAndForth.FinitePartialIso L M N := {
      dom := Set.range a
      finite_dom := Set.finite_range a
      toFun := f
      injective := by
        intro x y hxy
        have hx : a (Classical.choose x.property) = x := Classical.choose_spec x.property
        have hy : a (Classical.choose y.property) = y := Classical.choose_spec y.property
        exact Subtype.ext (hx.symm.trans (((heq _ _).mpr hxy).trans hy))
      atomic := by
        intro r φ hφ c
        let t : Fin r → Fin n := fun i => Classical.choose (c i).property
        have ht : a ∘ t = Subtype.val ∘ c := by
          funext i; exact Classical.choose_spec (c i).property
        have hh := atomic_agreement h (φ.relabel t) (hφ.relabel (Sum.inl ∘ t))
        rw [Formula.realize_relabel, Formula.realize_relabel, ht] at hh
        exact hh.symm }
    refine ⟨p, rfl, ?_, fun i => ⟨Set.mem_range_self i, hcoord i⟩⟩
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Classical.choose x.property, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨a i, Set.mem_range_self i⟩, hcoord i⟩
  · rintro ⟨p, _, _, htuple⟩
    choose hi hb using htuple
    let c : Fin n → p.dom := fun i => ⟨a i, hi i⟩
    have hc : p.toFun ∘ c = b := funext hb
    apply (atomicMatch_iff a b).mpr
    constructor
    · intro i j
      have hh := p.atomic ((Term.var i).equal (.var j)) (.equal _ _) c
      rw [hc] at hh
      exact hh.symm
    · intro r R v
      have hh := p.atomic (.rel R (fun i => .var (.inl (v i)))) (.rel _ _) c
      rw [hc] at hh
      exact hh.symm

theorem atomicMatch_iff_rank_zero [L.IsRelational]
    {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    AtomicMatch (L := L) a b ↔ RankAgreement (L := L) 0 a b := by
  constructor
  · intro h φ hφ
    have hq := rank_zero_qf φ (Nat.eq_zero_of_le_zero hφ)
    clear hφ
    induction hq with
    | falsum => rfl
    | of_isAtomic hφ => exact atomic_agreement h _ hφ
    | imp _ _ ihφ ihψ => simp only [Formula.realize_imp, ihφ, ihψ]
  · intro h i
    have hr : quantifierRank (tupleFormula (atomicFormula (L := L) n i)) = 0 := by
      rw [quantifierRank_tupleFormula]
      cases i with
      | inl ij => cases ij; rfl
      | inr rv => cases rv; rfl
    have hh := h (tupleFormula (atomicFormula n i)) (Nat.le_of_eq hr)
    exact (tupleFormula_realize _ a).symm.trans (hh.trans (tupleFormula_realize _ b))

end Lemmatheca.ModelTheory.FiniteRoundComparison
