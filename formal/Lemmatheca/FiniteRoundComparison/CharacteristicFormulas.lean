import Lemmatheca.FiniteRoundComparison.Games

/-! Actual finite characteristic formulas, indexed by finite truth-profile data. -/

namespace Lemmatheca.ModelTheory.FiniteRoundComparison

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}}

instance finiteAtomicIndex [Finite (Σ r : ℕ, L.Relations r)] (n : ℕ) :
    Finite (AtomicIndex L n) := by
  classical
  let : Fintype (Σ r : ℕ, L.Relations r) := Fintype.ofFinite _
  have h : Finite (Σ r : ℕ, L.Relations r × (Fin r → Fin n)) := by
    let f : (Σ r : ℕ, L.Relations r × (Fin r → Fin n)) →
        (Σ R : (Σ r : ℕ, L.Relations r), Fin R.1 → Fin n) :=
      fun ⟨r, R, v⟩ => ⟨⟨r, R⟩, v⟩
    exact Finite.of_injective f (by
      rintro ⟨r, R, v⟩ ⟨r', R', v'⟩ he
      cases he
      rfl)
  exact inferInstance

private theorem relational_free_term [L.IsRelational] {n : ℕ}
    (t : L.Term (Fin n ⊕ Fin 0)) : ∃ i : Fin n, t = .var (.inl i) := by
  cases t with
  | var x =>
    cases x with
    | inl i => exact ⟨i, rfl⟩
    | inr i => exact Fin.elim0 i
  | func f ts => exact isEmptyElim f

theorem atomic_formulas_finite [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    (n : ℕ) : {φ : L.Formula (Fin n) | φ.IsAtomic}.Finite := by
  classical
  let f : AtomicIndex L n → L.Formula (Fin n)
    | .inl ⟨i, j⟩ => (Term.var i).equal (.var j)
    | .inr ⟨r, R, v⟩ => R.formula (fun i => .var (v i))
  refine (Set.finite_range f).subset ?_
  intro φ hφ
  cases hφ with
  | equal t u =>
    obtain ⟨i, rfl⟩ := relational_free_term t
    obtain ⟨j, rfl⟩ := relational_free_term u
    exact ⟨.inl ⟨i, j⟩, rfl⟩
  | @rel r R ts =>
    choose v hv using fun i => relational_free_term (ts i)
    refine ⟨.inr ⟨r, R, v⟩, ?_⟩
    change BoundedFormula.rel R (fun i => .var (.inl (v i))) = .rel R ts
    congr 1
    exact funext fun i => (hv i).symm

/-- Finite truth-profile indices; these contain no formula constructors. -/
def Description (L : Language.{0, 0}) : ℕ → ℕ → Type
  | 0, n => AtomicIndex L n → Bool
  | k + 1, n => (AtomicIndex L n → Bool) × (Description L k (n + 1) → Bool)

instance finiteDescription [Finite (Σ r : ℕ, L.Relations r)] (k n : ℕ) :
    Finite (Description L k n) := by
  induction k generalizing n with
  | zero => change Finite (AtomicIndex L n → Bool); infer_instance
  | succ k ih =>
    have : Finite (Description L k (n + 1)) := ih (n + 1)
    change Finite ((AtomicIndex L n → Bool) × (Description L k (n + 1) → Bool))
    infer_instance

/-- Select the native atom or its negation for every atomic truth value. -/
noncomputable def atomicDescription [Finite (Σ r : ℕ, L.Relations r)]
    (n : ℕ) (s : AtomicIndex L n → Bool) : L.BoundedFormula Empty n :=
  BoundedFormula.iInf fun i => if s i then atomicFormula n i else (atomicFormula n i).not

/-- The characteristic formula for an index, using every previous existential test or its negation. -/
noncomputable def characteristic [Finite (Σ r : ℕ, L.Relations r)] :
    (k n : ℕ) → Description L k n → L.BoundedFormula Empty n
  | 0, n, d => atomicDescription n d
  | k + 1, n, (d, s) => atomicDescription n d ⊓
      BoundedFormula.iInf (fun e : Description L k (n + 1) =>
        if s e then (characteristic k (n + 1) e).ex
        else (characteristic k (n + 1) e).ex.not)

/-- The same actual characteristic formula with the tuple context as free variables. -/
noncomputable def characteristicFormula [Finite (Σ r : ℕ, L.Relations r)]
    (k n : ℕ) (d : Description L k n) : L.Formula (Fin n) :=
  tupleFormula (characteristic k n d)

/-- The atomic truth vector of a specified tuple. -/
noncomputable def atomicProfile {M : Type} [L.Structure M] {n : ℕ} (a : Fin n → M) :
    AtomicIndex L n → Bool := by
  classical
  exact fun i => decide ((atomicFormula n i).Realize default a)

/-- The actual finite profile: old atoms and the previous descriptions realized by an extension. -/
noncomputable def profile [Finite (Σ r : ℕ, L.Relations r)]
    {M : Type} [L.Structure M] : (k n : ℕ) → (Fin n → M) → Description L k n
  | 0, _, a => atomicProfile (L := L) a
  | k + 1, n, a => by
      classical
      exact (atomicProfile (L := L) a, fun d => decide (∃ x : M,
        (characteristic k (n + 1) d).Realize default (Fin.snoc a x)))

private theorem rank_iInf_le {α ι : Type} [Finite ι] {n : ℕ}
    (f : ι → L.BoundedFormula α n) (k : ℕ) (h : ∀ i, quantifierRank (f i) ≤ k) :
    quantifierRank (BoundedFormula.iInf f) ≤ k := by
  classical
  let := Fintype.ofFinite ι
  change quantifierRank ((Finset.univ.toList.map f).foldr (· ⊓ ·) ⊤) ≤ k
  generalize (Finset.univ : Finset ι).toList = l
  induction l with
  | nil => simp [quantifierRank]
  | cons i l ih =>
    simp only [List.map_cons, List.foldr_cons, quantifierRank_inf]
    exact max_le (h i) ih

private theorem atomicDescription_rank [Finite (Σ r : ℕ, L.Relations r)]
    (n : ℕ) (d : AtomicIndex L n → Bool) :
    quantifierRank (atomicDescription n d) ≤ 0 := by
  apply rank_iInf_le
  intro i
  have hi : quantifierRank (atomicFormula (L := L) n i) = 0 := by cases i <;> rfl
  cases d i <;> simp [quantifierRank_not, hi]

private theorem characteristic_bounded_rank [Finite (Σ r : ℕ, L.Relations r)]
    (k n : ℕ) (d : Description L k n) :
    quantifierRank (characteristic k n d) ≤ k := by
  induction k generalizing n with
  | zero => exact atomicDescription_rank n d
  | succ k ih =>
    rcases d with ⟨d, e⟩
    rw [characteristic, quantifierRank_inf]
    refine max_le ((atomicDescription_rank n d).trans (Nat.zero_le _)) ?_
    apply rank_iInf_le
    intro i
    cases e i <;>
      simp only [Bool.false_eq_true, ↓reduceIte, quantifierRank_not, quantifierRank_ex]
    · exact Nat.add_le_add_right (ih (n + 1) i) 1
    · exact Nat.add_le_add_right (ih (n + 1) i) 1

private theorem selected_realize {M : Type} [L.Structure M] {n : ℕ}
    (φ : L.BoundedFormula Empty n) (d : Bool) (a : Fin n → M) :
    (if d then φ else φ.not).Realize default a ↔
      @decide (φ.Realize default a) (Classical.propDecidable _) = d := by
  classical
  cases d <;> simp [BoundedFormula.realize_not]

private theorem atomicDescription_realize [Finite (Σ r : ℕ, L.Relations r)]
    {M : Type} [L.Structure M] (n : ℕ) (a : Fin n → M) (d : AtomicIndex L n → Bool) :
    (atomicDescription n d).Realize default a ↔ atomicProfile (L := L) a = d := by
  classical
  simp only [atomicDescription, BoundedFormula.realize_iInf, selected_realize, funext_iff,
    atomicProfile]

private theorem characteristic_bounded_realize [Finite (Σ r : ℕ, L.Relations r)]
    {M : Type} [L.Structure M] (k n : ℕ) (a : Fin n → M) (d : Description L k n) :
    (characteristic k n d).Realize default a ↔ profile (L := L) k n a = d := by
  classical
  cases k with
  | zero => exact atomicDescription_realize n a d
  | succ k =>
    rcases d with ⟨d, s⟩
    simp only [characteristic, BoundedFormula.realize_inf, atomicDescription_realize,
      BoundedFormula.realize_iInf, selected_realize, BoundedFormula.realize_ex,
      profile, funext_iff]
    constructor
    · rintro ⟨ha, hb⟩
      exact Prod.ext (funext ha) (funext hb)
    · intro h
      exact ⟨fun i => congrFun (congrArg Prod.fst h) i,
        fun i => congrFun (congrArg Prod.snd h) i⟩

theorem characteristic_rank [Finite (Σ r : ℕ, L.Relations r)]
    (k n : ℕ) (d : Description L k n) :
    quantifierRank (characteristicFormula k n d) ≤ k := by
  rw [characteristicFormula, quantifierRank_tupleFormula]
  exact characteristic_bounded_rank k n d

theorem characteristic_realize [Finite (Σ r : ℕ, L.Relations r)]
    {M : Type} [L.Structure M] (k n : ℕ) (a : Fin n → M) (d : Description L k n) :
    (characteristicFormula k n d).Realize a ↔ profile (L := L) k n a = d := by
  rw [characteristicFormula, tupleFormula_realize]
  exact characteristic_bounded_realize k n a d

theorem characteristic_family_finite [Finite (Σ r : ℕ, L.Relations r)] (k n : ℕ) :
    (Set.range (characteristicFormula (L := L) k n)).Finite := by
  exact Set.finite_range _

theorem characteristic_unique [Finite (Σ r : ℕ, L.Relations r)]
    {M : Type} [L.Structure M] (k n : ℕ) (a : Fin n → M) :
    ∃! d : Description L k n, (characteristicFormula k n d).Realize a := by
  refine ⟨profile (L := L) k n a, (characteristic_realize k n a _).mpr rfl, ?_⟩
  intro d hd
  exact ((characteristic_realize k n a d).mp hd).symm

private theorem atomicProfile_eq_iff {M N : Type} [L.Structure M] [L.Structure N]
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    atomicProfile (L := L) a = atomicProfile (L := L) b ↔ AtomicMatch (L := L) a b := by
  classical
  simp [funext_iff, atomicProfile, AtomicMatch]

private theorem profile_eq_wins [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    {M N : Type} [L.Structure M] [L.Structure N]
    (k n : ℕ) (a : Fin n → M) (b : Fin n → N)
    (h : profile (L := L) k n a = profile (L := L) k n b) : Wins (L := L) k a b := by
  classical
  induction k generalizing n with
  | zero => exact (atomicProfile_eq_iff a b).mp h
  | succ k ih =>
    have ha : AtomicMatch (L := L) a b :=
      (atomicProfile_eq_iff a b).mp (congrArg Prod.fst h)
    have he := congrArg Prod.snd h
    simp only [profile] at he
    refine ⟨ha, ?_, ?_⟩
    · intro x
      let d := profile (L := L) k (n + 1) (Fin.snoc a x)
      have hx : (characteristic k (n + 1) d).Realize default (Fin.snoc a x) :=
        (characteristic_bounded_realize k (n + 1) _ d).mpr rfl
      have hex : ∃ y : N, (characteristic k (n + 1) d).Realize default (Fin.snoc b y) := by
        apply of_decide_eq_true
        rw [← congrFun he d]
        exact decide_eq_true (show ∃ x : M,
          (characteristic k (n + 1) d).Realize default (Fin.snoc a x) from ⟨x, hx⟩)
      obtain ⟨y, hy⟩ := hex
      refine ⟨y, ih (n + 1) _ _ ?_⟩
      exact ((characteristic_bounded_realize k (n + 1) _ d).mp hy).symm
    · intro y
      let d := profile (L := L) k (n + 1) (Fin.snoc b y)
      have hy : (characteristic k (n + 1) d).Realize default (Fin.snoc b y) :=
        (characteristic_bounded_realize k (n + 1) _ d).mpr rfl
      have hex : ∃ x : M, (characteristic k (n + 1) d).Realize default (Fin.snoc a x) := by
        apply of_decide_eq_true
        rw [congrFun he d]
        exact decide_eq_true (show ∃ y : N,
          (characteristic k (n + 1) d).Realize default (Fin.snoc b y) from ⟨y, hy⟩)
      obtain ⟨x, hx⟩ := hex
      refine ⟨x, ih (n + 1) _ _ ?_⟩
      exact (characteristic_bounded_realize k (n + 1) _ d).mp hx

theorem characteristic_agreement [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    {M N : Type} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    {k n : ℕ} {a : Fin n → M} {b : Fin n → N} (d : Description L k n)
    (ha : (characteristicFormula k n d).Realize a)
    (hb : (characteristicFormula k n d).Realize b) :
    RankAgreement (L := L) k a b := by
  apply wins_preserves_formulas
  apply profile_eq_wins
  exact ((characteristic_realize _ _ _ d).mp ha).trans
    ((characteristic_realize _ _ _ d).mp hb).symm

theorem agreement_forth [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    {M N : Type} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    {k n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : RankAgreement (L := L) (k + 1) a b) (x : M) :
    ∃ y : N, RankAgreement (L := L) k (Fin.snoc a x) (Fin.snoc b y) := by
  let d := profile (L := L) k (n + 1) (Fin.snoc a x)
  let θ : L.Formula (Fin n) := tupleFormula (characteristic k (n + 1) d).ex
  have hqr : quantifierRank θ ≤ k + 1 := by
    rw [quantifierRank_tupleFormula, quantifierRank_ex]
    exact Nat.add_le_add_right (characteristic_bounded_rank k (n + 1) d) 1
  have hx : (characteristic k (n + 1) d).Realize default (Fin.snoc a x) :=
    (characteristic_bounded_realize _ _ _ d).mpr rfl
  have hθ : θ.Realize a :=
    (tupleFormula_realize _ a).mpr (BoundedFormula.realize_ex.mpr ⟨x, hx⟩)
  have hθ' := (h θ hqr).mp hθ
  obtain ⟨y, hy⟩ := BoundedFormula.realize_ex.mp ((tupleFormula_realize _ b).mp hθ')
  refine ⟨y, characteristic_agreement d ?_ ?_⟩
  · exact (tupleFormula_realize _ _).mpr hx
  · exact (tupleFormula_realize _ _).mpr hy

theorem agreement_back [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    {M N : Type} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    {k n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : RankAgreement (L := L) (k + 1) a b) (y : N) :
    ∃ x : M, RankAgreement (L := L) k (Fin.snoc a x) (Fin.snoc b y) := by
  have hs : RankAgreement (L := L) (k + 1) b a := fun φ hφ => (h φ hφ).symm
  obtain ⟨x, hx⟩ := agreement_forth hs y
  exact ⟨x, fun φ hφ => (hx φ hφ).symm⟩

theorem ef_theorem [L.IsRelational] [Finite (Σ r : ℕ, L.Relations r)]
    {M N : Type} [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
    (k : ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    Nonempty (WinningStrategy (L := L) k a b) ↔ RankAgreement (L := L) k a b := by
  rw [strategy_iff_wins]
  constructor
  · exact wins_preserves_formulas
  · intro h
    induction k generalizing n with
    | zero => exact (atomicMatch_iff_rank_zero a b).mpr h
    | succ k ih =>
      refine ⟨(atomicMatch_iff_rank_zero a b).mpr (fun φ hφ =>
        h φ (hφ.trans (Nat.zero_le _))), ?_, ?_⟩
      · intro x
        obtain ⟨y, hy⟩ := agreement_forth h x
        exact ⟨y, ih _ _ hy⟩
      · intro y
        obtain ⟨x, hx⟩ := agreement_back h y
        exact ⟨x, ih _ _ hx⟩

end Lemmatheca.ModelTheory.FiniteRoundComparison
