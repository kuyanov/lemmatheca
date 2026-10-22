import Lemmatheca.FiniteRoundComparison.NativeSyntax

/-! Finite game trees retain each selected pair and all earlier tuple values. -/

namespace Lemmatheca.ModelTheory.FiniteRoundComparison

open FirstOrder FirstOrder.Language

variable {L : Language.{0, 0}} {M N : Type} [L.Structure M] [L.Structure N]

/-- The recursive finite back-and-forth condition. -/
def Wins : (k : ℕ) → {n : ℕ} → (Fin n → M) → (Fin n → N) → Prop
  | 0, _, a, b => AtomicMatch (L := L) a b
  | k + 1, _, a, b => AtomicMatch (L := L) a b ∧
      (∀ x : M, ∃ y : N, Wins k (Fin.snoc a x) (Fin.snoc b y)) ∧
      (∀ y : N, ∃ x : M, Wins k (Fin.snoc a x) (Fin.snoc b y))

/-- A full winning strategy tree: responses for either first-move side and winning continuations. -/
def WinningStrategy : (k : ℕ) → {n : ℕ} → (Fin n → M) → (Fin n → N) → Type
  | 0, _, a, b => PLift (AtomicMatch (L := L) a b)
  | k + 1, _, a, b => PLift (AtomicMatch (L := L) a b) ×
      ((x : M) → Σ y : N, WinningStrategy k (Fin.snoc a x) (Fin.snoc b y)) ×
      ((y : N) → Σ x : M, WinningStrategy k (Fin.snoc a x) (Fin.snoc b y))

theorem strategy_iff_wins (k : ℕ) {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    Nonempty (WinningStrategy (L := L) k a b) ↔ Wins (L := L) k a b := by
  classical
  induction k generalizing n with
  | zero => simp [WinningStrategy, Wins]
  | succ k ih =>
    constructor
    · rintro ⟨p⟩
      refine ⟨p.1.down, ?_, ?_⟩
      · intro x
        exact ⟨(p.2.1 x).1, (ih _ _).mp ⟨(p.2.1 x).2⟩⟩
      · intro y
        exact ⟨(p.2.2 y).1, (ih _ _).mp ⟨(p.2.2 y).2⟩⟩
    · rintro ⟨ha, hf, hb⟩
      choose f hf using hf
      choose g hg using hb
      refine ⟨⟨⟨ha⟩, ?_, ?_⟩⟩
      · intro x
        exact ⟨f x, Classical.choice ((ih _ _).mpr (hf x))⟩
      · intro y
        exact ⟨g y, Classical.choice ((ih _ _).mpr (hg y))⟩

theorem wins_mono {k : ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    Wins (L := L) (k + 1) a b → Wins (L := L) k a b := by
  induction k generalizing n with
  | zero => exact fun h => h.1
  | succ k ih =>
    rintro ⟨ha, hf, hb⟩
    refine ⟨ha, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := hf x
      exact ⟨y, ih hy⟩
    · intro y
      obtain ⟨x, hx⟩ := hb y
      exact ⟨x, ih hx⟩

theorem wins_atomic {k : ℕ} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : Wins (L := L) k a b) : AtomicMatch (L := L) a b := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem repeated_response {k n : ℕ} {a : Fin n → M} {b : Fin n → N}
    {x : M} {y : N} (h : Wins (L := L) k (Fin.snoc a x) (Fin.snoc b y))
    (i : Fin n) (hi : x = a i) : y = b i := by
  have he := ((atomicMatch_iff (L := L) _ _).mp (wins_atomic h)).1
    (Fin.last n) (Fin.castSucc i)
  exact by simpa [hi] using he.mp (by simp [hi])

private theorem wins_bounded [L.IsRelational] :
    ∀ {n : ℕ} (φ : L.BoundedFormula Empty n) {k : ℕ}
      (a : Fin n → M) (b : Fin n → N),
      quantifierRank φ ≤ k → Wins (L := L) k a b →
      (φ.Realize default a ↔ φ.Realize default b) := by
  intro n φ
  induction φ with
  | falsum => intro k a b hr h; rfl
  | equal t u =>
    intro k a b hr h
    obtain ⟨i, hi⟩ := atomicFormula_complete (L := L) (.equal t u) (.equal t u)
    rw [← hi]
    exact wins_atomic h i
  | rel R ts =>
    intro k a b hr h
    obtain ⟨i, hi⟩ := atomicFormula_complete (L := L) (.rel R ts) (.rel R ts)
    rw [← hi]
    exact wins_atomic h i
  | imp φ ψ ihφ ihψ =>
    intro k a b hr h
    have hp : quantifierRank φ ≤ k := (le_max_left _ _).trans hr
    have hq : quantifierRank ψ ≤ k := (le_max_right _ _).trans hr
    simp only [BoundedFormula.realize_imp]
    exact imp_congr (ihφ a b hp h) (ihψ a b hq h)
  | all φ ih =>
    intro k a b hr h
    cases k with
    | zero => simp [quantifierRank] at hr
    | succ k =>
      have hp : quantifierRank φ ≤ k := Nat.le_of_succ_le_succ hr
      simp only [BoundedFormula.realize_all]
      constructor
      · intro ha y
        obtain ⟨x, hx⟩ := h.2.2 y
        exact (ih _ _ hp hx).mp (ha x)
      · intro hb x
        obtain ⟨y, hy⟩ := h.2.1 x
        exact (ih _ _ hp hy).mpr (hb y)

theorem wins_preserves_formulas [L.IsRelational]
    {k n : ℕ} {a : Fin n → M} {b : Fin n → N} (h : Wins (L := L) k a b) :
    RankAgreement (L := L) k a b := by
  intro φ hφ
  have hb := wins_bounded (tupleBounded φ) a b
    (by rw [quantifierRank_tupleBounded]; exact hφ) h
  exact (tupleBounded_realize φ a).symm.trans (hb.trans (tupleBounded_realize φ b))

end Lemmatheca.ModelTheory.FiniteRoundComparison
