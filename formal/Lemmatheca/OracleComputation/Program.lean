import Lemmatheca.UniversalComputation.UniversalComputation

/-! The ordinary paired program syntax with one Boolean membership query. -/
namespace Lemmatheca.ComputabilityTheory.OracleComputation

open UniversalComputation

set_option backward.isDefEq.respectTransparency false

inductive Code
  | zero | succ | left | right | query
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | find' : Code → Code
  deriving DecidableEq

noncomputable def eval (A : Set ℕ) : Code → ℕ → Part ℕ
  | .zero, _ => Part.some 0
  | .succ, x => Part.some (x + 1)
  | .left, x => Part.some x.unpair.1
  | .right, x => Part.some x.unpair.2
  | .query, x => Part.some (indicator (fun q => q ∈ A) x)
  | .pair c d, x => (eval A c x).bind fun u => (eval A d x).map (Nat.pair u)
  | .comp c d, x => (eval A d x).bind (eval A c)
  | .prec c d, x =>
      x.unpair.2.rec (eval A c x.unpair.1) fun j previous =>
        previous.bind fun value => eval A d (Nat.pair x.unpair.1 (Nat.pair j value))
  | .find' c, x =>
      (Nat.rfind fun j => (eval A c (Nat.pair x.unpair.1 (j + x.unpair.2))).map
        (fun value => decide (value = 0))).map (fun j => j + x.unpair.2)

def embed : Nat.Partrec.Code → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair c d => .pair (embed c) (embed d)
  | .comp c d => .comp (embed c) (embed d)
  | .prec c d => .prec (embed c) (embed d)
  | .rfind' c => .find' (embed c)

def PartialComputable (A : Set ℕ) (f : ℕ → Part ℕ) : Prop :=
  ∃ c : Code, eval A c = f

def zeroTest : Nat.Partrec.Code :=
  .comp (.prec (.comp .succ .zero) .zero) (.pair .zero (.pair .left .right))

def complementQuery : Code := .comp (embed zeroTest) .query

theorem initial_evaluations (A : Set ℕ) (x : ℕ) :
    eval A .zero x = Part.some 0 ∧
      eval A .succ x = Part.some (x + 1) ∧
      eval A .left x = Part.some x.unpair.1 ∧
      eval A .right x = Part.some x.unpair.2 ∧
      eval A .query x = Part.some (indicator (fun q => q ∈ A) x) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem eval_pair (A : Set ℕ) (c d : Code) (x y : ℕ) :
    y ∈ eval A (.pair c d) x ↔
      ∃ u v, u ∈ eval A c x ∧ v ∈ eval A d x ∧ y = Nat.pair u v := by
  simp only [eval, Part.mem_bind_iff, Part.mem_map_iff]
  aesop

theorem eval_comp (A : Set ℕ) (c d : Code) (x y : ℕ) :
    y ∈ eval A (.comp c d) x ↔
      ∃ v, v ∈ eval A d x ∧ y ∈ eval A c v := by
  exact Part.mem_bind_iff

theorem eval_prec_zero (A : Set ℕ) (c d : Code) (a : ℕ) :
    eval A (.prec c d) (Nat.pair a 0) = eval A c a := by
  simp [eval]

theorem eval_prec_succ (A : Set ℕ) (c d : Code) (a n : ℕ) :
    eval A (.prec c d) (Nat.pair a (n + 1)) =
      (eval A (.prec c d) (Nat.pair a n)).bind
        (fun value => eval A d (Nat.pair a (Nat.pair n value))) := by
  simp [eval]

theorem eval_find (A : Set ℕ) (c : Code) (a m j : ℕ) :
    j ∈ eval A (.find' c) (Nat.pair a m) ↔
      m ≤ j ∧ 0 ∈ eval A c (Nat.pair a j) ∧
        ∀ i, m ≤ i → i < j → ∃ value, value ∈ eval A c (Nat.pair a i) ∧ 0 < value := by
  rw [eval]
  simp only [Nat.unpair_pair]
  rw [Part.mem_map_iff]
  simp only [Nat.mem_rfind, Part.mem_map_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨k, ⟨⟨v, hv, hv0⟩, hk⟩, rfl⟩
    subst v
    refine ⟨by omega, hv, ?_⟩
    intro i hmi hik
    obtain ⟨v, hv, hn⟩ := hk (m := i - m) (by omega)
    refine ⟨v, ?_, Nat.pos_of_ne_zero hn⟩
    simpa [Nat.sub_add_cancel hmi] using hv
  · rintro ⟨hmj, hj, hi⟩
    refine ⟨j - m, ⟨⟨0, ?_, rfl⟩, ?_⟩, Nat.sub_add_cancel hmj⟩
    · simpa [Nat.sub_add_cancel hmj] using hj
    · intro k hk
      obtain ⟨v, hv, hp⟩ := hi (k + m) (by omega) (by omega)
      exact ⟨v, hv, Nat.ne_of_gt hp⟩

theorem eval_embed (A : Set ℕ) (c : Nat.Partrec.Code) (x : ℕ) :
    eval A (embed c) x = Nat.Partrec.Code.eval c x := by
  induction c generalizing x with
  | zero | succ | left | right => rfl
  | pair c d hc hd => simp [embed, eval, Nat.Partrec.Code.eval, hc, hd, Seq.seq]
  | comp c d hc hd => simp only [embed, eval, Nat.Partrec.Code.eval, funext hc, hd,
      Part.bind_eq_bind]
  | prec c d hc hd => simp [embed, eval, Nat.Partrec.Code.eval, Nat.unpaired, hc, hd]
  | rfind' c hc => simp [embed, eval, Nat.Partrec.Code.eval, Nat.unpaired, hc]

theorem ordinary_inclusion (A : Set ℕ) {f : ℕ → Part ℕ} (hf : Nat.Partrec f) :
    PartialComputable A f := by
  obtain ⟨c, rfl⟩ := Nat.Partrec.Code.exists_code.1 hf
  exact ⟨embed c, funext (eval_embed A c)⟩

theorem zeroTest_eval (x : ℕ) :
    Nat.Partrec.Code.eval zeroTest x = Part.some (if x = 0 then 1 else 0) := by
  rw [← eval_embed (∅ : Set ℕ) zeroTest x]
  simp only [zeroTest, embed, eval, Part.map_some, Part.bind_some, Nat.pair_unpair,
    Nat.unpair_pair]
  cases x with
  | zero => simp
  | succ n =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      induction n with
      | zero =>
          change (Part.some 1).bind (fun _ : ℕ => Part.some 0) = Part.some 0
          exact Part.bind_some _ _
      | succ n ih =>
          change ((Nat.rec (motive := fun _ => Part ℕ) (Part.some 1)
            (fun _ p => p.bind fun _ => Part.some 0) n).bind
            (fun _ => Part.some 0)).bind (fun _ => Part.some 0) = Part.some 0
          rw [ih]
          exact Part.bind_some _ _

theorem complement_query_eval (A : Set ℕ) (x : ℕ) :
    eval A complementQuery x = Part.some (indicator (fun q => q ∈ Aᶜ) x) := by
  classical
  simp [complementQuery, eval, eval_embed, zeroTest_eval, indicator]

end Lemmatheca.ComputabilityTheory.OracleComputation
