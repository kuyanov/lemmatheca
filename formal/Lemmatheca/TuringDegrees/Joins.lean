import Lemmatheca.TuringDegrees.Degrees
import Mathlib.Order.BoundedOrder.Lattice

/-! The specified even/odd join and its actual common-oracle program. -/
namespace Lemmatheca.ComputabilityTheory.TuringDegrees

open OracleComputation UniversalComputation

noncomputable section

def join (A B : Set ℕ) : Set ℕ :=
  (fun n : ℕ => 2 * n) '' A ∪ (fun n : ℕ => 2 * n + 1) '' B

private theorem mem_join_iff (A B : Set ℕ) (x : ℕ) :
    x ∈ join A B ↔ (x % 2 = 0 ∧ x / 2 ∈ A) ∨ (x % 2 = 1 ∧ x / 2 ∈ B) := by
  simp only [join, Set.mem_union, Set.mem_image]
  constructor
  · rintro (⟨n, hn, hx⟩ | ⟨n, hn, hx⟩)
    · have hq : x / 2 = n := by omega
      exact Or.inl ⟨by omega, hq.symm ▸ hn⟩
    · have hq : x / 2 = n := by omega
      exact Or.inr ⟨by omega, hq.symm ▸ hn⟩
  · rintro (⟨hx, hA⟩ | ⟨hx, hB⟩)
    · exact Or.inl ⟨x / 2, hA, by omega⟩
    · exact Or.inr ⟨x / 2, hB, by omega⟩

theorem join_indicator (A B : Set ℕ) (x : ℕ) :
    indicator (fun n => n ∈ join A B) x =
      if x % 2 = 0 then indicator (fun n => n ∈ A) (x / 2)
      else indicator (fun n => n ∈ B) (x / 2) := by
  classical
  by_cases h : x % 2 = 0
  · simp [indicator, mem_join_iff, h]
  · have h' : x % 2 = 1 := by omega
    simp [indicator, mem_join_iff, h']

theorem join_even_reduction (A B : Set ℕ) :
    Primrec (fun n : ℕ => 2 * n) ∧ ∀ n, n ∈ A ↔ 2 * n ∈ join A B := by
  exact ⟨Primrec.nat_mul.comp (Primrec.const 2) Primrec.id,
    fun n => by simp [mem_join_iff]⟩

theorem join_odd_reduction (A B : Set ℕ) :
    Primrec (fun n : ℕ => 2 * n + 1) ∧ ∀ n, n ∈ B ↔ 2 * n + 1 ∈ join A B := by
  refine ⟨Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.const 1), fun n => ?_⟩
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [mem_join_iff, hmod, hdiv]

private theorem half_has_code :
    ∃ r : Nat.Partrec.Code, ∀ x, Nat.Partrec.Code.eval r x = Part.some (x / 2) := by
  obtain ⟨r, hr⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.partrec))
  exact ⟨r, fun x => congrFun hr x⟩

def halfCode : Nat.Partrec.Code := Classical.choose half_has_code

theorem halfCode_eval (x : ℕ) :
    Nat.Partrec.Code.eval halfCode x = Part.some (x / 2) := by
  exact Classical.choose_spec half_has_code x

def selectorValue (x : ℕ) : ℕ :=
  if x.unpair.1 % 2 = 0 then x.unpair.2.unpair.1 else x.unpair.2.unpair.2

private theorem selector_has_code :
    ∃ r : Nat.Partrec.Code, ∀ x,
      Nat.Partrec.Code.eval r x = Part.some (selectorValue x) := by
  have hfirst : Primrec (fun x : ℕ => x.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hsecond : Primrec (fun x : ℕ => x.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hselector : Primrec selectorValue :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hfirst (Primrec.const 2))
      (Primrec.const 0)) (hfirst.comp hsecond) (hsecond.comp hsecond)
  obtain ⟨r, hr⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hselector.to_comp.partrec)
  exact ⟨r, fun x => congrFun hr x⟩

def selectorCode : Nat.Partrec.Code := Classical.choose selector_has_code

theorem selectorCode_eval (x a b : ℕ) :
    Nat.Partrec.Code.eval selectorCode (Nat.pair x (Nat.pair a b)) =
      Part.some (if x % 2 = 0 then a else b) := by
  simpa only [selectorCode, selectorValue, Nat.unpair_pair] using
    Classical.choose_spec selector_has_code (Nat.pair x (Nat.pair a b))

def bothProgram (c d : Code) : Code :=
  .pair (.comp c (embed halfCode)) (.comp d (embed halfCode))

def joinProgram (c d : Code) : Code :=
  .comp (embed selectorCode) (.pair (embed Nat.Partrec.Code.id) (bothProgram c d))

theorem bothProgram_eval {A B C : Set ℕ} (c d : Code)
    (hc : Reduces c A C) (hd : Reduces d B C) (x : ℕ) :
    eval C (bothProgram c d) x = Part.some
      (Nat.pair (indicator (fun n => n ∈ A) (x / 2))
        (indicator (fun n => n ∈ B) (x / 2))) := by
  simp only [bothProgram, eval, eval_embed, halfCode_eval, Part.bind_some, hc (x / 2), hd (x / 2),
    Part.map_some]

theorem joinProgram_reduces {A B C : Set ℕ} (c d : Code)
    (hc : Reduces c A C) (hd : Reduces d B C) :
    Reduces (joinProgram c d) (join A B) C := by
  intro x
  simp only [joinProgram, eval, eval_embed, bothProgram_eval c d hc hd,
    Nat.Partrec.Code.eval_id, Part.bind_some, Part.map_some, selectorCode_eval, join_indicator]

private theorem join_left_reducible (A B : Set ℕ) : Reducible A (join A B) :=
  manyOne_imp_reducible ⟨_, (join_even_reduction A B).1.to_comp,
    (join_even_reduction A B).2⟩

private theorem join_right_reducible (A B : Set ℕ) : Reducible B (join A B) :=
  manyOne_imp_reducible ⟨_, (join_odd_reduction A B).1.to_comp,
    (join_odd_reduction A B).2⟩

theorem join_reducible_iff (A B C : Set ℕ) :
    Reducible (join A B) C ↔ Reducible A C ∧ Reducible B C := by
  constructor
  · intro h
    exact ⟨reducible_trans (join_left_reducible A B) h,
      reducible_trans (join_right_reducible A B) h⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨joinProgram c d, joinProgram_reduces c d hc hd⟩

theorem join_degree_congr {A A' B B' : Set ℕ}
    (hA : Equivalent A A') (hB : Equivalent B B') :
    degree (join A B) = degree (join A' B') := by
  apply Quotient.sound
  constructor
  · exact (join_reducible_iff _ _ _).mpr
      ⟨reducible_trans hA.1 (join_left_reducible A' B'),
        reducible_trans hB.1 (join_right_reducible A' B')⟩
  · exact (join_reducible_iff _ _ _).mpr
      ⟨reducible_trans hA.2 (join_left_reducible A B),
        reducible_trans hB.2 (join_right_reducible A B)⟩

def degreeJoin : Degree → Degree → Degree :=
  Quotient.lift₂ (fun A B : Problem => degree (join A.carrier B.carrier))
    (fun _ _ _ _ hA hB => join_degree_congr hA hB)

theorem degreeJoin_degree (A B : Set ℕ) :
    degreeJoin (degree A) (degree B) = degree (join A B) := by
  rfl

theorem degreeJoin_le_iff (a b c : Degree) :
    degreeJoin a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  obtain ⟨B, rfl⟩ := degree_surjective b
  obtain ⟨C, rfl⟩ := degree_surjective c
  rw [degreeJoin_degree]
  exact join_reducible_iff A B C

private theorem degreeJoin_left (a b : Degree) : a ≤ degreeJoin a b := by
  exact ((degreeJoin_le_iff a b _).mp le_rfl).1

private theorem degreeJoin_right (a b : Degree) : b ≤ degreeJoin a b := by
  exact ((degreeJoin_le_iff a b _).mp le_rfl).2

instance degreeSemilatticeSup : SemilatticeSup Degree where
  toPartialOrder := inferInstance
  sup := degreeJoin
  le_sup_left := degreeJoin_left
  le_sup_right := degreeJoin_right
  sup_le _ _ _ ha hb := (degreeJoin_le_iff _ _ _).mpr ⟨ha, hb⟩

instance degreeOrderBot : OrderBot Degree where
  bot := zeroDegree
  bot_le := zeroDegree_le

theorem join_complement_equivalent (A : Set ℕ) : Equivalent (join A Aᶜ) A := by
  exact ⟨(join_reducible_iff _ _ _).mpr ⟨reducible_refl A, (complement_equivalent A).2⟩,
    join_left_reducible A Aᶜ⟩

end
end Lemmatheca.ComputabilityTheory.TuringDegrees
