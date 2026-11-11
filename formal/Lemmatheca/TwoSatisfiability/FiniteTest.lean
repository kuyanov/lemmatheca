import Lemmatheca.TwoSatisfiability.Assignment
import Mathlib.Data.List.Chain

namespace Lemmatheca.MathematicalLogic.TwoSatisfiability
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.DpllSatisfiability (Cnf opposite Models Sat)
universe u
variable {α : Type u}


def IsPath (Γ : Cnf α) (a b : PropLiteral α) (L : List (PropLiteral α)) : Prop :=
  L.head? = some a ∧ L.getLast? = some b ∧ L.IsChain (Edge Γ)

instance pathDecidable [DecidableEq α] (Γ : Cnf α) (a b : PropLiteral α)
    (L : List (PropLiteral α)) : Decidable (IsPath Γ a b L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def boundedPath [Fintype α] [DecidableEq α] (Γ : Cnf α) :
    ℕ → PropLiteral α → PropLiteral α → Bool
  | 0, _, _ => false
  | n+1, a, b => decide (a = b) ||
      decide (∃ c, Edge Γ a c ∧ boundedPath Γ n c b = true)

theorem literal_count [Fintype α] :
    Fintype.card (PropLiteral α) = 2 * Fintype.card α := by
  calc
    Fintype.card (PropLiteral α) = Fintype.card (α × Bool) := Fintype.card_congr literalEquiv
    _ = 2 * Fintype.card α := by simp [Nat.mul_comm]

private theorem path_reach (Γ : Cnf α) (a b : PropLiteral α)
    {L : List (PropLiteral α)} (hp : IsPath Γ a b L) : Reach Γ a b := by
  cases L with
  | nil => simp [IsPath] at hp
  | cons c rest =>
    have ha : c = a := by simpa using hp.1
    have hb : (c :: rest).getLast (List.cons_ne_nil _ _) = b := by
      exact Option.some.inj
        ((List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil c rest)).symm.trans hp.2.1)
    rw [← ha]
    exact List.relationReflTransGen_of_exists_isChain_cons rest hp.2.2 hb

private theorem reach_simple (Γ : Cnf α) (a b : PropLiteral α) (h : Reach Γ a b) :
    ∃ L, IsPath Γ a b L ∧ L.Nodup := by
  classical
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[b], by simp [IsPath], by simp⟩
  · intro c d e _ ih
    obtain ⟨L,hp,hnd⟩ := ih
    by_cases hm : c ∈ L
    · obtain ⟨s,t,he⟩ := List.mem_iff_append.mp hm
      rw [he] at hp hnd
      refine ⟨c :: t, ⟨rfl, ?_, hp.2.2.right_of_append⟩, hnd.of_append_right⟩
      simpa only [List.getLast?_append_cons] using hp.2.1
    · cases L with
      | nil => simp [IsPath] at hp
      | cons x xs =>
        have hx : x = d := by simpa using hp.1
        refine ⟨c :: x :: xs, ⟨rfl, ?_, ?_⟩, List.nodup_cons.mpr ⟨hm,hnd⟩⟩
        · simpa only [List.getLast?_cons_cons] using hp.2.1
        · exact .cons_cons (by simpa only [hx] using e) hp.2.2

theorem simple_path_bound [Fintype α] (Γ : Cnf α) (a b : PropLiteral α) :
    Reach Γ a b ↔ ∃ L, IsPath Γ a b L ∧ L.Nodup ∧ L.length ≤ 2 * Fintype.card α := by
  constructor
  · intro h
    obtain ⟨L,hp,hnd⟩ := reach_simple Γ a b h
    refine ⟨L,hp,hnd,?_⟩
    have hlen := hnd.length_le_card
    rw [literal_count] at hlen
    exact hlen
  · rintro ⟨L,hp,_,_⟩
    exact path_reach Γ a b hp

theorem boundedPath_spec [Fintype α] [DecidableEq α] (Γ : Cnf α)
    (n : ℕ) (a b : PropLiteral α) :
    boundedPath Γ n a b = true ↔ ∃ L, IsPath Γ a b L ∧ L.length ≤ n := by
  induction n generalizing a b with
  | zero =>
    simp only [boundedPath, Bool.false_eq_true, false_iff]
    rintro ⟨L,hp,hlen⟩
    have he : L = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [he, IsPath] at hp
  | succ n ih =>
    simp only [boundedPath, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (hab | ⟨c,he,hc⟩)
      · subst b
        exact ⟨[a], by simp [IsPath], by simp⟩
      · obtain ⟨L,hp,hlen⟩ := (ih c b).mp hc
        cases L with
        | nil => simp [IsPath] at hp
        | cons x xs =>
          have hx : x = c := by simpa using hp.1
          refine ⟨a :: x :: xs, ⟨rfl, ?_, ?_⟩, ?_⟩
          · simpa only [List.getLast?_cons_cons] using hp.2.1
          · exact .cons_cons (by simpa only [hx] using he) hp.2.2
          · simpa only [List.length_cons] using Nat.succ_le_succ hlen
    · rintro ⟨L,hp,hlen⟩
      cases L with
      | nil => simp [IsPath] at hp
      | cons x xs =>
        have hx : x = a := by simpa using hp.1
        cases xs with
        | nil =>
          have hb : x = b := by simpa using hp.2.1
          exact Or.inl (hx.symm.trans hb)
        | cons c rest =>
          refine Or.inr ⟨c, ?_, (ih c b).mpr ⟨c :: rest, ⟨rfl, ?_, ?_⟩, ?_⟩⟩
          · simpa only [hx] using (List.isChain_cons_cons.mp hp.2.2).1
          · simpa only [List.getLast?_cons_cons] using hp.2.1
          · exact (List.isChain_cons_cons.mp hp.2.2).2
          · simp only [List.length_cons] at hlen ⊢
            omega

def reachTest [Fintype α] [DecidableEq α] (Γ : Cnf α) (a b : PropLiteral α) : Bool :=
  boundedPath Γ (2 * Fintype.card α) a b

theorem reachTest_correct [Fintype α] [DecidableEq α] (Γ : Cnf α) (a b : PropLiteral α) :
    reachTest Γ a b = true ↔ Reach Γ a b := by
  rw [reachTest, boundedPath_spec]
  constructor
  · rintro ⟨L,hp,_⟩
    exact path_reach Γ a b hp
  · intro h
    obtain ⟨L,hp,_,hlen⟩ := (simple_path_bound Γ a b).mp h
    exact ⟨L,hp,hlen⟩

def finiteTest [Fintype α] [DecidableEq α] (Γ : Cnf α) : Bool :=
  decide ([] ∉ Γ) && decide (∀ a,
    ¬ (reachTest Γ a (opposite a) = true ∧ reachTest Γ (opposite a) a = true))

theorem finiteTest_correct [Fintype α] [DecidableEq α] (Γ : Cnf α) (h2 : IsTwo Γ) :
    finiteTest Γ = true ↔ Sat Γ := by
  rw [criterion Γ h2]
  simp only [finiteTest, Bool.and_eq_true, decide_eq_true_eq, reachTest_correct,
    Consistent, Mutual]

theorem finiteTest_model [Fintype α] [DecidableEq α] (Γ : Cnf α) (h2 : IsTwo Γ)
    (h : finiteTest Γ = true) : Models (orderedAssignment Γ (chosenRank Γ)) Γ := by
  obtain ⟨he,hc⟩ := (criterion Γ h2).mp ((finiteTest_correct Γ h2).mp h)
  exact ordered_model Γ h2 he hc (chosenRank Γ) (chosenRank_spec Γ).1

end Lemmatheca.MathematicalLogic.TwoSatisfiability

