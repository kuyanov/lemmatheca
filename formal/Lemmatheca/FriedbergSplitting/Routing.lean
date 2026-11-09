import Lemmatheca.FriedbergSplitting.Scheduler

/-! The specified least-requirement routing of each fresh input arrival. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergSplitting

open EffectiveEnumerations PrimitiveRecursion PrimitiveRecursiveAutomation UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def CESplit (A A₀ A₁ : Set ℕ) : Prop :=
  REPred A₀ ∧ REPred A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A

abbrev State := List ℕ × List ℕ

def sideList (z : State) (i : ℕ) : List ℕ := if i % 2 = 0 then z.1 else z.2

def Eligible (a s : ℕ) (z : State) (q : ℕ) : Prop :=
  q ≤ s ∧ HasArrival a s ∧ stageTest (q / 2) (s + 1) (arrival a s) = 1 ∧
    ∀ y ∈ sideList z q, stageTest (q / 2) (s + 1) y = 0

def priority (a s : ℕ) (z : State) : ℕ :=
  boundedSearch (fun p : (ℕ × ℕ) × State => Eligible p.1.1 p.1.2 p.2)
    ((a, s), z) (s + 1)

def HasAction (a s : ℕ) (z : State) : Prop := priority a s z < s + 1

def chosenSide (a s : ℕ) (z : State) : ℕ :=
  if HasAction a s z then priority a s z % 2 else 0

def routeNext (a s : ℕ) (z : State) : State :=
  if HasArrival a s then
    if chosenSide a s z = 0 then (arrival a s :: z.1, z.2)
    else (z.1, arrival a s :: z.2)
  else z

def routeStage (a : ℕ) : ℕ → State
  | 0 => ([], [])
  | s + 1 => routeNext a s (routeStage a s)

def pieceList (a i s : ℕ) : List ℕ := sideList (routeStage a s) i

def pieceStage (a i s : ℕ) : Set ℕ := {x | x ∈ pieceList a i s}

def pieceTest (a i s x : ℕ) : ℕ := if x ∈ pieceList a i s then 1 else 0

def piece (a i : ℕ) : Set ℕ := {x | ∃ s, x ∈ pieceStage a i s}

def Acts (a q s : ℕ) : Prop :=
  HasAction a s (routeStage a s) ∧ priority a s (routeStage a s) = q

theorem priority_data (a s : ℕ) (z : State) :
    (HasAction a s z → Eligible a s z (priority a s z)) ∧
      ∀ q, Eligible a s z q → HasAction a s z ∧ priority a s z ≤ q := by
  have h := boundedSearch_spec
    (fun p : (ℕ × ℕ) × State => Eligible p.1.1 p.1.2 p.2) ((a, s), z) (s + 1)
  change priority a s z ≤ s + 1 ∧
    (priority a s z < s + 1 → Eligible a s z (priority a s z) ∧
      ∀ q < priority a s z, ¬ Eligible a s z q) ∧
    (priority a s z = s + 1 ↔ ∀ q < s + 1, ¬ Eligible a s z q) at h
  refine ⟨fun hs => (h.2.1 hs).1, ?_⟩
  intro q hq
  have hl : HasAction a s z := by
    by_contra hn
    have he : priority a s z = s + 1 := by unfold HasAction at hn; omega
    exact h.2.2.mp he q (by have := hq.1; omega) hq
  refine ⟨hl, ?_⟩
  by_contra hn
  exact (h.2.1 hl).2 q (by omega) hq

private theorem chosen_bound (a s : ℕ) (z : State) : chosenSide a s z < 2 := by
  unfold chosenSide
  split <;> omega

private theorem side_primitive : Primrec (fun p : State × ℕ => sideList p.1 p.2) := by
  unfold sideList
  exact PrimitiveRecursiveAutomation.ite
    (PrimitiveRecursiveAutomation.eq (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
      (Primrec.const 0)) (by fun_prop) (by fun_prop)

private theorem all_stage_zero :
    PrimrecPred (fun p : List ℕ × (ℕ × ℕ) =>
      ∀ y ∈ p.1, stageTest p.2.1 p.2.2 y = 0) := by
  have hy : PrimrecRel (fun y : ℕ => fun es : ℕ × ℕ => stageTest es.1 es.2 y = 0) :=
    Primrec.eq.comp
      (stage_test_primitive.comp
        (show Primrec (fun p : ℕ × (ℕ × ℕ) => (p.2, p.1)) by fun_prop))
      (Primrec.const 0)
  exact hy.forall_mem_list

private theorem eligible_primitive :
    Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => Eligible p.1.1.1 p.1.1.2 p.1.2 p.2 |> decide) := by
  have ha : Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => arrival p.1.1.1 p.1.1.2) :=
    Primrec.comp scheduler_primitive.2.1 (by fun_prop)
  have hd : Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hv : Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => p.1.1.2 + 1) := by fun_prop
  have ht : Primrec (fun p : ((ℕ × ℕ) × State) × ℕ =>
      stageTest (p.2 / 2) (p.1.1.2 + 1) (arrival p.1.1.1 p.1.1.2)) :=
    stage_test_primitive.comp ((hd.pair hv).pair ha)
  have hl : Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => sideList p.1.2 p.2) :=
    side_primitive.comp (show Primrec (fun p : ((ℕ × ℕ) × State) × ℕ => (p.1.2, p.2)) by fun_prop)
  have hall : PrimrecPred (fun p : ((ℕ × ℕ) × State) × ℕ =>
      ∀ y ∈ sideList p.1.2 p.2, stageTest (p.2 / 2) (p.1.1.2 + 1) y = 0) :=
    all_stage_zero.comp (hl.pair (hd.pair hv))
  have he : PrimrecPred (fun p : ((ℕ × ℕ) × State) × ℕ =>
      Eligible p.1.1.1 p.1.1.2 p.1.2 p.2) :=
    (Primrec.nat_le.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).and
      ((Primrec.nat_lt.comp ha hv).and ((Primrec.eq.comp ht (Primrec.const 1)).and hall))
  exact he.decide

theorem routing_primitive :
    Primrec₂ routeStage ∧
      Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => pieceTest p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : (ℕ × ℕ) × State => priority p.1.1 p.1.2 p.2) :=
    (boundedSearch_primrec (R := fun p : (ℕ × ℕ) × State => Eligible p.1.1 p.1.2 p.2)
      eligible_primitive.primrecPred).comp Primrec.id (by fun_prop)
  have hc : Primrec (fun p : (ℕ × ℕ) × State => chosenSide p.1.1 p.1.2 p.2) := by
    unfold chosenSide HasAction
    exact (Primrec.ite
      (PrimitiveRecursiveAutomation.lt hp (show Primrec (fun p : (ℕ × ℕ) × State => p.1.2 + 1) by fun_prop)).primrecPred
      (Primrec.nat_mod.comp hp (Primrec.const 2)) (Primrec.const 0)).of_eq (by intro p; split_ifs <;> rfl)
  have ha : Primrec (fun p : (ℕ × ℕ) × State => arrival p.1.1 p.1.2) :=
    Primrec.comp scheduler_primitive.2.1 Primrec.fst
  have hzero : Primrec (fun p : (ℕ × ℕ) × State => (arrival p.1.1 p.1.2 :: p.2.1, p.2.2)) :=
    (PrimitiveRecursiveAutomation.listCons ha (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  have hone : Primrec (fun p : (ℕ × ℕ) × State => (p.2.1, arrival p.1.1 p.1.2 :: p.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (PrimitiveRecursiveAutomation.listCons ha (Primrec.snd.comp Primrec.snd))
  have hn : Primrec (fun p : (ℕ × ℕ) × State => routeNext p.1.1 p.1.2 p.2) := by
    exact (Primrec.ite
      (PrimitiveRecursiveAutomation.lt ha (show Primrec (fun p : (ℕ × ℕ) × State => p.1.2 + 1) by fun_prop)).primrecPred
      (Primrec.ite (PrimitiveRecursiveAutomation.eq hc (Primrec.const 0)).primrecPred hzero hone)
      Primrec.snd).of_eq (by intro p; unfold routeNext HasArrival; split_ifs <;> rfl)
  have hh : Primrec₂ (fun a (p : ℕ × State) => routeNext a p.1 p.2) :=
    hn.comp (show Primrec (fun p : ℕ × (ℕ × State) => ((p.1, p.2.1), p.2.2)) by fun_prop)
  have hr : Primrec₂ routeStage :=
    (Primrec.nat_rec (Primrec.const ([], [])) hh).of_eq (by
      intro a n
      induction n with
      | zero => rfl
      | succ n ih => simp only [routeStage, ih])
  refine ⟨hr, ?_⟩
  have hstage : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => routeStage p.1.1 p.2.1) :=
    Primrec.comp hr (show Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (p.1.1, p.2.1)) by fun_prop)
  have hl : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => pieceList p.1.1 p.1.2 p.2.1) :=
    side_primitive.comp (hstage.pair (Primrec.snd.comp Primrec.fst))
  unfold pieceTest
  exact PrimitiveRecursiveAutomation.ite
    (PrimitiveRecursiveAutomation.listMem (by fun_prop) hl) (Primrec.const 1) (Primrec.const 0)

theorem routing_transition (a i s x : ℕ) (hi : i < 2) :
    x ∈ pieceStage a i (s + 1) ↔ x ∈ pieceStage a i s ∨
      HasArrival a s ∧ chosenSide a s (routeStage a s) = i ∧ x = arrival a s := by
  have hb := chosen_bound a s (routeStage a s)
  have hcases : i = 0 ∨ i = 1 := by omega
  have hside : chosenSide a s (routeStage a s) = 0 ∨ chosenSide a s (routeStage a s) = 1 := by omega
  rcases hcases with rfl | rfl <;> rcases hside with hc | hc <;>
    by_cases ha : HasArrival a s <;>
    simp [pieceStage, pieceList, sideList, routeStage, routeNext, ha, hc, or_comm]

theorem routing_invariants (a s : ℕ) :
    (routeStage a s).1.Nodup ∧ (routeStage a s).2.Nodup ∧
      Disjoint (pieceStage a 0 s) (pieceStage a 1 s) ∧
      pieceStage a 0 s ∪ pieceStage a 1 s = processedSet a s := by
  induction s with
  | zero => simp [routeStage, pieceStage, pieceList, sideList, processedSet, processedList]
  | succ s ih =>
    by_cases ha : HasArrival a s
    · have hf := (arrival_data a s).2.2.1 ha |>.2.1
      have h0 : arrival a s ∉ (routeStage a s).1 := by
        intro hx
        apply hf
        rw [← ih.2.2.2]
        exact Or.inl hx
      have h1 : arrival a s ∉ (routeStage a s).2 := by
        intro hx
        apply hf
        rw [← ih.2.2.2]
        exact Or.inr hx
      by_cases hc : chosenSide a s (routeStage a s) = 0
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [routeStage, routeNext, ha, hc] using List.nodup_cons.mpr ⟨h0, ih.1⟩
        · simpa [routeStage, routeNext, ha, hc] using ih.2.1
        · apply Set.disjoint_left.mpr
          intro x hx hy
          rw [routing_transition a 0 s x (by omega)] at hx
          rw [routing_transition a 1 s x (by omega)] at hy
          rcases hx with hx | ⟨_, _, rfl⟩
          · exact Set.disjoint_left.mp ih.2.2.1 hx (hy.resolve_right (by simp [hc]))
          · exact h1 (hy.resolve_right (by simp [hc]))
        · ext x
          rw [Set.mem_union, routing_transition a 0 s x (by omega),
            routing_transition a 1 s x (by omega), scheduler_transition]
          have he : x ∈ pieceStage a 0 s ∨ x ∈ pieceStage a 1 s ↔ x ∈ processedSet a s := by
            rw [← ih.2.2.2]; rfl
          simp only [ha, hc, zero_ne_one, false_and, and_false, or_false, true_and]
          tauto
      · have hc1 : chosenSide a s (routeStage a s) = 1 := by
          have := chosen_bound a s (routeStage a s); omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [routeStage, routeNext, ha, hc] using ih.1
        · simpa [routeStage, routeNext, ha, hc] using List.nodup_cons.mpr ⟨h1, ih.2.1⟩
        · apply Set.disjoint_left.mpr
          intro x hx hy
          rw [routing_transition a 0 s x (by omega)] at hx
          rw [routing_transition a 1 s x (by omega)] at hy
          have hx' := hx.resolve_right (by simp [hc])
          rcases hy with hy | ⟨_, _, rfl⟩
          · exact Set.disjoint_left.mp ih.2.2.1 hx' hy
          · exact h0 hx'
        · ext x
          rw [Set.mem_union, routing_transition a 0 s x (by omega),
            routing_transition a 1 s x (by omega), scheduler_transition]
          have he : x ∈ pieceStage a 0 s ∨ x ∈ pieceStage a 1 s ↔ x ∈ processedSet a s := by
            rw [← ih.2.2.2]; rfl
          simp only [ha, hc1, true_and]
          tauto
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [routeStage, routeNext, ha] using ih.1
      · simpa [routeStage, routeNext, ha] using ih.2.1
      · simpa [pieceStage, pieceList, routeStage, routeNext, ha] using ih.2.2.1
      · ext x
        rw [Set.mem_union, routing_transition a 0 s x (by omega),
          routing_transition a 1 s x (by omega), scheduler_transition]
        simpa [ha] using congrArg (fun z : Set ℕ => x ∈ z) ih.2.2.2

theorem piece_stage_monotone (a i : ℕ) : Monotone (pieceStage a i) := by
  have he : pieceStage a i = pieceStage a (i % 2) := by
    funext s
    simp [pieceStage, pieceList, sideList]
  rw [he]
  apply monotone_nat_of_le_succ
  intro s x hx
  exact (routing_transition a (i % 2) s x (Nat.mod_lt _ (by omega))).mpr (Or.inl hx)

theorem routed_partition (a : ℕ) :
    REPred (piece a 0) ∧ REPred (piece a 1) ∧
      Disjoint (piece a 0) (piece a 1) ∧ piece a 0 ∪ piece a 1 = indexSet a := by
  have hc (i : ℕ) : REPred (piece a i) := by
    apply (enumerable_iff_decidable_certificate _).mpr
    refine ⟨fun x s => pieceTest a i s x = 1, ?_, ?_⟩
    · exact (Primrec.eq.decide.to_comp.comp
        (routing_primitive.2.to_comp.comp (show Primrec (fun p : ℕ × ℕ => ((a, i), (p.2, p.1))) by fun_prop).to_comp)
        (Computable.const 1)).computablePred
    · intro x
      change (∃ s, x ∈ pieceList a i s) ↔ _
      simp [pieceTest]
  have hsub (i : ℕ) (hi : i < 2) : piece a i ⊆ indexSet a := by
    rintro x ⟨s, hx⟩
    apply (scheduler_invariants a s).2.2
    rw [← (routing_invariants a s).2.2.2]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  refine ⟨hc 0, hc 1, Set.disjoint_left.mpr ?_, ?_⟩
  · rintro x ⟨s, hs⟩ ⟨t, ht⟩
    exact Set.disjoint_left.mp (routing_invariants a (max s t)).2.2.1
      (piece_stage_monotone a 0 (Nat.le_max_left _ _) hs)
      (piece_stage_monotone a 1 (Nat.le_max_right _ _) ht)
  · ext x
    constructor
    · rintro (hx | hx)
      · exact hsub 0 (by omega) hx
      · exact hsub 1 (by omega) hx
    · intro hx
      obtain ⟨s, hs⟩ := (scheduler_exhaustive a x).mp hx
      rw [← (routing_invariants a s).2.2.2] at hs
      rcases hs with hs | hs
      · exact Or.inl ⟨s, hs⟩
      · exact Or.inr ⟨s, hs⟩

end
end Lemmatheca.ComputabilityTheory.FriedbergSplitting
