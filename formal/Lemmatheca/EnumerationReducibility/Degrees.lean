import Lemmatheca.EnumerationReducibility.OracleSearch

namespace Lemmatheca.ComputabilityTheory.EnumerationReducibility

open UniversalComputation

private theorem mem_join_iff (A B : Set ℕ) (x : ℕ) :
    x ∈ TuringDegrees.join A B ↔ (x % 2 = 0 ∧ x / 2 ∈ A) ∨ (x % 2 = 1 ∧ x / 2 ∈ B) := by
  simp only [TuringDegrees.join,Set.mem_union,Set.mem_image]
  constructor
  · rintro (⟨n,hn,hx⟩ | ⟨n,hn,hx⟩)
    · have hq : x / 2 = n := by omega
      exact Or.inl ⟨by omega,hq.symm ▸ hn⟩
    · have hq : x / 2 = n := by omega
      exact Or.inr ⟨by omega,hq.symm ▸ hn⟩
  · rintro (⟨hx,hA⟩ | ⟨hx,hB⟩)
    · exact Or.inl ⟨x/2,hA,by omega⟩
    · exact Or.inr ⟨x/2,hB,by omega⟩

private theorem singleton_reduction (f : ℕ → ℕ) (hf : Primrec f)
    (A B : Set ℕ) (h : ∀ n, n ∈ A ↔ f n ∈ B) : Reducible A B := by
  classical
  have hu : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hR : JointCE (fun n d => d = singletonCode (f n)) :=
    (Primrec.eq.comp hv (singletonCode_primitive.comp (hf.comp hu))).computablePred.to_re
  obtain ⟨e,he⟩ := (jointCE_iff_index _).mp hR
  refine ⟨e,?_⟩
  ext n
  change (∃ d, indexedRule e n d ∧ (finiteSet d : Set ℕ) ⊆ B) ↔ n ∈ A
  simp only [he,exists_eq_left,finiteSet_singleton,Finset.coe_singleton,Set.singleton_subset_iff]
  exact (h n).symm

def interleaveRules (R S : RuleRelation) (n d : ℕ) : Prop :=
  if n % 2 = 0 then R (n/2) d else S (n/2) d

theorem interleaveRules_enumerable (R S : RuleRelation) (hR : JointCE R) (hS : JointCE S) :
    JointCE (interleaveRules R S) := by
  have hu : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hf : Computable (fun z : ℕ => Nat.pair (z.unpair.1/2) z.unpair.2) :=
    (Primrec₂.natPair.comp (Primrec.nat_div.comp hu (Primrec.const 2)) hv).to_comp
  have hp : PrimrecPred (fun z : ℕ => z.unpair.1 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp hu (Primrec.const 2)) (Primrec.const 0)
  have hr : REPred (fun z : ℕ => R (z.unpair.1/2) z.unpair.2) :=
    REPred.of_eq (hR.comp hf) (fun _ => by simp only [Nat.unpair_pair])
  have hs : REPred (fun z : ℕ => S (z.unpair.1/2) z.unpair.2) :=
    REPred.of_eq (hS.comp hf) (fun _ => by simp only [Nat.unpair_pair])
  exact (enumerable_union (enumerable_inter hp.computablePred.to_re hr)
    (enumerable_inter hp.not.computablePred.to_re hs)).of_eq
      (fun z => by by_cases hz : z.unpair.1 % 2 = 0 <;> simp [interleaveRules,hz])

theorem interleave_operator (R S : RuleRelation) (C : Set ℕ) :
    operatorOf (interleaveRules R S) C = TuringDegrees.join (operatorOf R C) (operatorOf S C) := by
  ext n
  by_cases hn : n % 2 = 0
  · simp [operatorOf,interleaveRules,mem_join_iff,hn]
  · have hn' : n % 2 = 1 := by omega
    simp [operatorOf,interleaveRules,mem_join_iff,hn']

theorem join_lower_bounds (A B : Set ℕ) :
    Reducible A (TuringDegrees.join A B) ∧ Reducible B (TuringDegrees.join A B) := by
  exact ⟨singleton_reduction _ (TuringDegrees.join_even_reduction A B).1 A _
      (TuringDegrees.join_even_reduction A B).2,
    singleton_reduction _ (TuringDegrees.join_odd_reduction A B).1 B _
      (TuringDegrees.join_odd_reduction A B).2⟩

theorem join_reducible_iff (A B C : Set ℕ) :
    Reducible (TuringDegrees.join A B) C ↔ Reducible A C ∧ Reducible B C := by
  constructor
  · intro h
    exact ⟨reducible_trans (join_lower_bounds A B).1 h,
      reducible_trans (join_lower_bounds A B).2 h⟩
  · rintro ⟨⟨r,hr⟩,⟨s,hs⟩⟩
    have hj (e : ℕ) : JointCE (indexedRule e) :=
      (jointCE_iff_index _).mpr ⟨e,fun _ _ => Iff.rfl⟩
    obtain ⟨e,he⟩ := (jointCE_iff_index _).mp
      (interleaveRules_enumerable _ _ (hj r) (hj s))
    refine ⟨e,?_⟩
    have heq : operator e C = operatorOf (interleaveRules (indexedRule r) (indexedRule s)) C := by
      ext n
      simp only [operator,operatorOf,Set.mem_ofPred_eq,he]
    rw [heq,interleave_operator]
    exact congrArg₂ TuringDegrees.join hr hs

structure Problem where
  carrier : Set ℕ

instance problemPreorder : Preorder Problem where
  le A B := Reducible A.carrier B.carrier
  le_refl A := reducible_refl A.carrier
  le_trans _ _ _ := reducible_trans

abbrev Degree := Antisymmetrization Problem (· ≤ ·)

def degree (A : Set ℕ) : Degree := toAntisymmetrization (· ≤ ·) ⟨A⟩

theorem degree_surjective : Function.Surjective degree := by
  intro d
  induction d using Antisymmetrization.ind with
  | _ A => exact ⟨A.carrier,rfl⟩

theorem degree_eq_iff (A B : Set ℕ) : degree A = degree B ↔ Equivalent A B := by
  exact toAntisymmetrization_eq (· ≤ ·) (⟨A⟩ : Problem) ⟨B⟩

theorem degree_le_iff (A B : Set ℕ) : degree A ≤ degree B ↔ Reducible A B := by
  rfl

def zeroDegree : Degree := degree ∅

theorem zeroDegree_le (d : Degree) : zeroDegree ≤ d := by
  obtain ⟨A,rfl⟩ := degree_surjective d
  apply (degree_le_iff ∅ A).mpr
  exact ce_reducible_everywhere ∅
    (ComputablePred.to_re ⟨inferInstance,by simpa using (Computable.const false : Computable (fun _ : ℕ => false))⟩) A

theorem degree_eq_zero_iff (A : Set ℕ) :
    degree A = zeroDegree ↔ REPred (fun n => n ∈ A) := by
  constructor
  · intro h
    exact (reducible_empty_iff A).mp ((degree_le_iff A ∅).mp (le_of_eq h))
  · intro h
    exact le_antisymm ((degree_le_iff A ∅).mpr ((reducible_empty_iff A).mpr h)) (zeroDegree_le _)

theorem join_degree_congr {A A' B B' : Set ℕ}
    (hA : Equivalent A A') (hB : Equivalent B B') :
    degree (TuringDegrees.join A B) = degree (TuringDegrees.join A' B') := by
  apply Quotient.sound
  constructor
  · exact (join_reducible_iff _ _ _).mpr
      ⟨reducible_trans hA.1 (join_lower_bounds A' B').1,
        reducible_trans hB.1 (join_lower_bounds A' B').2⟩
  · exact (join_reducible_iff _ _ _).mpr
      ⟨reducible_trans hA.2 (join_lower_bounds A B).1,
        reducible_trans hB.2 (join_lower_bounds A B).2⟩

def degreeJoin : Degree → Degree → Degree :=
  Quotient.lift₂ (fun A B : Problem => degree (TuringDegrees.join A.carrier B.carrier))
    (fun _ _ _ _ hA hB => join_degree_congr hA hB)

theorem degreeJoin_degree (A B : Set ℕ) :
    degreeJoin (degree A) (degree B) = degree (TuringDegrees.join A B) := by
  rfl

theorem degreeJoin_le_iff (a b c : Degree) : degreeJoin a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  obtain ⟨B,rfl⟩ := degree_surjective b
  obtain ⟨C,rfl⟩ := degree_surjective c
  rw [degreeJoin_degree]
  exact join_reducible_iff A B C

theorem degreeJoin_upper_bounds (a b : Degree) : a ≤ degreeJoin a b ∧ b ≤ degreeJoin a b := by
  exact (degreeJoin_le_iff a b _).mp le_rfl

instance degreeSemilatticeSup : SemilatticeSup Degree where
  toPartialOrder := inferInstance
  sup := degreeJoin
  le_sup_left a b := (degreeJoin_upper_bounds a b).1
  le_sup_right a b := (degreeJoin_upper_bounds a b).2
  sup_le a b c ha hb := (degreeJoin_le_iff a b c).mpr ⟨ha,hb⟩

instance degreeOrderBot : OrderBot Degree where
  bot := zeroDegree
  bot_le := zeroDegree_le

/-- Exchange the two middle residue classes modulo four. -/
def joinPermutation (n : ℕ) : ℕ :=
  4 * (n/4) + if n%4 = 1 then 2 else if n%4 = 2 then 1 else n%4

def imageRules (h : ℕ → ℕ) (n d : ℕ) : Prop := ∃ x, d = singletonCode x ∧ n = h x

theorem imageRules_enumerable (h : ℕ → ℕ) (hh : Computable h) : JointCE (imageRules h) := by
  unfold JointCE
  apply (enumerable_iff_total_range _).mpr
  refine Or.inr ⟨fun x => Nat.pair (h x) (singletonCode x),
    Primrec₂.natPair.to_comp.comp hh singletonCode_primitive.to_comp,?_⟩
  intro z
  constructor
  · rintro ⟨x,hd,hn⟩
    exact ⟨x,by change Nat.pair (h x) (singletonCode x) = z; rw [←hn,←hd,Nat.pair_unpair]⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,by simp only [Nat.unpair_pair],by simp only [Nat.unpair_pair]⟩

theorem image_operator (h : ℕ → ℕ) (A : Set ℕ) : operatorOf (imageRules h) A = h '' A := by
  ext n
  constructor
  · rintro ⟨d,⟨x,hd,rfl⟩,hsub⟩
    refine ⟨x,hsub ?_,rfl⟩
    simp [hd,finiteSet_singleton]
  · rintro ⟨x,hx,rfl⟩
    exact ⟨singletonCode x,⟨x,rfl,rfl⟩,by simpa [finiteSet_singleton]⟩

theorem joinPermutation_primitive : Primrec joinPermutation := by
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hd)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (Primrec.const 1) hm))

theorem joinPermutation_involution : Function.Involutive joinPermutation := by
  intro n
  simp only [joinPermutation]
  split_ifs <;> omega

theorem joinPermutation_totalInfo (A B : Set ℕ) :
    joinPermutation '' totalInfo (TuringDegrees.join A B) =
      TuringDegrees.join (totalInfo A) (totalInfo B) := by
  have point (n : ℕ) :
      joinPermutation n ∈ TuringDegrees.join (totalInfo A) (totalInfo B) ↔
        n ∈ totalInfo (TuringDegrees.join A B) := by
    obtain ⟨k,rfl | rfl | rfl | rfl⟩ :
        ∃ k, n = 4*k ∨ n = 4*k+1 ∨ n = 4*k+2 ∨ n = 4*k+3 := by
      refine ⟨n/4,?_⟩
      omega
    all_goals
      have hh : 4*k/2 = 2*k := by omega
      simp [joinPermutation,totalInfo,mem_join_iff,Nat.add_div,Nat.add_mod,Nat.mul_mod,hh]
  ext n
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact (point m).mpr hm
  · intro hn
    refine ⟨joinPermutation n,?_,joinPermutation_involution n⟩
    apply (point (joinPermutation n)).mp
    simpa only [joinPermutation_involution n] using hn

theorem totalInfo_join_equivalent (A B : Set ℕ) :
    Equivalent (totalInfo (TuringDegrees.join A B)) (TuringDegrees.join (totalInfo A) (totalInfo B)) := by
  have im (C : Set ℕ) : Reducible (joinPermutation '' C) C := by
    obtain ⟨e,he⟩ := (jointCE_iff_index _).mp
      (imageRules_enumerable joinPermutation joinPermutation_primitive.to_comp)
    refine ⟨e,?_⟩
    have heq : operator e C = operatorOf (imageRules joinPermutation) C := by
      ext n
      simp only [operator,operatorOf,Set.mem_ofPred_eq,he]
    rw [heq,image_operator]
  have hx := joinPermutation_totalInfo A B
  have hi : (fun n => joinPermutation (joinPermutation n)) = id :=
    funext (fun n => joinPermutation_involution n)
  have hy : joinPermutation '' TuringDegrees.join (totalInfo A) (totalInfo B) =
      totalInfo (TuringDegrees.join A B) := by
    rw [←hx,Set.image_image,hi,Set.image_id]
  constructor
  · rw [←hy]
    exact im _
  · rw [←hx]
    exact im _

theorem turing_degree_respects {A B : Set ℕ} (h : TuringDegrees.Equivalent A B) :
    degree (totalInfo A) = degree (totalInfo B) := by
  exact (degree_eq_iff _ _).mpr
    ⟨(totalInfo_reducible_iff _ _).mpr h.1,(totalInfo_reducible_iff _ _).mpr h.2⟩

def turingEmbedding : TuringDegrees.Degree → Degree :=
  Quotient.lift (fun A : TuringDegrees.Problem => degree (totalInfo A.carrier))
    (fun _ _ h => turing_degree_respects h)

theorem turingEmbedding_degree (A : Set ℕ) :
    turingEmbedding (TuringDegrees.degree A) = degree (totalInfo A) := by
  rfl

theorem turingEmbedding_le_iff (a b : TuringDegrees.Degree) :
    turingEmbedding a ≤ turingEmbedding b ↔ a ≤ b := by
  obtain ⟨A,rfl⟩ := TuringDegrees.degree_surjective a
  obtain ⟨B,rfl⟩ := TuringDegrees.degree_surjective b
  rw [turingEmbedding_degree,turingEmbedding_degree,degree_le_iff]
  exact totalInfo_reducible_iff A B

theorem turingEmbedding_injective : Function.Injective turingEmbedding := by
  intro a b h
  exact le_antisymm ((turingEmbedding_le_iff a b).mp (le_of_eq h))
    ((turingEmbedding_le_iff b a).mp (le_of_eq h.symm))

theorem turingEmbedding_zero : turingEmbedding TuringDegrees.zeroDegree = zeroDegree := by
  rw [TuringDegrees.zeroDegree,turingEmbedding_degree,degree_eq_zero_iff]
  have hp : REPred (fun n : ℕ => n % 2 = 1) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 1)).computablePred.to_re
  exact hp.of_eq (fun n => by simp [totalInfo,mem_join_iff])

theorem turingEmbedding_join (a b : TuringDegrees.Degree) :
    turingEmbedding (TuringDegrees.degreeJoin a b) = degreeJoin (turingEmbedding a) (turingEmbedding b) := by
  obtain ⟨A,rfl⟩ := TuringDegrees.degree_surjective a
  obtain ⟨B,rfl⟩ := TuringDegrees.degree_surjective b
  simp only [TuringDegrees.degreeJoin_degree,turingEmbedding_degree,degreeJoin_degree]
  exact (degree_eq_iff _ _).mpr (totalInfo_join_equivalent A B)

end Lemmatheca.ComputabilityTheory.EnumerationReducibility
