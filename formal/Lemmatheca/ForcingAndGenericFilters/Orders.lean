import Lemmatheca.Absoluteness.Absoluteness
import Lemmatheca.PressingDownAndDeltaSystems.FinitePartialMaps
import Mathlib.Order.PFilter
import Mathlib.Order.Zorn

/-! The ground-model/ZFC interpretation is metatheoretic. These are the actual
order and supplied-family constructions used in its countable external argument. -/
namespace Lemmatheca.SetTheory.ForcingAndGenericFilters
open Set Order
universe u
noncomputable section
attribute [local instance] Classical.propDecidable
variable {P : Type u} [PartialOrder P]

def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q
def Antichain (A : Set P) : Prop := A.Pairwise fun p q => ¬Compatible p q
def MaximalAntichain (A : Set P) : Prop :=
  Antichain A ∧ ∀ B, Antichain B → A ⊆ B → B = A
def Dense (D : Set P) : Prop := ∀ p, ∃ q ∈ D, q ≤ p
def DenseBelow (D : Set P) (p : P) : Prop := ∀ q, q ≤ p → ∃ r ∈ D, r ≤ q
def Open (D : Set P) : Prop := ∀ ⦃p q⦄, p ∈ D → q ≤ p → q ∈ D
def downwardClosure (D : Set P) : Set P := {q | ∃ d ∈ D, q ≤ d}
def Meets (G : PFilter P) (D : Set P) : Prop := ∃ p, p ∈ G ∧ p ∈ D
def GenericFor (G : PFilter P) (S : Set (Set P)) : Prop := ∀ D ∈ S, Dense D → Meets G D
def Atomless : Prop := ∀ p : P, ∃ q r, q ≤ p ∧ r ≤ p ∧ ¬Compatible q r

theorem comparable_compatible (p q : P) (h : p ≤ q ∨ q ≤ p) :
    Compatible p q := by
  rcases h with h | h
  · exact ⟨p,le_rfl,h⟩
  · exact ⟨q,h,le_rfl⟩

theorem filter_compatible (G : PFilter P) {p q : P} (hp : p ∈ G) (hq : q ∈ G) :
    Compatible p q := by
  obtain ⟨r,hr,hrp,hrq⟩ := G.directed p hp q hq
  exact ⟨r,hrp,hrq⟩

theorem downward_dense_open {D : Set P} (hD : Dense D) :
    Dense (downwardClosure D) ∧ Open (downwardClosure D) := by
  refine ⟨?_,?_⟩
  · intro p
    obtain ⟨q,hq,hqp⟩ := hD p
    exact ⟨q,⟨q,hq,le_rfl⟩,hqp⟩
  · rintro p q ⟨d,hd,hpd⟩ hqp
    exact ⟨d,hd,hqp.trans hpd⟩


private theorem compatible_symm {p q : P} (h : Compatible p q) : Compatible q p := by
  obtain ⟨r,hrp,hrq⟩ := h
  exact ⟨r,hrq,hrp⟩

private theorem antichain_insert {A : Set P} {p : P}
    (hA : Antichain A) (hp : ∀ a ∈ A, ¬Compatible p a) : Antichain (insert p A) := by
  intro a ha b hb hab
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact (hab rfl).elim
  · exact hp b hb
  · exact fun h => hp a ha (compatible_symm h)
  · exact hA ha hb hab

theorem maximal_antichain_iff (A : Set P) :
    MaximalAntichain A ↔ Antichain A ∧ ∀ p, ∃ a ∈ A, Compatible p a := by
  classical
  constructor
  · intro hA
    refine ⟨hA.1,?_⟩
    intro p
    by_contra hn
    have hp : ∀ a ∈ A, ¬Compatible p a := by simpa using hn
    have heq := hA.2 (insert p A) (antichain_insert hA.1 hp) (Set.subset_insert _ _)
    have hpA : p ∈ A := heq ▸ Set.mem_insert p A
    exact hp p hpA ⟨p,le_rfl,le_rfl⟩
  · rintro ⟨hA,hcompat⟩
    refine ⟨hA,?_⟩
    intro B hB hAB
    apply Set.Subset.antisymm _ hAB
    intro p hp
    obtain ⟨a,ha,hpa⟩ := hcompat p
    by_contra hpA
    have hne : p ≠ a := fun he => hpA (he ▸ ha)
    exact hB hp (hAB ha) hne hpa

theorem maximal_antichain_downward_dense {A : Set P} (hA : MaximalAntichain A) :
    Dense (downwardClosure A) := by
  intro p
  obtain ⟨a,ha,r,hrp,hra⟩ := ((maximal_antichain_iff A).mp hA).2 p
  exact ⟨r,⟨a,ha,hra⟩,hrp⟩

theorem exists_maximal_antichain_in_dense {D : Set P} (hD : Dense D) :
    ∃ A ⊆ D, MaximalAntichain A := by
  classical
  let S : Set (Set P) := {A | A ⊆ D ∧ Antichain A}
  obtain ⟨A,hA⟩ := zorn_subset S (by
    intro c hc hchain
    refine ⟨⋃₀c,?_,fun A hA => Set.subset_sUnion_of_mem hA⟩
    refine ⟨?_,?_⟩
    · rintro p ⟨A,hAc,hpA⟩
      exact (hc hAc).1 hpA
    · rintro p ⟨A,hAc,hpA⟩ q ⟨B,hBc,hqB⟩ hpq
      rcases hchain.total hAc hBc with hAB | hBA
      · exact (hc hBc).2 (hAB hpA) hqB hpq
      · exact (hc hAc).2 hpA (hBA hqB) hpq)
  refine ⟨A,hA.prop.1,(maximal_antichain_iff A).mpr ⟨hA.prop.2,?_⟩⟩
  intro p
  by_contra hn
  have hp : ∀ a ∈ A, ¬Compatible p a := by simpa using hn
  obtain ⟨d,hd,hdp⟩ := hD p
  have hdA : d ∉ A := by
    intro hdA
    exact hp d hdA ⟨d,hdp,le_rfl⟩
  have hdcompat : ∀ a ∈ A, ¬Compatible d a := by
    intro a ha ⟨r,hrd,hra⟩
    exact hp a ha ⟨r,hrd.trans hdp,hra⟩
  have hnew : insert d A ∈ S :=
    ⟨Set.insert_subset hd hA.prop.1,antichain_insert hA.prop.2 hdcompat⟩
  exact hdA (hA.le_of_ge hnew (Set.subset_insert _ _) (Set.mem_insert d A))

theorem dense_below_union {D : Set P} {p : P} (hD : DenseBelow D p) :
    Dense (D ∪ {q | ¬Compatible q p}) := by
  classical
  intro q
  by_cases hq : Compatible q p
  · obtain ⟨r,hrq,hrp⟩ := hq
    obtain ⟨s,hs,hsr⟩ := hD r hrp
    exact ⟨s,Or.inl hs,hsr.trans hrq⟩
  · exact ⟨q,Or.inr hq,le_rfl⟩

theorem generic_dense_below (G : PFilter P) (S : Set (Set P)) (hG : GenericFor G S)
    {D : Set P} {p : P} (hp : p ∈ G) (hD : DenseBelow D p)
    (hE : D ∪ {q | ¬Compatible q p} ∈ S) : Meets G D := by
  obtain ⟨q,hq,hqE⟩ := hG _ hE (dense_below_union hD)
  rcases hqE with hqD | hqp
  · exact ⟨q,hq,hqD⟩
  · exact (hqp (filter_compatible G hq hp)).elim

theorem generic_open_iff (G : PFilter P) (S : Set (Set P))
    (hdown : ∀ D ∈ S, Dense D → downwardClosure D ∈ S) :
    GenericFor G S ↔ ∀ D ∈ S, Dense D → Open D → Meets G D := by
  constructor
  · intro hG D hD hd _
    exact hG D hD hd
  · intro hopen D hD hd
    obtain ⟨q,hq,d,hdD,hqd⟩ :=
      hopen _ (hdown D hD hd) (downward_dense_open hd).1 (downward_dense_open hd).2
    exact ⟨d,PFilter.mem_of_le hqd hq,hdD⟩

theorem generic_antichain_iff (G : PFilter P) (S : Set (Set P))
    (hdown : ∀ A ∈ S, MaximalAntichain A → downwardClosure A ∈ S)
    (hanti : ∀ D ∈ S, Dense D → ∃ A ∈ S, A ⊆ D ∧ MaximalAntichain A) :
    GenericFor G S ↔ ∀ A ∈ S, MaximalAntichain A → Meets G A := by
  constructor
  · intro hG A hA hmA
    obtain ⟨q,hq,a,ha,hqa⟩ := hG _ (hdown A hA hmA) (maximal_antichain_downward_dense hmA)
    exact ⟨a,PFilter.mem_of_le hqa hq,ha⟩
  · intro hmeet D hD hd
    obtain ⟨A,hAS,hAD,hA⟩ := hanti D hD hd
    obtain ⟨a,haG,haA⟩ := hmeet A hAS hA
    exact ⟨a,haG,hAD haA⟩

theorem atomless_complement_dense (G : PFilter P) (hP : Atomless (P := P)) :
    Dense (G : Set P)ᶜ := by
  classical
  intro p
  by_cases hp : p ∈ G
  · obtain ⟨q,r,hqp,hrp,hqr⟩ := hP p
    by_cases hq : q ∈ G
    · exact ⟨r,fun hr => hqr (filter_compatible G hq hr),hrp⟩
    · exact ⟨q,hq,hqp⟩
  · exact ⟨p,hp,le_rfl⟩

theorem no_ambient_generic (G : PFilter P) (hP : Atomless (P := P)) :
    ¬GenericFor G Set.univ := by
  intro hG
  obtain ⟨p,hp,hpc⟩ := hG _ (Set.mem_univ _) (atomless_complement_dense G hP)
  exact hpc hp

theorem generic_not_mem_family (G : PFilter P) (S : Set (Set P))
    (hG : GenericFor G S) (hP : Atomless (P := P))
    (hcompl : ∀ D ∈ S, Dᶜ ∈ S) : (G : Set P) ∉ S := by
  intro hGS
  obtain ⟨p,hp,hpc⟩ := hG _ (hcompl _ hGS) (atomless_complement_dense G hP)
  exact hpc hp

section Enumeration
variable (e : ℕ → P) (he : Function.Surjective e)
    (D : ℕ → Set P) (hD : ∀ n, Dense (D n))
include he hD

theorem next_index_exists (n : ℕ) (p : P) :
    ∃ k, e k ∈ D n ∧ e k ≤ p := by
  obtain ⟨q,hq,hqp⟩ := hD n p
  obtain ⟨k,rfl⟩ := he q
  exact ⟨k,hq,hqp⟩

noncomputable def nextIndex (n : ℕ) (p : P) : ℕ :=
  Nat.find (next_index_exists e he D hD n p)

noncomputable def sequence (p : P) : ℕ → P
  | 0 => p
  | n+1 => e (nextIndex e he D hD n (sequence p n))

theorem sequence_spec (p : P) :
    sequence e he D hD p 0 = p ∧
    (∀ n, sequence e he D hD p (n+1) ∈ D n ∧
      sequence e he D hD p (n+1) ≤ sequence e he D hD p n) ∧
    (∀ n k, k < nextIndex e he D hD n (sequence e he D hD p n) →
      ¬(e k ∈ D n ∧ e k ≤ sequence e he D hD p n)) := by
  refine ⟨rfl,?_,?_⟩
  · intro n
    exact Nat.find_spec (next_index_exists e he D hD n (sequence e he D hD p n))
  · intro n k hk
    exact Nat.find_min (next_index_exists e he D hD n (sequence e he D hD p n)) hk

def sequenceClosure (p : P) : Set P := {q | ∃ n, sequence e he D hD p n ≤ q}

theorem sequence_closure_filter (p : P) :
    IsPFilter (sequenceClosure e he D hD p) := by
  have hanti : Antitone (sequence e he D hD p) :=
    antitone_nat_of_succ_le (fun n => ((sequence_spec e he D hD p).2.1 n).2)
  apply IsPFilter.of_def
  · exact ⟨p,0,le_rfl⟩
  · rintro q ⟨i,hi⟩ r ⟨j,hj⟩
    exact ⟨sequence e he D hD p (max i j),⟨max i j,le_rfl⟩,
      (hanti (le_max_left i j)).trans hi,(hanti (le_max_right i j)).trans hj⟩
  · rintro q r hqr ⟨i,hi⟩
    exact ⟨i,hi.trans hqr⟩

noncomputable def sequenceFilter (p : P) : PFilter P :=
  (sequence_closure_filter e he D hD p).toPFilter

theorem sequence_filter_spec (p : P) :
    (∀ q, q ∈ sequenceFilter e he D hD p ↔ ∃ n, sequence e he D hD p n ≤ q) ∧
    p ∈ sequenceFilter e he D hD p ∧
    ∀ n, sequence e he D hD p (n+1) ∈ sequenceFilter e he D hD p ∧
      sequence e he D hD p (n+1) ∈ D n := by
  refine ⟨fun _ => Iff.rfl,⟨0,le_rfl⟩,?_⟩
  intro n
  exact ⟨⟨n+1,le_rfl⟩,((sequence_spec e he D hD p).2.1 n).1⟩
end Enumeration

theorem generic_through_countable_family [Countable P] (S : Set (Set P))
    (hS : S.Countable) (p : P) :
    ∃ G : PFilter P, p ∈ G ∧ GenericFor G S := by
  classical
  let : Nonempty P := ⟨p⟩
  obtain ⟨e,he⟩ := exists_surjective_nat P
  let T : Set (Set P) := {D | D ∈ insert Set.univ S ∧ Dense D}
  have hT : T.Countable := (hS.insert Set.univ).mono (fun _ h => h.1)
  have hTne : T.Nonempty := ⟨Set.univ,Or.inl rfl,fun q => ⟨q,Set.mem_univ q,le_rfl⟩⟩
  obtain ⟨d,hd⟩ := hT.exists_surjective hTne
  let D : ℕ → Set P := fun n => (d n).val
  have hD : ∀ n, Dense (D n) := fun n => (d n).property.2
  refine ⟨sequenceFilter e he D hD p,(sequence_filter_spec e he D hD p).2.1,?_⟩
  intro A hA hAd
  let a : T := ⟨A,Or.inr hA,hAd⟩
  obtain ⟨n,hn⟩ := hd a
  refine ⟨sequence e he D hD p (n+1),(sequence_filter_spec e he D hD p).2.2 n |>.1,?_⟩
  have hnA : D n = A := congrArg Subtype.val hn
  exact hnA ▸ ((sequence_spec e he D hD p).2.1 n).1

section Top
variable [OrderTop P]

theorem dense_iff_denseBelow_top (D : Set P) : Dense D ↔ DenseBelow D ⊤ := by
  exact ⟨fun h q _ => h q,fun h q => h q le_top⟩

end Top
end
end Lemmatheca.SetTheory.ForcingAndGenericFilters
