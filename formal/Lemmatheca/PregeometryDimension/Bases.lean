import Lemmatheca.StronglyMinimalSets.FiniteDimension
import Mathlib.Data.Set.Card
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Finite.Lattice

namespace Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
universe w
noncomputable section
variable {X : Type w} (P : Pregeometry X)

theorem independent_iff_finite_subsets (I : Set X) :
    P.Independent I ↔ ∀ F : Finset X, (F : Set X) ⊆ I → P.Independent (F : Set X) := by
  classical
  constructor
  · intro hi F hF
    exact P.independent_subset hi hF
  · intro hf a ha hcl
    obtain ⟨F, hF, haF⟩ := (P.finite_character a (I \ {a})).mp hcl
    have hsub : (↑(insert a F) : Set X) ⊆ I := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · exact (hF hx).1
    have hh := hf (insert a F) hsub a (Finset.mem_insert_self a F)
    apply hh
    apply P.monotone (B := (↑(insert a F) : Set X) \ {a}) ?_ haF
    intro x hx
    exact ⟨Finset.mem_insert_of_mem hx, (hF hx).2⟩

theorem independent_sUnion_chain (c : Set (Set X))
    (hc : IsChain (· ⊆ ·) c) (hi : ∀ I ∈ c, P.Independent I) :
    P.Independent (⋃₀ c) := by
  classical
  apply (P.independent_iff_finite_subsets _).2
  intro F hF
  by_cases hn : c.Nonempty
  · obtain ⟨J, hJ, hFJ⟩ :=
      hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hn F.finite_toSet hF
    exact P.independent_subset (hi J hJ) hFJ
  · have he : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hfe : F = ∅ := by simpa [he] using hF
    subst F
    simpa using P.independent_empty

theorem exists_basis_extension {I S : Set X} (hi : P.Independent I) (his : I ⊆ S) :
    ∃ B : Set X, I ⊆ B ∧ B ⊆ S ∧ P.Independent B ∧ P.cl B = P.cl S := by
  classical
  let family : Set (Set X) := {J | J ⊆ S ∧ P.Independent J}
  have hchainbound : ∀ c ⊆ family, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ family, ∀ J ∈ c, J ⊆ ub := by
    intro c hcf hchain _
    refine ⟨⋃₀ c, ⟨?_, P.independent_sUnion_chain c hchain (fun J hJ => (hcf hJ).2)⟩, ?_⟩
    · exact Set.sUnion_subset (fun J hJ => (hcf hJ).1)
    · intro J hJ
      exact Set.subset_sUnion_of_mem hJ
  obtain ⟨B, hiB, hB⟩ := zorn_subset_nonempty family hchainbound I ⟨his, hi⟩
  refine ⟨B, hiB, hB.1.1, hB.1.2, ?_⟩
  have hspan : S ⊆ P.cl B := by
    intro a ha
    by_contra hn
    have hadj : B ∪ {a} ∈ family :=
      ⟨Set.union_subset hB.1.1 (Set.singleton_subset_iff.mpr ha),
        P.independent_adjoin hB.1.2 hn⟩
    have hb := hB.2 hadj Set.subset_union_left
    exact hn (P.extensive B (hb (Or.inr rfl)))
  apply Set.Subset.antisymm
  · exact P.monotone hB.1.1
  · simpa only [P.idempotent] using P.monotone hspan

theorem exists_closed_basis_extension {I C : Set X} (hC : P.Closed C)
    (hi : P.Independent I) (hiC : I ⊆ C) :
    ∃ B : Set X, I ⊆ B ∧ P.IsBasis B C := by
  obtain ⟨B, hiB, hBC, hb, hcl⟩ := P.exists_basis_extension hi hiC
  exact ⟨B, hiB, hBC, hb, hcl.trans hC⟩

theorem maximal_independent_iff_span {B S : Set X} (hb : P.Independent B) (hbs : B ⊆ S) :
    (∀ J : Set X, B ⊆ J → J ⊆ S → P.Independent J → J = B) ↔ P.cl B = P.cl S := by
  constructor
  · intro hm
    have hs : S ⊆ P.cl B := by
      intro a ha
      by_contra hn
      have he := hm (B ∪ {a}) Set.subset_union_left
        (Set.union_subset hbs (Set.singleton_subset_iff.mpr ha))
        (P.independent_adjoin hb hn)
      exact hn (P.extensive B (he ▸ (Or.inr rfl : a ∈ B ∪ {a})))
    exact Set.Subset.antisymm (P.monotone hbs)
      (by simpa only [P.idempotent] using P.monotone hs)
  · intro hcl J hBJ hJS hJ
    apply Set.Subset.antisymm ?_ hBJ
    intro a ha
    by_contra hn
    have haCl : a ∈ P.cl B := hcl ▸ P.extensive S (hJS ha)
    apply hJ a ha
    have hsub : B ⊆ J \ {a} := by
      intro x hx
      refine ⟨hBJ hx, ?_⟩
      intro hxa
      have he : x = a := hxa
      exact hn (he ▸ hx)
    exact P.monotone hsub haCl

theorem finite_span_bound {I : Set X} (F : Finset X) (hi : P.Independent I)
    (hspan : I ⊆ P.cl (F : Set X)) : I.Finite ∧ I.ncard ≤ F.card := by
  classical
  have hfin : I.Finite := by
    by_contra hn
    have hInf : I.Infinite := hn
    obtain ⟨J, hJI, hJfin, hJcard⟩ := hInf.exists_subset_ncard_eq (F.card + 1)
    have hle := P.finite_exchange_bound hJfin.toFinset F
      (P.independent_subset hi (by simpa using hJI)) (by simpa using hJI.trans hspan)
    rw [← Set.ncard_eq_toFinset_card J hJfin, hJcard] at hle
    omega
  refine ⟨hfin, ?_⟩
  simpa only [Set.ncard_eq_toFinset_card I hfin] using
    P.finite_exchange_bound hfin.toFinset F (by simpa using hi) (by simpa using hspan)

theorem finite_support_cover {B D C : Set X} (hB : P.IsBasis B C) (hD : P.IsBasis D C)
    (F : B → Finset X) (hF : ∀ b : B, (F b : Set X) ⊆ D ∧ b.1 ∈ P.cl (F b : Set X)) :
    D = ⋃ b : B, (F b : Set X) := by
  classical
  let U : Set X := ⋃ b : B, (F b : Set X)
  have hUD : U ⊆ D := Set.iUnion_subset fun b => (hF b).1
  have hBU : B ⊆ P.cl U := by
    intro b hb
    exact P.monotone (Set.subset_iUnion (fun b : B => (F b : Set X)) ⟨b, hb⟩) (hF ⟨b, hb⟩).2
  have hDU : D ⊆ P.cl U := by
    intro d hd
    have hc : C ⊆ P.cl U := by
      rw [← hB.2.2]
      simpa only [P.idempotent] using P.monotone hBU
    exact hc (hD.1 hd)
  apply Set.Subset.antisymm ?_ hUD
  intro d hd
  by_contra hn
  have hsub : U ⊆ D \ {d} := by
    intro x hx
    refine ⟨hUD hx, ?_⟩
    intro hxd
    have he : x = d := hxd
    exact hn (he ▸ hx)
  exact hD.2.1 d hd (P.monotone hsub (hDU hd))

theorem exists_finite_support_cover {B D C : Set X}
    (hB : P.IsBasis B C) (hD : P.IsBasis D C) :
    ∃ F : B → Finset X,
      (∀ b : B, (F b : Set X) ⊆ D ∧ b.1 ∈ P.cl (F b : Set X)) ∧
      D = ⋃ b : B, (F b : Set X) := by
  classical
  have hex : ∀ b : B, ∃ F : Finset X, (F : Set X) ⊆ D ∧ b.1 ∈ P.cl (F : Set X) := by
    intro b
    apply (P.finite_character b.1 D).mp
    rw [hD.2.2]
    exact hB.1 b.2
  choose F hF using hex
  exact ⟨F, hF, P.finite_support_cover hB hD F hF⟩

theorem infinite_basis_cardinal_le {B D C : Set X}
    (hB : P.IsBasis B C) (hD : P.IsBasis D C) (hbi : B.Infinite) :
    Cardinal.mk D ≤ Cardinal.mk B := by
  classical
  obtain ⟨F, _, hcover⟩ := P.exists_finite_support_cover hB hD
  have : Infinite B := hbi.to_subtype
  calc
    Cardinal.mk D = Cardinal.mk (⋃ b : B, (F b : Set X)) := congrArg (fun s : Set X => Cardinal.mk s) hcover
    _ ≤ Cardinal.mk B * ⨆ b : B, Cardinal.mk (F b : Set X) := Cardinal.mk_iUnion_le _
    _ ≤ Cardinal.mk B * Cardinal.aleph0 := by
      gcongr
      apply ciSup_le
      intro b
      have : Finite (F b : Set X) := (F b).finite_toSet
      exact Cardinal.mk_le_aleph0
    _ = Cardinal.mk B := Cardinal.mk_mul_aleph0_eq

theorem basis_cardinal_eq {B D C : Set X} (hB : P.IsBasis B C) (hD : P.IsBasis D C) :
    Cardinal.mk B = Cardinal.mk D := by
  classical
  have finite_case {B D : Set X} (hB : P.IsBasis B C) (hD : P.IsBasis D C) (hb : B.Finite) :
      Cardinal.mk D ≤ Cardinal.mk B := by
    have hd := P.finite_span_bound hb.toFinset hD.2.1
      (by simpa only [hb.coe_toFinset, hB.2.2] using hD.1)
    rw [← Set.cast_ncard hd.1, ← Set.cast_ncard hb]
    exact_mod_cast (by simpa only [← Set.ncard_eq_toFinset_card B hb] using hd.2)
  apply le_antisymm
  · rcases D.finite_or_infinite with hd | hd
    · exact finite_case hD hB hd
    · exact P.infinite_basis_cardinal_le hD hB hd
  · rcases B.finite_or_infinite with hb | hb
    · exact finite_case hB hD hb
    · exact P.infinite_basis_cardinal_le hB hD hb

theorem exists_generating_basis (S : Set X) :
    ∃ B : Set X, B ⊆ S ∧ P.Independent B ∧ P.cl B = P.cl S := by
  obtain ⟨B, _, hBS, hi, hcl⟩ := P.exists_basis_extension P.independent_empty (Set.empty_subset S)
  exact ⟨B, hBS, hi, hcl⟩

def chosenBasis (S : Set X) : Set X := Classical.choose (P.exists_generating_basis S)

theorem chosenBasis_spec (S : Set X) :
    P.chosenBasis S ⊆ S ∧ P.Independent (P.chosenBasis S) ∧
      P.cl (P.chosenBasis S) = P.cl S := by
  exact Classical.choose_spec (P.exists_generating_basis S)

def dimension (S : Set X) : Cardinal.{w} := Cardinal.mk (P.chosenBasis S)

theorem dimension_eq_mk {S B : Set X} (hB : P.IsBasis B (P.cl S)) :
    P.dimension S = Cardinal.mk B := by
  have hs := P.chosenBasis_spec S
  exact P.basis_cardinal_eq
    ⟨hs.1.trans (P.extensive S), hs.2.1, hs.2.2⟩ hB

theorem dimension_closure (S : Set X) : P.dimension (P.cl S) = P.dimension S := by
  have hs := P.chosenBasis_spec S
  calc
    P.dimension (P.cl S) = Cardinal.mk (P.chosenBasis S) :=
      P.dimension_eq_mk ⟨hs.1.trans ((P.extensive S).trans (P.extensive (P.cl S))), hs.2.1, hs.2.2.trans (P.idempotent S).symm⟩
    _ = P.dimension S := rfl

theorem dimension_eq_finiteDimension (C : Set X) (hC : P.FinitelyGenerated C) :
    P.dimension C = (P.finiteDimension C hC : Cardinal.{w}) := by
  obtain ⟨hclosed, F, hF, hcard⟩ := P.finitelyGenerated_finite_basis C hC
  calc
    P.dimension C = Cardinal.mk (F : Set X) :=
      P.dimension_eq_mk (by simpa only [(show P.cl C = C from hclosed)] using hF)
    _ = (F.card : Cardinal.{w}) := by simp
    _ = (P.finiteDimension C hC : Cardinal.{w}) := congrArg Nat.cast hcard

end
end Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
