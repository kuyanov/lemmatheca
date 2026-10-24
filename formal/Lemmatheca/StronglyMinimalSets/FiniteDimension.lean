import Lemmatheca.StronglyMinimalSets.Pregeometry
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Induction
import Mathlib.Order.WellFounded

namespace Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
universe w
noncomputable section
variable {X : Type w} (P : Pregeometry X)
local instance : DecidableEq X := Classical.decEq X

def greedyStep (B : Finset X) (a : X) : Finset X := by
  classical
  exact if a ∈ P.cl (B : Set X) then B else insert a B

def greedy (l : List X) : Finset X := l.foldl P.greedyStep ∅

private theorem greedy_invariant (l : List X) :
    P.Independent (P.greedy l : Set X) ∧ P.greedy l ⊆ l.toFinset ∧
    P.cl (P.greedy l : Set X) = P.cl (l.toFinset : Set X) := by
  classical
  induction l using List.reverseRecOn with
  | nil => exact ⟨by simpa [greedy] using P.independent_empty,by simp [greedy],by simp [greedy]⟩
  | append_singleton l a ih =>
    have hg : P.greedy (l ++ [a]) = P.greedyStep (P.greedy l) a := by simp [greedy,List.foldl_append]
    rw [hg]
    by_cases ha : a ∈ P.cl (P.greedy l : Set X)
    · rw [greedyStep,ite_eq_left ha]
      refine ⟨ih.1,?_,?_⟩
      · intro x hx
        simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.mem_union]
        exact Or.inl (ih.2.1 hx)
      · have hcl := P.closure_insert_of_mem (I := (l.toFinset : Set X)) (by rw [← ih.2.2]; exact ha)
        simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.coe_union,Finset.coe_singleton] using ih.2.2.trans hcl.symm
    · rw [greedyStep,ite_eq_right ha]
      refine ⟨by simpa only [Finset.coe_insert,Set.insert_eq,Set.union_comm] using P.independent_adjoin ih.1 ha,?_,?_⟩
      · intro x hx
        simp only [Finset.mem_insert,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.mem_union] at hx ⊢
        rcases hx with hxa | hx
        · exact Or.inr (Finset.mem_singleton.mpr hxa)
        · exact Or.inl (ih.2.1 hx)
      · simp only [Finset.coe_insert,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.coe_union,Finset.coe_singleton]
        apply Set.Subset.antisymm
        · rw [← P.idempotent (l.toFinset ∪ {a})]
          apply P.monotone
          intro x hx
          rcases hx with rfl | hx
          · exact P.extensive _ (Or.inr (Set.mem_singleton _))
          · exact P.monotone Set.subset_union_left (ih.2.2 ▸ P.extensive _ hx)
        · rw [← P.idempotent (insert a (↑(P.greedy l) : Set X))]
          apply P.monotone
          intro x hx
          rcases hx with hx | hx
          · apply P.monotone (B := insert a (↑(P.greedy l) : Set X)) (fun z hz => Or.inr hz)
            rw [ih.2.2]
            exact P.extensive _ hx
          · have hxa : x = a := hx
            exact P.extensive _ (Or.inl hxa)

theorem greedy_prefix_invariant (l : List X) (k : ℕ) (hk : k ≤ l.length) :
    P.Independent (P.greedy (l.take k) : Set X) ∧
      P.greedy (l.take k) ⊆ (l.take k).toFinset ∧
      P.cl (P.greedy (l.take k) : Set X) = P.cl ((l.take k).toFinset : Set X) := by
  have _ := hk
  exact P.greedy_invariant (l.take k)

def finiteBasis (S : Finset X) : Finset X := P.greedy S.toList

theorem finiteBasis_spec (S : Finset X) :
    P.finiteBasis S ⊆ S ∧ P.IsBasis (P.finiteBasis S : Set X) (P.cl (S : Set X)) := by
  have h := P.greedy_invariant S.toList
  have hs : S.toList.toFinset = S := by simp
  change P.greedy S.toList ⊆ S ∧ _
  refine ⟨by simpa only [hs] using h.2.1,?_,h.1,?_⟩
  · intro x hx
    exact P.extensive (S : Set X) ((by simpa only [hs] using h.2.1 : P.greedy S.toList ⊆ S) hx)
  · simpa only [finiteBasis,hs] using h.2.2

theorem empty_basis : P.IsBasis ∅ (P.cl ∅) := by
  exact ⟨P.extensive ∅,P.independent_empty,rfl⟩

theorem minimal_support {S : Finset X} {a : X} (ha : a ∈ P.cl (S : Set X)) :
    ∃ F : Finset X, F ⊆ S ∧ a ∈ P.cl (F : Set X) ∧
      ∀ G : Finset X, G ⊂ F → a ∉ P.cl (G : Set X) := by
  classical
  let T : Set (Finset X) := {F | F ⊆ S ∧ a ∈ P.cl (F : Set X)}
  obtain ⟨F,hF,hmin⟩ := (measure (fun F : Finset X => F.card)).wf.has_min T ⟨S,Finset.Subset.refl S,ha⟩
  refine ⟨F,hF.1,hF.2,?_⟩
  intro G hGF haG
  exact hmin G ⟨hGF.subset.trans hF.1,haG⟩ (Finset.card_lt_card hGF)

theorem replacement_step (S R : Finset X) (a : X) (hR : R ⊆ S)
    (ha : a ∉ S) (hspan : a ∈ P.cl (S : Set X)) (hnew : a ∉ P.cl (R : Set X)) :
    ∃ (F : Finset X) (b : X), F ⊆ S ∧ a ∈ P.cl (F : Set X) ∧
      (∀ G : Finset X, G ⊂ F → a ∉ P.cl (G : Set X)) ∧
      b ∈ F ∧ b ∉ R ∧
      letI := Classical.propDecidable
      let S' := insert a (S.erase b)
      S'.card = S.card ∧ R ⊆ S' ∧ a ∈ S' ∧ P.cl (S' : Set X) = P.cl (S : Set X) := by
  classical
  obtain ⟨F,hFS,haF,hmin⟩ := P.minimal_support hspan
  have hFR : ¬F ⊆ R := fun h => hnew (P.monotone (by intro x hx; exact h hx) haF)
  obtain ⟨b,hbF,hbR⟩ := Finset.not_subset.mp hFR
  have hbS := hFS hbF
  have haerase := hmin (F.erase b) (Finset.erase_ssubset hbF)
  have hbcl : b ∈ P.cl (((F.erase b : Finset X) : Set X) ∪ {a}) :=
    P.exchange (F.erase b : Set X) b a ⟨by
      apply P.monotone (B := (F.erase b : Set X) ∪ {b}) ?_ haF
      intro z hz
      by_cases hzb : z = b
      · exact Or.inr hzb
      · exact Or.inl (Finset.mem_erase.mpr ⟨hzb,hz⟩),haerase⟩
  let S' := insert a (S.erase b)
  have hsub : ((F.erase b : Finset X) : Set X) ∪ {a} ⊆ (S' : Set X) := by
    intro z hz
    rcases hz with hz | hz
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,hFS (Finset.mem_erase.mp hz).2⟩)
    · exact Finset.mem_insert.mpr (Or.inl hz)
  refine ⟨F,b,hFS,haF,hmin,hbF,hbR,?_,?_,Finset.mem_insert_self _ _,?_⟩
  · exact (Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h))).trans
      (by rw [Finset.card_erase_of_mem hbS]; exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨b,hbS⟩))
  · intro z hz
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by intro h; exact hbR (h ▸ hz),hR hz⟩)
  · apply Set.Subset.antisymm
    · rw [← P.idempotent (S : Set X)]
      apply P.monotone
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hspan
      · exact P.extensive _ (Finset.mem_of_mem_erase hz)
    · rw [← P.idempotent (S' : Set X)]
      apply P.monotone
      intro z hz
      by_cases hzb : z = b
      · exact hzb.symm ▸ P.monotone hsub hbcl
      · exact P.extensive _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzb,hz⟩))

theorem steinitz_replacement_sequence (S : Finset X) (l : List X) (hl : l.Nodup)
    (hi : P.Independent (l.toFinset : Set X))
    (hspan : (l.toFinset : Set X) ⊆ P.cl (S : Set X)) :
    ∃ G : ℕ → Finset X, G 0 = S ∧
      (∀ j ≤ l.length, (G j).card = S.card ∧
        P.cl (G j : Set X) = P.cl (S : Set X) ∧ (l.take j).toFinset ⊆ G j) ∧
      ∀ (j : ℕ) (hj : j < l.length), G (j+1) = G j ∨
        ∃ b ∈ G j, b ∉ (l.take j).toFinset ∧
          letI := Classical.propDecidable
          G (j+1) = insert (l.get ⟨j,hj⟩) ((G j).erase b) := by
  classical
  let H (j : ℕ) (T : Finset X) : Prop := T.card = S.card ∧
    P.cl (T : Set X) = P.cl (S : Set X) ∧ (l.take j).toFinset ⊆ T
  let Rule (j : ℕ) (T U : Finset X) : Prop := U = T ∨
    ∃ hj : j < l.length, ∃ b ∈ T, b ∉ (l.take j).toFinset ∧
      U = insert (l.get ⟨j,hj⟩) (T.erase b)
  have hstep (j : ℕ) (hj : j < l.length) (T : Finset X) (hT : H j T) :
      ∃ U : Finset X, H (j+1) U ∧ Rule j T U := by
    let a := l.get ⟨j,hj⟩
    have htake : (l.take (j+1)).toFinset = insert a (l.take j).toFinset := by
      rw [List.take_succ_eq_append_getElem hj]
      simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,Finset.union_singleton]
      rfl
    by_cases ha : a ∈ T
    · refine ⟨T,⟨hT.1,hT.2.1,?_⟩,Or.inl rfl⟩
      rw [htake]
      exact Finset.insert_subset ha hT.2.2
    · have haI : a ∈ l.toFinset := List.mem_toFinset.mpr (List.get_mem l ⟨j,hj⟩)
      have hanot : a ∉ (l.take j).toFinset := by
        intro h
        have hadrop : a ∈ l.drop j := by
          rw [← List.getElem_cons_drop hj]
          exact List.mem_cons_self
        exact List.disjoint_take_drop hl (le_refl j) (List.mem_toFinset.mp h) hadrop
      have hpref : ((l.take j).toFinset : Set X) ⊆ (l.toFinset : Set X) \ {a} := by
        intro z hz
        refine ⟨List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hz)),?_⟩
        intro hza
        have h : z = a := hza
        exact hanot (h ▸ hz)
      have hnew : a ∉ P.cl ((l.take j).toFinset : Set X) := by
        intro h
        exact hi a haI (P.monotone hpref h)
      have haspan : a ∈ P.cl (T : Set X) := hT.2.1.symm ▸ hspan haI
      obtain ⟨F,b,hFT,_,_,hbF,hbR,hcard,hret,haU,hcl⟩ :=
        P.replacement_step T (l.take j).toFinset a hT.2.2 ha haspan hnew
      let U := insert a (T.erase b)
      have hbT : b ∈ T := hFT hbF
      refine ⟨U,⟨hcard.trans hT.1,hcl.trans hT.2.1,?_⟩,Or.inr ⟨hj,b,hbT,hbR,rfl⟩⟩
      rw [htake]
      exact Finset.insert_subset haU hret
  let next (j : ℕ) (T : Finset X) : Finset X :=
    if h : ∃ U, H (j+1) U ∧ Rule j T U then Classical.choose h else T
  let G : ℕ → Finset X := Nat.rec S next
  have hG (j : ℕ) (hj : j ≤ l.length) : H j (G j) := by
    induction j with
    | zero => exact ⟨rfl,rfl,by simp [G]⟩
    | succ j ih =>
      have hp : ∃ U, H (j+1) U ∧ Rule j (G j) U := hstep j (Nat.lt_of_succ_le hj) (G j) (ih (Nat.le_of_succ_le hj))
      change H (j+1) (next j (G j))
      dsimp only [next]
      rw [dite_eq_left hp]
      exact (Classical.choose_spec hp).1
  refine ⟨G,rfl,hG,?_⟩
  intro j hj
  have hp : ∃ U, H (j+1) U ∧ Rule j (G j) U := hstep j hj (G j) (hG j hj.le)
  have hr : Rule j (G j) (G (j+1)) := by
    change Rule j (G j) (next j (G j))
    dsimp only [next]
    rw [dite_eq_left hp]
    exact (Classical.choose_spec hp).2
  rcases hr with hr | ⟨hj',b,hb,hbr,he⟩
  · exact Or.inl hr
  · exact Or.inr ⟨b,hb,hbr,he⟩

theorem finite_exchange_bound (I S : Finset X)
    (hi : P.Independent (I : Set X)) (hspan : (I : Set X) ⊆ P.cl (S : Set X)) :
    I.card ≤ S.card := by
  classical
  obtain ⟨G,_,hG,_⟩ := P.steinitz_replacement_sequence S I.toList I.nodup_toList
    (by simpa using hi) (by simpa using hspan)
  have h := hG I.toList.length le_rfl
  have hsub : I ⊆ G I.toList.length := by simpa only [List.take_length,Finset.toList_toFinset] using h.2.2
  exact (Finset.card_le_card hsub).trans_eq h.1

theorem finite_basis_card_eq (C : Set X) (B D : Finset X)
    (hB : P.IsBasis (B : Set X) C) (hD : P.IsBasis (D : Set X) C) :
    B.card = D.card := by
  apply Nat.le_antisymm
  · exact P.finite_exchange_bound B D hB.2.1 (by rw [hD.2.2]; exact hB.1)
  · exact P.finite_exchange_bound D B hD.2.1 (by rw [hB.2.2]; exact hD.1)

def finiteDimension (C : Set X) (hC : P.FinitelyGenerated C) : ℕ :=
  (P.finiteBasis (Classical.choose hC)).card

theorem finiteDimension_eq_card (C : Set X) (hC : P.FinitelyGenerated C)
    (B : Finset X) (hB : P.IsBasis (B : Set X) C) :
    P.finiteDimension C hC = B.card := by
  unfold finiteDimension
  have hs := P.finiteBasis_spec (Classical.choose hC)
  have he := Classical.choose_spec hC
  exact P.finite_basis_card_eq C _ B (by simpa only [he] using hs.2) hB

theorem finitelyGenerated_finite_basis (C : Set X) (hC : P.FinitelyGenerated C) :
    P.Closed C ∧ ∃ B : Finset X, P.IsBasis (B : Set X) C ∧
      B.card = P.finiteDimension C hC := by
  obtain ⟨S,hS⟩ := hC
  have hb := (P.finiteBasis_spec S).2
  rw [hS] at hb
  exact ⟨by change P.cl C = C; rw [← hS,P.idempotent],P.finiteBasis S,hb,(P.finiteDimension_eq_card C ⟨S,hS⟩ _ hb).symm⟩

end
end Lemmatheca.ModelTheory.StronglyMinimalSets.Pregeometry
