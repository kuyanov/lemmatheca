import Lemmatheca.MonadicLogic.Invariance

namespace Lemmatheca.MathematicalLogic.MonadicLogic
open FirstOrder FirstOrder.Language Structure

/-- Restriction to a finite subset; there are no constants requiring closure. -/
@[instance_reducible]
def restrictedStructure {k : ℕ} {M : Type*} [(lang k).Structure M] (D : Finset M) :
    (lang k).Structure D :=
  inferInstanceAs ((lang k).Structure (ExistentialUniversalSentences.induced 0 (arities k) D (fun i => i.elim0)))

noncomputable def Capped {M P : Type*} (r : ℕ) (π : M → P) (D : Finset M) : Prop := by
  classical
  exact ∀ p, (D.filter (fun x => π x = p)).card ≤ r ∧
    ((D.filter (fun x => π x = p)).card = r ∨ ∀ x, π x = p → x ∈ D)

private theorem finite_sample {M : Type*} (S : Set M) (r : ℕ) :
    ∃ A : Finset M, (∀ x ∈ A, x ∈ S) ∧ A.card ≤ r ∧
      (A.card = r ∨ ∀ x ∈ S, x ∈ A) := by
  classical
  induction r with
  | zero => exact ⟨∅,by simp,by simp,Or.inl rfl⟩
  | succ r ih =>
    obtain ⟨A,hAS,hcard,hfull⟩ := ih
    by_cases hcover : ∀ x ∈ S, x ∈ A
    · exact ⟨A,hAS,hcard.trans (Nat.le_succ _),Or.inr hcover⟩
    · have hcardr : A.card = r := hfull.resolve_right hcover
      push Not at hcover
      obtain ⟨x,hxS,hxA⟩ := hcover
      refine ⟨insert x A,?_,?_,Or.inl ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxS
        · exact hAS y hy
      · simp [Finset.card_insert_of_notMem hxA,hcardr]
      · simp [Finset.card_insert_of_notMem hxA,hcardr]

private theorem capacities_of_capped {M P : Type*} (r : ℕ) (π : M → P)
    (D : Finset M) (hC : Capped r π D) : Capacities r π (fun x : D => π x.val) := by
  classical
  intro p
  let A := D.filter (fun x => π x = p)
  let B : Finset D := A.subtype (fun x => x ∈ D)
  have hAB : A.card = B.card := by
    dsimp [B]
    rw [Finset.card_subtype]
    congr 1
    ext x
    simp [A, and_comm, and_left_comm]
  have hB : ∀ y : D, π y.val = p ↔ y ∈ B := by
    intro y
    simp [B,A]
  have hA : ∀ x ∈ A, π x = p := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨hcle,hfull⟩ := hC p
  by_cases hcr : A.card = r
  · exact Or.inr ⟨⟨A,hcr,hA⟩,⟨B,hAB.symm.trans hcr,fun y hy => (hB y).mpr hy⟩⟩
  · have hfull' : ∀ x, π x = p → x ∈ D := hfull.resolve_left hcr
    refine Or.inl ⟨A,B,?_,hB,hAB,lt_of_le_of_ne hcle hcr⟩
    intro x
    constructor
    · intro hp
      exact Finset.mem_filter.mpr ⟨hfull' x hp,hp⟩
    · exact fun hx => hA x hx

private theorem profile_restricted {k : ℕ} {M : Type*} [(lang k).Structure M]
    (D : Finset M) :
    letI := restrictedStructure (k := k) D
    ∀ x : D, profile (k := k) x = profile (k := k) (M := M) x.val := by
  intro x
  rfl

theorem capped_representatives {k : ℕ} {M : Type*} [(lang k).Structure M] [Nonempty M]
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : Finset M, D.Nonempty ∧ D.card ≤ r * 2^k ∧ Capped r (profile (k := k)) D ∧
      (letI := restrictedStructure (k := k) D
       Capacities r (profile (k := k) (M := M)) (profile (k := k) (M := D))) := by
  classical
  let : DecidableEq (Profile k) := Classical.decEq _
  choose A hAS hcard hfull using
    (fun p : Profile k => finite_sample {x : M | profile (k := k) x = p} r)
  let D : Finset M := Finset.univ.biUnion A
  have hAD : ∀ p, A p ⊆ D := by
    intro p x hx
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ p,hx⟩
  have hfilter : ∀ p, D.filter (fun x => profile (k := k) x = p) = A p := by
    intro p
    ext x
    constructor
    · intro hx
      obtain ⟨hxD,hxp⟩ := Finset.mem_filter.mp hx
      obtain ⟨p',_,hxp'⟩ := Finset.mem_biUnion.mp hxD
      have he : p' = p := (hAS p' x hxp').symm.trans hxp
      exact he ▸ hxp'
    · intro hx
      exact Finset.mem_filter.mpr ⟨hAD p hx,hAS p x hx⟩
  have hC : Capped r (profile (k := k)) D := by
    intro p
    change (D.filter (fun x => profile (k := k) x = p)).card ≤ r ∧
      ((D.filter (fun x => profile (k := k) x = p)).card = r ∨
        ∀ x, profile (k := k) x = p → x ∈ D)
    have hc := congrArg Finset.card (hfilter p)
    refine ⟨hc.trans_le (hcard p),?_⟩
    rcases hfull p with hlarge | hcomplete
    · exact Or.inl (hc.trans hlarge)
    · exact Or.inr (fun x hx => hAD p (hcomplete x hx))
  have hDcard : D.card ≤ r * 2^k := by
    calc
      D.card ≤ ∑ p ∈ Finset.univ, (A p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : Profile k, r := Finset.sum_le_sum (fun p _ => hcard p)
      _ = r * 2^k := by simp [Profile, Nat.mul_comm]
  have hne : D.Nonempty := by
    let a : M := Classical.choice inferInstance
    rcases hfull (profile (k := k) a) with hlarge | hcomplete
    · have hpos : 0 < (A (profile (k := k) a)).card := by omega
      obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
      exact ⟨x,hAD _ hx⟩
    · exact ⟨a,hAD _ (hcomplete a rfl)⟩
  refine ⟨D,hne,hDcard,hC,?_⟩
  let := restrictedStructure (k := k) D
  have hp : profile (k := k) (M := D) = fun x : D => profile (k := k) (M := M) x.val := by
    funext x
    exact profile_restricted (k := k) D x
  rw [hp]
  exact capacities_of_capped r _ D hC

def bound {k : ℕ} (φ : (lang k).Sentence) : ℕ := max 1 (quantifiers φ) * 2^k

theorem bound_positive {k : ℕ} (φ : (lang k).Sentence) : 0 < bound φ := by
  exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (pow_pos (by decide) _)

theorem top_zero_bound : quantifiers (⊤ : (lang 0).Sentence) = 0 ∧
    bound (⊤ : (lang 0).Sentence) = 1 := by
  constructor <;> rfl

theorem small_submodel {k : ℕ} {M : Type*} [(lang k).Structure M] [Nonempty M]
    (φ : (lang k).Sentence) (hφ : M ⊨ φ) :
    ∃ D : Finset M, D.Nonempty ∧ D.card ≤ bound φ ∧
      (letI := restrictedStructure (k := k) D
       D ⊨ φ) := by
  obtain ⟨D,hne,hcard,_,hcap⟩ := capped_representatives (k := k) (M := M) (max 1 (quantifiers φ)) (le_max_left _ _)
  let := restrictedStructure (k := k) D
  have hmatch : Matching (profile (k := k) (M := M)) (profile (k := k) (M := D))
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → D) :=
    ⟨fun i => i.elim0,fun i => i.elim0⟩
  have ht := truth_invariance hcap φ Fin.elim0 Fin.elim0 hmatch
    (by simpa only [Nat.zero_add] using le_max_right 1 (quantifiers φ))
  refine ⟨D,hne,hcard,?_⟩
  have hM : BoundedFormula.Realize (M := M) φ Empty.elim Fin.elim0 := by
    change BoundedFormula.Realize φ _ _ at hφ
    convert hφ using 1
  have hD := ht.mp hM
  change BoundedFormula.Realize φ _ _
  convert hD using 1

theorem bounded_table_model {k : ℕ} {M : Type*} [(lang k).Structure M] [Nonempty M]
    (φ : (lang k).Sentence) (hφ : M ⊨ φ) :
    ∃ d < bound φ, ∃ T : ExistentialUniversalSentences.Table 0 (arities k) d,
      ExistentialUniversalSentences.evaluate 0 (arities k) T φ Fin.elim0 = true := by
  classical
  obtain ⟨D,hne,hcard,hD⟩ := small_submodel φ hφ
  let := restrictedStructure (k := k) D
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hne)
  let e : D ≃ Fin (d+1) := (Fintype.equivFin D).trans
    (finCongr ((Fintype.card_coe D).trans hd))
  let : (lang k).Structure (Fin (d+1)) := e.inducedStructure
  have hfin : (Fin (d+1)) ⊨ φ :=
    (StrongHomClass.realize_sentence e.inducedStructureEquiv φ).mp hD
  refine ⟨d,by omega,ExistentialUniversalSentences.tableFromStructure 0 (arities k) d,?_⟩
  apply (ExistentialUniversalSentences.evaluate_correct 0 (arities k) _ φ Fin.elim0).mpr
  rw [ExistentialUniversalSentences.tableFromStructure_eq]
  change BoundedFormula.Realize φ _ _ at hfin
  convert hfin using 1

end Lemmatheca.MathematicalLogic.MonadicLogic
