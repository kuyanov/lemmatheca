import Lemmatheca.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories.Countability
namespace Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
universe u v
noncomputable section
local instance primeHenkinConstructionPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
local instance primeHenkinConstructionFormulaEq {L : Language.{u,v}} : DecidableEq (Fml L) := Classical.decEq _
variable {L : Language.{u,v}}
/-- The even-indexed members of the increasing enumeration of the unused supply. -/
def reserve (U : Universe) : Set ℕ := Set.range (fun n => Nat.nth (fun c => c ∉ U.carrier) (2*n))
/-- The odd-indexed members remain unused after enlargement. -/
def spare (U : Universe) : Set ℕ := Set.range (fun n => Nat.nth (fun c => c ∉ U.carrier) (2*n+1))
def enlargedCarrier (U : Universe) : Set ℕ := U.carrier ∪ reserve U

theorem reserve_partition (U : Universe) :
    (reserve U).Infinite ∧ (spare U).Infinite ∧ Disjoint (reserve U) (spare U) ∧
    U.carrierᶜ = reserve U ∪ spare U ∧ Disjoint U.carrier (reserve U) ∧
    Disjoint U.carrier (spare U) := by
  let e := Nat.nth (fun c => c ∉ U.carrier)
  have hinf : (Set.ofPred (fun c => c ∉ U.carrier)).Infinite := U.infinite_compl
  have he : Function.Injective e := Nat.nth_injective hinf
  have hmem (n : ℕ) : e n ∉ U.carrier := Nat.nth_mem_of_infinite hinf n
  have hR : (reserve U).Infinite := Set.infinite_range_of_injective
    (he.comp (by intro a b h; change 2*a = 2*b at h; omega : Function.Injective (fun n : ℕ => 2*n)))
  have hS : (spare U).Infinite := Set.infinite_range_of_injective
    (he.comp (by intro a b h; change 2*a+1 = 2*b+1 at h; omega : Function.Injective (fun n : ℕ => 2*n+1)))
  have hRS : Disjoint (reserve U) (spare U) := by
    apply Set.disjoint_left.mpr
    rintro c ⟨n,hn⟩ ⟨m,hm⟩
    have h := he (hn.trans hm.symm)
    omega
  refine ⟨hR,hS,hRS,?_,?_,?_⟩
  · ext c
    constructor
    · intro hc
      have hr : Set.range e = U.carrierᶜ := Nat.range_nth_of_infinite hinf
      obtain ⟨n,rfl⟩ := hr.symm ▸ hc
      have hn : n % 2 < 2 := Nat.mod_lt _ (by decide)
      have hd := Nat.mod_add_div n 2
      by_cases hz : n % 2 = 0
      · left
        exact ⟨n/2,congrArg e (by omega)⟩
      · right
        exact ⟨n/2,congrArg e (by omega)⟩
    · rintro (⟨n,rfl⟩ | ⟨n,rfl⟩) <;> exact hmem _
  · apply Set.disjoint_left.mpr
    rintro c hc ⟨n,rfl⟩
    exact hmem _ hc
  · apply Set.disjoint_left.mpr
    rintro c hc ⟨n,rfl⟩
    exact hmem _ hc


theorem enlargement_complement_infinite (U : Universe) : (enlargedCarrier U)ᶜ.Infinite := by
  obtain ⟨_,hS,hRS,_,_,hUS⟩ := reserve_partition U
  apply hS.mono
  intro c hc
  rintro (hU | hR)
  · exact Set.disjoint_left.mp hUS hU hc
  · exact Set.disjoint_left.mp hRS hR hc

/-- The actual larger universe uses the fixed even half of unused names. -/
def enlargement (U : Universe) : Universe where
  carrier := enlargedCarrier U
  nonempty := U.nonempty.mono Set.subset_union_left
  infinite_compl := enlargement_complement_infinite U

theorem exists_fresh_reserve (U : Universe) (F : Finset ℕ) : ∃ c, c ∈ reserve U ∧ c ∉ F := by
  obtain ⟨c,hc,hF⟩ := ((reserve_partition U).1.sdiff F.finite_toSet).nonempty
  exact ⟨c,hc,hF⟩

/-- The specified least fresh numerical parameter. -/
def freshName (U : Universe) (F : Finset ℕ) : ℕ := Nat.find (exists_fresh_reserve U F)

theorem freshName_spec (U : Universe) (F : Finset ℕ) :
    freshName U F ∈ reserve U ∧ freshName U F ∉ F ∧
      ∀ c < freshName U F, c ∉ reserve U ∨ c ∈ F := by
  obtain ⟨hR,hF⟩ := Nat.find_spec (exists_fresh_reserve U F)
  refine ⟨hR,hF,?_⟩
  intro c hc
  have hn := Nat.find_min (exists_fresh_reserve U F) hc
  simpa only [not_not] using not_and_or.mp hn


section CountableLanguage
variable [Countable L.Symbols]

theorem full_syntax_countable (L : Language.{u,v}) [Countable L.Symbols] :
    Countable (Σ n, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) := by
  exact countable_native_scopes


theorem formulas_countable (L : Language.{u,v}) [Countable L.Symbols] : Countable (Fml L) := by
  let _ := full_syntax_countable L
  exact Function.Injective.countable (f := fun A : Fml L =>
    (⟨0,A⟩ : Σ n, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n))
      (fun _ _ h => by cases h; rfl)

/-- Enumerate actual equality-free supported native formulas, defaulting to falsum. -/
def enumeration (U : Universe) : ℕ → Fml L :=
  letI : Countable (Fml L) := formulas_countable L
  Set.enumerateCountable (Set.to_countable (eligible (L := L) (enlargement U).carrier)) .falsum

theorem enumeration_range (U : Universe) :
    Set.range (enumeration (L := L) U) = eligible (enlargement U).carrier := by
  let _ := formulas_countable L
  apply Set.range_enumerateCountable_of_mem
  exact ⟨trivial, by simp [Supported,BoundedFormula.freeVarFinset]⟩

/-- Names appearing in the avoided conclusion, candidate and finite stage additions. -/
def forbidden (B F : Fml L) (Δ : Finset (Fml L)) : Finset ℕ :=
  B.freeVarFinset ∪ F.freeVarFinset ∪ Δ.biUnion (fun A => A.freeVarFinset)
/-- Test avoidance, then immediately add a witness for an accepted existential. -/
def stageStep (U : Universe) (Γ : Set (Fml L)) (B : Fml L) (n : ℕ)
    (Δ : Finset (Fml L)) : Finset (Fml L) :=
  let F := enumeration U n
  if Provable (Γ ∪ (↑(insert F Δ) : Set (Fml L))) B then Δ
  else match F with
    | .ex D => insert (D.instantiate (.var (freshName U (forbidden B F Δ)))) (insert F Δ)
    | _ => insert F Δ
/-- Only finite additions are recorded; the original premise set can be infinite. -/
def stageAdditions (U : Universe) (Γ : Set (Fml L)) (B : Fml L) : ℕ → Finset (Fml L)
  | 0 => ∅
  | n+1 => stageStep U Γ B n (stageAdditions U Γ B n)
def stage (U : Universe) (Γ : Set (Fml L)) (B : Fml L) (n : ℕ) : Set (Fml L) :=
  Γ ∪ (↑(stageAdditions U Γ B n) : Set (Fml L))
/-- The specified extension is the actual union of its displayed stages. -/
def extension (U : Universe) (Γ : Set (Fml L)) (B : Fml L) : Set (Fml L) := ⋃ n, stage U Γ B n

private theorem stageStep_contains (U : Universe) (Γ : Set (Fml L)) (B : Fml L) (n : ℕ)
    (Δ : Finset (Fml L)) : Δ ⊆ stageStep U Γ B n Δ := by
  unfold stageStep
  dsimp only
  split_ifs
  · exact Finset.Subset.rfl
  · split
    · exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    · exact Finset.subset_insert _ _

omit [Countable L.Symbols] in
private theorem eligible_mono {U V : Set ℕ} (hUV : U ⊆ V) {A : Fml L}
    (hA : A ∈ eligible U) : A ∈ eligible V :=
  ⟨hA.1, supported_mono hUV hA.2⟩

private theorem step_supported (U : Universe) (Γ : Set (Fml L)) (B : Fml L) (n : ℕ)
    (Δ : Finset (Fml L))
    (hΔ : ∀ A ∈ Δ, A ∈ eligible (enlargement U).carrier) :
    ∀ A ∈ stageStep U Γ B n Δ, A ∈ eligible (enlargement U).carrier := by
  have hF : enumeration (L := L) U n ∈ eligible (enlargement U).carrier := by
    rw [← enumeration_range U]
    exact Set.mem_range_self n
  unfold stageStep
  dsimp only
  split_ifs
  · exact hΔ
  · split
    next D hEq =>
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · have hD : D.EqualityFree ∧ Supported (enlargement U).carrier D := by
          simpa only [hEq,eligible,Set.mem_ofPred_eq,BoundedFormula.EqualityFree,
            Supported,BoundedFormula.freeVarFinset] using hF
        refine ⟨(instantiate_equalityFree D _).mpr hD.1,instantiate_supported D _ hD.2 ?_⟩
        intro c hc
        have he := Finset.mem_singleton.mp hc
        subst c
        exact Or.inr (freshName_spec U _).1
      · rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hF
        · exact hΔ _ hA
    next F hNotEx =>
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hF
      · exact hΔ _ hA

omit [Countable L.Symbols] in
private theorem insert_stage (Γ : Set (Fml L)) (F : Fml L) (Δ : Finset (Fml L)) :
    Γ ∪ (↑(insert F Δ) : Set (Fml L)) = insert F (Γ ∪ ↑Δ) := by
  ext A
  simp only [Set.mem_union,Finset.mem_coe,Finset.mem_insert,Set.mem_insert_iff]
  tauto

private theorem step_avoids (U : Universe) (Γ : Set (Fml L)) (B : Fml L) (n : ℕ)
    (Δ : Finset (Fml L)) (hΓ : Γ ⊆ eligible U.carrier)
    (h : Avoids (Γ ∪ (↑Δ : Set (Fml L))) B) :
    Avoids (Γ ∪ (↑(stageStep U Γ B n Δ) : Set (Fml L))) B := by
  unfold stageStep
  dsimp only
  split_ifs with hbad
  · exact h
  · split
    next D hEq =>
      let c := freshName U (forbidden B (enumeration U n) Δ)
      have hc := freshName_spec U (forbidden B (enumeration (L := L) U n) Δ)
      have hcB : c ∉ B.freeVarFinset := by
        intro hmem
        exact hc.2.1 (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hcD : c ∉ D.freeVarFinset := by
        intro hmem
        apply hc.2.1
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        simpa only [c,hEq,BoundedFormula.freeVarFinset] using hmem
      have hcΓ : ∀ A ∈ Γ ∪ (↑Δ : Set (Fml L)), c ∉ A.freeVarFinset := by
        intro A hA hmem
        rcases hA with hA | hA
        · exact Set.disjoint_left.mp (reserve_partition U).2.2.2.2.1
            ((hΓ hA).2 c hmem) hc.1
        · exact hc.2.1 (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A,hA,hmem⟩))
      have hs : Avoids (insert (.ex D) (Γ ∪ (↑Δ : Set (Fml L)))) B := by
        simpa only [Avoids,← hEq,← insert_stage] using hbad
      have hw := safe_witness D B c hcΓ hcD hcB hs
      simpa only [insert_stage,hEq,c] using hw
    next F hNotEx =>
      simpa only [Avoids,insert_stage] using hbad

theorem stages_increase (U : Universe) (Γ : Set (Fml L)) (B : Fml L) : Monotone (stage U Γ B) := by
  apply monotone_nat_of_le_succ
  intro n A hA
  rcases hA with hΓ | hΔ
  · exact Or.inl hΓ
  · exact Or.inr (stageStep_contains U Γ B n _ hΔ)


theorem stages_supported (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) : ∀ n, stage U Γ B n ⊆ eligible (enlargement U).carrier := by
  intro n
  have hΔ : ∀ n, ∀ A ∈ stageAdditions U Γ B n,
      A ∈ eligible (enlargement U).carrier := by
    intro n
    induction n with
    | zero => simp [stageAdditions]
    | succ n ih => exact step_supported U Γ B n _ ih
  intro A hA
  rcases hA with hA | hA
  · exact eligible_mono Set.subset_union_left (hΓ hA)
  · exact hΔ n A hA


theorem stages_avoid (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) (_hB : B ∈ eligible U.carrier) (h : Avoids Γ B) :
    ∀ n, Avoids (stage U Γ B n) B := by
  intro n
  induction n with
  | zero => simpa only [stage,stageAdditions,Finset.coe_empty,Set.union_empty] using h
  | succ n ih => exact step_avoids U Γ B n _ hΓ ih

theorem extension_contains (U : Universe) (Γ : Set (Fml L)) (B : Fml L) : Γ ⊆ extension U Γ B := by
  intro A hA
  exact Set.mem_iUnion.mpr ⟨0,Or.inl hA⟩


theorem extension_avoids (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) (hB : B ∈ eligible U.carrier) (h : Avoids Γ B) :
    Avoids (extension U Γ B) B := by
  intro hb
  obtain ⟨n,hn⟩ := (provable_increasing_union (stage U Γ B) (stages_increase U Γ B) B).mp hb
  exact stages_avoid U Γ B hΓ hB h n hn


theorem extension_maximal (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (F : Fml L) (hF : F ∈ eligible (enlargement U).carrier)
    (hnot : F ∉ extension U Γ B) : Provable (insert F (extension U Γ B)) B := by
  have hFr : F ∈ Set.range (enumeration (L := L) U) := (enumeration_range (L := L) U).symm ▸ hF
  obtain ⟨n,hFn⟩ := hFr
  have hbad : Provable (Γ ∪ (↑(insert F (stageAdditions U Γ B n)) : Set (Fml L))) B := by
    by_contra hsafe
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨n+1,Or.inr ?_⟩
    change F ∈ stageStep U Γ B n (stageAdditions U Γ B n)
    unfold stageStep
    rw [hFn]
    simp only [hsafe,ite_false]
    split <;> simp
  apply provable_mono ?_ hbad
  intro A hA
  rcases hA with hA | hA
  · exact Set.mem_insert_of_mem _ (extension_contains U Γ B hA)
  · rcases Finset.mem_insert.mp hA with rfl | hA
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n,Or.inr hA⟩)


omit [Countable L.Symbols] in
private theorem assumption_provable {T : Set (Fml L)} {A : Fml L} (hA : A ∈ T) : Provable T A := by
  exact ⟨⟨{A},by intro C hC; simpa only [Finset.mem_singleton.mp hC] using hA,
    Proof.assumption (Finset.mem_singleton_self _)⟩⟩

private theorem extension_supported (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) : extension U Γ B ⊆ eligible (enlargement U).carrier := by
  intro A hA
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hA
  exact stages_supported U Γ B hΓ n hn

theorem extension_witness (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) (hB : B ∈ eligible U.carrier) (h : Avoids Γ B)
    (D : Body L) (hD : (.ex D) ∈ extension U Γ B) :
    ∃ c ∈ (enlargement U).carrier, D.instantiate (.var c) ∈ extension U Γ B := by
  have hDf := extension_supported U Γ B hΓ hD
  have hDr : (.ex D) ∈ Set.range (enumeration (L := L) U) :=
    (enumeration_range (L := L) U).symm ▸ hDf
  obtain ⟨n,hn⟩ := hDr
  have hsafe : ¬Provable (Γ ∪ (↑(insert (.ex D) (stageAdditions U Γ B n)) : Set (Fml L))) B := by
    intro hbad
    apply extension_avoids U Γ B hΓ hB h
    apply provable_mono ?_ hbad
    intro A hA
    rcases hA with hA | hA
    · exact extension_contains U Γ B hA
    · rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hD
      · exact Set.mem_iUnion.mpr ⟨n,Or.inr hA⟩
  let c := freshName U (forbidden B (.ex D) (stageAdditions U Γ B n))
  refine ⟨c,Or.inr (freshName_spec U _).1,Set.mem_iUnion.mpr ⟨n+1,Or.inr ?_⟩⟩
  change D.instantiate (.var c) ∈ stageStep U Γ B n (stageAdditions U Γ B n)
  simp only [stageStep,hn,hsafe,ite_false]
  exact Finset.mem_insert_self _ _

omit [Countable L.Symbols] in
private theorem provable_disj_cases {T : Set (Fml L)} {A C B : Fml L}
    (hdisj : Provable T (.disj A C)) (hA : Provable (insert A T) B)
    (hC : Provable (insert C T) B) : Provable T B := by
  let Δ : Finset (Fml L) := {.disj A C,.impl A B,.impl C B}
  have hp : Proof false false L Δ B := by
    apply Proof.disjElim (A := A) (B := C)
    · exact Proof.assumption (by simp [Δ])
    · exact Proof.impElim (Proof.assumption (by simp [Δ]))
        (Proof.assumption (Finset.mem_insert_self _ _))
    · exact Proof.impElim (Proof.assumption (by simp [Δ]))
        (Proof.assumption (Finset.mem_insert_self _ _))
  apply theory_trans (theory_finset.mpr ⟨hp⟩)
  intro F hF
  simp only [Δ,Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hF
  rcases hF with rfl | rfl | rfl
  · exact hdisj
  · exact (provable_deduction T A B).mp hA
  · exact (provable_deduction T C B).mp hC

theorem extension_prime (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) (hB : B ∈ eligible U.carrier) (h : Avoids Γ B) :
    Theory (enlargement U) (extension U Γ B) := by
  let H := extension U Γ B
  have hs : H ⊆ eligible (enlargement U).carrier := extension_supported U Γ B hΓ
  have ha : Avoids H B := extension_avoids U Γ B hΓ hB h
  refine ⟨hs,?_,?_,?_,?_⟩
  · intro hf
    apply ha
    exact ⟨⟨{.falsum},by intro A hA; simpa only [Finset.mem_singleton.mp hA] using hf,
      Proof.falsumElim (Proof.assumption (Finset.mem_singleton_self _))⟩⟩
  · intro A hA hp
    by_contra hn
    exact ha (provable_cut hp (extension_maximal U Γ B A hA hn))
  · intro A C hdisj
    by_contra hn
    have hnA : A ∉ H := fun hA => hn (Or.inl hA)
    have hnC : C ∉ H := fun hC => hn (Or.inr hC)
    have hDC := hs hdisj
    have hA : A ∈ eligible (enlargement U).carrier :=
      ⟨hDC.1.1,fun c hc => hDC.2 c (Finset.mem_union_left _ hc)⟩
    have hC : C ∈ eligible (enlargement U).carrier :=
      ⟨hDC.1.2,fun c hc => hDC.2 c (Finset.mem_union_right _ hc)⟩
    exact ha (provable_disj_cases (assumption_provable hdisj)
      (extension_maximal U Γ B A hA hnA) (extension_maximal U Γ B C hC hnC))
  · intro D hD
    exact extension_witness U Γ B hΓ hB h D hD

theorem extension_omits (U : Universe) (Γ : Set (Fml L)) (B : Fml L)
    (hΓ : Γ ⊆ eligible U.carrier) (hB : B ∈ eligible U.carrier) (h : Avoids Γ B) :
    B ∉ extension U Γ B := by
  intro hmem
  exact extension_avoids U Γ B hΓ hB h (assumption_provable hmem)
end CountableLanguage
end
end Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
