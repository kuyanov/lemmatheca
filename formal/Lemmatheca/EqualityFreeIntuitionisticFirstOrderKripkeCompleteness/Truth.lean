import Lemmatheca.EqualityFreeIntuitionisticFirstOrderKripkeCompleteness.Grounding

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a
noncomputable section
local instance canonicalPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {α : Type a}

/-- The least available numerical name provides the fixed fallback variable. -/
def fallback (w : World L) : ℕ := Nat.find w.parameters.nonempty

theorem fallback_spec (w : World L) :
    fallback w ∈ w.parameters.carrier ∧ ∀ c ∈ w.parameters.carrier, fallback w ≤ c := by
  exact ⟨Nat.find_spec w.parameters.nonempty,fun c hc => Nat.find_min' w.parameters.nonempty hc⟩

def numericalAssignment (w : World L) (c : ℕ) : Domain w :=
  if hc : c ∈ w.parameters.carrier then .var ⟨c,hc⟩
  else .var ⟨fallback w,(fallback_spec w).1⟩

theorem numerical_erasure (w : World L) (c : ℕ) (hc : c ∈ w.parameters.carrier) :
    erase (numericalAssignment w c) = .var c := by
  simp [numericalAssignment,hc,erase]

private def numericalName (w : World L) (c : ℕ) : ℕ :=
  if c ∈ w.parameters.carrier then c else fallback w

private theorem numerical_value (w : World L) (c : ℕ) :
    erase (numericalAssignment w c) = .var (numericalName w c) := by
  by_cases hc : c ∈ w.parameters.carrier <;>
    simp [numericalAssignment,numericalName,hc,erase]

theorem numerical_ground (A : PrimeHenkin.Fml L) (w : World L)
    (hA : PrimeHenkin.Supported w.parameters.carrier A) :
    groundInstance A w (Sum.elim (numericalAssignment w) Fin.elim0) = A := by
  have he : groundInstance A w (Sum.elim (numericalAssignment w) Fin.elim0) = A.rename (numericalName w) := by
    unfold groundInstance BoundedFormula.toFormula BoundedFormula.subst BoundedFormula.rename
    rw [BoundedFormula.map_comp]
    congr 1
    funext x
    cases x with
    | inl c => simp [BoundedFormula.freeScope,Term.subst,numerical_value]
    | inr i => exact Fin.elim0 i
  rw [he]
  have hm := PrimeHenkin.rename_of_agree A (numericalName w) id (by
    intro c hc
    simp only [numericalName,ite_eq_left (hA c hc),id_eq])
  exact hm.trans A.rename_id

variable [Countable L.Symbols]

/-- Native forcing is membership of the actual scoped ground instance. -/
theorem truth {n : ℕ} (A : BoundedFormula L α n) (hA : A.EqualityFree)
    (w : World L) (s : α ⊕ Fin n → Domain w) :
    Kripke.Forces canonicalModel A w s ↔ groundInstance A w s ∈ w.theory := by
  induction A generalizing w with
  | falsum =>
      rw [ground_falsum]
      exact ⟨False.elim,fun h => w.prime.proper h⟩
  | equal t q => exact hA.elim
  | rel R ts =>
      rw [ground_relation]
      change ((.rel R (fun i => (erase (canonicalModel.termValue w s (ts i))).relabel Sum.inl) : PrimeHenkin.Fml L) ∈ w.theory) ↔ _
      simp only [erase_term_value]
  | conj A B ihA ihB =>
      change (Kripke.Forces canonicalModel A w s ∧ Kripke.Forces canonicalModel B w s) ↔ _
      rw [ground_conj,ihA hA.1,ihB hA.2]
      exact (PrimeHenkin.conjunction_membership w.prime _ _
        ⟨(ground_equalityFree A w s).mpr hA.1,ground_supported A w s⟩
        ⟨(ground_equalityFree B w s).mpr hA.2,ground_supported B w s⟩).symm
  | disj A B ihA ihB =>
      change (Kripke.Forces canonicalModel A w s ∨ Kripke.Forces canonicalModel B w s) ↔ _
      rw [ground_disj,ihA hA.1,ihB hA.2]
      exact (PrimeHenkin.disjunction_membership w.prime _ _
        ⟨(ground_equalityFree A w s).mpr hA.1,ground_supported A w s⟩
        ⟨(ground_equalityFree B w s).mpr hA.2,ground_supported B w s⟩).symm
  | neg A ih =>
      rw [ground_neg,PrimeHenkin.future_negation w.prime _
        ⟨(ground_equalityFree A w s).mpr hA,ground_supported A w s⟩]
      constructor
      · intro hf V S hS he hm
        let z : World L := ⟨V,S,hS⟩
        have hx : Kripke.Forces canonicalModel A z (transition he ∘ s) :=
          (ih hA z _).mpr ((ground_transition A (w := w) (z := z) he s).symm ▸ hm)
        exact hf z he hx
      · intro hm z he hx
        have ht := (ih hA z (transition he ∘ s)).mp hx
        rw [ground_transition] at ht
        exact hm z.parameters z.theory z.prime he ht
  | impl A B ihA ihB =>
      rw [ground_impl,PrimeHenkin.future_implication w.prime _ _
        ⟨(ground_equalityFree A w s).mpr hA.1,ground_supported A w s⟩
        ⟨(ground_equalityFree B w s).mpr hA.2,ground_supported B w s⟩]
      constructor
      · intro hf V S hS he hm
        let z : World L := ⟨V,S,hS⟩
        have hx : Kripke.Forces canonicalModel A z (transition he ∘ s) :=
          (ihA hA.1 z _).mpr ((ground_transition A (w := w) (z := z) he s).symm ▸ hm)
        have ht := (ihB hA.2 z (transition he ∘ s)).mp (hf z he hx)
        rw [ground_transition] at ht
        exact ht
      · intro hm z he hx
        apply (ihB hA.2 z (transition he ∘ s)).mpr
        rw [ground_transition]
        apply hm z.parameters z.theory z.prime he
        have ht := (ihA hA.1 z (transition he ∘ s)).mp hx
        rwa [ground_transition] at ht
  | ex B ih =>
      rw [ground_ex]
      constructor
      · rintro ⟨x,hx⟩
        apply (PrimeHenkin.existential_membership w.prime _
          ⟨(body_equalityFree B w s).mpr hA,body_supported B w s⟩).mpr
        refine ⟨erase x,erase_supported x,?_⟩
        have ht := (ih hA w (extendAssignment s x)).mp hx
        rwa [ground_extend B w s x] at ht
      · intro hm
        obtain ⟨c,hc,hi⟩ := w.prime.witness hm
        let x : Domain w := .var ⟨c,hc⟩
        refine ⟨x,(ih hA w (extendAssignment s x)).mpr ?_⟩
        rw [ground_extend]
        exact hi
  | all B ih =>
      rw [ground_all]
      constructor
      · intro hf
        by_contra hnot
        obtain ⟨c,hc⟩ := w.parameters.infinite_compl.nonempty
        obtain ⟨V,S,hS,he,hcV,hnotI⟩ := PrimeHenkin.missing_universal w.prime
          (groundBody B w s) ⟨(body_equalityFree B w s).mpr hA,body_supported B w s⟩ hnot c hc
        let z : World L := ⟨V,S,hS⟩
        let x : Domain z := .var ⟨c,hcV⟩
        have ht := (ih hA z (extendAssignment (transition he ∘ s) x)).mp (hf z he x)
        rw [ground_extend B z (transition he ∘ s) x,body_transition B he s] at ht
        exact hnotI ht
      · intro hm z he x
        apply (ih hA z (extendAssignment (transition he ∘ s) x)).mpr
        rw [ground_extend B z (transition he ∘ s) x,body_transition B he s]
        exact PrimeHenkin.universal_instance z.prime (groundBody B w s)
          ⟨(body_equalityFree B w s).mpr hA,
            PrimeHenkin.supported_mono he.1 (body_supported B w s)⟩
          (erase x) (erase_supported x) (he.2 hm)

theorem holds_truth (A : Formula L α) (hA : A.EqualityFree)
    (w : World L) (s : α → Domain w) :
    Kripke.Holds canonicalModel w A s ↔
      groundInstance A w (Sum.elim s Fin.elim0) ∈ w.theory := by
  exact truth A hA w (Sum.elim s Fin.elim0)

theorem numerical_truth (A : PrimeHenkin.Fml L) (w : World L)
    (hA : A ∈ PrimeHenkin.eligible w.parameters.carrier) :
    Kripke.Holds canonicalModel w A (numericalAssignment w) ↔ A ∈ w.theory := by
  rw [holds_truth A hA.1,numerical_ground A w hA.2]

/-- This world is the specified earlier extension, not an arbitrary existential choice. -/
def supportedWorld (U : PrimeHenkin.Universe) (Γ : Set (PrimeHenkin.Fml L))
    (A : PrimeHenkin.Fml L) (hΓ : Γ ⊆ PrimeHenkin.eligible U.carrier)
    (hA : A ∈ PrimeHenkin.eligible U.carrier) (hN : ¬PrimeHenkin.Provable Γ A) : World L where
  parameters := PrimeHenkin.enlargement U
  theory := PrimeHenkin.extension U Γ A
  prime := PrimeHenkin.extension_prime U Γ A hΓ hA hN

theorem supported_countermodel (U : PrimeHenkin.Universe) (Γ : Set (PrimeHenkin.Fml L))
    (A : PrimeHenkin.Fml L) (hΓ : Γ ⊆ PrimeHenkin.eligible U.carrier)
    (hA : A ∈ PrimeHenkin.eligible U.carrier) (hN : ¬PrimeHenkin.Provable Γ A) :
    let w := supportedWorld U Γ A hΓ hA hN
    Kripke.Countermodel canonicalModel w Γ A (numericalAssignment w) := by
  let w := supportedWorld U Γ A hΓ hA hN
  have hUV : U.carrier ⊆ w.parameters.carrier := fun _ hc => Or.inl hc
  constructor
  · intro B hB
    exact (numerical_truth B w ⟨(hΓ hB).1,PrimeHenkin.supported_mono hUV (hΓ hB).2⟩).mpr
      (PrimeHenkin.extension_contains U Γ A hB)
  · intro h
    exact PrimeHenkin.extension_omits U Γ A hΓ hA hN
      ((numerical_truth A w ⟨hA.1,PrimeHenkin.supported_mono hUV hA.2⟩).mp h)

end
end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
