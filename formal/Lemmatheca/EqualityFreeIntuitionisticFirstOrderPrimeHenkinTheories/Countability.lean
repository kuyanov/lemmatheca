import Lemmatheca.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories.Core
namespace Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v
noncomputable section
variable {L : Language.{u,v}} [Countable L.Symbols]
local instance primeHenkinRelationsCountable : Countable (Σ n, L.Relations n) :=
  @Function.Injective.countable _ _ ‹Countable L.Symbols› _ Sum.inr_injective

private def termCode {n : ℕ} (t : L.Term (ℕ ⊕ Fin n)) : ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _) t

private theorem termCode_injective {n : ℕ} :
    Function.Injective (termCode : L.Term (ℕ ⊕ Fin n) → ℕ) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

private def relationCode (R : Σ n, L.Relations n) : ℕ :=
  @Encodable.encode _ (Encodable.ofCountable _) R

private theorem relationCode_injective :
    Function.Injective (relationCode (L := L)) :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

/-- Distinct constructor tags and finite lists retain the actual native syntax tree. -/
private def nativeCode : {n : ℕ} → Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n → ℕ
  | _, .falsum => Nat.pair 0 0
  | _, .equal s t => Nat.pair 1 (Nat.pair (termCode s) (termCode t))
  | _, @BoundedFormula.rel _ _ _ k R ts => Nat.pair 2
      (Nat.pair (relationCode ⟨k,R⟩) (Encodable.encode (List.ofFn (fun i => termCode (ts i)))))
  | _, .neg A => Nat.pair 3 (nativeCode A)
  | _, .conj A B => Nat.pair 4 (Nat.pair (nativeCode A) (nativeCode B))
  | _, .disj A B => Nat.pair 5 (Nat.pair (nativeCode A) (nativeCode B))
  | _, .impl A B => Nat.pair 6 (Nat.pair (nativeCode A) (nativeCode B))
  | _, .all A => Nat.pair 7 (nativeCode A)
  | _, .ex A => Nat.pair 8 (nativeCode A)

private theorem nativeCode_injective {n : ℕ}
    (A : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) :
    ∀ B, nativeCode A = nativeCode B → A = B := by
  induction A with
  | falsum => intro B h; cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h ⊢
  | equal s t =>
    intro B h
    cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg₂ BoundedFormula.equal (termCode_injective h.1) (termCode_injective h.2)
  | @rel n k R ts =>
    intro B h
    cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h
    rename_i k' R' ts'
    have hr := relationCode_injective h.1
    cases hr
    have hv := h.2
    have hv' := List.ofFn_inj.mp hv
    congr 1
    funext i
    exact termCode_injective (congrFun hv' i)
  | neg A ih =>
    intro B h
    cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg BoundedFormula.neg (ih _ h)
  | conj A B ihA ihB =>
    intro C h
    cases C <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg₂ BoundedFormula.conj (ihA _ h.1) (ihB _ h.2)
  | disj A B ihA ihB =>
    intro C h
    cases C <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg₂ BoundedFormula.disj (ihA _ h.1) (ihB _ h.2)
  | impl A B ihA ihB =>
    intro C h
    cases C <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg₂ BoundedFormula.impl (ihA _ h.1) (ihB _ h.2)
  | all A ih =>
    intro B h
    cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg BoundedFormula.all (ih _ h)
  | ex A ih =>
    intro B h
    cases B <;> simp [nativeCode,Nat.pair_eq_pair] at h
    exact congrArg BoundedFormula.ex (ih _ h)

/-- Routine coding lemma for the full native syntax, including every scope size. -/
theorem countable_native_scopes :
    Countable (Σ n, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n) := by
  apply Function.Injective.countable (f := fun A : Σ n, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L ℕ n => Nat.pair A.1 (nativeCode A.2))
  rintro ⟨n,A⟩ ⟨m,B⟩ h
  obtain ⟨hn,hA⟩ := Nat.pair_eq_pair.mp h
  change n = m at hn
  subst m
  exact congrArg (Sigma.mk n) (nativeCode_injective A B hA)
end
end Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
