import Lemmatheca.MathematicalLogic.PAExistentialSyntax

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def prefixMatrix {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) (j : ℕ) : M :=
  modelFormulaCodeAt (prefixName x y j) (n - j) D

def prefixTarget {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) (j : ℕ) : M :=
  modelExPrefix (n - j) (prefixMatrix D x y j)

theorem prefixMatrix_bound {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) (j : ℕ) (hj : j ≤ n) :
    FormulaBound (n - j) (prefixMatrix D x y j) := by
  simpa only [prefixMatrix, Nat.add_zero] using modelFormulaCodeAt_bound
    (prefixName x y j) (n - j) (prefixName_bound x y j hj) D

theorem prefixMatrix_rewrite {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) (j : Fin n) :
    rewrite.value ![numeralValue M 2, zeroValue M, ProofPrograms.numeral.value ![y j],
      prefixMatrix D x y j.val] = prefixMatrix D x y (j.val + 1) := by
  unfold prefixMatrix
  rw [show n - j.val = (n - (j.val + 1)) + 1 by omega,
    rewrite_slot_modelFormulaCodeAt]
  congr 1
  funext i
  exact prefixName_rewrite x y j i

omit [language.Structure M] [M ⊨ PA] in
theorem prefixWitnesses_cons {n : ℕ} (y : Fin n → M) (j : Fin n) :
    (List.ofFn y).drop j.val = y j :: (List.ofFn y).drop (j.val + 1) := by
  have h := List.drop_eq_getElem_cons (l := List.ofFn y) (i := j.val)
    (by simpa only [List.length_ofFn] using j.isLt)
  simpa only [List.getElem_ofFn] using h

theorem prefixMatrix_last {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) :
    prefixMatrix D x y n = modelFormulaCodeAt
      (Sum.elim (fun i => ProofPrograms.numeral.value ![x i])
        (fun i => ProofPrograms.numeral.value ![y i])) 0 D := by
  unfold prefixMatrix
  rw [Nat.sub_self]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [prefixName, Sum.elim_inr, i.isLt, ↓reduceIte]

/-- Each recursively extracted body is the actual numeral-instantiation of the
next literal finite prefix. -/
theorem prefixTarget_chain {r n : ℕ} (D : language.Formula (Fin r ⊕ Fin n))
    (x : Fin r → M) (y : Fin n → M) (k j : ℕ) (hsplit : j + k = n) :
    ExistentialChain k (prefixTarget D x y j)
      (modelList ((List.ofFn y).drop j)) (prefixMatrix D x y n) := by
  induction k generalizing j with
  | zero =>
    have hj : j = n := by omega
    subst j
    change modelExPrefix (n - n) (prefixMatrix D x y n) = _
    rw [Nat.sub_self, modelExPrefix]
  | succ k ih =>
    have hj : j < n := by omega
    let i : Fin n := ⟨j, hj⟩
    let body := modelExPrefix k (prefixMatrix D x y j)
    have hlen : n - j = k + 1 := by omega
    have hlen' : n - (j + 1) = k := by omega
    have hbodyBound : FormulaBound 1 body := by
      apply modelExPrefix_bound k 1 (prefixMatrix D x y j)
      simpa only [hlen] using prefixMatrix_bound D x y j (by omega)
    have hbody := hbodyBound.namedForm
    have htarget : prefixTarget D x y j = exValue body := by
      simp only [prefixTarget, hlen, modelExPrefix_succ, body]
    have hsentence : isSentence.value ![prefixTarget D x y j] = numeralValue M 1 :=
      ((modelExPrefix_bound (n - j) 0 (prefixMatrix D x y j)
        (by simpa only [Nat.add_zero] using prefixMatrix_bound D x y j (by omega))).pure).sentence
    have hinst : instantiate.value ![body, ProofPrograms.numeral.value ![y i] ] =
        prefixTarget D x y (j + 1) := by
      rw [instantiate_value_of_tests _ _ hbody (PureTerm.numeral _).namedTerm]
      rw [show body = modelExPrefix k (prefixMatrix D x y j) from rfl,
        rewrite_slot_modelExPrefix, prefixMatrix_rewrite D x y i]
      simp only [prefixTarget, hlen', i]
    change ∃ b : M, _
    refine ⟨body, htarget, hbody, hsentence, ?_⟩
    have hsuf := prefixWitnesses_cons y i
    change (List.ofFn y).drop j = y i :: (List.ofFn y).drop (j + 1) at hsuf
    rw [hsuf, modelList_cons, head_cons_value, tail_cons_value, hinst]
    exact ih (j + 1) (by omega)

theorem certified_prefixTarget {r n : ℕ} (E : Program 2)
    (D : language.Formula (Fin r ⊕ Fin n)) (x : Fin r → M) (y : Fin n → M) (p : M)
    (hp : Certified E p (prefixMatrix D x y n)) :
    Certified E ((existentialPrefix n).value
      ![prefixTarget D x y 0, modelList (List.ofFn y), p]) (prefixTarget D x y 0) := by
  apply certified_existentialPrefix E n _ _ _ p
  · simpa only [List.drop_zero] using prefixTarget_chain D x y n 0 (by omega)
  · exact hp

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
