import Lemmatheca.ExactPairsAndFailureOfMeets.Protected

/-! A bounded protected-prefix checker over a formal total query function. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs
open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees
open PartialRecursiveFunctions (Args)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
local instance exactPairsCheckerDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable

private theorem uniform_of_eq {n : ℕ}
    {F G : (ℕ → ℕ) → Args n → ℕ} (hF : UniformPrimitive F)
    (h : ∀ q v, F q v = G q v) : UniformPrimitive G :=
  (funext (fun q => funext (h q))) ▸ hF

private theorem get_primitive {n : ℕ} (i : Fin n) : Primrec (fun v : Args n => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem uniform_precomp {m n : ℕ} {F : (ℕ → ℕ) → Args m → ℕ}
    (hF : UniformPrimitive F) (g : Fin m → Args n → ℕ) (hg : ∀ i, Primrec (g i)) :
    UniformPrimitive (fun q v => F q (List.Vector.ofFn (fun i => g i v))) :=
  UniformPrimitive.comp hF (fun i => uniform_ordinary_primitive (g i) (Nat.Primrec'.prim_iff.mpr (hg i)))

private theorem uniform_apply {m n : ℕ} (f : Args m → ℕ) (hf : Primrec f)
    (g : Fin m → (ℕ → ℕ) → Args n → ℕ) (hg : ∀ i, UniformPrimitive (g i)) :
    UniformPrimitive (fun q v => f (List.Vector.ofFn (fun i => g i q v))) :=
  UniformPrimitive.comp (uniform_ordinary_primitive f (Nat.Primrec'.prim_iff.mpr hf)) hg

@[simp 1100] private theorem appended_get {n : ℕ} (v : Args n) (a b : ℕ) (i : Fin (n + 2)) :
    (v ++ List.Vector.cons a (List.Vector.cons b List.Vector.nil)).get i =
      if h : i.val < n then v.get ⟨i.val, h⟩ else if i.val = n then a else b := by
  rcases v with ⟨l, rfl⟩
  change (l ++ [a,b])[i.val]'_ = if h : i.val < l.length then l[i.val]'h else if i.val = l.length then a else b
  rw [List.getElem_append]
  by_cases hi : i.val < l.length
  · simp [hi]
  · by_cases he : i.val = l.length
    · simp [he]
    · have he' : i.val - l.length = 1 := by omega
      simp [hi,he,he']

private def scan (q : ℕ → ℕ) (s u w : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if scan q s u w j = 0 ∧
      (wordLength u ≤ j → j.unpair.1 < s → wordBit w j = q j) then 0 else 1

private theorem test_zero (p : Prop) [Decidable p] : (if p then (0 : ℕ) else 1) = 0 ↔ p := by
  by_cases h : p <;> simp [h]

private theorem scan_zero (q : ℕ → ℕ) (s u w k : ℕ) :
    scan q s u w k = 0 ↔
      ∀ j < k, wordLength u ≤ j → j.unpair.1 < s → wordBit w j = q j := by
  induction k with
  | zero => simp [scan]
  | succ k ih =>
      simp only [scan, test_zero, ih]
      constructor
      · rintro ⟨hold,hk⟩ j hj
        by_cases he : j = k
        · simpa [he] using hk
        · exact hold j (by omega)
      · intro h
        exact ⟨fun j hj => h j (by omega),h k (by omega)⟩

private def stepSkeleton (v : Args 6) : ℕ :=
  if v.get 4 = 0 ∧ (wordLength (v.get 1) ≤ v.get 3 →
    (v.get 3).unpair.1 < v.get 0 → wordBit (v.get 2) (v.get 3) = v.get 5) then 0 else 1

private theorem step_primitive : Primrec stepSkeleton := by
  have ha := Primrec.nat_le.comp (FiniteSequenceCoding.primrec_length.comp (get_primitive (1 : Fin 6)))
    (get_primitive (3 : Fin 6))
  have hb := Primrec.nat_lt.comp ((Primrec.fst.comp Primrec.unpair).comp (get_primitive (3 : Fin 6)))
    (get_primitive (0 : Fin 6))
  have hc := Primrec.eq.comp (PostsTheorem.beta_primitive.comp (get_primitive (2 : Fin 6))
    (get_primitive (3 : Fin 6))) (get_primitive (5 : Fin 6))
  have ht : PrimrecPred (fun v : Args 6 => wordLength (v.get 1) ≤ v.get 3 →
      (v.get 3).unpair.1 < v.get 0 → wordBit (v.get 2) (v.get 3) = v.get 5) :=
    (ha.not.or (hb.not.or hc)).of_eq (fun _ => by tauto)
  exact Primrec.ite ((Primrec.eq.comp (get_primitive (4 : Fin 6)) (Primrec.const 0)).and ht)
    (Primrec.const 0) (Primrec.const 1)

private def step (q : ℕ → ℕ) (v : Args 5) : ℕ :=
  if v.get 4 = 0 ∧ (wordLength (v.get 1) ≤ v.get 3 →
    (v.get 3).unpair.1 < v.get 0 → wordBit (v.get 2) (v.get 3) = q (v.get 3)) then 0 else 1

private theorem step_uniform : UniformPrimitive step := by
  have hquery : UniformPrimitive (fun q (v : Args 5) => q (v.get 3)) := by
    simpa only [List.Vector.get_ofFn] using
      (UniformPrimitive.comp UniformPrimitive.query (fun _ : Fin 1 => UniformPrimitive.proj (3 : Fin 5)))
  let inn : Fin 6 → (ℕ → ℕ) → Args 5 → ℕ :=
    Fin.cases (fun _ v => v.get 0) (Fin.cases (fun _ v => v.get 1)
      (Fin.cases (fun _ v => v.get 2) (Fin.cases (fun _ v => v.get 3)
        (Fin.cases (fun _ v => v.get 4) (fun _ q v => q (v.get 3))))))
  have hi : ∀ i, UniformPrimitive (inn i) := by
    intro i
    fin_cases i
    · exact UniformPrimitive.proj 0
    · exact UniformPrimitive.proj 1
    · exact UniformPrimitive.proj 2
    · exact UniformPrimitive.proj 3
    · exact UniformPrimitive.proj 4
    · exact hquery
  exact uniform_of_eq (uniform_apply stepSkeleton step_primitive inn hi) (fun _ _ => rfl)

private theorem scan_uniform : UniformPrimitive (fun q (v : Args 4) =>
    scan q (v.get 0) (v.get 1) (v.get 2) (v.get 3)) := by
  have hr (q : ℕ → ℕ) (v : Args 3) (t : ℕ) :
      PrimitiveRecursion.recValue (fun _ : Args 3 => 0)
        (fun v j z => step q (v ++ List.Vector.cons j (List.Vector.cons z List.Vector.nil))) v t =
      scan q (v.get 0) (v.get 1) (v.get 2) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
        simpa [PrimitiveRecursion.recValue,scan,step] using congrArg
          (fun z => step q (v ++ List.Vector.cons t (List.Vector.cons z List.Vector.nil))) ih
  apply uniform_of_eq (UniformPrimitive.prec (UniformPrimitive.zero 3) step_uniform)
  intro q v
  simpa [PrimitiveRecursion.lastRec,PrimitiveRecursion.initialPart] using
    hr q (PrimitiveRecursion.initialPart v) (v.get 3)

private def checkSkeleton (v : Args 6) : ℕ :=
  if Prefix (v.get 2) (v.get 4) ∧ 0 < certificateValue (v.get 4) (v.get 1) (v.get 3) ∧
    v.get 5 = 0 then 0 else 1

private theorem check_skeleton_primitive : Primrec checkSkeleton := by
  have hp := prefix_primitive.comp ((get_primitive (2 : Fin 6)).pair (get_primitive (4 : Fin 6)))
  have hv := Primrec.nat_lt.comp (Primrec.const 0) (certificate_primitive.comp
    (((get_primitive (4 : Fin 6)).pair (get_primitive (1 : Fin 6))).pair (get_primitive (3 : Fin 6))))
  have hz := Primrec.eq.comp (get_primitive (5 : Fin 6)) (Primrec.const 0)
  exact Primrec.ite (hp.and (hv.and hz)) (Primrec.const 0) (Primrec.const 1)

/-- The exact body of the reviewed protected checker, independent of Search.lean. -/
theorem checkFamily_primitive_helper : UniformPrimitive
    (fun q (v : Args 5) => if Prefix (v.get 2) (v.get 4) ∧
      0 < certificateValue (v.get 4) (v.get 1) (v.get 3) ∧
      ∀ j < wordLength (v.get 4), wordLength (v.get 2) ≤ j →
        j.unpair.1 < v.get 0 → wordBit (v.get 4) j = q j then 0 else 1) := by
  let coords : Fin 4 → Args 5 → ℕ :=
    Fin.cases (fun v => v.get 0) (Fin.cases (fun v => v.get 2)
      (Fin.cases (fun v => v.get 4) (fun _ v => wordLength (v.get 4))))
  have hc : ∀ i, Primrec (coords i) := by
    intro i
    fin_cases i
    · exact get_primitive 0
    · exact get_primitive 2
    · exact get_primitive 4
    · exact FiniteSequenceCoding.primrec_length.comp (get_primitive 4)
  have hs : UniformPrimitive (fun q (v : Args 5) =>
      scan q (v.get 0) (v.get 2) (v.get 4) (wordLength (v.get 4))) :=
    uniform_of_eq (uniform_precomp scan_uniform coords hc) (fun _ _ => rfl)
  let inn : Fin 6 → (ℕ → ℕ) → Args 5 → ℕ :=
    Fin.cases (fun _ v => v.get 0) (Fin.cases (fun _ v => v.get 1)
      (Fin.cases (fun _ v => v.get 2) (Fin.cases (fun _ v => v.get 3)
        (Fin.cases (fun _ v => v.get 4)
          (fun _ q v => scan q (v.get 0) (v.get 2) (v.get 4) (wordLength (v.get 4)))))))
  have hi : ∀ i, UniformPrimitive (inn i) := by
    intro i
    fin_cases i
    · exact UniformPrimitive.proj 0
    · exact UniformPrimitive.proj 1
    · exact UniformPrimitive.proj 2
    · exact UniformPrimitive.proj 3
    · exact UniformPrimitive.proj 4
    · exact hs
  apply uniform_of_eq (uniform_apply checkSkeleton check_skeleton_primitive inn hi)
  intro q v
  change (if Prefix (v.get 2) (v.get 4) ∧
    0 < certificateValue (v.get 4) (v.get 1) (v.get 3) ∧
    scan q (v.get 0) (v.get 2) (v.get 4) (wordLength (v.get 4)) = 0 then 0 else 1) = _
  simp only [scan_zero]
end
end Lemmatheca.ComputabilityTheory.ExactPairs
