import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion

namespace Lemmatheca.ComputabilityTheory.PrimitiveRecursion
open List.Vector

def firstToLast {n : ℕ} (v : Args (n+1)) : Args (n+1) :=
  v.tail ++ v.head ::ᵥ nil

def lastTwoToFirst {n : ℕ} (v : Args (n+2)) : Args (n+2) :=
  v.get ⟨n, by omega⟩ ::ᵥ v.get (Fin.last (n+1)) ::ᵥ initialPart (initialPart v)

private theorem prefix_snoc' {n : ℕ} (x : Args n) (a : ℕ) :
    initialPart (x ++ a ::ᵥ nil) = x := by
  apply List.Vector.ext
  intro i
  change (List.Vector.ofFn (fun j : Fin n => (x ++ a ::ᵥ nil).get j.castSucc)).get i = _
  rw [List.Vector.get_ofFn]
  change (x.toList ++ [a])[i.val]'_ = x.toList[i.val]'_
  exact List.getElem_append_left (by simp)

private theorem last_snoc' {n : ℕ} (x : Args n) (a : ℕ) :
    (x ++ a ::ᵥ nil).get (Fin.last n) = a := by
  rcases x with ⟨l,rfl⟩
  change (l ++ [a])[l.length]'_ = a
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem lastTwoToFirst_snoc {n : ℕ} (x : Args n) (a b : ℕ) :
    lastTwoToFirst (x ++ a ::ᵥ b ::ᵥ nil) = a ::ᵥ b ::ᵥ x := by
  have he : x ++ a ::ᵥ b ::ᵥ nil = (x ++ a ::ᵥ nil) ++ b ::ᵥ nil := by
    apply List.Vector.toList_injective
    simp
  unfold lastTwoToFirst
  rw [he,prefix_snoc',prefix_snoc',last_snoc']
  congr 1
  change ((x.toList ++ [a]) ++ [b])[n]'_ = a
  rw [List.getElem_append_left (by simp)]
  simp

private theorem lastRec_first {n : ℕ} (f : Args n → ℕ) (g : Args (n+2) → ℕ)
    (x : Args n) (a : ℕ) :
    lastRec f (g ∘ lastTwoToFirst) (x ++ a ::ᵥ nil) =
      a.rec (f x) (fun i u => g (i ::ᵥ u ::ᵥ x)) := by
  induction a with
  | zero => exact (lastRec_equations f (g ∘ lastTwoToFirst) x 0).1
  | succ a ih =>
    rw [(lastRec_equations f (g ∘ lastTwoToFirst) x a).2]
    simp only [Function.comp_apply,lastTwoToFirst_snoc,ih]

private def firstPermutation (n : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  if h : i.val < n then ⟨i.val+1,by omega⟩ else 0

private def stepPermutation (n : ℕ) : Fin (n+2) → Fin (n+2) :=
  Fin.cases ⟨n,by omega⟩ (Fin.cases (Fin.last (n+1)) (fun j : Fin n => j.castAdd 2))

set_option backward.isDefEq.respectTransparency false in
private theorem firstToLast_ofFn {n : ℕ} (v : Args (n+1)) :
    (List.Vector.ofFn (fun i => v.get (firstPermutation n i))) = firstToLast v := by
  apply List.Vector.ext
  intro i
  rw [List.Vector.get_ofFn]
  unfold firstToLast firstPermutation
  by_cases hi : i.val < n
  · simp only [hi,↓reduceDIte]
    change v.toList[i.val+1]'_ = (v.tail.toList ++ [v.head])[i.val]'_
    rw [List.getElem_append_left (by simpa)]
    change v.get ⟨i.val+1,by omega⟩ = v.tail.get ⟨i.val,hi⟩
    exact (List.Vector.get_tail v ⟨i.val,hi⟩).symm
  · have hiv := i.isLt
    have he : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    simp only [Fin.val_last,lt_self_iff_false,↓reduceDIte,get_zero]
    exact (last_snoc' (n := n) v.tail v.head).symm

private theorem lastTwoToFirst_ofFn {n : ℕ} (v : Args (n+2)) :
    (List.Vector.ofFn (fun i => v.get (stepPermutation n i))) = lastTwoToFirst v := by
  apply List.Vector.ext
  intro i
  rw [List.Vector.get_ofFn]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · rfl
  · rfl
  · simp [lastTwoToFirst,stepPermutation,initialPart]
    rfl

/-- Last-coordinate recursion generates the entire finite-arity class, rather
than merely a subclass closed under the displayed recursion operation. -/
theorem generated_by_lastRec
    (C : {n : ℕ} → (Args n → ℕ) → Prop)
    (hz : C (fun _ : Args 0 => 0))
    (hs : C (fun v : Args 1 => Nat.succ v.head))
    (hp : ∀ {n} (i : Fin n), C (fun v : Args n => v.get i))
    (hc : ∀ {m n} (f : Args n → ℕ) (g : Fin n → Args m → ℕ),
      C f → (∀ i, C (g i)) → C (fun v => f (List.Vector.ofFn (fun i => g i v))))
    (hr : ∀ {n} (f : Args n → ℕ) (g : Args (n+2) → ℕ),
      C f → C g → C (lastRec f g))
    {n : ℕ} {f : Args n → ℕ} (hf : Nat.Primrec' f) : C f := by
  induction hf with
  | zero => exact hz
  | succ => exact hs
  | get i => exact hp i
  | comp g _ _ ihf ihg => exact hc _ g ihf ihg
  | @prec n f g _ _ ihf ihg =>
    have hg : C (g ∘ lastTwoToFirst) := by
      have h := hc g (fun i v => v.get (stepPermutation n i)) ihg (fun i => hp _)
      simpa only [lastTwoToFirst_ofFn,Function.comp_def] using h
    have h := hc (lastRec f (g ∘ lastTwoToFirst))
      (fun i v => v.get (firstPermutation n i)) (hr f _ ihf hg) (fun i => hp _)
    simpa only [firstToLast_ofFn,firstToLast,lastRec_first] using h

end Lemmatheca.ComputabilityTheory.PrimitiveRecursion
