import Lemmatheca.OracleComputation.Closure
import Lemmatheca.OracleComputation.Use

/-! The specified syntax substitutions and ordinary query-elimination compiler. -/
namespace Lemmatheca.ComputabilityTheory.OracleComputation

open UniversalComputation

set_option backward.isDefEq.respectTransparency false

def subst (d : Code) : Code → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => d
  | .pair c e => .pair (subst d c) (subst d e)
  | .comp c e => .comp (subst d c) (subst d e)
  | .prec c e => .prec (subst d c) (subst d e)
  | .find' c => .find' (subst d c)

def erase (r : Nat.Partrec.Code) : Code → Nat.Partrec.Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => r
  | .pair c d => .pair (erase r c) (erase r d)
  | .comp c d => .comp (erase r c) (erase r d)
  | .prec c d => .prec (erase r c) (erase r d)
  | .find' c => .rfind' (erase r c)

theorem subst_eval (A B : Set ℕ) (d : Code)
    (hd : ∀ q, eval B d q = Part.some (indicator (fun n => n ∈ A) q))
    (c : Code) (x : ℕ) :
    eval B (subst d c) x = eval A c x := by
  induction c generalizing x with
  | zero | succ | left | right => rfl
  | query => exact hd x
  | pair c e hc he => simp only [subst,eval,hc,he]
  | comp c e hc he => simp only [subst,eval,funext hc,he]
  | prec c e hc he => simp only [subst,eval,hc,he]
  | find' c hc => simp only [subst,eval,hc]

theorem embed_erase (r : Nat.Partrec.Code) (c : Code) :
    embed (erase r c) = subst (embed r) c := by
  induction c <;> simp_all [erase,embed,subst]

theorem erase_eval (A : Set ℕ) (r : Nat.Partrec.Code)
    (hr : ∀ q, Nat.Partrec.Code.eval r q = Part.some (indicator (fun n => n ∈ A) q))
    (c : Code) (x : ℕ) :
    Nat.Partrec.Code.eval (erase r c) x = eval A c x := by
  have h := subst_eval A ∅ (embed r) (fun q => by rw [eval_embed,hr]) c x
  rw [← embed_erase,eval_embed] at h
  exact h

theorem computable_oracle_elimination (A : Set ℕ)
    (hA : ComputablePred (fun q => q ∈ A)) :
    ∃ r : Nat.Partrec.Code,
      (∀ q, Nat.Partrec.Code.eval r q = Part.some (indicator (fun n => n ∈ A) q)) ∧
      ∀ c x, Nat.Partrec.Code.eval (erase r c) x = eval A c x := by
  obtain ⟨f,hf,hfA⟩ := (decidable_iff_characteristic (fun q => q ∈ A)).mp hA
  obtain ⟨r,hr⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  have hrA : ∀ q, r.eval q = Part.some (indicator (fun n => n ∈ A) q) := by
    intro q
    rw [hr]
    change Part.some (f q) = _
    rw [hfA]
  exact ⟨r,hrA,erase_eval A r hrA⟩

theorem computable_oracle_iff (A : Set ℕ) (hA : ComputablePred (fun q => q ∈ A))
    (f : ℕ → Part ℕ) : PartialComputable A f ↔ Nat.Partrec f := by
  constructor
  · rintro ⟨c,rfl⟩
    obtain ⟨r,_,hr⟩ := computable_oracle_elimination A hA
    exact Nat.Partrec.Code.exists_code.mpr ⟨erase r c,funext (hr c)⟩
  · exact ordinary_inclusion A

end Lemmatheca.ComputabilityTheory.OracleComputation
