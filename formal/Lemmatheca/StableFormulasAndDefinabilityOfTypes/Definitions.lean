import Lemmatheca.StableFormulasAndDefinabilityOfTypes.Separation
import Mathlib.SetTheory.Cardinal.Finite

namespace Lemmatheca.ModelTheory.StableDefinability
open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.ModelTheory.OrderPatternsAndStability
universe u v w
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] {n m k : ℕ}

/-- Substitute the named object coordinates and retain the original parameter block as free. -/
def rowFormula (φ : L.Formula (Fin (n+m))) (a : Fin n → M) :
    L[[(Set.univ : Set M)]].Formula (Fin m) :=
  ((L.lhomWithConstants (Set.univ : Set M)).onFormula φ).subst
    (Fin.addCases (fun i => Constants.term (L.con (⟨a i,Set.mem_univ _⟩ : (Set.univ : Set M)))) Term.var)

def cellFormula (φ : L.Formula (Fin (n+m))) (a : Fin k → Fin n → M)
    (η : Fin k → Bool) : L[[(Set.univ : Set M)]].Formula (Fin m) :=
  Formula.iInf (fun i => if η i then rowFormula φ (a i) else (rowFormula φ (a i)).not)

def cellUnionFormula (φ : L.Formula (Fin (n+m))) (a : Fin k → Fin n → M)
    (S : Set (Fin k → Bool)) : L[[(Set.univ : Set M)]].Formula (Fin m) :=
  Formula.iSup (fun η : S => cellFormula φ a η.val)

def positivePatterns (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : Fin k → Fin n → M) : Set (Fin k → Bool) :=
  rowVector φ a '' P

theorem rowFormula_realize (φ : L.Formula (Fin (n+m))) (a : Fin n → M) (b : Fin m → M) :
    (rowFormula φ a).Realize b ↔ Truth φ a b := by
  let tf : Fin (n+m) → L[[(Set.univ : Set M)]].Term (Fin m) :=
    Fin.addCases (fun i => Constants.term (L.con (⟨a i,Set.mem_univ _⟩ : (Set.univ : Set M)))) Term.var
  change (((L.lhomWithConstants (Set.univ : Set M)).onFormula φ).subst tf).Realize b default ↔ _
  simp only [Formula.Realize,BoundedFormula.realize_subst]
  change ((L.lhomWithConstants (Set.univ : Set M)).onFormula φ).Realize
    (fun i => (tf i).realize b) ↔ _
  rw [LHom.realize_onFormula]
  apply Iff.of_eq
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [tf,Fin.addCases_left,Fin.addCases_right,Term.realize_var,
      Term.realize_constants,pairAssignment]
  all_goals rfl

theorem cellFormula_realize (φ : L.Formula (Fin (n+m))) (a : Fin k → Fin n → M)
    (η : Fin k → Bool) (b : Fin m → M) :
    (cellFormula φ a η).Realize b ↔ rowVector φ a b = η := by
  classical
  rw [cellFormula,Formula.realize_iInf,funext_iff]
  apply forall_congr'
  intro i
  cases hη : η i <;> simp [rowVector,rowFormula_realize]

theorem cellUnionFormula_realize (φ : L.Formula (Fin (n+m))) (a : Fin k → Fin n → M)
    (S : Set (Fin k → Bool)) (b : Fin m → M) :
    (cellUnionFormula φ a S).Realize b ↔ rowVector φ a b ∈ S := by
  rw [cellUnionFormula,Formula.realize_iSup]
  simp only [cellFormula_realize]
  constructor
  · rintro ⟨η,hη⟩
    exact hη.symm ▸ η.property
  · intro hb
    exact ⟨⟨rowVector φ a b,hb⟩,rfl⟩

theorem separated_definition (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : Fin k → Fin n → M) (h : Separates φ P a) (b : Fin m → M) :
    (cellUnionFormula φ a (positivePatterns φ P a)).Realize b ↔ b ∈ P := by
  rw [cellUnionFormula_realize]
  constructor
  · rintro ⟨c,hc,he⟩
    by_contra hb
    exact ((separates_iff_vectors φ P a).mp h c hc b hb) he
  · intro hb
    exact ⟨b,hb,rfl⟩

theorem empty_cell_truth (φ : L.Formula (Fin (n+m))) (b : Fin m → M) :
    (cellFormula φ (Fin.elim0 : Fin 0 → Fin n → M) Fin.elim0).Realize b := by
  rw [cellFormula_realize]
  exact Subsingleton.elim _ _

theorem empty_union_false (φ : L.Formula (Fin (n+m)))
    (a : Fin k → Fin n → M) (b : Fin m → M) :
    ¬ (cellUnionFormula φ a ∅).Realize b := by
  rw [cellUnionFormula_realize]
  exact Set.notMem_empty _

/-- The codes contain only finitely many actual rows and finitely many Boolean patterns. -/
def DefinitionCode (M : Type w) (n : ℕ) :=
  Σ k : ℕ, (Fin k → Fin n → M) × Set (Fin k → Bool)

def codeFormula (φ : L.Formula (Fin (n+m))) (d : DefinitionCode M n) :
    L[[(Set.univ : Set M)]].Formula (Fin m) :=
  cellUnionFormula φ d.2.1 d.2.2

theorem stable_defining_code [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ) (P : Set (Fin m → M))
    (hP : IsLocalType φ P) :
    ∃ d : DefinitionCode M n, ∀ b : Fin m → M, (codeFormula φ d).Realize b ↔ b ∈ P := by
  obtain ⟨k,a,ha⟩ := finite_separation T φ hs P hP
  exact ⟨⟨k,a,positivePatterns φ P a⟩,fun b => separated_definition φ P a ha b⟩

theorem stable_finitely_definable [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ) (P : Set (Fin m → M))
    (hP : IsLocalType φ P) :
    ∃ A : Finset M, (A : Set M).Definable L P := by
  obtain ⟨d,hd⟩ := stable_defining_code T φ hs P hP
  have hdef : (Set.univ : Set M).Definable L P :=
    ⟨codeFormula φ d,Set.ext (fun b => (hd b).symm)⟩
  obtain ⟨A,_,hA⟩ := Set.definable_iff_finitely_definable.mp hdef
  exact ⟨A,hA⟩

theorem definition_code_card [Infinite M] : #(DefinitionCode M n) ≤ #M := by
  have hκ : ℵ₀ ≤ #M := Cardinal.aleph0_le_mk M
  have hf (k : ℕ) : #((Fin k → Fin n → M) × Set (Fin k → Bool)) ≤ #M := by
    have hrows : #(Fin k → Fin n → M) ≤ #M := by
      simp only [Cardinal.mk_arrow,Cardinal.mk_fin,
        Cardinal.lift_uzero,Cardinal.lift_natCast]
      exact (Cardinal.power_le_power_right (Cardinal.power_nat_le hκ)).trans
        (Cardinal.power_nat_le hκ)
    have hpat : Cardinal.lift.{w} #(Set (Fin k → Bool)) ≤ #M :=
      (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0).trans hκ
    calc
      #((Fin k → Fin n → M) × Set (Fin k → Bool)) =
          #(Fin k → Fin n → M) * Cardinal.lift.{w} #(Set (Fin k → Bool)) := by
        simp only [Cardinal.mk_prod,Cardinal.lift_uzero]
      _ ≤ #M := Cardinal.mul_le_of_le hκ hrows hpat
  change #(Σ k : ℕ, (Fin k → Fin n → M) × Set (Fin k → Bool)) ≤ #M
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun k : ℕ => #((Fin k → Fin n → M) × Set (Fin k → Bool))) ≤
        Cardinal.sum (fun _ : ℕ => #M) := Cardinal.sum_le_sum _ _ hf
    _ = #M := by
      simp only [Cardinal.sum_const,Cardinal.mk_nat,Cardinal.lift_aleph0,
        Cardinal.lift_uzero,Cardinal.aleph0_mul_eq hκ]

/-- Choose the actual finite-row definition before testing any parameter tuple. -/
def chosenCode [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ)
    (p : LocalType (M := M) φ) : DefinitionCode M n :=
  Classical.choose (stable_defining_code T φ hs p.val p.property)

theorem chosenCode_truth [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ)
    (p : LocalType (M := M) φ) (b : Fin m → M) :
    (codeFormula φ (chosenCode T φ hs p)).Realize b ↔ b ∈ p.val := by
  exact Classical.choose_spec (stable_defining_code T φ hs p.val p.property) b

theorem chosenCode_injective [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ) :
    Function.Injective (chosenCode (M := M) T φ hs) := by
  intro p q hpq
  apply Subtype.ext
  ext b
  exact (chosenCode_truth T φ hs p b).symm.trans (by
    rw [hpq]
    exact chosenCode_truth T φ hs q b)

theorem local_type_card [Infinite M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ) :
    #(LocalType (M := M) φ) ≤ #M := by
  exact (Cardinal.mk_le_of_injective (chosenCode_injective T φ hs)).trans definition_code_card

end
end Lemmatheca.ModelTheory.StableDefinability
