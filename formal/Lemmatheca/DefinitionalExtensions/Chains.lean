import Lemmatheca.DefinitionalExtensions.DefinitionalExtensions

namespace Lemmatheca.MathematicalLogic.DefinitionalExtensions
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w z
noncomputable section
variable (L : Language.{u,v}) (K : ℕ → Language.{u,v})

/-- The actual successive disjoint-union signatures. -/
def towerLanguage : ℕ → Language.{u,v}
  | 0 => L
  | n+1 => (towerLanguage n).sum (K n)

variable {L K}
variable (d : ∀ i, DefinitionPackage (towerLanguage L K i) (K i))

def towerTheory (T : L.Theory) : (n : ℕ) → (towerLanguage L K n).Theory
  | 0 => T
  | n+1 => (d n).extension (towerTheory T n)

def towerMap : (n : ℕ) → L →ᴸ towerLanguage L K n
  | 0 => LHom.id L
  | n+1 => LHom.sumInl.comp (towerMap n)

def towerTranslate {α : Type z} : (n : ℕ) → (towerLanguage L K n).Formula α → L.Formula α
  | 0, A => A
  | n+1, A => towerTranslate n ((d n).translate A)

/-- A final structure preserves the specified initial structure and satisfies every
successive package of defining axioms in its corresponding reduct. -/
def TowerExpansion (d : ∀ i, DefinitionPackage (towerLanguage L K i) (K i)) (M : Type w) [s : L.Structure M] :
    (n : ℕ) → (towerLanguage L K n).Structure M → Prop
  | 0, S => S = s
  | n+1, S =>
      letI : ((towerLanguage L K n).sum (K n)).Structure M := S
      letI := (LHom.sumInl : towerLanguage L K n →ᴸ (towerLanguage L K n).sum (K n)).reduct M
      TowerExpansion d M n inferInstance ∧ M ⊨ (d n).definitions

theorem tower_derives_iff (T : L.Theory) (n : ℕ)
    (hd : ∀ i < n, Admissible (d i) (towerTheory d T i)) (A : L.Sentence) :
    Derives (towerTheory d T n) ((towerMap (L := L) (K := K) n).onSentence A) ↔
      Derives T A := by
  induction n with
  | zero =>
    have he : (towerMap (L := L) (K := K) 0).onSentence A = A :=
      congrFun (LHom.id_onBoundedFormula (L := L)) A
    exact Iff.of_eq (congrArg (Derives T) he)
  | succ n ih =>
    have hp : ∀ i < n, Admissible (d i) (towerTheory d T i) :=
      fun i hi => hd i (Nat.lt_trans hi (Nat.lt_succ_self n))
    have he : (towerMap (L := L) (K := K) (n+1)).onSentence A =
        (LHom.sumInl : towerLanguage L K n →ᴸ (towerLanguage L K n).sum (K n)).onSentence
          ((towerMap n).onSentence A) :=
      congrFun (LHom.comp_onBoundedFormula LHom.sumInl (towerMap n)) A
    rw [he]
    exact ((d n).derives_extension_iff _ (hd n (Nat.lt_succ_self n)) _).trans (ih hp)

private theorem sum_reducts {L K : Language} {M : Type*} (S : (L.sum K).Structure M) :
    @Language.sumStructure L K M
      (@LHom.reduct L (L.sum K) LHom.sumInl M S)
      (@LHom.reduct K (L.sum K) LHom.sumInr M S) = S := by
  apply Structure.ext
  · funext n f x
    cases f <;> rfl
  · funext n R x
    cases R <;> rfl

private theorem tower_model (T : L.Theory) (n : ℕ) (M : Type w)
    [s : L.Structure M] [M ⊨ T] (S : (towerLanguage L K n).Structure M)
    (h : TowerExpansion d M n S) : @Theory.Model (towerLanguage L K n) M S (towerTheory d T n) := by
  induction n with
  | zero =>
    change S = s at h
    subst S
    change M ⊨ T
    exact inferInstance
  | succ n ih =>
    let : ((towerLanguage L K n).sum (K n)).Structure M := S
    let S₀ := (LHom.sumInl : towerLanguage L K n →ᴸ (towerLanguage L K n).sum (K n)).reduct M
    let : (towerLanguage L K n).Structure M := S₀
    have hpair := h
    change @TowerExpansion L K d M s n S₀ ∧ M ⊨ (d n).definitions at hpair
    have hmodel : M ⊨ towerTheory d T n := ih S₀ hpair.1
    let : (LHom.sumInl : towerLanguage L K n →ᴸ
        (towerLanguage L K n).sum (K n)).IsExpansionOn M :=
      @LHom.isExpansionOn_reduct (towerLanguage L K n) ((towerLanguage L K n).sum (K n))
        LHom.sumInl M S
    exact Theory.Model.union
      ((LHom.onTheory_model (LHom.sumInl : towerLanguage L K n →ᴸ
        (towerLanguage L K n).sum (K n)) _).mpr hmodel) hpair.2

theorem tower_unique_expansion (T : L.Theory) (n : ℕ)
    (hd : ∀ i < n, Admissible (d i) (towerTheory d T i))
    (M : Type w) [s : L.Structure M] [Nonempty M] [M ⊨ T] :
    ∃! S : (towerLanguage L K n).Structure M, TowerExpansion d M n S := by
  induction n with
  | zero =>
    change ∃! S : L.Structure M, S = s
    exact ⟨inferInstance, rfl, fun S h => h⟩
  | succ n ih =>
    have hp : ∀ i < n, Admissible (d i) (towerTheory d T i) :=
      fun i hi => hd i (Nat.lt_trans hi (Nat.lt_succ_self n))
    obtain ⟨S₀,hS₀,uS₀⟩ := ih hp
    let : (towerLanguage L K n).Structure M := S₀
    have : M ⊨ towerTheory d T n := tower_model d T n M S₀ hS₀
    obtain ⟨S₁,hS₁,uS₁⟩ := (d n).unique_expansion (towerTheory d T n)
      (hd n (Nat.lt_succ_self n)) (M := M)
    let S := @Language.sumStructure (towerLanguage L K n) (K n) M S₀ S₁
    refine ⟨S, ?_, ?_⟩
    · change @TowerExpansion L K d M s n S₀ ∧ @Theory.Model _ M S (d n).definitions
      exact ⟨hS₀,hS₁⟩
    · intro S' hS'
      let : ((towerLanguage L K n).sum (K n)).Structure M := S'
      let R₀ := (LHom.sumInl : towerLanguage L K n →ᴸ (towerLanguage L K n).sum (K n)).reduct M
      let R₁ := (LHom.sumInr : K n →ᴸ (towerLanguage L K n).sum (K n)).reduct M
      have hpair := hS'
      change @TowerExpansion L K d M s n R₀ ∧ @Theory.Model _ M S' (d n).definitions at hpair
      have he₀ : R₀ = S₀ := uS₀ R₀ hpair.1
      have hsplit : @Language.sumStructure (towerLanguage L K n) (K n) M R₀ R₁ = S' :=
        sum_reducts S'
      have hdef : @DefinitionPackage.IsDefinedExpansion (towerLanguage L K n) (K n) (d n) M S₀ R₁ := by
        change @Theory.Model _ M
          (@Language.sumStructure (towerLanguage L K n) (K n) M S₀ R₁) (d n).definitions
        rw [← he₀, hsplit]
        exact hpair.2
      have he₁ : R₁ = S₁ := uS₁ R₁ hdef
      change S' = @Language.sumStructure (towerLanguage L K n) (K n) M S₀ S₁
      exact hsplit.symm.trans (congrArg₂ (fun a b =>
        @Language.sumStructure (towerLanguage L K n) (K n) M a b) he₀ he₁)

theorem tower_elimination (n : ℕ) {α : Type z} (A : (towerLanguage L K n).Formula α)
    (M : Type w) [s : L.Structure M] (S : (towerLanguage L K n).Structure M)
    (h : TowerExpansion d M n S) (v : α → M) :
    @Formula.Realize (towerLanguage L K n) M S α A v ↔
      (towerTranslate d n A).Realize v := by
  induction n with
  | zero =>
    cases h
    exact Iff.rfl
  | succ n ih =>
    let : ((towerLanguage L K n).sum (K n)).Structure M := S
    let S₀ := (LHom.sumInl : towerLanguage L K n →ᴸ (towerLanguage L K n).sum (K n)).reduct M
    let : (towerLanguage L K n).Structure M := S₀
    have hpair := h
    change @TowerExpansion L K d M s n S₀ ∧ M ⊨ (d n).definitions at hpair
    have hstep := ((d n).realize_translate ((d n).goodExpansion_iff_models.mpr hpair.2) A v).symm
    exact hstep.trans (ih ((d n).translate A) S₀ hpair.1)

end
end Lemmatheca.MathematicalLogic.DefinitionalExtensions
