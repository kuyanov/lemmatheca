import Lemmatheca.PaInductionAndHistories.PAChineseRemainder
import Mathlib.ModelTheory.Definability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! Closure lemmas used to certify that internal arithmetic induction invariants
are formulas, with finitely many parameters extracted by definable induction.
-/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] {α : Type}

local notation "DFun" => Set.DefinableFun language (Set.univ : Set M)
abbrev DPred (P : (α → M) → Prop) : Prop := (Set.univ : Set M).Definable language {v | P v}

theorem dp_and (P Q : (α → M) → Prop) (hP : DPred P) (hQ : DPred Q) :
    DPred (fun v => P v ∧ Q v) := hP.inter hQ

theorem dp_or (P Q : (α → M) → Prop) (hP : DPred P) (hQ : DPred Q) :
    DPred (fun v => P v ∨ Q v) := hP.union hQ

theorem dp_not (P : (α → M) → Prop) (hP : DPred P) :
    DPred (fun v => ¬ P v) := hP.compl

theorem dp_imp (P Q : (α → M) → Prop) (hP : DPred P) (hQ : DPred Q) :
    DPred (fun v => P v → Q v) := by
  convert hP.himp hQ using 1
  ext v
  rw [himp_eq]
  change (P v → Q v) ↔ Q v ∨ ¬ P v
  tauto

theorem dp_exists (P : (α → M) → M → Prop)
    (hP : DPred (fun w : α ⊕ Unit → M => P (w ∘ Sum.inl) (w (.inr ())))) :
    DPred (fun v => ∃ x, P v x) := by
  convert Set.Definable.exists_of_finite (β := Unit) hP using 1
  ext v
  change (∃ x, P v x) ↔ ∃ x : Unit → M, P v (x ())
  exact ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨x, hx⟩ => ⟨x (), hx⟩⟩

theorem dp_forall (P : (α → M) → M → Prop)
    (hP : DPred (fun w : α ⊕ Unit → M => P (w ∘ Sum.inl) (w (.inr ())))) :
    DPred (fun v => ∀ x, P v x) := by
  convert Set.Definable.forall_of_finite (β := Unit) hP using 1
  ext v
  change (∀ x, P v x) ↔ ∀ x : Unit → M, P v (x ())
  exact ⟨fun h x => h (x ()), fun h x => h (fun _ => x)⟩

@[fun_prop] theorem df_const (c : M) : DFun (fun _ : α → M => c) :=
  language.definableFun_const α (Set.mem_univ c)

@[fun_prop] theorem df_proj (i : α) : DFun (fun v : α → M => v i) :=
  Set.DefinableFun.proj language

@[fun_prop] theorem df_add (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DFun (fun v => addValue M (f v) (g v)) := by
  have h : (Set.univ : Set M).DefinableFun language (Structure.funMap (L := language) .add) :=
    (Set.DefinableFun.fun_symbol (L := language) .add).mono (Set.empty_subset _)
  exact h.comp (fun i => by fin_cases i; exact hf; exact hg)

@[fun_prop] theorem df_mul (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DFun (fun v => mulValue M (f v) (g v)) := by
  have h : (Set.univ : Set M).DefinableFun language (Structure.funMap (L := language) .mul) :=
    (Set.DefinableFun.fun_symbol (L := language) .mul).mono (Set.empty_subset _)
  exact h.comp (fun i => by fin_cases i; exact hf; exact hg)

@[fun_prop] theorem df_succ (f : (α → M) → M) (hf : DFun f) :
    DFun (fun v => succValue M (f v)) := by
  have h : (Set.univ : Set M).DefinableFun language (Structure.funMap (L := language) .succ) :=
    (Set.DefinableFun.fun_symbol (L := language) .succ).mono (Set.empty_subset _)
  exact h.comp (fun _ => hf)

theorem dp_eq (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DPred (fun v => f v = g v) := hf.ofPred_eq hg

variable [Finite α]

theorem dp_le (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DPred (fun v => leValue M (f v) (g v)) := by
  apply dp_exists (fun v z => addValue M z (f v) = g v)
  apply dp_eq
  · exact df_add _ _ (df_proj _) (hf.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i)))
  · exact hg.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i))

theorem dp_divides (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DPred (fun v => DividesModel M (f v) (g v)) := by
  apply dp_exists (fun v z => mulValue M (f v) z = g v)
  apply dp_eq
  · exact df_mul _ _ (hf.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i))) (df_proj _)
  · exact hg.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i))

theorem dp_coprime (f g : (α → M) → M) (hf : DFun f) (hg : DFun g) :
    DPred (fun v => CoprimeModel M (f v) (g v)) := by
  apply dp_forall (fun v r => DividesModel M r (f v) →
    DividesModel M r (g v) → r = numeralValue M 1)
  apply dp_imp
  · exact dp_divides _ _ (df_proj _) (hf.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i)))
  · apply dp_imp
    · exact dp_divides _ _ (df_proj _) (hg.comp (fun i => df_proj (α := α ⊕ Unit) (Sum.inl i)))
    · exact dp_eq _ _ (df_proj _) (df_const _)

syntax "pa_definable" : tactic
macro_rules
| `(tactic| pa_definable) => `(tactic|
  first
  | apply dp_and <;> pa_definable
  | apply dp_or <;> pa_definable
  | apply dp_imp <;> pa_definable
  | apply dp_not <;> pa_definable
  | apply dp_exists <;> pa_definable
  | apply dp_forall <;> pa_definable
  | apply dp_eq <;> fun_prop
  | apply dp_le <;> fun_prop
  | apply dp_divides <;> fun_prop
  | apply dp_coprime <;> fun_prop)

end
end Lemmatheca.ProofTheory.PAComputations
