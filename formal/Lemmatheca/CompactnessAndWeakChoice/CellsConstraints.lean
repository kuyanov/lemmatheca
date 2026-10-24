import Lemmatheca.CompactnessAndWeakChoice.TruthSets

namespace Lemmatheca.SetTheory.CompactnessAndWeakChoice
open Set Filter Order
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open Lemmatheca.SetTheory.BooleanAlgebras
universe u
variable {B : Type u} [BooleanAlgebra B]
noncomputable section
attribute [local instance] Classical.propDecidable

def cell {n : ℕ} (bs : Fin n → B) (ε : Fin n → Bool) : B :=
  Finset.univ.inf fun i => if ε i then bs i else (bs i)ᶜ
def finiteGenerated (K : Finset B) : BooleanSubalgebra B := BooleanSubalgebra.closure (↑K : Set B)

private theorem pf_inf_mem {ι : Type*} (U : PFilter B) (E : Finset ι) (f : ι → B) :
    E.inf f ∈ U ↔ ∀ i ∈ E, f i ∈ U := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih => simp [Finset.inf_insert, PFilter.inf_mem_iff, ih]

private theorem uf_sup_mem {ι : Type*} (U : StoneSpace B) (E : Finset ι) (f : ι → B) :
    E.sup f ∈ U.val ↔ ∃ i ∈ E, f i ∈ U.val := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    simpa [IsProperFilter] using U.prop.1
  | @insert a E ha ih =>
    have hu : f a ⊔ E.sup f ∈ U.val ↔ f a ∈ U.val ∨ E.sup f ∈ U.val := by
      refine ⟨(ultrafilter_characterizations U.val U.prop.1).2.mp U.prop _ _, ?_⟩
      rintro (h | h)
      · exact PFilter.mem_of_le le_sup_left h
      · exact PFilter.mem_of_le le_sup_right h
    simp only [Finset.sup_insert, hu, ih, Finset.mem_insert]
    aesop

private theorem uf_compl_mem (U : StoneSpace B) (b : B) :
    bᶜ ∈ U.val ↔ b ∉ U.val := by
  simpa using (ultrafilter_characterizations U.val U.prop.1).1.mp U.prop bᶜ

private def pattern {n : ℕ} (bs : Fin n → B) (U : StoneSpace B) : Fin n → Bool :=
  fun i => decide (bs i ∈ U.val)

private theorem cell_mem {n : ℕ} (bs : Fin n → B) (U : StoneSpace B) (ε : Fin n → Bool) :
    cell bs ε ∈ U.val ↔ ε = pattern bs U := by
  rw [cell, pf_inf_mem]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro h
    funext i
    have hi := h i
    cases he : ε i <;> simp [he, uf_compl_mem] at hi
    · simp [pattern, hi]
    · simp [pattern, hi]
  · intro h i
    rw [h]
    by_cases hi : bs i ∈ U.val <;> simp [pattern, hi, uf_compl_mem]

private theorem cell_complement {n : ℕ} (bs : Fin n → B) (E : Finset (Fin n → Bool)) :
    (E.sup (cell bs))ᶜ = (Finset.univ \ E).sup (cell bs) := by
  apply stoneMap_injective
  ext U
  change (E.sup (cell bs))ᶜ ∈ U.val ↔ (Finset.univ \ E).sup (cell bs) ∈ U.val
  simp only [uf_compl_mem, uf_sup_mem, cell_mem, Finset.mem_sdiff,
    Finset.mem_univ, true_and, exists_eq_right]

private theorem subalgebra_inf {ι : Type*} (C : BooleanSubalgebra B)
    (E : Finset ι) (f : ι → B) (hf : ∀ i ∈ E, f i ∈ C) : E.inf f ∈ C := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih =>
    rw [Finset.inf_insert]
    exact C.inf_mem (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem subalgebra_sup {ι : Type*} (C : BooleanSubalgebra B)
    (E : Finset ι) (f : ι → B) (hf : ∀ i ∈ E, f i ∈ C) : E.sup f ∈ C := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih =>
    rw [Finset.sup_insert]
    exact C.sup_mem (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem cell_in_closure {n : ℕ} (bs : Fin n → B) (ε : Fin n → Bool) :
    cell bs ε ∈ BooleanSubalgebra.closure (Set.range bs) := by
  apply subalgebra_inf
  intro i _
  have hi : bs i ∈ BooleanSubalgebra.closure (Set.range bs) :=
    BooleanSubalgebra.subset_closure (Set.mem_range_self i)
  cases ε i <;> simpa using (BooleanSubalgebra.closure (Set.range bs)).compl_mem hi

theorem cells_partition {n : ℕ} (bs : Fin n → B) :
    (∀ ε δ : Fin n → Bool, ε ≠ δ → Disjoint (cell bs ε) (cell bs δ)) ∧
    Finset.univ.sup (cell bs) = ⊤ ∧
    ∀ i, bs i = (Finset.univ.filter (fun ε => ε i = true)).sup (cell bs) := by
  refine ⟨?_,?_,?_⟩
  · intro ε δ hne
    rw [disjoint_iff]
    apply stoneMap_injective
    ext U
    change cell bs ε ⊓ cell bs δ ∈ U.val ↔ (⊥ : B) ∈ U.val
    rw [PFilter.inf_mem_iff, cell_mem, cell_mem]
    constructor
    · rintro ⟨hε,hδ⟩
      exact (hne (hε.trans hδ.symm)).elim
    · intro hbot
      exact (U.prop.1 hbot).elim
  · apply stoneMap_injective
    ext U
    change Finset.univ.sup (cell bs) ∈ U.val ↔ (⊤ : B) ∈ U.val
    rw [uf_sup_mem]
    simp [cell_mem]
  · intro i
    apply stoneMap_injective
    ext U
    change bs i ∈ U.val ↔
      (Finset.univ.filter fun ε => ε i = true).sup (cell bs) ∈ U.val
    rw [uf_sup_mem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cell_mem, exists_eq_right]
    simp [pattern]

theorem cells_normal_form {n : ℕ} (bs : Fin n → B) (b : B) :
    b ∈ BooleanSubalgebra.closure (Set.range bs) ↔
      ∃ E : Finset (Fin n → Bool), b = E.sup (cell bs) := by
  constructor
  · intro hb
    induction hb using BooleanSubalgebra.closure_bot_sup_induction with
    | mem b hb =>
      obtain ⟨i,rfl⟩ := hb
      exact ⟨Finset.univ.filter (fun ε => ε i = true), (cells_partition bs).2.2 i⟩
    | bot => exact ⟨∅,by simp⟩
    | sup a ha b hb iha ihb =>
      obtain ⟨E,rfl⟩ := iha
      obtain ⟨F,rfl⟩ := ihb
      exact ⟨E ∪ F, (Finset.sup_union).symm⟩
    | compl b hb ih =>
      obtain ⟨E,rfl⟩ := ih
      exact ⟨Finset.univ \ E,cell_complement bs E⟩
  · rintro ⟨E,rfl⟩
    exact subalgebra_sup _ E _ (fun ε _ => cell_in_closure bs ε)

theorem finite_generated_finite (K : Finset B) : Finite (finiteGenerated K) := by
  classical
  let bs : Fin (Fintype.card K) → B := fun i => ((Fintype.equivFin K).symm i).val
  have hrange : Set.range bs = (↑K : Set B) := by
    ext b
    constructor
    · rintro ⟨i,rfl⟩
      exact ((Fintype.equivFin K).symm i).property
    · intro hb
      exact ⟨Fintype.equivFin K ⟨b,hb⟩,by simp [bs]⟩
  let f : Finset (Fin (Fintype.card K) → Bool) → finiteGenerated K :=
    fun E => ⟨E.sup (cell bs), by
      change E.sup (cell bs) ∈ BooleanSubalgebra.closure (↑K : Set B)
      rw [← hrange]
      exact (cells_normal_form bs _).mpr ⟨E,rfl⟩⟩
  apply Finite.of_surjective f
  intro b
  obtain ⟨E,hE⟩ := (cells_normal_form bs b.val).mp (by
    rw [hrange]
    exact b.property)
  exact ⟨E,Subtype.ext hE.symm⟩

theorem cell_character {n : ℕ} (bs : Fin n → B)
    (m : BooleanSubalgebra.closure (Set.range bs)) (hm : (m : B) ≠ ⊥) :
    ∃ ε : Fin n → Bool, cell bs ε ≠ ⊥ ∧ cell bs ε ≤ (m : B) ∧
      ∃ h : BoundedLatticeHom (BooleanSubalgebra.closure (Set.range bs)) Bool,
        (∀ c, h c = decide (cell bs ε ≤ (c : B))) ∧ h m = true := by
  classical
  obtain ⟨U,hU,hmU⟩ := exists_ultrafilter_of_ne_bot (m : B) hm
  let u : StoneSpace B := ⟨U,hU⟩
  let ε := pattern bs u
  have hcellU : cell bs ε ∈ U := (cell_mem bs u ε).mpr rfl
  have hcell : cell bs ε ≠ ⊥ := by
    intro h
    exact hU.1 (h ▸ hcellU)
  have hiff (c : BooleanSubalgebra.closure (Set.range bs)) :
      cell bs ε ≤ (c : B) ↔ (c : B) ∈ U := by
    refine ⟨fun h => PFilter.mem_of_le h hcellU, ?_⟩
    intro hc
    obtain ⟨E,hE⟩ := (cells_normal_form bs c.val).mp c.property
    rw [hE] at hc ⊢
    obtain ⟨δ,hδ,hδU⟩ := (uf_sup_mem u E _).mp hc
    have hδε : δ = ε := (cell_mem bs u δ).mp hδU
    subst δ
    exact Finset.le_sup hδ
  let h : BoundedLatticeHom (BooleanSubalgebra.closure (Set.range bs)) Bool :=
    { toFun := fun c => decide ((c : B) ∈ U)
      map_bot' := by
        exact decide_eq_false hU.1
      map_top' := by simp
      map_inf' := by
        intro a b
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.min_eq_and, Bool.and_eq_true, decide_eq_true_eq]
        exact PFilter.inf_mem_iff
      map_sup' := by
        intro a b
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.max_eq_or, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨(ultrafilter_characterizations U hU.1).2.mp hU _ _, ?_⟩
        rintro (ha | hb)
        · exact PFilter.mem_of_le le_sup_left ha
        · exact PFilter.mem_of_le le_sup_right hb }
  refine ⟨ε,hcell,(hiff m).mpr hmU,h,?_,?_⟩
  · intro c
    change decide ((c : B) ∈ U) = decide (cell bs ε ≤ (c : B))
    rw [hiff]
  · exact decide_eq_true hmU

theorem finite_character (K : Finset B) (m : finiteGenerated K) (hm : (m : B) ≠ ⊥) :
    ∃ h : BoundedLatticeHom (finiteGenerated K) Bool, h m = true := by
  classical
  let bs : Fin (Fintype.card K) → B := fun i => ((Fintype.equivFin K).symm i).val
  have hrange : Set.range bs = (↑K : Set B) := by
    ext b
    constructor
    · rintro ⟨i,rfl⟩
      exact ((Fintype.equivFin K).symm i).property
    · intro hb
      exact ⟨Fintype.equivFin K ⟨b,hb⟩,by simp [bs]⟩
  let m' : BooleanSubalgebra.closure (Set.range bs) :=
    ⟨m.val,by rw [hrange]; exact m.property⟩
  have hm' : (m' : B) ≠ ⊥ := hm
  obtain ⟨ε,hε,hεm,h,hh,hhm⟩ := cell_character bs m' hm'
  let e : finiteGenerated K ≃o BooleanSubalgebra.closure (Set.range bs) :=
    { toFun := fun c => ⟨c.val,by rw [hrange]; exact c.property⟩
      invFun := fun c => ⟨c.val,by change c.val ∈ BooleanSubalgebra.closure (↑K : Set B); rw [← hrange]; exact c.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let eh : BoundedLatticeHom (finiteGenerated K) (BooleanSubalgebra.closure (Set.range bs)) :=
    { toFun := e
      map_bot' := BotHomClass.map_bot e
      map_top' := TopHomClass.map_top e
      map_inf' := InfHomClass.map_inf e
      map_sup' := SupHomClass.map_sup e }
  refine ⟨h.comp eh,?_⟩
  exact hhm

inductive Constraint (F : PFilter B)
  | top : Constraint F
  | bottom : Constraint F
  | compl (b : B) : Constraint F
  | meet (b c : B) : Constraint F
  | join (b c : B) : Constraint F
  | filter (b : B) (hb : b ∈ F) : Constraint F

namespace Constraint
variable {F : PFilter B}
def formula : Constraint F → PropFormula B
  | .top => .atom ⊤
  | .bottom => .neg (.atom ⊥)
  | .compl b => biconditional (.atom bᶜ) (.neg (.atom b))
  | .meet b c => biconditional (.atom (b ⊓ c)) (.conj (.atom b) (.atom c))
  | .join b c => biconditional (.atom (b ⊔ c)) (.disj (.atom b) (.atom c))
  | .filter b _ => .atom b
def labels (c : Constraint F) : Finset B := atoms c.formula
end Constraint

def constraintTheory (F : PFilter B) : Theory B := Set.range (Constraint.formula (F := F))
def selectedLabels {F : PFilter B} (cs : Finset (Constraint F)) : Finset B :=
  cs.biUnion Constraint.labels
def selectedFilterLabels {F : PFilter B} (cs : Finset (Constraint F)) : Finset B :=
  cs.biUnion fun c => match c with | .filter b _ => {b} | _ => ∅
def selectedMeet {F : PFilter B} (cs : Finset (Constraint F)) : B :=
  (selectedFilterLabels cs).inf id

def partialCharacterValuation (C : BooleanSubalgebra B) (h : BoundedLatticeHom C Bool) :
    Valuation B :=
  fun b => if hb : b ∈ C then h ⟨b,hb⟩ else false

omit [BooleanAlgebra B] in
private theorem biconditional_truth (v : Valuation B) (A C : PropFormula B) :
    Satisfies v (biconditional A C) ↔ eval v A = eval v C := by
  cases ha : eval v A <;> cases hc : eval v C <;>
    simp [Satisfies, biconditional, eval, ha, hc]

theorem selected_meet (F : PFilter B) (hF : IsProperFilter F) (cs : Finset (Constraint F)) :
    selectedMeet cs ∈ finiteGenerated (selectedLabels cs) ∧ selectedMeet cs ∈ F ∧
      selectedMeet cs ≠ ⊥ := by
  have hlabel (b : B) (hb : b ∈ selectedFilterLabels cs) :
      b ∈ selectedLabels cs ∧ b ∈ F := by
    obtain ⟨c,hc,hb⟩ := Finset.mem_biUnion.mp hb
    cases c with
    | filter d hd =>
      simp only [Finset.mem_singleton] at hb
      subst b
      refine ⟨Finset.mem_biUnion.mpr ⟨Constraint.filter d hd,hc,?_⟩,hd⟩
      simp [Constraint.labels,Constraint.formula,atoms]
    | top => simp at hb
    | bottom => simp at hb
    | compl d => simp at hb
    | meet d e => simp at hb
    | join d e => simp at hb
  have hC : selectedMeet cs ∈ finiteGenerated (selectedLabels cs) := by
    apply subalgebra_inf
    intro b hb
    exact BooleanSubalgebra.subset_closure (hlabel b hb).1
  have hmF : selectedMeet cs ∈ F :=
    (pf_inf_mem F _ id).mpr (fun b hb => (hlabel b hb).2)
  exact ⟨hC,hmF,fun h => hF (h ▸ hmF)⟩

theorem finite_constraint_model (F : PFilter B) (hF : IsProperFilter F)
    (cs : Finset (Constraint F)) :
    ∃ h : BoundedLatticeHom (finiteGenerated (selectedLabels cs)) Bool,
      ∀ c ∈ cs, Satisfies (partialCharacterValuation _ h) c.formula := by
  let C := finiteGenerated (selectedLabels cs)
  obtain ⟨hmC,hmF,hmne⟩ := selected_meet F hF cs
  let m : C := ⟨selectedMeet cs,hmC⟩
  obtain ⟨h,hm⟩ := finite_character (selectedLabels cs) m hmne
  refine ⟨h,?_⟩
  have heval (b : B) (hb : b ∈ C) :
      partialCharacterValuation C h b = h ⟨b,hb⟩ := by
    simp [partialCharacterValuation,hb]
  intro c hc
  have hlabel (b : B) (hb : b ∈ Constraint.labels c) : b ∈ C :=
    BooleanSubalgebra.subset_closure (Finset.mem_biUnion.mpr ⟨c,hc,hb⟩)
  cases c with
  | top =>
    change partialCharacterValuation C h ⊤ = true
    rw [heval _ C.top_mem]
    exact h.map_top'
  | bottom =>
    change (Bool.not (partialCharacterValuation C h ⊥)) = true
    rw [heval _ C.bot_mem]
    have hb : h (⟨⊥,C.bot_mem⟩ : C) = false := h.map_bot'
    rw [hb]
    rfl
  | compl b =>
    have hb : b ∈ C := hlabel b (by simp [Constraint.labels,Constraint.formula,biconditional,atoms])
    have hbc : bᶜ ∈ C := C.compl_mem hb
    apply (biconditional_truth _ _ _).mpr
    change partialCharacterValuation C h bᶜ = !(partialCharacterValuation C h b)
    rw [heval _ hbc,heval _ hb]
    exact map_compl' h (⟨b,hb⟩ : C)
  | meet b d =>
    have hb : b ∈ C := hlabel b (by simp [Constraint.labels,Constraint.formula,biconditional,atoms])
    have hd : d ∈ C := hlabel d (by simp [Constraint.labels,Constraint.formula,biconditional,atoms])
    have hbd : b ⊓ d ∈ C := C.inf_mem hb hd
    apply (biconditional_truth _ _ _).mpr
    change partialCharacterValuation C h (b ⊓ d) =
      (partialCharacterValuation C h b && partialCharacterValuation C h d)
    rw [heval _ hbd,heval _ hb,heval _ hd]
    exact h.map_inf' (⟨b,hb⟩ : C) (⟨d,hd⟩ : C)
  | join b d =>
    have hb : b ∈ C := hlabel b (by simp [Constraint.labels,Constraint.formula,biconditional,atoms])
    have hd : d ∈ C := hlabel d (by simp [Constraint.labels,Constraint.formula,biconditional,atoms])
    have hbd : b ⊔ d ∈ C := C.sup_mem hb hd
    apply (biconditional_truth _ _ _).mpr
    change partialCharacterValuation C h (b ⊔ d) =
      (partialCharacterValuation C h b || partialCharacterValuation C h d)
    rw [heval _ hbd,heval _ hb,heval _ hd]
    exact h.map_sup' (⟨b,hb⟩ : C) (⟨d,hd⟩ : C)
  | filter b hbF =>
    have hb : b ∈ C := hlabel b (by simp [Constraint.labels,Constraint.formula,atoms])
    have hE : b ∈ selectedFilterLabels cs :=
      Finset.mem_biUnion.mpr ⟨Constraint.filter b hbF,hc,by simp⟩
    have hmb : m ≤ (⟨b,hb⟩ : C) := Finset.inf_le hE
    have hle := OrderHomClass.mono h hmb
    rw [hm] at hle
    change partialCharacterValuation C h b = true
    rw [heval _ hb]
    exact top_le_iff.mp hle

theorem constraint_finite_satisfiable (F : PFilter B) (hF : IsProperFilter F) :
    FiniteSatisfiable (constraintTheory F) := by
  classical
  intro Δ hΔ
  have horigin : ∀ A : Δ, ∃ c : Constraint F, c.formula = A.val :=
    fun A => hΔ A.property
  let origin (A : Δ) : Constraint F := Classical.choose (horigin A)
  have hformula (A : Δ) : (origin A).formula = A.val := Classical.choose_spec (horigin A)
  let cs : Finset (Constraint F) := Finset.univ.image origin
  obtain ⟨h,hh⟩ := finite_constraint_model F hF cs
  refine ⟨partialCharacterValuation _ h, ?_⟩
  intro A hA
  let a : Δ := ⟨A,hA⟩
  have hc : origin a ∈ cs := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  simpa only [hformula] using hh (origin a) hc


theorem valuation_character (F : PFilter B) (v : Valuation B)
    (hv : ModelsTheory v (constraintTheory F)) :
    ∃ h : BoundedLatticeHom B Bool, (∀ b, h b = v b) ∧ ∀ b ∈ F, h b = true := by
  have htop : v ⊤ = true := hv _ ⟨Constraint.top,rfl⟩
  have hbot : v ⊥ = false := by
    have hb := hv _ ⟨Constraint.bottom,rfl⟩
    simpa [Constraint.formula, Satisfies, eval] using hb
  have hinf (b c : B) : v (b ⊓ c) = v b ⊓ v c := by
    have hc := hv _ ⟨Constraint.meet b c,rfl⟩
    exact (biconditional_truth v _ _).mp hc
  have hsup (b c : B) : v (b ⊔ c) = v b ⊔ v c := by
    have hc := hv _ ⟨Constraint.join b c,rfl⟩
    exact (biconditional_truth v _ _).mp hc
  let h : BoundedLatticeHom B Bool :=
    { toFun := v, map_bot' := hbot, map_top' := htop, map_inf' := hinf, map_sup' := hsup }
  refine ⟨h, fun _ => rfl, ?_⟩
  intro b hb
  exact hv _ ⟨Constraint.filter b hb,rfl⟩

theorem valuation_filter_closed (F : PFilter B) (v : Valuation B)
    (hv : ModelsTheory v (constraintTheory F)) :
    Order.IsPFilter {b : B | v b = true} := by
  obtain ⟨h,hh,hF⟩ := valuation_character F v hv
  apply Order.IsPFilter.of_def
  · refine ⟨⊤,?_⟩
    change v ⊤ = true
    rw [← hh]
    exact h.map_top'
  · intro b hb c hc
    refine ⟨b ⊓ c, ?_, inf_le_left, inf_le_right⟩
    change v (b ⊓ c) = true
    have hi : h (b ⊓ c) = h b ⊓ h c := h.map_inf' b c
    rw [← hh, hi, hh, hh]
    exact congrArg₂ (· ⊓ ·) hb hc
  · intro b c hbc hb
    change v c = true
    have hle := OrderHomClass.mono h hbc
    rw [hh, hh, hb] at hle
    exact top_le_iff.mp hle

def valuationFilter (F : PFilter B) (v : Valuation B)
    (hv : ModelsTheory v (constraintTheory F)) : PFilter B :=
  (valuation_filter_closed F v hv).toPFilter

theorem valuation_filter_spec (F : PFilter B) (v : Valuation B)
    (hv : ModelsTheory v (constraintTheory F)) :
    (∀ b, b ∈ valuationFilter F v hv ↔ v b = true) ∧
    IsUltrafilter (valuationFilter F v hv) ∧ F ≤ valuationFilter F v hv := by
  obtain ⟨h,hh,hF⟩ := valuation_character F v hv
  have hp : IsProperFilter (valuationFilter F v hv) := by
    change ¬v ⊥ = true
    have hb : h ⊥ = false := h.map_bot'
    rw [← hh, hb]
    decide
  refine ⟨fun _ => Iff.rfl, ?_, ?_⟩
  · apply (ultrafilter_characterizations _ hp).1.mpr
    intro b
    change v b = true ↔ ¬v bᶜ = true
    rw [← hh, ← hh, map_compl']
    cases h b <;> decide
  · intro b hb
    change v b = true
    rw [← hh]
    exact hF b hb

end
end Lemmatheca.SetTheory.CompactnessAndWeakChoice
