import Lemmatheca.ExistentialUniversalSentences.Syntax
import Mathlib.Data.Fintype.EquivFin
import Mathlib.ModelTheory.Substructures

/-! Witness-generated models and executable finite structure tables. -/
namespace Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
open FirstOrder FirstOrder.Language
open Structure

variable (c : ℕ) (arities : List ℕ)

/-- All vectors, with their actual finite functions retained. -/
def vectors (d : ℕ) : (n : ℕ) → List (Fin n → Fin (d+1))
  | 0 => [Fin.elim0]
  | n+1 => (List.finRange (d+1)).flatMap fun a =>
      (vectors d n).map (Fin.cons a)

/-- Enumerate maps by replacing their values on an explicit list of arguments. -/
def maps {α β : Type} [DecidableEq α] (domain : List α) (values : List β)
    (fallback : β) : List (α → β) :=
  match domain with
  | [] => [fun _ => fallback]
  | a :: aa => (maps aa values fallback).flatMap fun f =>
      values.map (fun b => Function.update f a b)

abbrev Cell (arities : List ℕ) (d : ℕ) :=
  (i : Fin arities.length) × (Fin arities[i] → Fin (d+1))

abbrev Table (c : ℕ) (arities : List ℕ) (d : ℕ) :=
  (Fin c → Fin (d+1)) × (Cell arities d → Bool)

def cells (d : ℕ) : List (Cell arities d) :=
  (List.finRange arities.length).flatMap fun i => (vectors d arities[i]).map (Sigma.mk i)

def tables (d : ℕ) : List (Table c arities d) :=
  (maps (List.finRange c) (List.finRange (d+1)) (0 : Fin (d+1))).flatMap fun f =>
    (maps (cells arities d) [false,true] false).map (fun r => (f,r))

/-- The structure literally described by a finite table. -/
@[instance_reducible]
def tableStructure {d : ℕ} (T : Table c arities d) : (lang c arities).Structure (Fin (d+1)) where
  funMap := fun f _ => match f with | .constant i => T.1 i
  RelMap := fun r a => T.2 ⟨r.val, fun j => a (Fin.cast r.property j)⟩ = true

/-- Evaluate terms in a table without using a proposition-valued truth oracle. -/
def termValue {d : ℕ} (T : Table c arities d) {α : Type}
    (v : α → Fin (d+1)) : (lang c arities).Term α → Fin (d+1)
  | .var i => v i
  | .func (.constant i) _ => T.1 i

/-- Evaluate the actual shared syntax, including arbitrary quantifiers, on a table. -/
def evaluate {d : ℕ} (T : Table c arities d) : {n : ℕ} →
    (lang c arities).BoundedFormula Empty n → (Fin n → Fin (d+1)) → Bool
  | _, .falsum, _ => false
  | _, .equal t u, v => decide
      (termValue c arities T (Sum.elim Empty.elim v) t =
       termValue c arities T (Sum.elim Empty.elim v) u)
  | _, .rel r ts, v => T.2 ⟨r.val, fun j =>
      termValue c arities T (Sum.elim Empty.elim v) (ts (Fin.cast r.property j))⟩
  | _, .imp φ ψ, v => !(evaluate T φ v) || evaluate T ψ v
  | _, .all φ, v => (List.finRange (d+1)).all fun a => evaluate T φ (Fin.snoc v a)

/-- Search the fixed existential tuple, then check every universal tuple. -/
def accepts {d m n : ℕ} (T : Table c arities d)
    (φ : (lang c arities).BoundedFormula Empty (m+n)) : Bool :=
  (vectors d m).any fun w => (vectors d n).all fun y => evaluate c arities T φ (Fin.append w y)

def induced {M : Type*} [(lang c arities).Structure M] (D : Finset M)
    (hc : ∀ i : Fin c, funMap (L := lang c arities) (.constant i) Fin.elim0 ∈ D) :
    (lang c arities).Substructure M where
  carrier := {x | x ∈ D}
  fun_mem := by
    intro n f a _
    cases f with
    | constant i =>
      change funMap (L := lang c arities) (ConstantSymbol.constant i) a ∈ D
      simpa only [Subsingleton.elim a Fin.elim0] using hc i

/-- Satisfaction of the displayed existential--universal prefix. -/
def MatrixTrue {M : Type*} [(lang c arities).Structure M] {m n : ℕ}
    (φ : (lang c arities).BoundedFormula Empty (m+n)) : Prop :=
  ∃ w : Fin m → M, ∀ y : Fin n → M, φ.Realize Empty.elim (Fin.append w y)

theorem vectors_complete (d n : ℕ) (v : Fin n → Fin (d+1)) :
    v ∈ vectors d n := by
  induction n with
  | zero => simp [vectors, Subsingleton.elim v Fin.elim0]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨v 0, by simp, ?_⟩
    exact List.mem_map.mpr ⟨Fin.tail v, ih (Fin.tail v), Fin.cons_self_tail v⟩

private theorem maps_agree {α β : Type} [DecidableEq α] (domain : List α)
    (values : List β) (fallback : β) (f : α → β) (hf : ∀ x, f x ∈ values) :
    ∃ g ∈ maps domain values fallback, ∀ x ∈ domain, g x = f x := by
  induction domain with
  | nil => exact ⟨fun _ => fallback, by simp [maps], by simp⟩
  | cons a aa ih =>
    obtain ⟨g,hg,hagree⟩ := ih
    refine ⟨Function.update g a (f a), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨g,hg,List.mem_map.mpr ⟨f a,hf a,rfl⟩⟩
    · intro x hx
      by_cases hxa : x = a
      · subst x; simp
      · exact (Function.update_of_ne hxa _ _).trans (hagree x (List.mem_cons.mp hx |>.resolve_left hxa))

private theorem maps_complete {α β : Type} [DecidableEq α] (domain : List α)
    (values : List β) (fallback : β) (f : α → β)
    (hd : ∀ x, x ∈ domain) (hf : ∀ x, f x ∈ values) :
    f ∈ maps domain values fallback := by
  obtain ⟨g,hg,hagree⟩ := maps_agree domain values fallback f hf
  have he : g = f := funext (fun x => hagree x (hd x))
  exact he ▸ hg

theorem table_card (d : ℕ) :
    Nat.card (Table c arities d) =
      (d+1)^c * 2^((arities.map (fun r => (d+1)^r)).sum) := by
  classical
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simp only [Table, Nat.card_prod, Nat.card_fun, Nat.card_fin, hb]
  congr 2
  simp only [Cell, Nat.card_sigma, Nat.card_fun, Nat.card_fin]
  rw [← List.sum_ofFn]
  congr 1
  simp

theorem tables_complete {d : ℕ} (T : Table c arities d) : T ∈ tables c arities d := by
  apply List.mem_flatMap.mpr
  refine ⟨T.1, maps_complete _ _ _ T.1 (by simp) (by simp), ?_⟩
  apply List.mem_map.mpr
  refine ⟨T.2, maps_complete _ _ _ T.2 ?_ (by intro x; cases T.2 x <;> simp), rfl⟩
  rintro ⟨i,v⟩
  exact List.mem_flatMap.mpr ⟨i, by simp, List.mem_map.mpr ⟨v, vectors_complete d arities[i] v, rfl⟩⟩

private theorem termValue_correct {d : ℕ} (T : Table c arities d) {α : Type}
    (v : α → Fin (d+1)) (t : (lang c arities).Term α) :
    letI := tableStructure c arities T
    termValue c arities T v t = t.realize v := by
  cases t with
  | var i => rfl
  | func f ts => cases f; rfl

theorem evaluate_correct {d : ℕ} (T : Table c arities d) {n : ℕ}
    (φ : (lang c arities).BoundedFormula Empty n) (v : Fin n → Fin (d+1)) :
    letI := tableStructure c arities T
    evaluate c arities T φ v = true ↔ φ.Realize Empty.elim v := by
  let := tableStructure c arities T
  induction φ with
  | falsum => simp [evaluate, BoundedFormula.Realize]
  | equal t u => simp [evaluate, termValue_correct, BoundedFormula.Realize]
  | rel r ts =>
    simp only [evaluate, termValue_correct, BoundedFormula.Realize]
    rfl
  | imp φ ψ ihφ ihψ =>
    change ((!evaluate c arities T φ v || evaluate c arities T ψ v) = true) ↔
      (φ.Realize Empty.elim v → ψ.Realize Empty.elim v)
    have hp := ihφ v
    have hq := ihψ v
    constructor
    · intro h hφ
      have he := hp.mpr hφ
      have hψ : evaluate c arities T ψ v = true := by simpa [he] using h
      exact hq.mp hψ
    · intro h
      cases he : evaluate c arities T φ v with
      | false => simp
      | true => simp [hq.mpr (h (hp.mp he))]
  | all φ ih => simp [evaluate, BoundedFormula.Realize, ih]

private theorem allBlock_realize {M : Type*} [(lang c arities).Structure M]
    (n : ℕ) {m : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) (v : Fin m → M) :
    (allBlock c arities n φ).Realize Empty.elim v ↔
      ∀ y : Fin n → M, φ.Realize Empty.elim (Fin.append v y) := by
  induction n with
  | zero => simp [allBlock, Fin.append_right_nil _ _ rfl]
  | succ n ih =>
    simp only [allBlock, ih, BoundedFormula.realize_all]
    constructor
    · intro h y
      rw [← Fin.snoc_init_self y, Fin.append_snoc]
      exact h (Fin.init y) (y (Fin.last n))
    · intro h y a
      rw [← Fin.append_snoc]
      exact h (Fin.snoc y a)

private theorem exBlock_eq_exs (m : ℕ) (φ : (lang c arities).BoundedFormula Empty m) :
    exBlock c arities m φ = φ.exs := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih φ.ex

theorem sentence_realize {M : Type*} [(lang c arities).Structure M] {m n : ℕ}
    (φ : (lang c arities).BoundedFormula Empty (m+n)) :
    M ⊨ sentence c arities φ ↔ MatrixTrue c arities (M := M) φ := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simp only [sentence, exBlock_eq_exs, Sentence.Realize, he,
    BoundedFormula.realize_exs, allBlock_realize, MatrixTrue]

theorem accepts_correct {d m n : ℕ} (T : Table c arities d)
    (φ : (lang c arities).BoundedFormula Empty (m+n)) :
    letI := tableStructure c arities T
    accepts c arities T φ = true ↔ (Fin (d+1)) ⊨ sentence c arities φ := by
  let := tableStructure c arities T
  rw [sentence_realize]
  simp only [accepts, List.any_eq_true, List.all_eq_true, MatrixTrue]
  constructor
  · rintro ⟨w,_,hw⟩
    refine ⟨w, fun y => ?_⟩
    exact (evaluate_correct c arities T φ _).mp (hw y (vectors_complete d n y))
  · rintro ⟨w,hw⟩
    refine ⟨w,vectors_complete d m w,fun y _ => ?_⟩
    exact (evaluate_correct c arities T φ _).mpr (hw y)

theorem qf_restriction {M : Type*} [(lang c arities).Structure M]
    (D : Finset M) (hc : ∀ i : Fin c,
      funMap (L := lang c arities) (.constant i) Fin.elim0 ∈ D)
    {n : ℕ} (φ : (lang c arities).BoundedFormula Empty n) (hq : φ.IsQF)
    (v : Fin n → induced c arities D hc) :
    φ.Realize Empty.elim (fun i => (v i).val) ↔ φ.Realize Empty.elim v := by
  have h := hq.realize_embedding (induced c arities D hc).subtype
    (v := (Empty.elim : Empty → induced c arities D hc)) (xs := v)
  have he : (⇑(induced c arities D hc).subtype ∘ Empty.elim) = (Empty.elim : Empty → M) :=
    funext (fun x => x.elim)
  rw [he] at h
  exact h

theorem small_submodel {M : Type*} [(lang c arities).Structure M] [Nonempty M]
    {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) (hq : φ.IsQF)
    (hφ : MatrixTrue c arities (M := M) φ) :
    ∃ (D : Finset M) (hc : ∀ i : Fin c,
      funMap (L := lang c arities) (.constant i) Fin.elim0 ∈ D),
      D.Nonempty ∧ D.card ≤ max 1 (m+c) ∧
        @MatrixTrue c arities (induced c arities D hc) inferInstance m n φ := by
  classical
  obtain ⟨w,hw⟩ := hφ
  let k : Fin c → M := fun i => funMap (L := lang c arities) (.constant i) Fin.elim0
  let D₀ := Finset.univ.image w ∪ Finset.univ.image k
  let a₀ : M := Classical.choice inferInstance
  let D : Finset M := if D₀ = ∅ then {a₀} else D₀
  have hsub : D₀ ⊆ D := by
    intro x hx
    dsimp [D]
    split
    · rename_i he
      simp [he] at hx
    · exact hx
  have hc : ∀ i : Fin c, funMap (L := lang c arities) (.constant i) Fin.elim0 ∈ D := by
    intro i
    exact hsub (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hwD : ∀ i, w i ∈ D := by
    intro i
    exact hsub (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
  have hne : D.Nonempty := by
    dsimp [D]
    split
    · exact Finset.singleton_nonempty _
    · exact Finset.nonempty_iff_ne_empty.mpr ‹D₀ ≠ ∅›
  have hcard : D.card ≤ max 1 (m+c) := by
    dsimp [D]
    split
    · simp
    · calc
        D₀.card ≤ (Finset.univ.image w).card + (Finset.univ.image k).card := Finset.card_union_le _ _
        _ ≤ m+c := by
          have hwc := Finset.card_image_le (s := Finset.univ) (f := w)
          have hkc := Finset.card_image_le (s := Finset.univ) (f := k)
          simpa using Nat.add_le_add hwc hkc
        _ ≤ max 1 (m+c) := le_max_right _ _
  refine ⟨D,hc,hne,hcard,?_⟩
  let w' : Fin m → induced c arities D hc := fun i => ⟨w i,hwD i⟩
  refine ⟨w',fun y => ?_⟩
  apply (qf_restriction c arities D hc φ hq (Fin.append w' y)).mp
  have he : (fun i => (Fin.append w' y i).val) =
      Fin.append w (fun i => (y i).val) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [w']
  rw [he]
  exact hw (fun i => (y i).val)

noncomputable def tableFromStructure (d : ℕ) [(lang c arities).Structure (Fin (d+1))] :
    Table c arities d := by
  classical
  exact (fun i => funMap (L := lang c arities) (.constant i) Fin.elim0,
    fun p => decide (RelMap (L := lang c arities) ⟨p.1,rfl⟩ p.2))

theorem tableFromStructure_eq (d : ℕ) [hM : (lang c arities).Structure (Fin (d+1))] :
    tableStructure c arities (tableFromStructure c arities d) = hM := by
  classical
  apply Structure.ext
  · funext n f a
    cases f with
    | constant i =>
      change funMap (L := lang c arities) (.constant i) Fin.elim0 =
        funMap (L := lang c arities) (.constant i) a
      congr 1
      exact Subsingleton.elim _ _
  · funext n r a
    rcases r with ⟨i,hi⟩
    cases hi
    exact @decide_eq_true_eq (RelMap (L := lang c arities) ⟨i,rfl⟩ a)
      (Classical.propDecidable _)

theorem bounded_table_model {M : Type*} [(lang c arities).Structure M] [Nonempty M]
    {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) (hq : φ.IsQF)
    (hφ : M ⊨ sentence c arities φ) :
    ∃ d < max 1 (m+c), ∃ T : Table c arities d,
      accepts c arities T φ = true := by
  classical
  obtain ⟨D,hc,hne,hcard,hD⟩ := small_submodel c arities φ hq
    ((sentence_realize c arities φ).mp hφ)
  let S := induced c arities D hc
  let eD : S ≃ D := {
    toFun x := ⟨x.val,x.property⟩
    invFun x := ⟨x.val,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let : Fintype S := Fintype.ofEquiv D eD.symm
  have hcount : Fintype.card S = D.card := (Fintype.card_congr eD).trans (Fintype.card_coe D)
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hne)
  let e : S ≃ Fin (d+1) := (Fintype.equivFin S).trans (finCongr (hcount.trans hd))
  let : (lang c arities).Structure (Fin (d+1)) := e.inducedStructure
  have hs : S ⊨ sentence c arities φ := (sentence_realize c arities φ).mpr hD
  have hn : (Fin (d+1)) ⊨ sentence c arities φ :=
    (StrongHomClass.realize_sentence e.inducedStructureEquiv _).mp hs
  refine ⟨d,by omega,tableFromStructure c arities d,?_⟩
  apply (accepts_correct c arities _ φ).mpr
  rw [tableFromStructure_eq]
  exact hn

end Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
