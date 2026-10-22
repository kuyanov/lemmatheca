import Lemmatheca.DefinabilityAndAutomorphisms.Definability
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Data.Fintype.Pi

/-! Definable and algebraic closure inside a specified first-order structure. -/

namespace Lemmatheca.ModelTheory.Closures

open FirstOrder FirstOrder.Language

universe u v w w' z

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]

/-- Points singled out by a formula with parameters in `A`. -/
def dcl (A : Set M) : Set M := {b | A.Definable₁ L {b}}

/-- Points belonging to a finite solution set defined over `A`. -/
def acl (A : Set M) : Set M :=
  {b | ∃ s : Set M, A.Definable₁ L s ∧ s.Finite ∧ b ∈ s}

variable {L} {A B : Set M}

theorem subset_dcl (A : Set M) : A ⊆ dcl L A := by
  exact fun _ ha => Set.Definable.singleton_of_mem (L := L) ha

theorem dcl_subset_acl (A : Set M) : dcl L A ⊆ acl L A := by
  exact fun b hb => ⟨{b}, hb, Set.finite_singleton b, Set.mem_singleton b⟩

theorem dcl_mono (hAB : A ⊆ B) : dcl L A ⊆ dcl L B := by
  exact fun _ h => h.mono hAB

theorem acl_mono (hAB : A ⊆ B) : acl L A ⊆ acl L B := by
  rintro b ⟨s, hs, hfin, hb⟩
  exact ⟨s, hs.mono hAB, hfin, hb⟩

theorem mem_dcl_finite {b : M} :
    b ∈ dcl L A ↔ ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ dcl L (A₀ : Set M) := by
  exact Set.definable_iff_finitely_definable

theorem mem_acl_finite {b : M} :
    b ∈ acl L A ↔ ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ acl L (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hs, hfin, hb⟩
    obtain ⟨A₀, hA₀, hs₀⟩ := Set.definable_iff_finitely_definable.mp hs
    exact ⟨A₀, hA₀, s, hs₀, hfin, hb⟩
  · rintro ⟨A₀, hA₀, hb⟩
    exact acl_mono hA₀ hb

/-- Unique definitions eliminate a finite tuple of intermediate parameters. -/
theorem definable_over_dcl {α : Type z} {s : Set (α → M)}
    (hB : B ⊆ dcl L A) (hs : B.Definable L s) : A.Definable L s := by
  classical
  obtain ⟨B₀, hB₀, hs₀⟩ := Set.definable_iff_finitely_definable.mp hs
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs₀
  have hC : ∀ i : B₀, A.Definable L
      {v : (α ⊕ B₀) → M | v (Sum.inr i) = (i : M)} := by
    intro i
    have h := (hB (hB₀ i.property)).preimage_comp (fun _ : Fin 1 => (Sum.inr i : α ⊕ B₀))
    exact h
  have hR₀ : (∅ : Set M).Definable L
      {v : (α ⊕ B₀) → M | φ.Realize (v ∘ Sum.swap)} := by
    apply Set.empty_definable_iff.mpr
    exact ⟨φ.relabel Sum.swap, by ext v; simp⟩
  have hD : A.Definable L {v : (α ⊕ B₀) → M |
      (∀ i, v (Sum.inr i) = (i : M)) ∧ φ.Realize (v ∘ Sum.swap)} := by
    convert (Set.definable_iInter_of_finite hC).inter (hR₀.mono (Set.empty_subset A)) using 1
    ext v
    simp
  have hproj := hD.exists_of_finite
  convert hproj using 1
  ext x
  rw [hφ]
  change φ.Realize (Sum.elim Subtype.val x) ↔
    ∃ b : B₀ → M, (∀ i, b i = (i : M)) ∧
      φ.Realize (Sum.elim x b ∘ Sum.swap)
  constructor
  · intro hx
    refine ⟨Subtype.val, fun _ => rfl, ?_⟩
    have hv : Sum.elim x (Subtype.val : B₀ → M) ∘ Sum.swap =
        Sum.elim (Subtype.val : ↥(B₀ : Set M) → M) x := by
      funext i
      cases i <;> rfl
    rw [hv]
    exact hx
  · rintro ⟨b, hb, hx⟩
    have heq : b = Subtype.val := funext hb
    rw [heq] at hx
    have hv : Sum.elim x (Subtype.val : B₀ → M) ∘ Sum.swap =
        Sum.elim (Subtype.val : ↥(B₀ : Set M) → M) x := by
      funext i
      cases i <;> rfl
    rw [hv] at hx
    exact hx

/-- The actual first-order formula saying a fiber is covered by `m` witnesses.
Its free context is exactly the original parameter context `α`. -/
noncomputable def fiberBound {α : Type z} (φ : L.Formula (α ⊕ Fin 1))
    (m : ℕ) : L.Formula α :=
  (((φ.relabel (Sum.map Sum.inl id)).imp
    (Formula.iSup fun j : Fin m =>
      (Term.var (Sum.inr (0 : Fin 1))).equal
        (Term.var (Sum.inl (Sum.inr j))))).iAlls (Fin 1)).iExs (Fin m)

theorem fiberBound_realize {α : Type z} (φ : L.Formula (α ⊕ Fin 1))
    (m : ℕ) (a : α → M) :
    (fiberBound φ m).Realize a ↔
      ∃ b : Fin m → M, ∀ x : M,
        φ.Realize (Sum.elim a (fun _ => x)) → ∃ j, x = b j := by
  simp only [fiberBound, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_relabel, Formula.realize_iSup,
    Formula.realize_equal, Term.realize_var]
  simp only [Sum.elim_comp_map, Sum.elim_comp_inl, Function.comp_id,
    Sum.elim_inl, Sum.elim_inr]
  apply exists_congr
  intro b
  constructor
  · intro h x hx
    exact h (fun _ => x) hx
  · intro h x hx
    have hx' : (fun _ : Fin 1 => x 0) = x := by
      funext i
      congr 1
      exact Subsingleton.elim _ _
    rw [← hx'] at hx
    exact h (x 0) hx

theorem fiberBound_iff_finite_card [Nonempty M] {α : Type z}
    (φ : L.Formula (α ⊕ Fin 1)) (m : ℕ) (a : α → M) :
    (fiberBound φ m).Realize a ↔
      ∃ s : Finset M, s.card ≤ m ∧
        ∀ x, φ.Realize (Sum.elim a (fun _ => x)) ↔ x ∈ s := by
  classical
  rw [fiberBound_realize]
  constructor
  · rintro ⟨b, hb⟩
    let s := (Finset.univ.image b).filter (fun x => φ.Realize (Sum.elim a (fun _ => x)))
    refine ⟨s, (Finset.card_filter_le _ _).trans ?_, ?_⟩
    · simpa using (Finset.card_image_le (s := Finset.univ) (f := b))
    · intro x
      simp only [s, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun hx => ⟨(hb x hx).elim (fun j hj => ⟨j, hj.symm⟩), hx⟩,
        fun hx => hx.2⟩
  · rintro ⟨s, hm, hs⟩
    let b : Fin m → M := fun j =>
      if h : j.val < s.card then (s.equivFin.symm ⟨j.val, h⟩ : M)
      else Classical.arbitrary M
    refine ⟨b, ?_⟩
    intro x hx
    let k := s.equivFin ⟨x, (hs x).mp hx⟩
    let j : Fin m := ⟨k.val, k.isLt.trans_le hm⟩
    refine ⟨j, ?_⟩
    dsimp only [b]
    rw [dite_eq_left k.isLt]
    exact (congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨x, (hs x).mp hx⟩)).symm

theorem dcl_idempotent (A : Set M) : dcl L (dcl L A) = dcl L A := by
  apply Set.Subset.antisymm
  · exact fun _ h => definable_over_dcl (Set.Subset.refl _) h
  · exact subset_dcl (dcl L A)

theorem acl_idempotent (A : Set M) : acl L (acl L A) = acl L A := by
  classical
  apply Set.Subset.antisymm
  · rintro c ⟨s, hs, hfin, hc⟩
    obtain ⟨B₀, hB₀, hs₀⟩ := Set.definable_iff_finitely_definable.mp hs
    obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs₀
    have hw : ∀ i : B₀, ∃ t : Set M, A.Definable₁ L t ∧ t.Finite ∧ (i : M) ∈ t :=
      fun i => hB₀ i.property
    choose t ht htf hti using hw
    let m := hfin.toFinset.card
    have hsFormula (x : M) :
        φ.Realize (Sum.elim (Subtype.val : B₀ → M) (fun _ : Fin 1 => x)) ↔ x ∈ s := by
      have h := congrArg (fun r : Set (Fin 1 → M) => (fun _ => x) ∈ r) hφ
      exact (Iff.of_eq h).symm
    have hbound : (fiberBound φ m).Realize (Subtype.val : B₀ → M) := by
      apply (fiberBound_realize φ m _).mpr
      let b : Fin m → M := fun j => (hfin.toFinset.equivFin.symm j : M)
      refine ⟨b, ?_⟩
      intro x hx
      let j := hfin.toFinset.equivFin ⟨x, hfin.mem_toFinset.mpr ((hsFormula x).mp hx)⟩
      exact ⟨j, (congrArg Subtype.val
        (hfin.toFinset.equivFin.symm_apply_apply ⟨x, hfin.mem_toFinset.mpr
          ((hsFormula x).mp hx)⟩)).symm⟩
    let D : Set (B₀ → M) := {y | (∀ i, y i ∈ t i) ∧ (fiberBound φ m).Realize y}
    have hDf : D.Finite := (Set.Finite.pi' htf).subset (fun _ h => h.1)
    have hC : ∀ i : B₀, A.Definable L {y : B₀ → M | y i ∈ t i} := by
      intro i
      exact (ht i).preimage_comp (fun _ : Fin 1 => i)
    have hBoundDef : A.Definable L {y : B₀ → M | (fiberBound φ m).Realize y} := by
      apply Set.Definable.mono (B := A) _ (Set.empty_subset A)
      exact Set.empty_definable_iff.mpr ⟨fiberBound φ m, rfl⟩
    have hD : A.Definable L D := by
      convert (Set.definable_iInter_of_finite hC).inter hBoundDef using 1
      ext y
      simp [D]
    have hR₀ : (∅ : Set M).Definable L
        {v : (Fin 1 ⊕ B₀) → M | φ.Realize (v ∘ Sum.swap)} := by
      apply Set.empty_definable_iff.mpr
      exact ⟨φ.relabel Sum.swap, by ext v; simp⟩
    have hχ := ((hD.preimage_comp (Sum.inr : B₀ → Fin 1 ⊕ B₀)).inter
      (hR₀.mono (Set.empty_subset A))).exists_of_finite
    let χ : Set M := {x | ∃ y ∈ D, φ.Realize (Sum.elim y (fun _ : Fin 1 => x))}
    have hχdef : A.Definable₁ L χ := by
      change A.Definable L {x : Fin 1 → M | x 0 ∈ χ}
      convert hχ using 1
      ext x
      change (∃ y ∈ D, φ.Realize (Sum.elim y (fun _ => x 0))) ↔
        ∃ y, Sum.elim x y ∘ Sum.inr ∈ D ∧ φ.Realize (Sum.elim x y ∘ Sum.swap)
      have hx : (fun _ : Fin 1 => x 0) = x := by
        funext i
        congr 1
        exact Subsingleton.elim _ _
      simp only [hx, Sum.elim_comp_inr, Sum.elim_swap]
    have hχfin : χ.Finite := by
      have hfib : ∀ y ∈ D, {x : M | φ.Realize (Sum.elim y (fun _ => x))}.Finite := by
        intro y hy
        obtain ⟨b, hb⟩ := (fiberBound_realize φ m y).mp hy.2
        exact (Set.finite_range b).subset (fun x hx => (hb x hx).elim
          (fun j hj => ⟨j, hj.symm⟩))
      convert hDf.biUnion hfib using 1
      ext x
      simp [χ]
    refine ⟨χ, hχdef, hχfin, ?_⟩
    exact ⟨Subtype.val, ⟨hti, hbound⟩, (hsFormula c).mpr hc⟩
  · exact fun b hb => acl_mono ((subset_dcl A).trans (dcl_subset_acl A)) hb

private theorem function_value_definable (S : Set M) {n : ℕ} (f : L.Functions n)
    (b : Fin n → M) (hb : ∀ i, b i ∈ S) : Structure.funMap f b ∈ dcl L S := by
  change S.Definable L {x : Fin 1 → M | x 0 ∈ {Structure.funMap f b}}
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨(Term.var (Sum.inr (0 : Fin 1))).equal
    (Term.func f (fun i => Term.var (Sum.inl (⟨b i, hb i⟩ : S)))), ?_⟩
  ext x
  simp

theorem dcl_functions_closed (A : Set M) {n : ℕ} (f : L.Functions n)
    (b : Fin n → M) (hb : ∀ i, b i ∈ dcl L A) :
    Structure.funMap f b ∈ dcl L A := by
  rw [← dcl_idempotent A]
  exact function_value_definable (dcl L A) f b hb

theorem acl_functions_closed (A : Set M) {n : ℕ} (f : L.Functions n)
    (b : Fin n → M) (hb : ∀ i, b i ∈ acl L A) :
    Structure.funMap f b ∈ acl L A := by
  rw [← acl_idempotent A]
  exact dcl_subset_acl _ (function_value_definable (acl L A) f b hb)

/-- The substructure whose carrier is the actual definable closure. -/
def dclSubstructure (A : Set M) : L.Substructure M where
  carrier := dcl L A
  fun_mem := dcl_functions_closed A

/-- The substructure whose carrier is the actual algebraic closure. -/
def aclSubstructure (A : Set M) : L.Substructure M where
  carrier := acl L A
  fun_mem := acl_functions_closed A

variable {N : Type w'} [L.Structure N]

private noncomputable def fiberCover {α : Type z}
    (φ : L.Formula (α ⊕ Fin 1)) (m : ℕ) : L.Formula (α ⊕ Fin m) :=
  ((φ.relabel (Sum.map Sum.inl id)).iff
    (Formula.iSup fun j : Fin m =>
      (Term.var (Sum.inr (0 : Fin 1))).equal
        (Term.var (Sum.inl (Sum.inr j))))).iAlls (Fin 1)

private theorem fiberCover_realize {α : Type z}
    (φ : L.Formula (α ⊕ Fin 1)) (m : ℕ) (a : α → M) (b : Fin m → M) :
    (fiberCover φ m).Realize (Sum.elim a b) ↔
      ∀ x : M, φ.Realize (Sum.elim a (fun _ => x)) ↔ ∃ j, x = b j := by
  simp only [fiberCover, Formula.realize_iAlls, Formula.realize_iff,
    Formula.realize_relabel, Formula.realize_iSup, Formula.realize_equal,
    Term.realize_var, Sum.elim_comp_map, Sum.elim_comp_inl, Function.comp_id,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x
    exact h (fun _ => x)
  · intro h x
    have hx : (fun _ : Fin 1 => x 0) = x := by
      funext i
      congr 1
      exact Subsingleton.elim _ _
    simpa only [hx] using h (x 0)

/-- Elementarity preserves the entire fiber, with the specified map and tuple. -/
theorem elementary_finite_fiber {α : Type z} (f : M ↪ₑ[L] N)
    (φ : L.Formula (α ⊕ Fin 1)) (a : α → M)
    (hs : {x : M | φ.Realize (Sum.elim a (fun _ => x))}.Finite) :
    {y : N | φ.Realize (Sum.elim (f ∘ a) (fun _ => y))} =
      f '' {x : M | φ.Realize (Sum.elim a (fun _ => x))} := by
  classical
  let t := hs.toFinset
  let m := t.card
  let b : Fin m → M := fun j => (t.equivFin.symm j : M)
  have hM : ∀ x : M, φ.Realize (Sum.elim a (fun _ => x)) ↔ ∃ j, x = b j := by
    intro x
    constructor
    · intro hx
      let j := t.equivFin ⟨x, hs.mem_toFinset.mpr hx⟩
      exact ⟨j, (congrArg Subtype.val
        (t.equivFin.symm_apply_apply ⟨x, hs.mem_toFinset.mpr hx⟩)).symm⟩
    · rintro ⟨j, rfl⟩
      exact hs.mem_toFinset.mp (t.equivFin.symm j).property
  have hφM := (fiberCover_realize φ m a b).mpr hM
  have hφN := (f.map_formula (fiberCover φ m) (Sum.elim a b)).mpr hφM
  have hp : f ∘ Sum.elim a b = Sum.elim (f ∘ a) (f ∘ b) := by
    funext i
    cases i <;> rfl
  rw [hp] at hφN
  have hN := (fiberCover_realize φ m (f ∘ a) (f ∘ b)).mp hφN
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := (hN y).mp hy
    exact ⟨b j, (hM (b j)).mpr ⟨j, rfl⟩, hj.symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := (hM x).mp hx
    exact (hN (f x)).mpr ⟨j, congrArg f hj⟩

private theorem image_finite_definable (f : M ↪ₑ[L] N) {s : Set M}
    (hs : A.Definable₁ L s) (hfin : s.Finite) :
    (f '' A).Definable₁ L (f '' s) := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs
  have hM : {x : M | φ.Realize (Sum.elim Subtype.val (fun _ => x))} = s := by
    ext x
    exact (Iff.of_eq (congrArg (fun r : Set (Fin 1 → M) => (fun _ => x) ∈ r) hφ)).symm
  have hff := elementary_finite_fiber f φ (Subtype.val : A → M) (hM.symm ▸ hfin)
  rw [hM] at hff
  let e := Equiv.Set.image f A f.injective
  change (f '' A).Definable L {x : Fin 1 → N | x 0 ∈ f '' s}
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨φ.relabel (Sum.map e id), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
  have hp : Sum.elim (Subtype.val : ↥(f '' A) → N) x ∘ Sum.map e id =
      Sum.elim (f ∘ (Subtype.val : A → M)) x := by
    funext i
    cases i <;> rfl
  rw [hp]
  have hx : (fun _ : Fin 1 => x 0) = x := by
    funext i
    congr 1
    exact Subsingleton.elim _ _
  rw [← hx]
  exact (Iff.of_eq (congrArg (fun r : Set N => x 0 ∈ r) hff)).symm

private theorem preimage_definable (f : M ↪ₑ[L] N) {s : Set N}
    (hs : (f '' A).Definable₁ L s) : A.Definable₁ L (f ⁻¹' s) := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs
  let e := Equiv.Set.image f A f.injective
  change A.Definable L {x : Fin 1 → M | f (x 0) ∈ s}
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨φ.relabel (Sum.map e.symm id), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
  have hp : f ∘ Sum.elim (fun a : ↥(f '' A) => (e.symm a : M)) x =
      Sum.elim (Subtype.val : ↥(f '' A) → N) (f ∘ x) := by
    funext i
    cases i with
    | inl a => exact congrArg Subtype.val (e.apply_symm_apply a)
    | inr i => rfl
  have hmap := f.map_formula φ (Sum.elim (fun a : ↥(f '' A) => (e.symm a : M)) x)
  rw [hp] at hmap
  have hN := Iff.of_eq (congrArg (fun r : Set (Fin 1 → N) => (f ∘ x) ∈ r) hφ)
  have henv : Sum.elim (Subtype.val : A → M) x ∘ Sum.map e.symm id =
      Sum.elim (fun a : ↥(f '' A) => (e.symm a : M)) x := by
    funext i
    cases i <;> rfl
  rw [henv]
  exact hN.trans hmap

private theorem finite_image_preimage (f : M ↪ₑ[L] N) {s : Set N}
    (hs : (f '' A).Definable₁ L s) (hfin : s.Finite) : s = f '' (f ⁻¹' s) := by
  classical
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs
  let e := Equiv.Set.image f A f.injective
  let a : ↥(f '' A) → M := fun c => (e.symm c : M)
  have ha : f ∘ a = Subtype.val := by
    funext c
    exact congrArg Subtype.val (e.apply_symm_apply c)
  have hN (x : N) : φ.Realize (Sum.elim Subtype.val (fun _ : Fin 1 => x)) ↔ x ∈ s :=
    (Iff.of_eq (congrArg (fun r : Set (Fin 1 → N) => (fun _ => x) ∈ r) hφ)).symm
  have hM : {x : M | φ.Realize (Sum.elim a (fun _ => x))} = f ⁻¹' s := by
    ext x
    have hp : f ∘ Sum.elim a (fun _ : Fin 1 => x) =
        Sum.elim (Subtype.val : ↥(f '' A) → N) (fun _ : Fin 1 => f x) := by
      funext i
      cases i with
      | inl c => exact congrFun ha c
      | inr i => rfl
    have hm := f.map_formula φ (Sum.elim a (fun _ : Fin 1 => x))
    rw [hp] at hm
    exact hm.symm.trans (hN (f x))
  have hfinM : {x : M | φ.Realize (Sum.elim a (fun _ => x))}.Finite := by
    rw [hM]
    exact Set.Finite.preimage f.injective.injOn hfin
  have hff := elementary_finite_fiber f φ a hfinM
  rw [ha, hM] at hff
  have heq : {x : N | φ.Realize (Sum.elim Subtype.val (fun _ => x))} = s :=
    Set.ext hN
  rwa [heq] at hff

theorem elementary_image_dcl (f : M ↪ₑ[L] N) (A : Set M) :
    f '' dcl L A = dcl L (f '' A) := by
  classical
  ext c
  constructor
  · rintro ⟨b, hb, rfl⟩
    change (f '' A).Definable₁ L {f b}
    have h := image_finite_definable f hb (Set.finite_singleton b)
    simpa only [Set.image_singleton] using h
  · intro hc
    have hfin := Set.finite_singleton c
    have him := finite_image_preimage f hc hfin
    obtain ⟨b, hb, hbc⟩ := (show c ∈ f '' (f ⁻¹' {c}) by rw [← him]; simp)
    have hp : f ⁻¹' ({c} : Set N) = {b} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => f.injective (hx.trans hbc.symm), fun hx => hx ▸ hbc⟩
    refine ⟨b, ?_, hbc⟩
    change A.Definable₁ L {b}
    rw [← hp]
    exact preimage_definable f hc

theorem elementary_image_acl (f : M ↪ₑ[L] N) (A : Set M) :
    f '' acl L A = acl L (f '' A) := by
  ext c
  constructor
  · rintro ⟨b, ⟨s, hs, hfin, hb⟩, rfl⟩
    exact ⟨f '' s, image_finite_definable f hs hfin, hfin.image f, ⟨b, hb, rfl⟩⟩
  · rintro ⟨s, hs, hfin, hc⟩
    have him := finite_image_preimage f hs hfin
    obtain ⟨b, hb, hbc⟩ := (show c ∈ f '' (f ⁻¹' s) by rw [← him]; exact hc)
    exact ⟨b, ⟨f ⁻¹' s, preimage_definable f hs,
      Set.Finite.preimage f.injective.injOn hfin, hb⟩, hbc⟩

theorem automorphism_fixes_dcl (g : M ≃[L] M) (hg : Definability.Fixes g A) :
    Definability.Fixes g (dcl L A) := by
  intro b hb
  have h := Definability.definable_invariant hb g hg (fun _ : Fin 1 => b)
  exact h.mp (by simp)

end Lemmatheca.ModelTheory.Closures
