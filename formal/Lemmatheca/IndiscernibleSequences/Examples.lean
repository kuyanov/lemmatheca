import Lemmatheca.IndiscernibleSequences.Construction
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.Logic.Equiv.Fintype

/-! Equality, orders, unary colours, and repeated-coordinate counterexamples. -/
namespace Lemmatheca.Entry.IndiscernibleSequences
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.IndiscernibleSequences

universe w w' z
variable {I : Type z} [LinearOrder I]

private def oneSelection {J : Type*} [LinearOrder J] (i : J) : Fin 1 ↪o J where
  toFun := fun _ => i
  inj' := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff' := by
    intro a b
    have hab : a = b := Subsingleton.elim _ _
    simp only [hab,le_refl]

private theorem repeated_equality_blocks {M : Type*} [Language.empty.Structure M]
    (a : I → M) (ha : Function.Injective a) (m : ℕ) :
    SetIndiscernible (L := Language.empty) (∅ : Set M) (fun i (_ : Fin m) => a i) := by
  classical
  have _ := (inferInstance : LinearOrder I)
  intro n hn φ s t
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair (a ∘ s) (a ∘ t)
    (ha.comp s.injective) (ha.comp t.injective)
  let e : M ≃[Language.empty[[(∅ : Set M)]]] M :=
    { toEquiv := σ
      map_fun' := by
        intro n f
        rcases f with f | c
        · exact Empty.elim f
        · cases n with
          | zero => exact (Set.notMem_empty _ c.property).elim
          | succ n => exact isEmptyElim c
      map_rel' := by
        intro n r
        rcases r with r | r <;> exact Empty.elim r }
  have hmap : e ∘ tupleAssignment (fun i (_ : Fin m) => a i) s =
      tupleAssignment (fun i (_ : Fin m) => a i) t := by
    funext x
    exact hσ (finProdFinEquiv.symm x).1
  have hφ := (StrongHomClass.realize_formula e φ
    (v := tupleAssignment (fun i (_ : Fin m) => a i) s)).symm
  rw [hmap] at hφ
  exact hφ

theorem equality_distinct_set_indiscernible {M : Type w}
    [Language.empty.Structure M] [Infinite M] (a : I → M) (ha : Function.Injective a) :
    SetIndiscernible (L := Language.empty) (∅ : Set M) (fun i (_ : Fin 1) => a i) := by
  exact repeated_equality_blocks a ha 1

private def twoSelection {J : Type*} (i j : J) (hij : i ≠ j) : Fin 2 ↪ J where
  toFun := ![i,j]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem dense_order_increasing_indiscernible {M : Type w}
    [LinearOrder M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (a : I → M) (ha : StrictMono a) :
    letI : binaryRelLanguage.Structure M := binaryRelStructure M (· < ·)
    OrderIndiscernible (L := binaryRelLanguage) (∅ : Set M) (fun i (_ : Fin 1) => a i) := by
  let := binaryRelStructure M (· < ·)
  intro n hn φ s t
  let ψ : binaryRelLanguage.Formula (Fin (n*1)) :=
    (LEquiv.addEmptyConstants binaryRelLanguage (∅ : Set M)).symm.toLHom.onFormula φ
  let p : binaryRelLanguage.BoundedFormula Empty (n*1) :=
    BoundedFormula.relabel (n := n*1) (k := 0) (Sum.inr : Fin (n*1) → Empty ⊕ Fin (n*1)) ψ
  let q := Lemmatheca.ModelTheory.QuantifierElimination.Shared.fromShared (o := true) p
  have bridge (x : Fin (n*1) → M) :
      q.Realize (fun x y : M => x < y) x ↔ φ.Realize x := by
    exact (Lemmatheca.ModelTheory.QuantifierElimination.Shared.fromStrict_realize p x).trans
      ((Formula.realize_relabel_sumInr ψ).trans
        (LHom.realize_onFormula _ φ))
  let b (r : Fin n ↪o I) := tupleAssignment (fun i (_ : Fin 1) => a i) r
  have hb (r : Fin n ↪o I) : Function.Injective (b r) := by
    intro x y hxy
    apply finProdFinEquiv.symm.injective
    apply Prod.ext
    · exact r.injective (ha.injective hxy)
    · exact Subsingleton.elim _ _
  apply (bridge (b s)).symm.trans
  apply Iff.trans _ (bridge (b t))
  apply Lemmatheca.ModelTheory.QuantifierElimination.realize_of_patterns
    Lemmatheca.ModelTheory.QuantifierElimination.dlo_extends
    Lemmatheca.ModelTheory.QuantifierElimination.dlo_extends
  rintro (⟨i,j⟩ | ⟨_,i,j⟩)
  · exact (hb s).eq_iff.trans (hb t).eq_iff.symm
  · change a (s (finProdFinEquiv.symm i).1) < a (s (finProdFinEquiv.symm j).1) ↔
      a (t (finProdFinEquiv.symm i).1) < a (t (finProdFinEquiv.symm j).1)
    rw [ha.lt_iff_lt,s.lt_iff_lt,ha.lt_iff_lt,t.lt_iff_lt]

theorem dense_order_not_set_indiscernible {M : Type w}
    [LinearOrder M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    [Nontrivial I] (a : I → M) (ha : StrictMono a) :
    letI : binaryRelLanguage.Structure M := binaryRelStructure M (· < ·)
    ¬SetIndiscernible (L := binaryRelLanguage) (∅ : Set M) (fun i (_ : Fin 1) => a i) := by
  let := binaryRelStructure M (· < ·)
  intro h
  obtain ⟨i,j,hij⟩ := exists_pair_lt I
  let φ : binaryRelLanguage[[(∅ : Set M)]].Formula (Fin (2*1)) :=
    ((binaryRelLanguage.lhomWithConstants (∅ : Set M)).onRelation
      BinaryRelationSymbol.rel).formula ![.var 0,.var 1]
  have hφ := h 2 (by decide) φ (twoSelection i j (ne_of_lt hij))
    (twoSelection j i (ne_of_lt hij).symm)
  change (a i < a j ↔ a j < a i) at hφ
  exact (not_lt_of_gt (ha hij)) (hφ.mp (ha hij))

theorem naming_entry_distinguishes {L : Language} {M : Type w} [L.Structure M]
    (A : Set M) (a : I → M) (ha : Function.Injective a)
    (i j : I) (hij : i ≠ j) (hi : a i ∈ A) :
    ¬OrderIndiscernible (L := L) A (fun k (_ : Fin 1) => a k) := by
  intro h
  let φ : L[[A]].Formula (Fin (1*1)) :=
    (Term.var 0).equal (Constants.term (L.con (⟨a i,hi⟩ : A)))
  have hφ := h 1 (by decide) φ (oneSelection i) (oneSelection j)
  change (a i = a i ↔ a j = a i) at hφ
  exact hij (ha (hφ.mp rfl)).symm

theorem alternating_unary_not_indiscernible {L : Language} {M : Type w} [L.Structure M]
    (P : L.Relations 1) (a : ℕ → M)
    (hP : ∀ i, Structure.RelMap P ![a i] ↔ Even i) :
    ¬OrderIndiscernible (L := L) (∅ : Set M) (fun i (_ : Fin 1) => a i) := by
  intro h
  let φ : L[[(∅ : Set M)]].Formula (Fin (1*1)) :=
    (L.lhomWithConstants (∅ : Set M)).onFormula (P.formula ![.var 0])
  have hφ := h 1 (by decide) φ (oneSelection 0) (oneSelection 1)
  change ((L.lhomWithConstants (∅ : Set M)).onFormula (P.formula ![.var 0])).Realize _ ↔
    ((L.lhomWithConstants (∅ : Set M)).onFormula (P.formula ![.var 0])).Realize _ at hφ
  simp only [LHom.realize_onFormula] at hφ
  have heval (k : ℕ) :
      (P.formula ![.var 0]).Realize
        (tupleAssignment (fun i (_ : Fin 1) => a i) (oneSelection k)) ↔
          Structure.RelMap P ![a k] := by
    rw [Formula.realize_rel]
    have hv : (fun j : Fin 1 =>
        ((![Term.var (0 : Fin (1*1))] j) : L.Term (Fin (1*1))).realize
          (tupleAssignment (fun i (_ : Fin 1) => a i) (oneSelection k))) = ![a k] := by
      funext j
      fin_cases j
      rfl
    rw [hv]
  rw [heval 0,heval 1] at hφ
  have hc : Even (1 : ℕ) := (hP 1).mp (hφ.mp ((hP 0).mpr (by decide)))
  norm_num at hc

inductive ColouredSymbol : ℕ → Type
  | colour : ColouredSymbol 1
  | point (n : ℕ) : ColouredSymbol 1

def colouredLanguage : Language := ⟨fun _ => Empty, ColouredSymbol⟩

instance colouredNatStructure : colouredLanguage.Structure ℕ where
  funMap f _ := f.elim
  RelMap R xs := match R with
    | .colour => Even (xs 0)
    | .point n => xs 0 = n

def colourAtom : colouredLanguage.Formula (Fin 1) :=
  Relations.formula₁ (L := colouredLanguage) ColouredSymbol.colour (.var 0)

theorem alternating_colour_example :
    ¬OrderIndiscernible (L := colouredLanguage) (∅ : Set ℕ) (fun i (_ : Fin 1) => i) ∧
    (∀ i : ℕ, colourAtom.Realize ![2 * i]) ∧
    ¬OrderIndiscernible (L := colouredLanguage) (∅ : Set ℕ)
      (fun i (_ : Fin 1) => 2 * i) := by
  refine ⟨alternating_unary_not_indiscernible ColouredSymbol.colour id (fun _ => Iff.rfl),?_,?_⟩
  · intro i
    change Even (2*i)
    exact even_two_mul i
  · intro h
    let φ : colouredLanguage[[(∅ : Set ℕ)]].Formula (Fin (1*1)) :=
      ((colouredLanguage.lhomWithConstants (∅ : Set ℕ)).onRelation
        (ColouredSymbol.point 0)).formula ![.var 0]
    have hφ := h 1 (by decide) φ (oneSelection 0) (oneSelection 1)
    change ((2*(0:ℕ)) = 0 ↔ 2*1 = 0) at hφ
    norm_num at hφ

inductive SingletonSymbol : ℕ → Type
  | point (n : ℕ) : SingletonSymbol 1

def singletonLanguage : Language := ⟨fun _ => Empty, SingletonSymbol⟩

instance singletonNatStructure : singletonLanguage.Structure ℕ where
  funMap f _ := f.elim
  RelMap R xs := match R with | .point n => xs 0 = n

def singletonAtom (n : ℕ) : singletonLanguage.Formula (Fin 1) :=
  Relations.formula₁ (L := singletonLanguage) (SingletonSymbol.point n) (.var 0)

theorem singleton_predicates_no_indiscernible_subsequence [Nontrivial I]
    (a : I → ℕ) (ha : Function.Injective a) :
    ¬OrderIndiscernible (L := singletonLanguage) (∅ : Set ℕ)
      (fun i (_ : Fin 1) => a i) := by
  intro h
  obtain ⟨i,j,hij⟩ := exists_pair_ne I
  let φ : singletonLanguage[[(∅ : Set ℕ)]].Formula (Fin (1*1)) :=
    ((singletonLanguage.lhomWithConstants (∅ : Set ℕ)).onRelation
      (SingletonSymbol.point (a i))).formula ![.var 0]
  have hφ := h 1 (by decide) φ (oneSelection i) (oneSelection j)
  change (a i = a i ↔ a j = a i) at hφ
  exact hij (ha (hφ.mp rfl)).symm

theorem finite_singleton_tests (S : Finset ℕ) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ n ∈ S, ∀ i ∈ H, ¬(singletonAtom n).Realize ![i] := by
  refine ⟨(↑S : Set ℕ)ᶜ,S.finite_toSet.infinite_compl,?_⟩
  intro n hn i hi
  change ¬i = n
  intro h
  exact hi (h ▸ hn)

theorem doubled_equality_tuples {M : Type w} [Language.empty.Structure M] [Infinite M]
    (a : I → M) (ha : Function.Injective a) :
    Function.Injective (fun i => ![a i, a i]) ∧
      SetIndiscernible (L := Language.empty) (∅ : Set M) (fun i => ![a i, a i]) := by
  have he : (fun i => ![a i,a i]) = (fun i (_ : Fin 2) => a i) := by
    funext i k
    fin_cases k <;> rfl
  rw [he]
  refine ⟨?_,repeated_equality_blocks a ha 2⟩
  intro i j hij
  exact ha (congrFun hij 0)

theorem locally_based_doubled_coordinates {M : Type w} {N : Type w'}
    [Language.empty.Structure M] [Language.empty.Structure N]
    (a : ℕ → M) (f : M ↪ₑ[Language.empty] N) (b : I → Fin 2 → N)
    (h : LocallyBased (L := Language.empty) (∅ : Set M) f (fun i => ![a i, a i]) b) :
    ∀ i, b i 0 = b i 1 := by
  classical
  intro i
  let φ : Language.empty[[(∅ : Set M)]].Formula (Fin (1*2)) :=
    (Term.var 0).equal (Term.var 1)
  obtain ⟨t,ht⟩ := h 1 (by decide) {φ} (oneSelection i)
  have hs : φ.Realize (tupleAssignment (fun i => ![a i,a i]) t) := by rfl
  have hb := (ht φ (Finset.mem_singleton_self φ)).mpr hs
  exact hb

end Lemmatheca.Entry.IndiscernibleSequences
