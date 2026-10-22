import Lemmatheca.FraisseLimits.FraisseLimits
import Lemmatheca.BackAndForth.BackAndForth
import Lemmatheca.FirstOrderStructures.BasicStructures
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.Data.Nat.BitIndices
import Mathlib.Combinatorics.Colex

/-! The binary Rado graph, fresh finite extension requests, and its actual first-order theory. -/

namespace Lemmatheca.ModelTheory.RandomGraph

open FirstOrder FirstOrder.Language CategoryTheory
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open scoped BigOperators FirstOrder


abbrev Lang := binaryRelLanguage

instance : Lang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ n, Lang.Functions n) :=
  inferInstanceAs (Countable (Σ _ : ℕ, Empty))

universe u v w

def edge {M : Type u} [Lang.Structure M] (a b : M) : Prop :=
  Structure.RelMap (L := Lang) .rel ![a, b]

def IsGraph (M : Type u) [Lang.Structure M] : Prop :=
  (∀ a b : M, edge a b → edge b a) ∧ ∀ a : M, ¬edge a a

private theorem relMap_edge {M : Type u} [Lang.Structure M] (xs : Fin 2 → M) :
    Structure.RelMap (L := Lang) .rel xs ↔ edge (xs 0) (xs 1) := by
  have hx : xs = ![xs 0, xs 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  rfl

theorem embedding_iff {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N] (f : M → N) :
    (Function.Injective f ∧ ∀ a b, edge a b ↔ edge (f a) (f b)) ↔
      ∃ e : M ↪[Lang] N, (e : M → N) = f := by
  constructor
  · rintro ⟨hinj, hrel⟩
    exact ⟨{ toFun := f
             inj' := hinj
             map_fun' := fun F => F.elim
             map_rel' := fun R xs => by
               cases R
               rw [relMap_edge, relMap_edge]
               exact (hrel (xs 0) (xs 1)).symm }, rfl⟩
  · rintro ⟨e, rfl⟩
    refine ⟨e.injective, fun a b => ?_⟩
    have h := e.map_rel .rel ![a, b]
    rw [relMap_edge, relMap_edge] at h
    exact h.symm

def FiniteExtension (M : Type u) [Lang.Structure M] : Prop :=
  ∀ U V : Finset M, Disjoint U V →
    ∃ z : M, z ∉ (U : Set M) ∪ (V : Set M) ∧ (∀ a ∈ U, edge z a) ∧ (∀ a ∈ V, ¬edge z a)

def digit (i n : ℕ) : ℕ := n / 2 ^ i % 2

def radoEdge (a b : ℕ) : Prop :=
  (a < b ∧ digit a b = 1) ∨ (b < a ∧ digit b a = 1)

instance radoStructure : Lang.Structure ℕ := binaryRelStructure ℕ radoEdge

def binaryWitness (m : ℕ) (U : Finset ℕ) : ℕ := 2 ^ m + ∑ u ∈ U, 2 ^ u

theorem rado_isGraph : IsGraph ℕ := by
  constructor
  · intro a b hab
    change radoEdge a b at hab
    change radoEdge b a
    exact hab.elim (fun h => Or.inr h) (fun h => Or.inl h)
  · intro a
    change ¬radoEdge a a
    simp [radoEdge]

theorem finite_solutions_infinite {M : Type u} [Lang.Structure M]
    (h : FiniteExtension M) (U V : Finset M) (hd : Disjoint U V) :
    {z : M | z ∉ (U : Set M) ∪ (V : Set M) ∧ (∀ a ∈ U, edge z a) ∧ (∀ a ∈ V, ¬edge z a)}.Infinite := by
  classical
  intro hfin
  let W := hfin.toFinset
  have hdisj : Disjoint U (V ∪ W) := by
    apply Finset.disjoint_left.mpr
    intro a ha hVW
    rcases Finset.mem_union.mp hVW with hV | hW
    · exact Finset.disjoint_left.mp hd ha hV
    · have hs := hfin.mem_toFinset.mp hW
      exact hs.1 (Or.inl ha)
  obtain ⟨z, hz, hU, hVW⟩ := h U (V ∪ W) hdisj
  have hsol : z ∉ (U : Set M) ∪ (V : Set M) ∧
      (∀ a ∈ U, edge z a) ∧ (∀ a ∈ V, ¬edge z a) := by
    refine ⟨?_, hU, fun a ha => hVW a (Finset.mem_union_left W ha)⟩
    rintro (hmem | hmem)
    · exact hz (Or.inl hmem)
    · exact hz (Or.inr (Finset.mem_union_left W hmem))
  have hzW : z ∈ W := hfin.mem_toFinset.mpr hsol
  exact hz (Or.inr (Finset.mem_union_right V hzW))

theorem infinite_of_finiteExtension {M : Type u} [Lang.Structure M]
    (h : FiniteExtension M) : Infinite M := by
  have hi := finite_solutions_infinite h ∅ ∅ (by simp)
  exact Set.infinite_univ_iff.mp (hi.mono (Set.subset_univ _))

theorem digit_sum_powers (F : Finset ℕ) (i : ℕ) :
    digit i (∑ j ∈ F, 2 ^ j) = 1 ↔ i ∈ F := by
  have h : i ∈ (∑ j ∈ F, 2 ^ j).bitIndices.toFinset ↔ i ∈ F := by
    rw [Finset.toFinset_bitIndices_sum_two_pow]
  simpa only [List.mem_toFinset, Nat.mem_bitIndices, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq, digit] using h

theorem binaryWitness_answers (U V : Finset ℕ) (hd : Disjoint U V)
    (m : ℕ) (hm : ∀ a ∈ U ∪ V, a < m) :
    binaryWitness m U ∉ U ∪ V ∧
      (∀ a ∈ U, edge (binaryWitness m U) a) ∧
      (∀ a ∈ V, ¬edge (binaryWitness m U) a) := by
  have hmU : m ∉ U := fun h => (hm m (Finset.mem_union_left V h)).false
  have hw : binaryWitness m U = ∑ j ∈ insert m U, 2 ^ j := by
    simp [binaryWitness, Finset.sum_insert, hmU]
  have hlt (a : ℕ) (ha : a ∈ U ∪ V) : a < binaryWitness m U :=
    (hm a ha).trans ((show m < 2 ^ m from Nat.lt_two_pow_self).trans_le (Nat.le_add_right _ _))
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    exact (hlt _ hmem).false
  · intro a ha
    change radoEdge (binaryWitness m U) a
    refine Or.inr ⟨hlt a (Finset.mem_union_left V ha), ?_⟩
    rw [hw, digit_sum_powers]
    exact Finset.mem_insert_of_mem ha
  · intro a ha hE
    change radoEdge (binaryWitness m U) a at hE
    rcases hE with ⟨hbad, _⟩ | ⟨_, hbit⟩
    · exact (hlt a (Finset.mem_union_right U ha)).asymm hbad
    · rw [hw, digit_sum_powers, Finset.mem_insert] at hbit
      rcases hbit with rfl | hU
      · exact (hm _ (Finset.mem_union_right U ha)).false
      · exact Finset.disjoint_left.mp hd hU ha

theorem rado_finiteExtension : FiniteExtension ℕ := by
  intro U V hd
  let m := (U ∪ V).sup id + 1
  refine ⟨binaryWitness m U, ?_⟩
  simpa only [Set.mem_union, Finset.mem_coe, Finset.mem_union] using
    binaryWitness_answers U V hd m
      (fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := id) ha))

private theorem partial_edge {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N]
    (p : BackAndForth.FinitePartialIso Lang M N) (a b : p.dom) :
    edge (p.toFun a) (p.toFun b) ↔ edge (a : M) (b : M) := by
  let φ : Lang.Formula (Fin 2) := .rel .rel ![.var (.inl 0), .var (.inl 1)]
  have h := p.atomic φ (.rel _ _) ![a, b]
  simpa [φ, Formula.Realize, BoundedFormula.Realize, Term.realize, relMap_edge] using h

private def partialOfGraphMap {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N]
    (D : Set M) (hD : D.Finite) (f : D → N) (hinj : Function.Injective f)
    (hrel : ∀ a b, edge (f a) (f b) ↔ edge (a : M) (b : M)) :
    BackAndForth.FinitePartialIso Lang M N := by
  let : Lang.Structure D := binaryRelStructure D (fun a b => edge (a : M) (b : M))
  let g : D ↪[Lang] N := {
    toFun := f
    inj' := hinj
    map_fun' := fun F => F.elim
    map_rel' := fun R xs => by
      cases R
      rw [relMap_edge, relMap_edge]
      exact hrel (xs 0) (xs 1) }
  let j : D ↪[Lang] M := {
    toFun := Subtype.val
    inj' := Subtype.val_injective
    map_fun' := fun F => F.elim
    map_rel' := fun R xs => by
      cases R
      rw [relMap_edge, relMap_edge]
      rfl }
  exact {
    dom := D
    finite_dom := hD
    toFun := f
    injective := hinj
    atomic := fun φ hφ a => by
      have hN := hφ.isQF.realize_embedding g (v := a) (xs := default)
      have hM := hφ.isQF.realize_embedding j (v := a) (xs := default)
      simp only [Formula.boundedFormula_realize_eq_realize] at hN hM
      exact hN.trans hM.symm }

theorem one_vertex_extension {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N]
    (hM : IsGraph M) (hN : IsGraph N) (hEP : FiniteExtension N)
    (p : BackAndForth.FinitePartialIso Lang M N) (a : M) :
    ∃ q : BackAndForth.FinitePartialIso Lang M N, p ≤ q ∧ a ∈ q.dom := by
  classical
  by_cases ha : a ∈ p.dom
  · exact ⟨p, le_rfl, ha⟩
  let : Fintype p.dom := p.finite_dom.fintype
  let U := (Finset.univ.filter fun x : p.dom => edge a x).image p.toFun
  let V := (Finset.univ.filter fun x : p.dom => ¬edge a x).image p.toFun
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro b hbU hbV
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hbU
    obtain ⟨y, hy, he'⟩ := Finset.mem_image.mp hbV
    have hxy : x = y := p.injective (he.trans he'.symm)
    exact (Finset.mem_filter.mp hy).2 (hxy ▸ (Finset.mem_filter.mp hx).2)
  obtain ⟨z, hz, hU, hV⟩ := hEP U V hd
  have hcover (b : p.dom) : p.toFun b ∈ U ∪ V := by
    by_cases hb : edge a b
    · exact Finset.mem_union_left V (Finset.mem_image.mpr ⟨b, by simp [hb], rfl⟩)
    · exact Finset.mem_union_right U (Finset.mem_image.mpr ⟨b, by simp [hb], rfl⟩)
  have hne (b : p.dom) : z ≠ p.toFun b := by
    intro he
    apply hz
    rw [he]
    exact Finset.mem_union.mp (hcover b)
  have hinc (b : p.dom) : edge z (p.toFun b) ↔ edge a (b : M) := by
    by_cases hb : edge a b
    · exact iff_of_true (hU _ (Finset.mem_image.mpr ⟨b, by simp [hb], rfl⟩)) hb
    · exact iff_of_false (hV _ (Finset.mem_image.mpr ⟨b, by simp [hb], rfl⟩)) hb
  let D : Set M := insert a p.dom
  let old (x : D) (hx : (x : M) ≠ a) : p.dom :=
    ⟨x, (Set.mem_insert_iff.mp x.2).resolve_left hx⟩
  let f (x : D) := if hx : (x : M) = a then z else p.toFun (old x hx)
  have hinj : Function.Injective f := by
    intro x y hxy
    dsimp only [f] at hxy
    split_ifs at hxy with hx hy hy
    · exact Subtype.ext (hx.trans hy.symm)
    · exact (hne (old y hy) hxy).elim
    · exact (hne (old x hx) hxy.symm).elim
    · exact Subtype.ext (congrArg (fun b : p.dom => (b : M)) (p.injective hxy))
  have hrel (x y : D) : edge (f x) (f y) ↔ edge (x : M) (y : M) := by
    by_cases hx : (x : M) = a <;> by_cases hy : (y : M) = a
    · simp only [f, dite_eq_left hx, dite_eq_left hy, hx, hy]
      exact iff_of_false (hN.2 z) (hM.2 a)
    · simp only [f, dite_eq_left hx, dite_eq_right hy, hx]
      exact hinc (old y hy)
    · simp only [f, dite_eq_right hx, dite_eq_left hy, hy]
      have hsN : edge (p.toFun (old x hx)) z ↔ edge z (p.toFun (old x hx)) :=
        ⟨hN.1 _ _, hN.1 _ _⟩
      have hsM : edge a (x : M) ↔ edge (x : M) a := ⟨hM.1 _ _, hM.1 _ _⟩
      exact hsN.trans ((hinc (old x hx)).trans hsM)
    · simp only [f, dite_eq_right hx, dite_eq_right hy]
      exact partial_edge p (old x hx) (old y hy)
  let q := partialOfGraphMap D (p.finite_dom.insert a) f hinj hrel
  refine ⟨q, ⟨Set.subset_insert a p.dom, ?_⟩, Set.mem_insert a p.dom⟩
  intro b
  have hb : (b : M) ≠ a := fun he => ha (he ▸ b.2)
  change f ⟨b, Set.mem_insert_of_mem a b.2⟩ = p.toFun b
  simp only [f, dite_eq_right hb]
  rfl

theorem finite_placements {A : Type u} {B : Type v} {H : Type w}
    [Lang.Structure A] [Lang.Structure B]
    [Lang.Structure H] [Finite A] [Finite B]
    (_hA : IsGraph A) (hB : IsGraph B) (hH : IsGraph H) (hEP : FiniteExtension H)
    (f : A ↪[Lang] H) (g : A ↪[Lang] B) :
    ∃ h : B ↪[Lang] H, h.comp g = f := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let S := g.toHom.range
  let fS : S ↪[Lang] H := f.comp g.equivRange.symm.toEmbedding
  have hfS (a b : S) : edge (fS a) (fS b) ↔ edge (a : B) (b : B) := by
    have he := ((embedding_iff fS).mpr ⟨fS, rfl⟩).2 a b
    exact he.symm.trans (((embedding_iff S.subtype).mpr ⟨S.subtype, rfl⟩).2 a b)
  let p := partialOfGraphMap (S : Set B) (Set.finite_range g) fS fS.injective hfS
  have extend (T : Finset B) : ∃ q : BackAndForth.FinitePartialIso Lang B H,
      p ≤ q ∧ ∀ b ∈ T, b ∈ q.dom := by
    induction T using Finset.induction_on with
    | empty => exact ⟨p, le_rfl, by simp⟩
    | @insert b T hb ih =>
      obtain ⟨q, hpq, hT⟩ := ih
      obtain ⟨r, hqr, hbr⟩ := one_vertex_extension hB hH hEP q b
      refine ⟨r, hpq.trans hqr, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbr
      · exact hqr.1 (hT x hx)
  obtain ⟨q, hpq, hq⟩ := extend Finset.univ
  let qfun (b : B) := q.toFun ⟨b, hq b (Finset.mem_univ b)⟩
  have hinj : Function.Injective qfun := by
    intro a b he
    exact congrArg (fun x : q.dom => (x : B)) (q.injective he)
  have hrel (a b : B) : edge a b ↔ edge (qfun a) (qfun b) :=
    (partial_edge q ⟨a, hq a (Finset.mem_univ a)⟩
      ⟨b, hq b (Finset.mem_univ b)⟩).symm
  obtain ⟨h, hh⟩ := (embedding_iff qfun).mp ⟨hinj, hrel⟩
  refine ⟨h, ?_⟩
  ext a
  change h (g a) = f a
  rw [congrFun hh]
  change q.toFun ⟨g a, _⟩ = f a
  rw [hpq.2 ⟨g a, ⟨a, rfl⟩⟩]
  change f (g.equivRange.symm (g.equivRange a)) = f a
  rw [Language.Equiv.symm_apply_apply]

private theorem isGraph_of_embedding {A : Type u} {B : Type v}
    [Lang.Structure A] [Lang.Structure B] (hB : IsGraph B) (f : A ↪[Lang] B) :
    IsGraph A := by
  have he (a b : A) : edge a b ↔ edge (f a) (f b) :=
    ((embedding_iff f).mpr ⟨f, rfl⟩).2 a b
  exact ⟨fun a b hab => (he b a).mpr (hB.1 _ _ ((he a b).mp hab)),
    fun a haa => hB.2 (f a) ((he a a).mp haa)⟩

def finiteGraphs : Set (Bundled.{0} Lang.Structure) := {A | Finite A ∧ IsGraph A}

theorem age_eq_finiteGraphs {M : Type} [Lang.Structure M]
    (hG : IsGraph M) (hEP : FiniteExtension M) : Lang.age M = finiteGraphs := by
  ext A
  constructor
  · rintro ⟨hfg, ⟨e⟩⟩
    exact ⟨hfg.finite, isGraph_of_embedding hG e⟩
  · rintro ⟨hfinite, hA⟩
    have : Finite A := hfinite
    let : Lang.Structure Empty := binaryRelStructure Empty (fun _ _ => False)
    have hEmpty : IsGraph Empty := ⟨fun a => a.elim, fun a => a.elim⟩
    obtain ⟨f, _⟩ := (embedding_iff (Empty.elim : Empty → M)).mp
      ⟨fun a => a.elim, fun a => a.elim⟩
    obtain ⟨g, _⟩ := (embedding_iff (Empty.elim : Empty → A)).mp
      ⟨fun a => a.elim, fun a => a.elim⟩
    obtain ⟨e, _⟩ := finite_placements hEmpty hA hG hEP f g
    exact ⟨Structure.FG.of_finite, ⟨e⟩⟩

theorem extension_property {M : Type} [Lang.Structure M]
    (hG : IsGraph M) (hEP : FiniteExtension M) :
    FraisseLimits.ExtensionProperty finiteGraphs M := by
  intro A B hA hB f g
  have : Finite A := hA.1
  have : Finite B := hB.1
  exact finite_placements hA.2 hB.2 hG hEP f g

theorem rado_isFraisseLimit : Lang.IsFraisseLimit finiteGraphs ℕ := by
  have hage := age_eq_finiteGraphs rado_isGraph rado_finiteExtension
  exact ⟨(FraisseLimits.extension_property_iff_ultrahomogeneous hage).mp
    (extension_property rado_isGraph rado_finiteExtension), hage⟩

theorem rado_ultrahomogeneous : Lang.IsUltrahomogeneous ℕ :=
  rado_isFraisseLimit.ultrahomogeneous

theorem countable_universality {M : Type} [Lang.Structure M] [Countable M]
    (hG : IsGraph M) : Nonempty (M ↪[Lang] ℕ) := by
  apply FraisseLimits.countable_universality
    (age_eq_finiteGraphs rado_isGraph rado_finiteExtension)
    (extension_property rado_isGraph rado_finiteExtension)
  rintro A ⟨hfg, ⟨e⟩⟩
  exact ⟨hfg.finite, isGraph_of_embedding hG e⟩

theorem finiteGraphs_amalgamation : Lang.Amalgamation finiteGraphs := by
  simpa only [rado_isFraisseLimit.age] using rado_ultrahomogeneous.amalgamation_age

abbrev eqAtom {n : ℕ} (i j : Fin n) : Lang.BoundedFormula Empty n :=
  QuantifierElimination.Shared.atomToShared (o := true) (.inl (i, j))

abbrev edgeAtom {n : ℕ} (i j : Fin n) : Lang.BoundedFormula Empty n :=
  QuantifierElimination.Shared.atomToShared (o := true) (.inr ((), i, j))

def conjunction {n : ℕ} (k : ℕ) (φ : Fin k → Lang.BoundedFormula Empty n) :
    Lang.BoundedFormula Empty n := (List.ofFn φ).foldr (· ⊓ ·) ⊤

def irreflexiveAxiom : Lang.Sentence := (edgeAtom (n := 1) 0 0).not.all

def symmetricAxiom : Lang.Sentence :=
  ((edgeAtom (n := 2) 0 1).imp (edgeAtom 1 0)).all.all

def crossDistinct (m n : ℕ) : Lang.BoundedFormula Empty (m + n) :=
  conjunction m fun i => conjunction n fun j =>
    (eqAtom (i.castAdd n) (j.natAdd m)).not

def positiveRequest (m n : ℕ) : Lang.BoundedFormula Empty (m + n + 1) :=
  conjunction m fun i =>
    (eqAtom (Fin.last (m + n)) (i.castAdd n).castSucc).not ⊓
      edgeAtom (Fin.last (m + n)) (i.castAdd n).castSucc

def negativeRequest (m n : ℕ) : Lang.BoundedFormula Empty (m + n + 1) :=
  conjunction n fun j =>
    (eqAtom (Fin.last (m + n)) (j.natAdd m).castSucc).not ⊓
      (edgeAtom (Fin.last (m + n)) (j.natAdd m).castSucc).not

def extensionSentence (m n : ℕ) : Lang.Sentence :=
  ((crossDistinct m n).imp ((positiveRequest m n ⊓ negativeRequest m n).ex)).alls

def graphTheory : Lang.Theory :=
  {irreflexiveAxiom, symmetricAxiom} ∪
    Set.range (fun p : ℕ × ℕ => extensionSentence p.1 p.2)

private theorem eqAtom_realize {M : Type u} [Lang.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (eqAtom i j).Realize Empty.elim xs ↔ xs i = xs j := Iff.rfl

private theorem edgeAtom_realize {M : Type u} [Lang.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (edgeAtom i j).Realize Empty.elim xs ↔ edge (xs i) (xs j) :=
  QuantifierElimination.Shared.ltAtom_realize i j xs Empty.elim

private theorem conjunction_realize {M : Type u} [Lang.Structure M] {n : ℕ}
    (k : ℕ) (φ : Fin k → Lang.BoundedFormula Empty n) (xs : Fin n → M) :
    (conjunction k φ).Realize Empty.elim xs ↔ ∀ i, (φ i).Realize Empty.elim xs := by
  simp [conjunction, BoundedFormula.realize_foldr_inf]

theorem extensionSentence_realize {M : Type u} [Lang.Structure M] (m n : ℕ) :
    M ⊨ extensionSentence m n ↔
      ∀ x : Fin m → M, ∀ y : Fin n → M,
        (∀ i j, x i ≠ y j) →
          ∃ z : M, (∀ i, z ≠ x i ∧ edge z (x i)) ∧
            (∀ j, z ≠ y j ∧ ¬edge z (y j)) := by
  rw [extensionSentence, Sentence.Realize]
  have hv : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  rw [hv, BoundedFormula.realize_alls]
  simp only [BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    crossDistinct, positiveRequest, negativeRequest, conjunction_realize,
    BoundedFormula.realize_not, eqAtom_realize, edgeAtom_realize,
    Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h x y hxy
    simpa using h (Fin.append x y) (by simpa using hxy)
  · intro h xs hxy
    exact h (fun i => xs (i.castAdd n)) (fun j => xs (j.natAdd m)) hxy

private theorem schemas_iff {M : Type u} [Lang.Structure M] :
    (∀ m n, M ⊨ extensionSentence m n) ↔ FiniteExtension M := by
  classical
  constructor
  · intro h U V hd
    let eU := Fintype.equivFin U
    let eV := Fintype.equivFin V
    let x (i : Fin (Fintype.card U)) : M := eU.symm i
    let y (i : Fin (Fintype.card V)) : M := eV.symm i
    have hxy (i j) : x i ≠ y j := by
      intro he
      have hi := (eU.symm i).2
      have hj := (eV.symm j).2
      change x i ∈ U at hi
      change y j ∈ V at hj
      exact Finset.disjoint_left.mp hd (he ▸ hi) hj
    obtain ⟨z, hzU, hzV⟩ := (extensionSentence_realize _ _).mp (h _ _) x y hxy
    have hU (a : M) (ha : a ∈ U) : z ≠ a ∧ edge z a := by
      simpa only [x, Equiv.symm_apply_apply] using hzU (eU ⟨a, ha⟩)
    have hV (a : M) (ha : a ∈ V) : z ≠ a ∧ ¬edge z a := by
      simpa only [y, Equiv.symm_apply_apply] using hzV (eV ⟨a, ha⟩)
    refine ⟨z, ?_, fun a ha => (hU a ha).2, fun a ha => (hV a ha).2⟩
    rintro (hzu | hzv)
    · exact (hU z hzu).1 rfl
    · exact (hV z hzv).1 rfl
  · intro h m n
    apply (extensionSentence_realize m n).mpr
    intro x y hxy
    let U := Finset.univ.image x
    let V := Finset.univ.image y
    have hd : Disjoint U V := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
      exact hxy i j hj.symm
    obtain ⟨z, hz, hU, hV⟩ := h U V hd
    have hx (i) : x i ∈ U := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hy (j) : y j ∈ V := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    refine ⟨z, fun i => ⟨?_, hU _ (hx i)⟩, fun j => ⟨?_, hV _ (hy j)⟩⟩
    · intro he
      exact hz (Or.inl (he ▸ hx i))
    · intro he
      exact hz (Or.inr (he ▸ hy j))

theorem model_graphTheory_iff {M : Type u} [Lang.Structure M] :
    M ⊨ graphTheory ↔ IsGraph M ∧ FiniteExtension M := by
  have hi : (M ⊨ irreflexiveAxiom) ↔ ∀ a : M, ¬edge a a := by
    simp [irreflexiveAxiom, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, edgeAtom,
      QuantifierElimination.Shared.atomToShared, BoundedFormula.Realize,
      relMap_edge, Fin.snoc]
  have hs : (M ⊨ symmetricAxiom) ↔ ∀ a b : M, edge a b → edge b a := by
    simp [symmetricAxiom, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, edgeAtom,
      QuantifierElimination.Shared.atomToShared, BoundedFormula.Realize,
      relMap_edge, Fin.snoc]
  constructor
  · intro h
    have hm := (Theory.model_iff graphTheory).mp h
    refine ⟨⟨hs.mp (hm _ (Or.inl (by simp))),
      hi.mp (hm _ (Or.inl (by simp)))⟩, ?_⟩
    exact schemas_iff.mp (fun m n => hm _ (Or.inr ⟨(m, n), rfl⟩))
  · rintro ⟨hG, hEP⟩
    apply (Theory.model_iff graphTheory).mpr
    intro φ hφ
    rcases hφ with hφ | ⟨⟨m, n⟩, rfl⟩
    · rcases Set.mem_insert_iff.mp hφ with rfl | hφ
      · exact hi.mpr hG.2
      · have he := Set.mem_singleton_iff.mp hφ
        rw [he]
        exact hs.mpr hG.1
    · exact schemas_iff.mpr hEP m n

theorem rado_model : ℕ ⊨ graphTheory :=
  model_graphTheory_iff.mpr ⟨rado_isGraph, rado_finiteExtension⟩

theorem graphTheory_models_infinite {M : Type u} [Lang.Structure M]
    [graphTheory.Model M] : Infinite M :=
  infinite_of_finiteExtension
    (model_graphTheory_iff.mp (inferInstance : M ⊨ graphTheory)).2

theorem countable_prescribed_isomorphism {M N : Type}
    [Lang.Structure M] [Lang.Structure N] [Countable M] [Countable N]
    [graphTheory.Model M] [graphTheory.Model N]
    (S : Lang.Substructure M) (hS : S.FG) (f : S ↪[Lang] N) :
    ∃ e : M ≃[Lang] N, e.toEmbedding.comp S.subtype = f := by
  have hM := model_graphTheory_iff.mp (inferInstance : M ⊨ graphTheory)
  have hN := model_graphTheory_iff.mp (inferInstance : N ⊨ graphTheory)
  exact FraisseLimits.extend_prescribed_isomorphism
    (age_eq_finiteGraphs hM.1 hM.2) (extension_property hM.1 hM.2)
    (age_eq_finiteGraphs hN.1 hN.2) (extension_property hN.1 hN.2) S hS f

theorem graphTheory_complete : graphTheory.IsComplete := by
  have hcat : Cardinal.aleph0.Categorical graphTheory := by
    intro M N hM hN
    let : Countable M := Cardinal.mk_le_aleph0_iff.mp hM.le
    let : Countable N := Cardinal.mk_le_aleph0_iff.mp hN.le
    have hm := model_graphTheory_iff.mp (inferInstance : M ⊨ graphTheory)
    have hn := model_graphTheory_iff.mp (inferInstance : N ⊨ graphTheory)
    have hFm : Lang.IsFraisseLimit finiteGraphs M :=
      ⟨(FraisseLimits.extension_property_iff_ultrahomogeneous
        (age_eq_finiteGraphs hm.1 hm.2)).mp (extension_property hm.1 hm.2),
        age_eq_finiteGraphs hm.1 hm.2⟩
    have hFn : Lang.IsFraisseLimit finiteGraphs N :=
      ⟨(FraisseLimits.extension_property_iff_ultrahomogeneous
        (age_eq_finiteGraphs hn.1 hn.2)).mp (extension_property hn.1 hn.2),
        age_eq_finiteGraphs hn.1 hn.2⟩
    exact hFm.nonempty_equiv hFn
  apply Cardinal.Categorical.isComplete.{0, 0, 0} Cardinal.aleph0 graphTheory hcat le_rfl
  · simpa only [Cardinal.lift_id, FirstOrder.Language.card] using
      (Cardinal.mk_le_aleph0_iff.mpr (inferInstance : Countable Lang.Symbols))
  · let : graphTheory.Model ℕ := rado_model
    exact Theory.Model.isSatisfiable ℕ
  · intro M
    exact graphTheory_models_infinite

private noncomputable def partialSymm {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N]
    (p : BackAndForth.FinitePartialIso Lang M N) :
    BackAndForth.FinitePartialIso Lang N M := by
  have : Finite p.dom := p.finite_dom.to_subtype
  let e := _root_.Equiv.ofInjective p.toFun p.injective
  apply partialOfGraphMap (Set.range p.toFun) (Set.finite_range p.toFun)
    (fun b => (e.symm b : M)) (Subtype.val_injective.comp e.symm.injective)
  intro b c
  have hb : p.toFun (e.symm b) = (b : N) := congrArg Subtype.val (e.apply_symm_apply b)
  have hc : p.toFun (e.symm c) = (c : N) := congrArg Subtype.val (e.apply_symm_apply c)
  exact (partial_edge p (e.symm b) (e.symm c)).symm.trans (by rw [hb, hc])

private theorem partialSymm_apply {M : Type u} {N : Type v}
    [Lang.Structure M] [Lang.Structure N]
    (p : BackAndForth.FinitePartialIso Lang M N) (a : p.dom) :
    (partialSymm p).toFun ⟨p.toFun a, ⟨a, rfl⟩⟩ = (a : M) :=
  congrArg Subtype.val ((_root_.Equiv.ofInjective p.toFun p.injective).symm_apply_apply a)

theorem finite_partial_elementary {M N : Type} [Lang.Structure M] [Lang.Structure N]
    [graphTheory.Model M] [graphTheory.Model N]
    (p : BackAndForth.FinitePartialIso Lang M N) {n : ℕ}
    (φ : Lang.BoundedFormula Empty n) (a : Fin n → p.dom) :
    φ.Realize Empty.elim (p.toFun ∘ a) ↔
      φ.Realize Empty.elim (Subtype.val ∘ a) := by
  induction φ generalizing M N with
  | falsum => exact Iff.rfl
  | equal t s =>
    simp only [BoundedFormula.Realize,
      QuantifierElimination.Shared.termIndex_realize (o := true), Function.comp_apply]
    exact ⟨fun h => congrArg (fun b : p.dom => (b : M)) (p.injective h),
      fun h => congrArg p.toFun (Subtype.ext h)⟩
  | rel R ts =>
    cases R
    simp only [BoundedFormula.Realize, relMap_edge,
      QuantifierElimination.Shared.termIndex_realize (o := true), Function.comp_apply]
    exact partial_edge p _ _
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ p a) (ihψ p a)
  | @all n φ ih =>
    have hM := model_graphTheory_iff.mp (inferInstance : M ⊨ graphTheory)
    have hN := model_graphTheory_iff.mp (inferInstance : N ⊨ graphTheory)
    change (∀ y : N, φ.Realize Empty.elim (Fin.snoc (p.toFun ∘ a) y)) ↔
      ∀ x : M, φ.Realize Empty.elim (Fin.snoc (Subtype.val ∘ a) x)
    constructor
    · intro h x
      obtain ⟨q, hpq, hx⟩ := one_vertex_extension hM.1 hN.1 hN.2 p x
      let aq : Fin n → q.dom := fun i => ⟨a i, hpq.1 (a i).2⟩
      let xq : q.dom := ⟨x, hx⟩
      have hv : Subtype.val ∘ Fin.snoc aq xq = Fin.snoc (Subtype.val ∘ a) x := by
        rw [Fin.comp_snoc]
        rfl
      have hf : q.toFun ∘ Fin.snoc aq xq =
          Fin.snoc (p.toFun ∘ a) (q.toFun xq) := by
        rw [Fin.comp_snoc]
        congr 1
        funext i
        exact hpq.2 (a i)
      have he := ih q (Fin.snoc aq xq)
      rw [hf, hv] at he
      exact he.mp (h (q.toFun xq))
    · intro h y
      let r := partialSymm p
      obtain ⟨q, hrq, hy⟩ := one_vertex_extension hN.1 hM.1 hM.2 r y
      let b : Fin n → r.dom := fun i => ⟨p.toFun (a i), ⟨a i, rfl⟩⟩
      let bq : Fin n → q.dom := fun i => ⟨b i, hrq.1 (b i).2⟩
      let yq : q.dom := ⟨y, hy⟩
      have hv : Subtype.val ∘ Fin.snoc bq yq = Fin.snoc (p.toFun ∘ a) y := by
        rw [Fin.comp_snoc]
        rfl
      have hf : q.toFun ∘ Fin.snoc bq yq =
          Fin.snoc (Subtype.val ∘ a) (q.toFun yq) := by
        rw [Fin.comp_snoc]
        congr 1
        funext i
        exact (hrq.2 (b i)).trans (partialSymm_apply p (a i))
      have he := ih q (Fin.snoc bq yq)
      rw [hf, hv] at he
      exact he.mp (h (q.toFun yq))

theorem pattern_elementarity {M N : Type} [Lang.Structure M] [Lang.Structure N]
    [graphTheory.Model M] [graphTheory.Model N] {n : ℕ}
    (a : Fin n → M) (b : Fin n → N)
    (h : QuantifierElimination.pattern (o := true) edge a = QuantifierElimination.pattern (o := true) edge b)
    (φ : Lang.BoundedFormula Empty n) :
    φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b := by
  classical
  have hs : QuantifierElimination.Similar (o := true) edge edge a b := by
    intro atom
    have hc := congrFun h atom
    have hh := congrArg (fun x : Bool => x = true) hc
    simpa only [QuantifierElimination.pattern, decide_eq_true_eq] using hh.to_iff
  have heq (i j : Fin n) : a i = a j ↔ b i = b j := hs (.inl (i, j))
  let index (x : Set.range a) : Fin n := Classical.choose x.2
  have hindex (x : Set.range a) : a (index x) = (x : M) := Classical.choose_spec x.2
  let f (x : Set.range a) : N := b (index x)
  have hf (i : Fin n) : f ⟨a i, ⟨i, rfl⟩⟩ = b i :=
    (heq _ _).mp (hindex ⟨a i, ⟨i, rfl⟩⟩)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact (hindex x).symm.trans (((heq _ _).mpr hxy).trans (hindex y))
  have hrel (x y : Set.range a) : edge (f x) (f y) ↔ edge (x : M) (y : M) := by
    have he := hs (.inr ((), index x, index y))
    change edge (a (index x)) (a (index y)) ↔ edge (f x) (f y) at he
    exact he.symm.trans (by rw [hindex, hindex])
  let p := partialOfGraphMap (Set.range a) (Set.finite_range a) f hinj hrel
  let ap : Fin n → p.dom := fun i => ⟨a i, ⟨i, rfl⟩⟩
  have hp : p.toFun ∘ ap = b := funext hf
  have hv : Subtype.val ∘ ap = a := rfl
  have he := finite_partial_elementary p φ ap
  rw [hp, hv] at he
  exact he.symm

theorem graphTheory_hasQuantifierElimination : QuantifierElimination.HasQuantifierElimination graphTheory := by
  classical
  intro n φ
  let good (p : QuantifierElimination.Atom true n → Bool) : Prop :=
    ∃ M : graphTheory.ModelType, ∃ xs : Fin n → M,
      QuantifierElimination.pattern (o := true) edge xs = p ∧
        φ.Realize Empty.elim xs
  let patterns := Finset.univ.filter good
  let ψ := ((patterns.toList.map fun p =>
    QuantifierElimination.Shared.atomicPatternFormula p).foldr (· ⊔ ·) ⊥)
  have hqf (l : List (QuantifierElimination.Atom true n → Bool)) :
      ((l.map fun p => QuantifierElimination.Shared.atomicPatternFormula p).foldr
        (· ⊔ ·) ⊥).IsQF := by
    induction l with
    | nil => exact BoundedFormula.isQF_bot
    | cons p l ih =>
      exact (QuantifierElimination.Shared.atomicPatternFormula_isQF p).sup ih
  refine ⟨ψ, hqf patterns.toList, ?_⟩
  intro M v xs
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  have hr : QuantifierElimination.Shared.relation (o := true) (M := M) =
      edge (M := M) := by
    funext a b
    rfl
  have hψ : ψ.Realize Empty.elim xs ↔
      ∃ p ∈ patterns, QuantifierElimination.pattern (o := true) edge xs = p := by
    simp only [ψ, BoundedFormula.realize_foldr_sup, List.mem_map,
      Finset.mem_toList, exists_exists_and_eq_and,
      QuantifierElimination.Shared.atomicPatternFormula_realize, hr]
  rw [hψ]
  constructor
  · intro hφ
    refine ⟨QuantifierElimination.pattern (o := true) edge xs, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨M, xs, rfl, hφ⟩⟩
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨N, ys, hyp, hφ⟩ := (Finset.mem_filter.mp hp).2
    exact (pattern_elementarity xs ys (hxp.trans hyp.symm) φ).mpr hφ

def commonNeighbor : Lang.BoundedFormula Empty 2 :=
  (edgeAtom (n := 3) 2 0 ⊓ edgeAtom 2 1).ex

def mixedNeighbor : Lang.BoundedFormula Empty 2 :=
  (edgeAtom (n := 3) 2 0 ⊓ (edgeAtom 2 1).not).ex

theorem commonNeighbor_equiv : graphTheory.Iff commonNeighbor ⊤ := by
  classical
  intro M v xs
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  simp only [commonNeighbor, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    edgeAtom_realize, BoundedFormula.realize_top]
  change (∃ z : M, edge z (xs 0) ∧ edge z (xs 1)) ↔ True
  have hEP := (model_graphTheory_iff.mp M.is_model).2
  obtain ⟨z, _, hU, _⟩ := hEP {xs 0, xs 1} ∅ (by simp)
  apply iff_of_true _ True.intro
  refine ⟨z, ?_, ?_⟩
  · simpa [Fin.snoc] using hU (xs 0) (by simp)
  · simpa [Fin.snoc] using hU (xs 1) (by simp)

theorem mixedNeighbor_equiv : graphTheory.Iff mixedNeighbor (eqAtom 0 1).not := by
  classical
  intro M v xs
  have hv : v = Empty.elim := Subsingleton.elim _ _
  subst v
  rw [BoundedFormula.realize_iff]
  simp only [mixedNeighbor, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, edgeAtom_realize, eqAtom_realize]
  change (∃ z : M, edge z (xs 0) ∧ ¬edge z (xs 1)) ↔ xs 0 ≠ xs 1
  constructor
  · rintro ⟨z, hU, hV⟩ he
    exact hV (he ▸ hU)
  · intro hxy
    have hEP := (model_graphTheory_iff.mp M.is_model).2
    obtain ⟨z, _, hU, hV⟩ := hEP {xs 0} {xs 1} (by simp [hxy])
    exact ⟨z, hU _ (by simp), hV _ (by simp)⟩

end Lemmatheca.ModelTheory.RandomGraph
