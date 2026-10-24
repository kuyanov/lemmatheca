import Lemmatheca.ForcingAndGenericFilters.Orders
import Lemmatheca.Absoluteness.BoundedRelations
import Lemmatheca.NaturalNumbersAsSets.NaturalNumbersAsSets

namespace Lemmatheca.SetTheory.ForcingAndGenericFilters
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.NaturalNumbersAsSets
universe u

private theorem holds_conj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (p.conj q).Holds (fun x y => x ∈ y) a ↔
      p.Holds (fun x y => x ∈ y) a ∧ q.Holds (fun x y => x ∈ y) a := by
  classical
  simp [DeltaZero.conj,DeltaZero.neg,DeltaZero.Holds]
private theorem holds_disj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (p.disj q).Holds (fun x y => x ∈ y) a ↔
      p.Holds (fun x y => x ∈ y) a ∨ q.Holds (fun x y => x ∈ y) a := by
  classical
  by_cases hp : p.Holds (fun x y => x ∈ y) a <;>
    simp_all [DeltaZero.disj,DeltaZero.neg,DeltaZero.Holds]
private theorem holds_subset {n} (x y : Fin n) (a : Fin n → ZFSet.{u}) :
    (subsetTest x y).Holds (fun x y => x ∈ y) a ↔ a x ⊆ a y :=
  (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
    (subsetTest_correct x y a)
private theorem holds_relation {n} (x y R : Fin n) (a : Fin n → ZFSet.{u}) :
    (relationTest x y R).Holds (fun x y => x ∈ y) a ↔ ZFSet.pair (a x) (a y) ∈ a R :=
  (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
    (relationTest_correct x y R a)
private theorem holds_empty {n} (x : Fin n) (a : Fin n → ZFSet.{u}) :
    (emptyTest x).Holds (fun x y => x ∈ y) a ↔ a x = ∅ :=
  (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
    (emptyTest_correct x a)
private theorem insert_self_eq (x : ZFSet.{u}) : insert x x = x ∪ {x} := by
  ext y
  simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  exact or_comm

def densityTest {n} (P D R : Fin n) : DeltaZero n :=
  .conj (subsetTest D P)
    (.ball P (.bex D.castSucc
      (relationTest (Fin.last (n+1)) (Fin.last n).castSucc R.castSucc.castSucc)))

def densityBelowTest {n} (P D R p : Fin n) : DeltaZero n :=
  .conj (subsetTest D P)
    (.ball P (.imp (relationTest (Fin.last n) p.castSucc R.castSucc)
      (.bex D.castSucc
        (relationTest (Fin.last (n+1)) (Fin.last n).castSucc R.castSucc.castSucc))))

theorem densityTest_correct {n} (P D R : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (densityTest P D R).toShared a ↔
      a D ⊆ a P ∧ ∀ p ∈ a P, ∃ q ∈ a D, ZFSet.pair q p ∈ a R := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  simp only [densityTest,holds_conj,holds_subset,DeltaZero.Holds,
    DeltaZero.bex_realize,holds_relation,Fin.snoc_castSucc,Fin.snoc_last]

theorem densityBelowTest_correct {n} (P D R p : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (densityBelowTest P D R p).toShared a ↔
      a D ⊆ a P ∧ ∀ q ∈ a P, ZFSet.pair q (a p) ∈ a R →
        ∃ r ∈ a D, ZFSet.pair r q ∈ a R := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  simp only [densityBelowTest,holds_conj,holds_subset,DeltaZero.Holds,
    DeltaZero.bex_realize,holds_relation,Fin.snoc_castSucc,Fin.snoc_last]

theorem density_absolute (M : ZFSet.{u}) (hM : M.IsTransitive) {n}
    (P D R : Fin n) (a : Fin n → M) :
    setSatisfies M (densityTest P D R).toShared a ↔
      (a D).val ⊆ (a P).val ∧
        ∀ p ∈ (a P).val, ∃ q ∈ (a D).val, ZFSet.pair q p ∈ (a R).val := by
  exact (bounded_to_universe M hM _ a).trans (densityTest_correct P D R _)

theorem density_below_absolute (M : ZFSet.{u}) (hM : M.IsTransitive) {n}
    (P D R p : Fin n) (a : Fin n → M) :
    setSatisfies M (densityBelowTest P D R p).toShared a ↔
      (a D).val ⊆ (a P).val ∧ ∀ q ∈ (a P).val, ZFSet.pair q (a p).val ∈ (a R).val →
        ∃ r ∈ (a D).val, ZFSet.pair r q ∈ (a R).val := by
  exact (bounded_to_universe M hM _ a).trans (densityBelowTest_correct P D R p _)

theorem density_native_bridge {Q : Type u} [PartialOrder Q]
    (P D R : ZFSet.{u}) (code : Q ≃ P) (hD : D ⊆ P)
    (hR : ∀ q p, ZFSet.pair (code q).val (code p).val ∈ R ↔ q ≤ p) :
    universeSatisfies (densityTest (0 : Fin 3) 1 2).toShared ![P,D,R] ↔
      Dense {q : Q | (code q).val ∈ D} := by
  rw [densityTest_correct]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨_,h⟩ p
    obtain ⟨z,hz,hr⟩ := h (code p).val (code p).property
    let q := code.symm ⟨z,hD hz⟩
    have hq : (code q).val = z := congrArg Subtype.val (code.apply_symm_apply _)
    refine ⟨q,?_,?_⟩
    · change (code q).val ∈ D
      rw [hq]; exact hz
    · exact (hR q p).mp (hq.symm ▸ hr)
  · intro h
    refine ⟨hD,?_⟩
    intro p hp
    let q := code.symm ⟨p,hp⟩
    have hq : (code q).val = p := congrArg Subtype.val (code.apply_symm_apply _)
    obtain ⟨r,hr,hle⟩ := h q
    refine ⟨(code r).val,hr,?_⟩
    rw [← hq]
    exact (hR r q).mpr hle

def successorTest {n} (i : Fin n) : DeltaZero n :=
  .bex i (.conj (subsetTest (Fin.last n) i.castSucc)
    (.ball i.castSucc (.disj
      (.mem (Fin.last (n+1)) (Fin.last n).castSucc)
      (.equal (Fin.last (n+1)) (Fin.last n).castSucc))))

def limitTest {n} (i : Fin n) : DeltaZero n :=
  .conj (.neg (emptyTest i))
    (.ball i (.bex i.castSucc (.mem (Fin.last n).castSucc (Fin.last (n+1)))))

def omegaTest {n} (i : Fin n) : DeltaZero n :=
  .conj (ordinalTest i) (.conj (limitTest i)
    (.ball i (.disj (emptyTest (Fin.last n)) (successorTest (Fin.last n)))))

theorem successorTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (successorTest i).toShared a ↔
      ∃ y ∈ a i, a i = y ∪ {y} := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  simp only [successorTest,DeltaZero.bex_realize,holds_conj,holds_subset,
    DeltaZero.Holds,holds_disj,Fin.snoc_castSucc,Fin.snoc_last]
  constructor
  · rintro ⟨y,hy,hsub,hall⟩
    refine ⟨y,hy,ZFSet.ext fun z => ?_⟩
    simp only [ZFSet.mem_union,ZFSet.mem_singleton]
    exact ⟨fun hz => hall z hz,fun hz => hz.elim (fun h => hsub h) (fun h => h ▸ hy)⟩
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_,?_⟩
    · intro z hz
      rw [he]
      exact ZFSet.mem_union.mpr (Or.inl hz)
    · intro z hz
      rw [he] at hz
      simpa only [ZFSet.mem_union,ZFSet.mem_singleton] using hz

theorem limitTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (limitTest i).toShared a ↔
      a i ≠ ∅ ∧ ∀ y ∈ a i, ∃ z ∈ a i, y ∈ z := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  simp only [limitTest,holds_conj,DeltaZero.neg,DeltaZero.Holds,holds_empty,
    DeltaZero.bex_realize,Fin.snoc_castSucc,Fin.snoc_last]

theorem omegaTest_correct {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (omegaTest i).toShared a ↔ a i = ZFSet.omega := by
  classical
  open Lemmatheca.SetTheory.NaturalNumbersAsSets in
  have hsem :
      universeSatisfies (omegaTest i).toShared a ↔
        (a i).IsOrdinal ∧ (a i ≠ ∅ ∧ ∀ y ∈ a i, ∃ z ∈ a i, y ∈ z) ∧
          ∀ y ∈ a i, y = ∅ ∨ ∃ z ∈ y, y = z ∪ {z} := by
    apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
    have ho {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
        (ordinalTest i).Holds (fun x y => x ∈ y) a ↔ (a i).IsOrdinal :=
      (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
        (ordinalTest_correct i a)
    have hl {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
        (limitTest i).Holds (fun x y => x ∈ y) a ↔
          a i ≠ ∅ ∧ ∀ y ∈ a i, ∃ z ∈ a i, y ∈ z :=
      (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
        (limitTest_correct i a)
    have hs {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
        (successorTest i).Holds (fun x y => x ∈ y) a ↔
          ∃ z ∈ a i, a i = z ∪ {z} :=
      (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
        (successorTest_correct i a)
    simp only [omegaTest,holds_conj,ho,hl,DeltaZero.Holds,holds_disj,holds_empty,hs,Fin.snoc_last]
  rw [hsem]
  constructor
  · rintro ⟨hord,⟨hne,hlim⟩,hmem⟩
    have hsub : a i ⊆ ZFSet.omega := by
      intro y hy
      induction y using ZFSet.inductionOn with
      | _ y ih =>
        rcases hmem y hy with he | ⟨z,hz,he⟩
        · rw [he]; exact ZFSet.omega_zero
        · have hzω := ih z hz (hord.mem_trans hz hy)
          rw [he,← insert_self_eq]
          exact ZFSet.omega_succ hzω
    have hω : ZFSet.IsOrdinal ZFSet.omega.{u} :=
      omega_eq_ordinal ▸ ZFSet.isOrdinal_toZFSet _
    rcases (hord.subset_iff_eq_or_mem hω).mp hsub with he | hfin
    · exact he
    · obtain ⟨z,⟨hz,he⟩,_⟩ := omega_peano.2.2 (a i) hfin hne
      have hzx : z ∈ a i := he ▸ ZFSet.mem_insert z z
      obtain ⟨w,hw,hzw⟩ := hlim z hzx
      rw [← he,ZFSet.mem_insert_iff] at hw
      rcases hw with rfl | hw
      · exact (ZFSet.mem_irrefl _ hzw).elim
      · exact (ZFSet.mem_asymm hzw hw).elim
  · intro he
    rw [he]
    refine ⟨omega_eq_ordinal ▸ ZFSet.isOrdinal_toZFSet _,⟨?_,omega_no_greatest⟩,?_⟩
    · intro h
      exact ZFSet.notMem_empty ∅ (h ▸ ZFSet.omega_zero)
    · intro y hy
      by_cases h0 : y = ∅
      · exact Or.inl h0
      · obtain ⟨z,⟨hz,hzy⟩,_⟩ := omega_peano.2.2 y hy h0
        refine Or.inr ⟨z,hzy ▸ ZFSet.mem_insert z z,?_⟩
        exact hzy.symm.trans (insert_self_eq z)

theorem omega_in_transitive_domain (M : ZFSet.{u}) (hM : M.IsTransitive)
    (a : Fin 1 → M) :
    setSatisfies M (omegaTest (0 : Fin 1)).toShared a ↔ (a 0).val = ZFSet.omega := by
  exact (bounded_to_universe M hM _ a).trans (omegaTest_correct _ _)

end Lemmatheca.SetTheory.ForcingAndGenericFilters
