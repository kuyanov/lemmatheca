import Lemmatheca.ForcingNames.Constructors

namespace Lemmatheca.SetTheory.ForcingNames
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
open Lemmatheca.SetTheory.Absoluteness
open Lemmatheca.SetTheory.AxiomaticSetTheory
open scoped ZFSet
universe u

def emptySentence : membershipLanguage.Sentence :=
  (memScoped (α := Empty) (n := 2) 1 0).not.all.ex

def pairingSentence : membershipLanguage.Sentence :=
  ((memScoped (α := Empty) (n := 4) 3 2).iff
    ((BoundedFormula.equal (.var (.inr 3)) (.var (.inr 0))) ⊔
      (BoundedFormula.equal (.var (.inr 3)) (.var (.inr 1))))).all.ex.all.all

def unionSentence : membershipLanguage.Sentence :=
  ((memScoped (α := Empty) (n := 3) 2 1).iff
    ((memScoped (n := 4) 2 3) ⊓ (memScoped (n := 4) 3 0)).ex).all.ex.all

def successorRelationTest {n} (z y : Fin n) : DeltaZero n :=
  .conj (.mem y z) (.conj (subsetTest y z)
    (.ball z (.disj (.mem (Fin.last n) y.castSucc) (.equal (Fin.last n) y.castSucc))))

def infinitySentence : membershipLanguage.Sentence :=
  (DeltaZero.toShared (DeltaZero.conj
    (.bex (0 : Fin 1) (emptyTest (Fin.last 1)))
    (.ball (0 : Fin 1) (.bex (0 : Fin 2)
      (successorRelationTest (Fin.last 2) (Fin.last 1).castSucc))))).ex

def structuralTheory : membershipLanguage.Theory :=
  {extensionalitySentence,foundationSentence,emptySentence,pairingSentence,unionSentence,infinitySentence}

private theorem scopedMem_realize (D : ZFSet.{u}) {n} (i j : Fin n)
    (v : Empty → D) (a : Fin n → D) :
    let := actualMembershipStructure D
    (memScoped (α := Empty) i j).Realize v a ↔ (a i).val ∈ (a j).val := by rfl

theorem successorRelationTest_correct {n} (z y : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (successorRelationTest z y).toShared a ↔
      a z = a y ∪ {a y} := by
  classical
  rw [show universeSatisfies (successorRelationTest z y).toShared a ↔
    (successorRelationTest z y).Holds (fun x y : ZFSet.{u} => x ∈ y) a from
      DeltaZero.toShared_realize _ _ _]
  simp only [successorRelationTest, subsetTest, DeltaZero.conj, DeltaZero.disj,
    DeltaZero.neg, DeltaZero.Holds, Fin.snoc_last, Fin.snoc_castSucc,
    imp_false, not_not, not_imp]
  constructor
  · rintro ⟨hy, hsub, hall⟩
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_union, ZFSet.mem_singleton]
    constructor
    · intro hw
      by_cases hm : w ∈ a y
      · exact Or.inl hm
      · exact Or.inr (hall w hw hm)
    · intro hw
      exact hw.elim (hsub w) (fun he => he ▸ hy)
  · intro h
    rw [h]
    simp only [ZFSet.mem_union, ZFSet.mem_singleton]
    exact ⟨Or.inr trivial, fun _ hw => Or.inl hw,
      fun _ hw hn => hw.resolve_left hn⟩

theorem emptySentence_realize (D : ZFSet.{u}) (hD : D.IsTransitive) :
    let := actualMembershipStructure D
    D ⊨ emptySentence ↔ (∅ : ZFSet.{u}) ∈ D := by
  dsimp only
  let := actualMembershipStructure D
  have sem : D ⊨ emptySentence ↔ ∃ x : D, ∀ z : D, z.val ∉ x.val := by
    simp only [emptySentence, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_all, BoundedFormula.realize_not,
      scopedMem_realize]
    rfl
  rw [sem]
  constructor
  · rintro ⟨x,hx⟩
    have he : x.val = ∅ := by
      apply (ZFSet.eq_empty _).mpr
      intro z hz
      exact hx ⟨z,hD.mem_trans hz x.property⟩ hz
    exact he ▸ x.property
  · intro h
    exact ⟨⟨∅,h⟩, fun z => ZFSet.notMem_empty z.val⟩

theorem pairingSentence_realize (D : ZFSet.{u}) (hD : D.IsTransitive) :
    let := actualMembershipStructure D
    D ⊨ pairingSentence ↔ ∀ x ∈ D, ∀ y ∈ D, ({x,y} : ZFSet.{u}) ∈ D := by
  dsimp only
  let := actualMembershipStructure D
  have sem : D ⊨ pairingSentence ↔ ∀ x y : D, ∃ p : D,
      ∀ z : D, z.val ∈ p.val ↔ z = x ∨ z = y := by
    simp only [pairingSentence, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_iff,
      BoundedFormula.realize_sup, scopedMem_realize]
    rfl
  rw [sem]
  constructor
  · intro h x hx y hy
    obtain ⟨p,hp⟩ := h ⟨x,hx⟩ ⟨y,hy⟩
    have he : p.val = {x,y} := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_pair]
      constructor
      · intro hz
        simpa only [Subtype.ext_iff] using (hp ⟨z,hD.mem_trans hz p.property⟩).mp hz
      · intro h
        rcases h with hxz | hyz
        · subst z; exact (hp ⟨x,hx⟩).mpr (Or.inl rfl)
        · subst z; exact (hp ⟨y,hy⟩).mpr (Or.inr rfl)
    exact he ▸ p.property
  · intro h x y
    refine ⟨⟨{x.val,y.val},h _ x.property _ y.property⟩,fun z => ?_⟩
    simp only [ZFSet.mem_pair, Subtype.ext_iff]

theorem unionSentence_realize (D : ZFSet.{u}) (hD : D.IsTransitive) :
    let := actualMembershipStructure D
    D ⊨ unionSentence ↔ ∀ x ∈ D, ⋃₀x ∈ D := by
  dsimp only
  let := actualMembershipStructure D
  have sem : D ⊨ unionSentence ↔ ∀ x : D, ∃ z : D,
      ∀ w : D, w.val ∈ z.val ↔ ∃ y : D, w.val ∈ y.val ∧ y.val ∈ x.val := by
    simp only [unionSentence, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_iff,
      BoundedFormula.realize_inf, scopedMem_realize]
    rfl
  rw [sem]
  constructor
  · intro h x hx
    obtain ⟨z,hz⟩ := h ⟨x,hx⟩
    have he : z.val = ⋃₀x := by
      apply ZFSet.ext
      intro w
      rw [ZFSet.mem_sUnion]
      constructor
      · intro hw
        obtain ⟨y,hw',hy⟩ := (hz ⟨w,hD.mem_trans hw z.property⟩).mp hw
        exact ⟨y.val,hy,hw'⟩
      · rintro ⟨y,hy,hw⟩
        have hyD := hD.mem_trans hy hx
        exact (hz ⟨w,hD.mem_trans hw hyD⟩).mpr ⟨⟨y,hyD⟩,hw,hy⟩
    exact he ▸ z.property
  · intro h x
    refine ⟨⟨⋃₀x.val,h _ x.property⟩,fun w => ?_⟩
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y,hy,hw⟩
      exact ⟨⟨y,hD.mem_trans hy x.property⟩,hw,hy⟩
    · rintro ⟨y,hw,hy⟩
      exact ⟨y.val,hy,hw⟩

private theorem holdsConj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (DeltaZero.conj p q).Holds (fun x y : ZFSet.{u} => x ∈ y) a ↔
      p.Holds (fun x y : ZFSet.{u} => x ∈ y) a ∧
      q.Holds (fun x y : ZFSet.{u} => x ∈ y) a := by
  classical
  simp only [DeltaZero.conj, DeltaZero.neg, DeltaZero.Holds, imp_false, not_not, not_imp]

private theorem holdsEmpty {n} (i : Fin n) (a : Fin n → ZFSet.{u}) :
    (emptyTest i).Holds (fun x y : ZFSet.{u} => x ∈ y) a ↔ a i = ∅ :=
  (DeltaZero.toShared_realize _ _ _).symm.trans (emptyTest_correct _ _)

private theorem holdsSucc {n} (z y : Fin n) (a : Fin n → ZFSet.{u}) :
    (successorRelationTest z y).Holds (fun x y : ZFSet.{u} => x ∈ y) a ↔
      a z = a y ∪ {a y} :=
  (DeltaZero.toShared_realize _ _ _).symm.trans (successorRelationTest_correct _ _ _)

private theorem infinityMatrix (a : Fin 1 → ZFSet.{u}) :
    universeSatisfies (DeltaZero.toShared (DeltaZero.conj
      (.bex (0 : Fin 1) (emptyTest (Fin.last 1)))
      (.ball (0 : Fin 1) (.bex (0 : Fin 2)
        (successorRelationTest (Fin.last 2) (Fin.last 1).castSucc))))) a ↔
      IsInductive (a 0) := by
  rw [show universeSatisfies _ a ↔ DeltaZero.Holds (fun x y : ZFSet.{u} => x ∈ y) _ a from
    DeltaZero.toShared_realize _ _ _]
  simp only [holdsConj, DeltaZero.bex_realize, holdsEmpty, DeltaZero.Holds,
    holdsSucc, Fin.snoc_last, Fin.snoc_castSucc]
  change (∃ x, x ∈ a 0 ∧ x = ∅) ∧
    (∀ x, x ∈ a 0 → ∃ y, y ∈ a 0 ∧ y = x ∪ {x}) ↔ _
  have hsucc (x : ZFSet.{u}) : x ∪ {x} = insert x x := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
    exact or_comm
  simp only [hsucc, exists_eq_right, IsInductive]

theorem infinitySentence_realize (D : ZFSet.{u}) (hD : D.IsTransitive) :
    let := actualMembershipStructure D
    D ⊨ infinitySentence ↔ ∃ x ∈ D, IsInductive x := by
  dsimp only
  let := actualMembershipStructure D
  let p : DeltaZero 1 := DeltaZero.conj
    (.bex (0 : Fin 1) (emptyTest (Fin.last 1)))
    (.ball (0 : Fin 1) (.bex (0 : Fin 2)
      (successorRelationTest (Fin.last 2) (Fin.last 1).castSucc)))
  have sem : D ⊨ infinitySentence ↔ ∃ x : D, setSatisfies D p.toShared (Fin.snoc default x) := by
    simp only [infinitySentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex]
    rfl
  rw [sem]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x.val,x.property,?_⟩
    exact (infinityMatrix _).mp ((bounded_to_universe D hD p _).mp hx)
  · rintro ⟨x,hx,hi⟩
    refine ⟨⟨x,hx⟩,(bounded_to_universe D hD p _).mpr ?_⟩
    exact (infinityMatrix _).mpr hi

theorem structural_model (D : ZFSet.{u}) (hD : D.IsTransitive) (h0 : (∅ : ZFSet.{u}) ∈ D)
    (hpair : ∀ x ∈ D, ∀ y ∈ D, ({x,y} : ZFSet.{u}) ∈ D)
    (hunion : ∀ x ∈ D, ⋃₀x ∈ D) (homega : ZFSet.omega.{u} ∈ D) :
    TransitiveSetModel D structuralTheory := by
  refine ⟨?_,hD,?_⟩
  · intro he
    exact ZFSet.notMem_empty ∅ (he ▸ h0)
  · let := actualMembershipStructure D
    have hh := Lemmatheca.SetTheory.MostowskiCollapse.transitive_membership_hypotheses D hD
    refine ⟨?_⟩
    intro p hp
    simp only [structuralTheory, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (extensionality_realize _).mpr hh.2
    · exact (foundation_realize _).mpr (wellFounded_internalFoundation hh.1)
    · exact (emptySentence_realize D hD).mpr h0
    · exact (pairingSentence_realize D hD).mpr hpair
    · exact (unionSentence_realize D hD).mpr hunion
    · exact (infinitySentence_realize D hD).mpr
        ⟨ZFSet.omega,homega,ZFSet.omega_zero,fun _ => ZFSet.omega_succ⟩

theorem extension_structural_model (P R M G t : ZFSet.{u}) (hM : M.IsTransitive)
    (hG : CodedFilter P R G) (htP : t ∈ P) (htG : t ∈ G)
    (h0 : (∅ : ZFSet.{u}) ∈ M) (homega : ZFSet.omega.{u} ∈ M)
    (hcheck : ∀ x ∈ M, checkName t x ∈ M)
    (hpair : ∀ σ ∈ M, ∀ τ ∈ M, pairName t σ τ ∈ M)
    (hunion : ∀ τ ∈ M, IsName P τ → unionName P R τ ∈ M) :
    TransitiveSetModel (extension P M G) structuralTheory := by
  have hg := extension_contains_ground P M G t htP htG hcheck
  exact structural_model _ (extension_transitive P M G hM) (hg h0)
    (extension_pair_closed P M G t htP htG hpair)
    (extension_union_closed P R M G hG hunion) (hg homega)

end Lemmatheca.SetTheory.ForcingNames
