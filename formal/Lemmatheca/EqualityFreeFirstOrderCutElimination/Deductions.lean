import Lemmatheca.EqualityFreeFirstOrderCutElimination.Cut
import Lemmatheca.EqualityFreeFirstOrderSignedFormulaDeductions.Public
import Lemmatheca.IntuitionisticFirstOrderDeduction.EqualityErasure

/-! Actual-tree correspondence with the equality-disabled classical native
calculus. Native endpoints are pure; purification handles intermediates. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.CutDeductions
open _root_.FirstOrder _root_.FirstOrder.Language

universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section
local instance cutNativeFormulaEq {δ : Type w} :
    DecidableEq (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L δ) := Classical.decEq _

/-- Negative normalizations of all the supplied equality-free allowed formulas. -/
def negativeContext (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ) : Sequent L α :=
  Γ.attach.image (fun G => Nnf.normalize G.val (hΓ G.val G.property) false)

/-- The actual signed encoding of a finite native deduction endsequent. -/
def encodeNative (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α) (hF : F.EqualityFree) : Sequent L α :=
  insert (Nnf.normalize F hF true) (negativeContext Γ hΓ)

/-- Negative full readings used by the native refutation interpretation. -/
def negativeReadings (Ξ : Sequent L α) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α :=
  Ξ.image (fun A => .neg A.read)

open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Derivation)

private theorem back_normalize_rename
    (F : Lemmatheca.ProofTheory.FirstOrder.Formula L α) (hF : F.EqualityFree)
    (f : α → β) (hF' : (F.rename f).EqualityFree) (b : Bool) :
    Nnf.normalize (F.rename f) hF' b = (Nnf.normalize F hF b).rename f := by
  exact Nnf.normalize_map F hF _ b

private theorem back_negativeContext_rename
    (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α)
    (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (f : α → β)
    (hΓ' : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure
      (Γ.image (fun G => G.rename f))) :
    negativeContext (Γ.image (fun G => G.rename f)) hΓ' =
      renameContext (negativeContext Γ hΓ) f := by
  classical
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨⟨G, hGmem⟩, _, hG⟩
    rcases Finset.mem_image.mp hGmem with ⟨F, hF, hFG⟩
    subst G
    refine Finset.mem_image.mpr ⟨Nnf.normalize F (hΓ F hF) false, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨F, hF⟩, Finset.mem_attach _ _, rfl⟩
    · have hFp : (F.rename f).EqualityFree :=
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 (hΓ F hF)
      exact (back_normalize_rename F (hΓ F hF) f hFp false).symm.trans hG
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨B, hB, hBA⟩
    rcases Finset.mem_image.mp hB with ⟨F, _, hF⟩
    let G : {G // G ∈ Γ.image (fun G => G.rename f)} :=
      ⟨F.val.rename f, Finset.mem_image.mpr ⟨F.val, F.property, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨G, Finset.mem_attach _ _, ?_⟩
    rw [back_normalize_rename F.val (hΓ F.val F.property) f]
    exact (congrArg (fun C => C.rename f) hF).trans hBA

private theorem back_pure_rename
    {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}
    (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (f : α → β) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure
      (Γ.image (fun G => G.rename f)) := by
  intro G hG
  rcases Finset.mem_image.mp hG with ⟨F, hF, rfl⟩
  exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 (hΓ F hF)

private def back_readingAt {Ξ : Sequent L α} {A : Nnf L α 0} (hA : A ∈ Ξ) :
    Derivation true false L (negativeReadings Ξ) (.neg A.read) :=
  .assumption (Finset.mem_image.mpr ⟨A, hA, rfl⟩)

private def back_replaceReadings {Ξ : Sequent L α}
    {Δ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}
    {F : Lemmatheca.ProofTheory.FirstOrder.Formula L α}
    (p : Derivation true false L (negativeReadings Ξ) F)
    (supply : ∀ A ∈ Ξ, Derivation true false L Δ (.neg A.read)) :
    Derivation true false L Δ F := by
  classical
  apply p.replace
  intro C hC
  have hx := Finset.mem_image.mp hC
  let A := Classical.choose hx
  have hA := Classical.choose_spec hx
  exact hA.2 ▸ supply A hA.1

private def back_offer {Ξ : Sequent L α} (A : Nnf L α 0)
    {Δ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}
    (p : Derivation true false L (negativeReadings (insert A Ξ)) .falsum)
    (supply : ∀ B ∈ Ξ, Derivation true false L Δ (.neg B.read)) :
    Derivation true false L Δ A.read := by
  classical
  apply Derivation.classicalContradiction rfl
  apply back_replaceReadings p
  intro B hB
  by_cases he : B = A
  · subst B
    exact .assumption (Finset.mem_insert_self _ _)
  · exact (supply B ((Finset.mem_insert.mp hB).resolve_left he)).weaken
      (Finset.subset_insert _ _)

private def back_liftSupply {Ξ : Sequent L α}
    {Δ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}
    (supply : ∀ A ∈ Ξ, Derivation true false L Δ (.neg A.read)) :
    ∀ B ∈ liftContext Ξ,
      Derivation true false L
        (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Δ) (.neg B.read) := by
  classical
  intro B hB
  have hx := Finset.mem_image.mp hB
  let A := Classical.choose hx
  have hA := Classical.choose_spec hx
  have hp := (supply A hA.1).rename (Sum.inl : α → α ⊕ Fin 1)
  rw [← hA.2]
  simpa only [Nnf.read_rename,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg, A] using hp

/-- Both sides use exactly the same renaming, independently of purity proofs. -/
theorem encodeNative_rename (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α) (hF : F.EqualityFree) (f : α → β)
    (hΓ' : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure (Γ.image (fun G => G.rename f)))
    (hF' : (F.rename f).EqualityFree) :
    encodeNative (Γ.image (fun G => G.rename f)) hΓ' (F.rename f) hF' =
      renameContext (encodeNative Γ hΓ F hF) f := by
  classical
  unfold encodeNative
  rw [back_negativeContext_rename Γ hΓ f hΓ']
  unfold renameContext
  rw [Finset.image_insert, back_normalize_rename F hF f hF' true]

open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Context ContextPure)

local instance forward_nativeEq {δ : Type w} :
    DecidableEq (Lemmatheca.ProofTheory.FirstOrder.Formula L δ) := Classical.decEq _

private theorem forward_mem_negative (Γ : Context L α) (hΓ : ContextPure Γ)
    (A : Nnf L α 0) : A ∈ negativeContext Γ hΓ ↔
      ∃ (F : Lemmatheca.ProofTheory.FirstOrder.Formula L α) (hF : F ∈ Γ),
        Nnf.normalize F (hΓ F hF) false = A := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨F, _, rfl⟩
    exact ⟨F.val, F.property, rfl⟩
  · rintro ⟨F,hF,rfl⟩
    exact Finset.mem_image.mpr ⟨⟨F,hF⟩, Finset.mem_attach _ _, rfl⟩

private theorem forward_negative_insert (Γ : Context L α) (hΓ : ContextPure Γ)
    (F : Lemmatheca.ProofTheory.FirstOrder.Formula L α) (hF : F.EqualityFree)
    (hΓF : ContextPure (insert F Γ)) :
    negativeContext (insert F Γ) hΓF =
      insert (Nnf.normalize F hF false) (negativeContext Γ hΓ) := by
  ext A
  simp only [forward_mem_negative, Finset.mem_insert]
  constructor
  · rintro ⟨G,hG,hA⟩
    rcases hG with rfl | hG
    · exact Or.inl hA.symm
    · exact Or.inr ⟨G,hG,hA⟩
  · rintro (rfl | ⟨G,hG,hA⟩)
    · exact ⟨F, Or.inl rfl, rfl⟩
    · exact ⟨G, Or.inr hG, hA⟩

private theorem forward_normalize_rename {n} (F : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α n)
    (hF : F.EqualityFree) (f : α → β) (hF' : (F.rename f).EqualityFree) (b : Bool) :
    Nnf.normalize (F.rename f) hF' b = (Nnf.normalize F hF b).rename f := by
  exact Nnf.normalize_map F hF _ b

private theorem forward_normalize_open {n} (F : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α n)
    (hF : F.EqualityFree) (hF' : F.toFormula.EqualityFree) (b : Bool) :
    Nnf.normalize F.toFormula hF' b = (Nnf.normalize F hF b).toFormula := by
  exact Nnf.normalize_map F hF _ b

private theorem forward_normalize_instance (F : Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α 1)
    (hF : F.EqualityFree) (t : L.Term α) (hF' : (F.instantiate t).EqualityFree) (b : Bool) :
    Nnf.normalize (F.instantiate t) hF' b = (Nnf.normalize F hF b).instantiate t := by
  exact Nnf.normalize_map F hF _ b

private theorem forward_negative_rename (Γ : Context L α) (hΓ : ContextPure Γ)
    (f : α → β) (hΓ' : ContextPure (Γ.image (fun G => G.rename f))) :
    negativeContext (Γ.image (fun G => G.rename f)) hΓ' =
      renameContext (negativeContext Γ hΓ) f := by
  ext A
  constructor
  · intro h
    rcases (forward_mem_negative _ _ _).mp h with ⟨G,hG,hA⟩
    rcases Finset.mem_image.mp hG with ⟨F,hF,rfl⟩
    rw [forward_normalize_rename F (hΓ F hF)] at hA
    exact Finset.mem_image.mpr ⟨_, (forward_mem_negative _ _ _).mpr ⟨F,hF,rfl⟩, hA⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨B,hB,rfl⟩
    rcases (forward_mem_negative _ _ _).mp hB with ⟨F,hF,rfl⟩
    apply (forward_mem_negative _ _ _).mpr
    refine ⟨F.rename f, Finset.mem_image.mpr ⟨F,hF,rfl⟩, ?_⟩
    exact forward_normalize_rename F (hΓ F hF) f _ false

private theorem forward_negative_lift (Γ : Context L α) (hΓ : ContextPure Γ)
    (hΓ' : ContextPure (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ)) :
    negativeContext (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) hΓ' =
      liftContext (negativeContext Γ hΓ) := by
  exact forward_negative_rename Γ hΓ Sum.inl hΓ'

private def forward_identity (A : Nnf L α 0) (Ξ : Sequent L α)
    (hA : A ∈ Ξ) (hD : A.dual ∈ Ξ) : CutProof L Ξ :=
  (CutProof.ofCore (CoreProof.compoundIdentity A Ξ)).weaken (by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hA
    · rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hD
      · exact hB)

private def forward_cut (A : Nnf L α 0) {Ξ : Sequent L α}
    (p : CutProof L (insert A Ξ)) (q : CutProof L (insert A.dual Ξ)) : CutProof L Ξ := by
  simpa only [Finset.union_self] using CutProof.cut A p q

private def forward_switch {Ξ : Sequent L α} {A B : Nnf L α 0}
    (p : CutProof L (insert A (insert B Ξ))) : CutProof L (insert B (insert A Ξ)) :=
  (Finset.insert_comm A B Ξ) ▸ p

private def forward_remove_bot {Ξ : Sequent L α} (p : CutProof L (insert .bot Ξ)) :
    CutProof L Ξ := forward_cut .bot p (.truth (Finset.mem_insert_self _ _))

private theorem forward_lift_insert (Ξ : Sequent L α) (A : Nnf L α 0) :
    liftContext (insert A Ξ) = insert (A.rename Sum.inl) (liftContext Ξ) := by
  simp only [liftContext, renameContext, Finset.image_insert]

private theorem forward_pure_context {Γ : Context L α}
    {F : Lemmatheca.ProofTheory.FirstOrder.Formula L α}
    (p : Derivation true false L Γ F) (hp : p.Pure) : ContextPure Γ := by
  cases p <;> exact hp.1

private theorem forward_pure_formula {Γ : Context L α}
    {F : Lemmatheca.ProofTheory.FirstOrder.Formula L α}
    (p : Derivation true false L Γ F) (hp : p.Pure) : F.EqualityFree := by
  cases p <;> exact hp.2.1

set_option maxHeartbeats 1200000 in
private def forward_fromPureNative {Γ : Context L α}
    {F : Lemmatheca.ProofTheory.FirstOrder.Formula L α}
    (p : Derivation true false L Γ F) :
    (hp : p.Pure) → CutProof L (encodeNative Γ (forward_pure_context p hp) F (forward_pure_formula p hp)) := by
  induction p with
  | assumption hA =>
      intro hp
      let A := Nnf.normalize _ hp.2.1 true
      apply forward_identity A _
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        have hm := (forward_mem_negative _ hp.1 _).mpr ⟨_,hA,rfl⟩
        simpa only [Nnf.normalize_dual] using hm
  | conjIntro _ _ ihP ihQ =>
      intro hp
      exact .andIntro (ihP hp.2.2.1) (ihQ hp.2.2.2)
  | @conjElimLeft α Γ A B p ih =>
      intro hp
      let a := Nnf.normalize A hp.2.1 true
      let b := Nnf.normalize B (forward_pure_formula p hp.2.2).2 true
      let Ξ := encodeNative Γ hp.1 A hp.2.1
      have pp : CutProof L (insert (.and a b) Ξ) :=
        (ih hp.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      apply forward_cut (.and a b) pp
      apply CutProof.orIntro
      exact forward_identity a _ (by simp [Ξ, encodeNative, a]) (by simp)
  | @conjElimRight α Γ A B p ih =>
      intro hp
      let a := Nnf.normalize A (forward_pure_formula p hp.2.2).1 true
      let b := Nnf.normalize B hp.2.1 true
      let Ξ := encodeNative Γ hp.1 B hp.2.1
      have pp : CutProof L (insert (.and a b) Ξ) :=
        (ih hp.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      apply forward_cut (.and a b) pp
      apply CutProof.orIntro
      exact forward_identity b _ (by simp [Ξ, encodeNative, b]) (by simp)
  | @disjIntroLeft α Γ A B p ih =>
      intro hp
      apply CutProof.orIntro
      exact (ih hp.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  | @disjIntroRight α Γ A B p ih =>
      intro hp
      apply CutProof.orIntro
      exact (ih hp.2.2).weaken (Finset.subset_insert _ _)
  | @disjElim α Γ A B C p q r ihP ihQ ihR =>
      intro hp
      let a := Nnf.normalize A (forward_pure_formula p hp.2.2.1).1 true
      let b := Nnf.normalize B (forward_pure_formula p hp.2.2.1).2 true
      let Ξ := encodeNative Γ hp.1 C hp.2.1
      have pp : CutProof L (insert (.or a b) Ξ) :=
        (ihP hp.2.2.1).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have pq : CutProof L (insert a.dual Ξ) := by
        have z := ihQ hp.2.2.2.1
        rw [encodeNative, forward_negative_insert _ hp.1 A (forward_pure_formula p hp.2.2.1).1,
          Nnf.normalize_dual] at z
        exact forward_switch z
      have pr : CutProof L (insert b.dual Ξ) := by
        have z := ihR hp.2.2.2.2
        rw [encodeNative, forward_negative_insert _ hp.1 B (forward_pure_formula p hp.2.2.1).2,
          Nnf.normalize_dual] at z
        exact forward_switch z
      exact forward_cut (.or a b) pp (.andIntro pq pr)
  | @impIntro α Γ A B p ih =>
      intro hp
      apply CutProof.orIntro
      have z := ih hp.2.2
      rw [encodeNative, forward_negative_insert _ hp.1 A hp.2.1.1] at z
      exact forward_switch z
  | @impElim α Γ A B p q ihP ihQ =>
      intro hp
      let a := Nnf.normalize A (forward_pure_formula q hp.2.2.2) true
      let b := Nnf.normalize B hp.2.1 true
      let Ξ := encodeNative Γ hp.1 B hp.2.1
      have pp0 : CutProof L (insert (.or a.dual b) (negativeContext Γ hp.1)) := by
        simpa only [encodeNative, Nnf.normalize, Nnf.normalize_dual] using ihP hp.2.2.1
      have pp : CutProof L (insert (.or a.dual b) Ξ) :=
        pp0.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have pq : CutProof L (insert a Ξ) :=
        (ihQ hp.2.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have pr : CutProof L (insert b.dual Ξ) :=
        forward_identity b _ (by simp [Ξ, encodeNative, b]) (by simp)
      apply forward_cut (.or a.dual b) pp
      simpa only [Nnf.dual, Nnf.dual_dual] using CutProof.andIntro pq pr
  | @negIntro α Γ A p ih =>
      intro hp
      apply forward_remove_bot
      simpa only [encodeNative, forward_negative_insert _ hp.1 A hp.2.1,
        Nnf.normalize, Bool.not_true, Bool.not_false] using ih hp.2.2
  | @negElim α Γ A p q ihP ihQ =>
      intro hp
      rcases hp with ⟨hΓ,hF,hP,hQ⟩
      apply CutProof.botIntro
      have pp := ihP hP
      have pq := ihQ hQ
      change CutProof L (insert (Nnf.normalize A (forward_pure_formula p hP) false) (negativeContext Γ hΓ)) at pq
      rw [Nnf.normalize_dual] at pq
      exact forward_cut (Nnf.normalize A (forward_pure_formula p hP) true) pp pq
  | falsumElim _ ih =>
      intro hp
      exact (forward_remove_bot (ih hp.2.2)).weaken (Finset.subset_insert _ _)
  | @classicalContradiction α Γ A _ p ih =>
      intro hp
      apply forward_remove_bot
      simpa only [encodeNative, forward_negative_insert _ hp.1 (.neg A) hp.2.1,
        Nnf.normalize, Bool.not_true, Bool.not_false] using ih hp.2.2
  | @allElim α Γ B t p ih =>
      intro hp
      let b := Nnf.normalize B (forward_pure_formula p hp.2.2) true
      let a := b.instantiate t
      let Ξ := encodeNative Γ hp.1 (B.instantiate t) hp.2.1
      have pp : CutProof L (insert (.all b) Ξ) :=
        (ih hp.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have ha : a ∈ Ξ := by
        change a ∈ insert (Nnf.normalize (B.instantiate t) hp.2.1 true) _
        rw [forward_normalize_instance B (forward_pure_formula p hp.2.2) t hp.2.1 true]
        exact Finset.mem_insert_self _ _
      have pq : CutProof L (insert a.dual Ξ) :=
        forward_identity a _ (Finset.mem_insert_of_mem ha) (Finset.mem_insert_self _ _)
      apply forward_cut (.all b) pp
      apply CutProof.exIntro b.dual t
      change CutProof L (insert (b.dual.map _) Ξ)
      rw [← Nnf.map_dual]
      exact pq
  | @exIntro α Γ B t p ih =>
      intro hp
      apply CutProof.exIntro (Nnf.normalize B hp.2.1 true) t
      simpa only [encodeNative, forward_normalize_instance B hp.2.1 t] using ih hp.2.2
  | @allIntro α Γ B p ih =>
      intro hp
      apply CutProof.allIntro (Nnf.normalize B hp.2.1 true)
      simpa only [encodeNative, forward_normalize_open B hp.2.1,
        forward_negative_lift Γ hp.1] using ih hp.2.2
  | @exElim α Γ C B p q ihP ihQ =>
      intro hp
      rcases hp with ⟨hΓ,hC,hP,hQ⟩
      have hB : B.EqualityFree := forward_pure_formula p hP
      let b := Nnf.normalize B hB true
      let Ξ := encodeNative Γ hΓ C hC
      have pp : CutProof L (insert (.ex b) Ξ) :=
        (ihP hP).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have hLift : ContextPure (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) :=
        fun G hG => forward_pure_context q hQ G (Finset.mem_insert_of_mem hG)
      have pq : CutProof L (insert b.dual.toFormula (liftContext Ξ)) := by
        have z := ihQ hQ
        rw [encodeNative,
          forward_negative_insert _ hLift B.toFormula (forward_pure_context q hQ _ (Finset.mem_insert_self _ _)),
          forward_negative_lift Γ hΓ,
          forward_normalize_open B hB,
          forward_normalize_rename C hC,
          Nnf.normalize_dual] at z
        change CutProof L (insert b.dual.toFormula (liftContext (insert (Nnf.normalize C hC true) (negativeContext Γ hΓ))))
        rw [forward_lift_insert]
        exact forward_switch z
      exact forward_cut (.ex b) pp (.allIntro b.dual pq)
  | equalIntro _ h => cases h
  | equalElim _ _ _ h _ _ _ _ => cases h


/-- Every native constructor is interpreted into the actual cutful family. -/
def fromNativeCutful {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L Γ F) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (hF : F.EqualityFree) : CutProof L (encodeNative Γ hΓ F hF) := by
  let q := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.purify p hΓ hF
  exact forward_fromPureNative q.val q.property

/-- Refute the negated readings by a finite equality-disabled native tree. -/
def toNativeRefutation {Ξ : Sequent L α} (p : CoreProof L Ξ) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L (negativeReadings Ξ) .falsum := by
  classical
  induction p with
  | identity R ts hp hn => exact .negElim (back_readingAt hp) (back_readingAt hn)
  | truth htop =>
    exact .negElim (.negIntro (.assumption (Finset.mem_insert_self _ _)))
      (back_readingAt htop)
  | @andIntro α Γ A B p q ihp ihq =>
    let supply : ∀ C ∈ Γ, Derivation true false L
        (negativeReadings (insert (.and A B) Γ)) (.neg C.read) :=
      fun C hC => back_readingAt (Finset.mem_insert_of_mem hC)
    exact .negElim (.conjIntro (back_offer A ihp supply) (back_offer B ihq supply))
      (back_readingAt (Finset.mem_insert_self _ _))
  | @orIntro α Γ A B p ih =>
    have hAB := (SignedDeductions.Bridge.negDisj A.read B.read).forward
      (back_readingAt (Ξ := insert (.or A B) Γ) (Finset.mem_insert_self _ _))
    apply back_replaceReadings ih
    intro C hC
    by_cases hCA : C = A
    · subst C
      exact .conjElimLeft hAB
    by_cases hCB : C = B
    · subst C
      exact .conjElimRight hAB
    exact back_readingAt (Finset.mem_insert_of_mem
      ((Finset.mem_insert.mp ((Finset.mem_insert.mp hC).resolve_left hCA)).resolve_left hCB))
  | botIntro p ih =>
    exact back_replaceReadings ih (fun C hC => back_readingAt (Finset.mem_insert_of_mem hC))
  | @allIntro α Γ B p ih =>
    let supply : ∀ C ∈ Γ, Derivation true false L
        (negativeReadings (insert (.all B) Γ)) (.neg C.read) :=
      fun C hC => back_readingAt (Finset.mem_insert_of_mem hC)
    have hOpen := back_offer B.toFormula ih (back_liftSupply supply)
    have hAll : Derivation true false L (negativeReadings (insert (.all B) Γ))
        (.all B.read) := .allIntro (by simpa only [Nnf.read_toFormula] using hOpen)
    exact .negElim hAll (back_readingAt (Finset.mem_insert_self _ _))
  | @exIntro α Γ B t p ih =>
    have hAllNeg := (SignedDeductions.Bridge.negEx B.read).forward
      (back_readingAt (Ξ := insert (.ex B) Γ) (Finset.mem_insert_self _ _))
    have hInst : Derivation true false L (negativeReadings (insert (.ex B) Γ))
        (.neg (B.instantiate t).read) := by
      simpa only [Nnf.read_instantiate,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map] using
        (Derivation.allElim t hAllNeg)
    apply back_replaceReadings ih
    intro C hC
    by_cases he : C = B.instantiate t
    · subst C
      exact hInst
    · exact back_readingAt (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hC).resolve_left he))

/-- Native-to-cut-free transformation, after purification and cut elimination. -/
def fromNative {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L Γ F) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (hF : F.EqualityFree) : CoreProof L (encodeNative Γ hΓ F hF) := by
  exact (fromNativeCutful p hΓ hF).eliminate

/-- Refutation replacement and the actual backward signed converters give F. -/
def toNative {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α}
    (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ) (hF : F.EqualityFree)
    (p : CoreProof L (encodeNative Γ hΓ F hF)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L Γ F := by
  classical
  apply Derivation.classicalContradiction rfl
  apply back_replaceReadings (toNativeRefutation p)
  intro A hA
  by_cases he : A = Nnf.normalize F hF true
  · subst A
    apply Derivation.negIntro
    have hPos : Derivation true false L
        (insert (Nnf.normalize F hF true).read (insert (.neg F) Γ))
        (Nnf.normalize F hF true).read := .assumption (Finset.mem_insert_self _ _)
    exact .negElim (SignedDeductions.Raw.fromPositive F hF hPos)
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  · have hNeg := (Finset.mem_insert.mp hA).resolve_left he
    have hx := Finset.mem_image.mp hNeg
    let G := Classical.choose hx
    have hG := Classical.choose_spec hx
    have hEq : Nnf.normalize G.val (hΓ G.val G.property) false = A := hG.2
    rw [← hEq]
    apply Derivation.negIntro
    have hNegG : Derivation true false L
        (insert (Nnf.normalize G.val (hΓ G.val G.property) false).read (insert (.neg F) Γ))
        (Nnf.normalize G.val (hΓ G.val G.property) false).read :=
      .assumption (Finset.mem_insert_self _ _)
    exact .negElim (.assumption (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem G.property)))
      (SignedDeductions.Raw.fromNegative G.val (hΓ G.val G.property) hNegG)

/-- Public forward operation keeps the same countable reserve. -/
def fromNativePublic {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true false L Γ F) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (hF : F.EqualityFree) : Proof (encodeNative Γ hΓ F hF) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p
  change CoreProof L (renameContext (encodeNative Γ hΓ F hF) Sum.inl)
  let hΓ' := back_pure_rename hΓ (Sum.inl : α → α ⊕ ℕ)
  have hF' : (F.rename (Sum.inl : α → α ⊕ ℕ)).EqualityFree :=
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 hF
  have q := fromNative p hΓ' hF'
  rw [encodeNative_rename Γ hΓ F hF (Sum.inl : α → α ⊕ ℕ) hΓ' hF'] at q
  exact q

def toNativePublic {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α}
    (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ) (hF : F.EqualityFree)
    (p : Proof (encodeNative Γ hΓ F hF)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true false L Γ F := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof
  let hΓ' := back_pure_rename hΓ (Sum.inl : α → α ⊕ ℕ)
  have hF' : (F.rename (Sum.inl : α → α ⊕ ℕ)).EqualityFree :=
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 hF
  apply toNative hΓ' hF'
  rw [encodeNative_rename Γ hΓ F hF (Sum.inl : α → α ⊕ ℕ) hΓ' hF']
  exact p

theorem raw_native_iff (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α) (hF : F.EqualityFree) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L Γ F) ↔
      Nonempty (CoreProof L (encodeNative Γ hΓ F hF)) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨fromNative p hΓ hF⟩
  · rintro ⟨p⟩
    exact ⟨toNative hΓ hF p⟩

theorem public_native_iff (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) (hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure Γ)
    (F : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Formula L α) (hF : F.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true false L Γ F ↔ Derives (encodeNative Γ hΓ F hF) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨fromNativePublic p hΓ hF⟩
  · rintro ⟨p⟩
    exact ⟨toNativePublic hΓ hF p⟩

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.CutDeductions
