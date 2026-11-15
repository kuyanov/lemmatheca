import Lemmatheca.OrderPatternsAndStability.TypesAndCuts
import Mathlib.ModelTheory.Definability

namespace Lemmatheca.ModelTheory.StableDefinability
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.OrderPatternsAndStability
universe u v w z
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] {n m : ℕ}

/-- Truth of the actual partitioned native formula at the supplied two blocks. -/
abbrev Truth (φ : L.Formula (Fin (n+m))) (a : Fin n → M) (b : Fin m → M) : Prop :=
  φ.Realize (pairAssignment a b)

/-- The complete signed finite test for a positive set of parameter tuples. -/
def IsLocalType (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M)) : Prop :=
  ∀ F : Finset (Fin m → M), ∃ a : Fin n → M,
    ∀ b ∈ F, Truth φ a b ↔ b ∈ P

abbrev LocalType (φ : L.Formula (Fin (n+m))) :=
  {P : Set (Fin m → M) // IsLocalType φ P}

/-- Exactly the existing native parameter instance, with every base point named. -/
abbrev test (φ : L.Formula (Fin (n+m))) (b : Fin m → M) :=
  parameterInstance (Set.univ : Set M) φ b (fun _ => Set.mem_univ _)

/-- Each parameter tuple contributes its prescribed native positive or negative instance. -/
def signedInstance (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (b : Fin m → M) : L[[(Set.univ : Set M)]].Formula (Fin n) := by
  classical
  exact if b ∈ P then test φ b else (test φ b).not

def signedInstances (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M)) :
    Set (L[[(Set.univ : Set M)]].Formula (Fin n)) :=
  Set.range (signedInstance φ P)

/-- Restrict an actual complete type in the full named language to this formula's tests. -/
def localRestriction (φ : L.Formula (Fin (n+m)))
    (q : TypesOver (L := L) (Set.univ : Set M) n) : Set (Fin m → M) :=
  {b | test φ b ∈ Types.formulas q}

variable [Nonempty M]

omit [Nonempty M] in
private theorem test_realize_through {N : Type z} [L.Structure N]
    (φ : L.Formula (Fin (n+m))) (b : Fin m → M) (h : M ↪ₑ[L] N) (a : Fin n → N) :
    @Formula.Realize _ (h.toEmbedding.withConstants (Set.univ : Set M)) _ _
      (test φ b) a ↔ Truth φ a (h ∘ b) :=
  parameterInstance_realize (Set.univ : Set M) φ b (fun _ => Set.mem_univ _) h a

omit [Nonempty M] in
private theorem signed_realize_through {N : Type z} [L.Structure N]
    (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (h : M ↪ₑ[L] N) (a : Fin n → N) (b : Fin m → M) :
    @Formula.Realize _ (h.toEmbedding.withConstants (Set.univ : Set M)) _ _
      (signedInstance φ P b) a ↔ (Truth φ a (h ∘ b) ↔ b ∈ P) := by
  classical
  by_cases hb : b ∈ P
  · simp only [signedInstance,hb,iff_true]
    exact test_realize_through φ b h a
  · simp only [signedInstance,hb,iff_false]
    exact not_congr (test_realize_through φ b h a)

omit [Nonempty M] in
private theorem signed_realize (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : Fin n → M) (b : Fin m → M) :
    (signedInstance φ P b).Realize a ↔ (Truth φ a b ↔ b ∈ P) := by
  exact signed_realize_through φ P (ElementaryEmbedding.refl L M) a b

omit [Nonempty M] in
private theorem complete_not_iff (q : TypesOver (L := L) (Set.univ : Set M) n)
    (ψ : L[[(Set.univ : Set M)]].Formula (Fin n)) :
    ψ.not ∈ Types.formulas q ↔ ψ ∉ Types.formulas q := by
  change Formula.equivSentence ψ.not ∈ q ↔ Formula.equivSentence ψ ∉ q
  rw [Formula.equivSentence_not]
  exact q.not_mem_iff _

private def finiteRequest (s : Finset (L[[(Set.univ : Set M)]].Formula (Fin n))) :
    L[[(Set.univ : Set M)]].Sentence :=
  (Formula.relabel Sum.inr (Formula.iInf (fun γ : s => γ.val))).iExs (Fin n)

omit [Nonempty M] [L.Structure M] in
private theorem finiteRequest_realize {D : Type z} [L[[(Set.univ : Set M)]].Structure D]
    (s : Finset (L[[(Set.univ : Set M)]].Formula (Fin n))) :
    D ⊨ finiteRequest s ↔ ∃ c : Fin n → D, ∀ γ ∈ s, γ.Realize c := by
  simp only [finiteRequest,Sentence.Realize,Formula.realize_iExs,Formula.realize_relabel,
    Function.comp_def,Sum.elim_inr,Formula.realize_iInf,Subtype.forall]

theorem local_iff_signed_finite (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M)) :
    IsLocalType φ P ↔ Types.FinitelyRealized M (signedInstances φ P) := by
  classical
  rcases (inferInstance : Nonempty M) with ⟨_⟩
  constructor
  · intro hP s hs
    let pick (γ : s) : Fin m → M := Classical.choose (hs γ.property)
    have hpick (γ : s) : signedInstance φ P (pick γ) = γ.val :=
      Classical.choose_spec (hs γ.property)
    let F := s.attach.image pick
    obtain ⟨a,ha⟩ := hP F
    refine ⟨a,fun γ hγ => ?_⟩
    let γ' : s := ⟨γ,hγ⟩
    have hm : pick γ' ∈ F := Finset.mem_image.mpr ⟨γ',Finset.mem_attach _ _,rfl⟩
    have ht := (signed_realize φ P a (pick γ')).mpr (ha _ hm)
    rw [hpick γ'] at ht
    exact ht
  · intro hp F
    let s := F.image (signedInstance φ P)
    obtain ⟨a,ha⟩ := hp s (by
      rintro γ hγ
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hγ
      exact ⟨b,rfl⟩)
    refine ⟨a,fun b hb => ?_⟩
    exact (signed_realize φ P a b).mp (ha _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩))

theorem local_iff_signed_partial (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M)) :
    IsLocalType φ P ↔
      Types.IsPartial (L[[(Set.univ : Set M)]].completeTheory M) (signedInstances φ P) := by
  exact (local_iff_signed_finite φ P).trans
    (Types.partial_iff_finitelyRealized_completeTheory (signedInstances φ P)).symm

theorem restriction_local (φ : L.Formula (Fin (n+m)))
    (q : TypesOver (L := L) (Set.univ : Set M) n) :
    IsLocalType φ (localRestriction φ q) := by
  classical
  have hsign : signedInstances φ (localRestriction φ q) ⊆ Types.formulas q := by
    rintro γ ⟨b,rfl⟩
    by_cases hb : test φ b ∈ Types.formulas q
    · simp [signedInstance,localRestriction,hb]
    · have hn := (complete_not_iff q (test φ b)).mpr hb
      simpa [signedInstance,localRestriction,hb] using hn
  apply (local_iff_signed_finite φ _).mpr
  have hf := (Types.partial_iff_finitelyRealized_completeTheory (Types.formulas q)).mp
    (Types.partial_formulas q)
  intro s hs
  exact hf s (hs.trans hsign)

theorem exists_complete_restriction (φ : L.Formula (Fin (n+m)))
    (P : Set (Fin m → M)) (hP : IsLocalType φ P) :
    ∃ q : TypesOver (L := L) (Set.univ : Set M) n,
      signedInstances φ P ⊆ Types.formulas q ∧ localRestriction φ q = P := by
  classical
  obtain ⟨q,hq⟩ := Types.exists_complete_extension (signedInstances φ P)
    ((local_iff_signed_partial φ P).mp hP)
  refine ⟨q,hq,?_⟩
  ext b
  change test φ b ∈ Types.formulas q ↔ b ∈ P
  have hs : signedInstance φ P b ∈ signedInstances φ P := ⟨b,rfl⟩
  by_cases hb : b ∈ P
  · have hp : test φ b ∈ Types.formulas q := by
      simpa only [signedInstance,ite_eq_left hb] using hq hs
    exact iff_of_true hp hb
  · have hn : (test φ b).not ∈ Types.formulas q := by
      simpa only [signedInstance,ite_eq_right hb] using hq hs
    exact iff_of_false ((complete_not_iff q _).mp hn) hb

theorem local_iff_elementary_realization (φ : L.Formula (Fin (n+m)))
    (P : Set (Fin m → M)) :
    IsLocalType φ P ↔
      ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N),
        ∃ (h : M ↪ₑ[L] N) (a : Fin n → N),
          ∀ b : Fin m → M, Truth φ a (h ∘ b) ↔ b ∈ P := by
  constructor
  · intro hp
    obtain ⟨N,SN,hN,h,a,ha⟩ :=
      (Types.parameter_realization (Set.univ : Set M) (signedInstances φ P)).mp
        ((local_iff_signed_finite φ P).mp hp)
    let := SN
    let := hN
    exact ⟨N,SN,hN,h,a,fun b => (signed_realize_through φ P h a b).mp (ha _ ⟨b,rfl⟩)⟩
  · rintro ⟨N,SN,hN,h,a,ha⟩
    let := SN
    let := hN
    apply (local_iff_signed_finite φ P).mpr
    apply (Types.parameter_realization (Set.univ : Set M) (signedInstances φ P)).mpr
    refine ⟨N,SN,hN,h,a,?_⟩
    rintro γ ⟨b,rfl⟩
    exact (signed_realize_through φ P h a b).mpr (ha b)

theorem realized_local {N : Type z} [L.Structure N] [Nonempty N]
    (φ : L.Formula (Fin (n+m))) (h : M ↪ₑ[L] N) (a : Fin n → N) :
    IsLocalType φ {b | Truth φ a (h ∘ b)} := by
  classical
  rcases (inferInstance : Nonempty M) with ⟨_⟩
  rcases (inferInstance : Nonempty N) with ⟨_⟩
  let P : Set (Fin m → M) := {b | Truth φ a (h ∘ b)}
  intro F
  let s := F.image (signedInstance φ P)
  let : L[[(Set.univ : Set M)]].Structure N :=
    inferInstanceAs (L[[(Set.univ : Set M)]].Structure (h.toEmbedding.withConstants (Set.univ : Set M)))
  have hn : N ⊨ finiteRequest s := (finiteRequest_realize s).mpr ⟨a,by
    intro γ hγ
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hγ
    exact (signed_realize_through φ P h a b).mpr Iff.rfl⟩
  have hm : M ⊨ finiteRequest s :=
    ((h.liftWithConstants (Set.univ : Set M)).map_sentence (finiteRequest s)).mpr hn
  obtain ⟨c,hc⟩ := (finiteRequest_realize s).mp hm
  refine ⟨c,fun b hb => ?_⟩
  exact (signed_realize φ P c b).mp (hc _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩))

theorem finite_local_realization [Finite M] (φ : L.Formula (Fin (n+m)))
    (P : Set (Fin m → M)) (hP : IsLocalType φ P) :
    ∃ a : Fin n → M, ∀ b : Fin m → M, Truth φ a b ↔ b ∈ P := by
  classical
  rcases (inferInstance : Nonempty M) with ⟨_⟩
  let : Fintype (Fin m → M) := Fintype.ofFinite _
  obtain ⟨a,ha⟩ := hP Finset.univ
  exact ⟨a,fun b => ha b (Finset.mem_univ _)⟩

end
end Lemmatheca.ModelTheory.StableDefinability
