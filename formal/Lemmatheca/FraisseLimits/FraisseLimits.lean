import Lemmatheca.AgesAndAmalgamation.AgesAndAmalgamation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Basic.Finite.Sigma

/-! Finite amalgamation batches and the construction of countable Fraïssé limits. -/

namespace Lemmatheca.ModelTheory.FraisseLimits

open FirstOrder FirstOrder.Language CategoryTheory
open scoped FirstOrder
open Structure

universe u v w

variable {L : Language.{u, v}} {K : Set (Bundled.{w} L.Structure)}

/-- Every finite extension can be placed while preserving the supplied common-part map. -/
def ExtensionProperty (K : Set (Bundled.{w} L.Structure)) (M : Type w)
    [L.Structure M] : Prop :=
  ∀ (A B : Bundled.{w} L.Structure), A ∈ K → B ∈ K →
    ∀ (f : A ↪[L] M) (g : A ↪[L] B), ∃ h : B ↪[L] M, h.comp g = f

/-- In a finite relational language, the library's countability/FG conditions are automatic. -/
theorem isFraisse_iff [L.IsRelational] [Finite (Σ n, L.Relations n)]
    (hfinite : ∀ A ∈ K, Finite A) :
    IsFraisse K ↔ K.Nonempty ∧ AgesAndAmalgamation.IsoClosed K ∧
      Hereditary K ∧ JointEmbedding K ∧ Amalgamation K := by
  constructor
  · intro hK
    have : IsFraisse K := hK
    exact ⟨hK.is_nonempty, fun A B h => IsFraisse.is_equiv_invariant h,
      hK.hereditary, hK.jointEmbedding, hK.amalgamation⟩
  · rintro ⟨hne, _, hp, hj, ha⟩
    exact ⟨hne, fun A hA => Structure.fg_iff_finite.mpr (hfinite A hA),
      AgesAndAmalgamation.countable_finite_isomorphism_types K hfinite, hp, hj, ha⟩

/-- Representatives can be repeated to give one natural-number list. -/
theorem exists_representatives (hK : IsFraisse K) :
    ∃ A : ℕ → Bundled.{w} L.Structure,
      (∀ n, A n ∈ K) ∧ ∀ B ∈ K, ∃ n, Nonempty (B ≃[L] A n) := by
  classical
  obtain ⟨F, hF⟩ := hK.is_essentially_countable.exists_eq_range (hK.is_nonempty.image _)
  refine ⟨fun n => (F n).out, ?_, ?_⟩
  · intro n
    have hmem : F n ∈ Quotient.mk' '' K := by rw [hF]; exact Set.mem_range_self n
    obtain ⟨B, hB, heq⟩ := hmem
    have hiso : Nonempty ((F n).out ≃[L] B) :=
      Quotient.exact ((Quotient.out_eq _).trans heq.symm)
    exact (hK.hereditary.is_equiv_invariant_of_fg hK.FG _ _ hiso).mpr hB
  · intro B hB
    have hmem : Quotient.mk' B ∈ Set.range F := by rw [← hF]; exact ⟨B, hB, rfl⟩
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, Quotient.exact (hn.symm.trans (Quotient.out_eq _).symm)⟩

/-- Simultaneously complete a finite family, preserving the specified old embedding. -/
theorem finite_amalgamation {ι : Type*} [Finite ι] (hAP : Amalgamation K)
    (B : Bundled.{w} L.Structure) (hB : B ∈ K)
    (C D : ι → Bundled.{w} L.Structure) (hC : ∀ i, C i ∈ K) (hD : ∀ i, D i ∈ K)
    (f : ∀ i, C i ↪[L] B) (g : ∀ i, C i ↪[L] D i) :
    ∃ Q ∈ K, ∃ b : B ↪[L] Q, ∃ h : ∀ i, D i ↪[L] Q,
      ∀ i, b.comp (f i) = (h i).comp (g i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have aux : ∀ s : Finset ι, ∃ Q ∈ K, ∃ b : B ↪[L] Q,
      ∃ h : ∀ i, i ∈ s → D i ↪[L] Q,
        ∀ i (hi : i ∈ s), b.comp (f i) = (h i hi).comp (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨B, hB, Embedding.refl L B, fun i hi => False.elim ?_, ?_⟩
      · simp at hi
      · intro i hi
        simp at hi
    | @insert a s _ ih =>
      obtain ⟨Q, hQ, b, h, hh⟩ := ih
      obtain ⟨R, q, d, hR, hd⟩ := hAP (C a) Q (D a) (b.comp (f a)) (g a)
        (hC a) hQ (hD a)
      let h' : ∀ i, i ∈ insert a s → D i ↪[L] R := fun i hi => by
        by_cases hia : i = a
        · subst i; exact d
        · exact q.comp (h i ((Finset.mem_insert.mp hi).resolve_left hia))
      refine ⟨R, hR, q.comp b, h', ?_⟩
      intro i hi
      by_cases hia : i = a
      · subst i
        rw [Embedding.comp_assoc]
        simpa only [h', dite_eq_left rfl] using hd
      · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
        have hval : h' i hi = q.comp (h i his) := by simp only [h', dite_eq_right hia]
        rw [hval]
        change q.comp (b.comp (f i)) = q.comp ((h i his).comp (g i))
        rw [hh i his]
  obtain ⟨Q, hQ, b, h, hh⟩ := aux Finset.univ
  exact ⟨Q, hQ, b, fun i => h i (Finset.mem_univ i), fun i => hh i (Finset.mem_univ i)⟩

/-- One stage includes its designated representative and completes all requests up to its index. -/
def StageRequests (A : ℕ → Bundled.{w} L.Structure) (n : ℕ)
    (B D : Bundled.{w} L.Structure) (b : B ↪[L] D) : Prop :=
  Nonempty (A n ↪[L] D) ∧ ∀ (C : L.Substructure B) (r : ℕ), r ≤ n →
    ∀ g : C ↪[L] A r, ∃ h : A r ↪[L] D, h.comp g = b.comp C.subtype

/-- The finite task set is formed using the original stage B, not the growing intermediate amalgams. -/
theorem exists_next_stage [L.IsRelational] (hK : IsFraisse K)
    (A : ℕ → Bundled.{w} L.Structure) (hA : ∀ n, A n ∈ K) (n : ℕ)
    (B : Bundled.{w} L.Structure) (hB : B ∈ K) :
    ∃ D ∈ K, ∃ b : B ↪[L] D, StageRequests A n B D b := by
  classical
  have : Finite B := (hK.FG B hB).finite
  have : ∀ r, Finite (A r) := fun r => (hK.FG (A r) (hA r)).finite
  have : Finite (L.Substructure B) :=
    Finite.of_injective (fun S : L.Substructure B => (S : Set B)) SetLike.coe_injective
  have finiteC (C : L.Substructure B) : Finite C :=
    Finite.of_injective (fun c : C => (c : B)) Subtype.val_injective
  have : ∀ (C : L.Substructure B) (r : Fin (n + 1)), Finite (C ↪[L] A r.val) :=
    fun C r => by
      have : Finite C := finiteC C
      exact Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let Job := Σ C : L.Substructure B, Σ r : Fin (n + 1), C ↪[L] A r.val
  have : Finite Job := by
    dsimp only [Job]
    infer_instance
  obtain ⟨E, hE, ⟨b⟩, ⟨a⟩⟩ := hK.jointEmbedding B hB (A n) (hA n)
  obtain ⟨D, hD, d, h, hh⟩ := finite_amalgamation (ι := Job) hK.amalgamation E hE
    (fun j => Bundled.of j.1) (fun j => A j.2.1.val)
    (fun j => hK.hereditary B hB
      ⟨Structure.fg_iff_finite.mpr (finiteC j.1), ⟨j.1.subtype⟩⟩)
    (fun j => hA j.2.1.val) (fun j => b.comp j.1.subtype) (fun j => j.2.2)
  refine ⟨D, hD, d.comp b, ⟨d.comp a⟩, ?_⟩
  intro C r hr g
  let job : Job := ⟨C, ⟨⟨r, Nat.lt_succ_of_le hr⟩, g⟩⟩
  exact ⟨h job, (hh job).symm⟩

/-- A sequence of members of K and embeddings between successive stages. -/
structure Chain (K : Set (Bundled.{w} L.Structure)) where
  stage : ℕ → Bundled.{w} L.Structure
  mem : ∀ n, stage n ∈ K
  next : ∀ n, stage n ↪[L] stage (n + 1)

namespace Chain

/-- All transition maps are composites of the specified successor embeddings. -/
abbrev map (C : Chain K) (i j : ℕ) (h : i ≤ j) : C.stage i ↪[L] C.stage j :=
  DirectedSystem.natLERec C.next i j h

/-- The union up to the canonical identifications of the old carriers. -/
abbrev Limit (C : Chain K) :=
  Language.DirectLimit (fun n => C.stage n) C.map

/-- The specified inclusion of a stage into the union. -/
noncomputable abbrev intoLimit (C : Chain K) (n : ℕ) : C.stage n ↪[L] C.Limit :=
  DirectLimit.of L ℕ (fun n => C.stage n) C.map n

private theorem map_succ_apply (C : Chain K) (i n : ℕ) (hin : i ≤ n) (x : C.stage i) :
    C.map i (n + 1) (Nat.le_succ_of_le hin) x = C.next n (C.map i n hin x) := by
  dsimp only [map, DirectedSystem.natLERec]
  rw [Nat.leRecOn_succ hin]
  rfl

/-- Every request over an earlier stage is eventually completed with its common map unchanged. -/
def IsFair (C : Chain K) (A : ℕ → Bundled.{w} L.Structure) : Prop :=
  ∀ (i : ℕ) (S : L.Substructure (C.stage i)) (r : ℕ) (g : S ↪[L] A r),
    ∃ (n : ℕ) (hin : i ≤ n) (h : A r ↪[L] C.stage n),
      h.comp g = (C.map i n hin).comp S.subtype

/-- Every specified embedding of a finite carrier into the limit factors through one stage. -/
theorem factor_finite_embedding (C : Chain K) (A : Type w) [L.Structure A] [Finite A]
    (f : A ↪[L] C.Limit) :
    ∃ (i : ℕ) (g : A ↪[L] C.stage i), (C.intoLimit i).comp g = f := by
  obtain ⟨i, y, hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun n => C.stage n) C.map (f : A → C.Limit)
  have heq : (C.intoLimit i) ∘ y = f := by
    funext a
    exact (congrFun hy a).symm
  let g : A ↪[L] C.stage i := {
    toFun := y
    inj' := fun a b h => f.injective (by rw [← heq]; exact congrArg (C.intoLimit i) h)
    map_fun' := fun F xs => by
      apply (C.intoLimit i).injective
      calc
        C.intoLimit i (y (funMap F xs)) = f (funMap F xs) := congrFun heq _
        _ = funMap F (f ∘ xs) := f.map_fun F xs
        _ = funMap F (C.intoLimit i ∘ (y ∘ xs)) := by rw [← Function.comp_assoc, heq]
        _ = C.intoLimit i (funMap F (y ∘ xs)) := ((C.intoLimit i).map_fun F _).symm
    map_rel' := fun R xs => by
      apply ((C.intoLimit i).map_rel R (y ∘ xs)).symm.trans
      rw [← Function.comp_assoc, heq]
      exact f.map_rel R xs }
  exact ⟨i, g, Embedding.ext (congrFun heq)⟩

/-- A union of finite stages is countable. -/
theorem limit_countable [L.IsRelational] (hK : IsFraisse K) (C : Chain K) :
    Countable C.Limit := by
  have : ∀ n, Finite (C.stage n) := fun n => (hK.FG _ (C.mem n)).finite
  change Countable (Quotient (Language.DirectLimit.setoid (fun n => C.stage n) C.map))
  infer_instance

end Chain

/-- Finite batches, processed at successively larger bounds, yield a fair chain. -/
theorem exists_fair_chain [L.IsRelational] (hK : IsFraisse K)
    (A : ℕ → Bundled.{w} L.Structure) (hA : ∀ n, A n ∈ K) :
    ∃ C : Chain K, (∀ r, ∃ n, Nonempty (A r ↪[L] C.stage n)) ∧ C.IsFair A := by
  classical
  choose D hD b hb using fun (n : ℕ) (B : K) => exists_next_stage hK A hA n B.val B.prop
  let F : ℕ → K := Nat.rec ⟨A 0, hA 0⟩ (fun n B => ⟨D n B, hD n B⟩)
  let C : Chain K := {
    stage := fun n => (F n).val
    mem := fun n => (F n).prop
    next := fun n => b n (F n) }
  refine ⟨C, ?_, ?_⟩
  · intro r
    exact ⟨r + 1, (hb r (F r)).1⟩
  · intro i S r g
    let N := max i r
    have hiN : i ≤ N := le_max_left i r
    let p : S ↪[L] C.stage N := (C.map i N hiN).comp S.subtype
    let T := p.toHom.range
    let req : T ↪[L] A r := g.comp p.equivRange.symm.toEmbedding
    obtain ⟨h, hh⟩ := (hb N (F N)).2 T r (le_max_right i r) req
    refine ⟨N + 1, Nat.le_succ_of_le hiN, h, ?_⟩
    ext s
    have hs := congrArg (fun q : T ↪[L] C.stage (N + 1) => q (p.equivRange s)) hh
    change h (g (p.equivRange.symm (p.equivRange s))) = C.next N (p s) at hs
    rw [Language.Equiv.symm_apply_apply] at hs
    change h (g s) = C.map i (N + 1) (Nat.le_succ_of_le hiN) (S.subtype s)
    rw [Chain.map_succ_apply]
    exact hs

/-- The prescribed representatives and HP identify the exact age of the constructed union. -/
theorem fair_limit_age (hK : IsFraisse K)
    (A : ℕ → Bundled.{w} L.Structure) (_hA : ∀ n, A n ∈ K)
    (hreps : ∀ B ∈ K, ∃ r, Nonempty (B ≃[L] A r)) (C : Chain K)
    (huniv : ∀ r, ∃ n, Nonempty (A r ↪[L] C.stage n)) : L.age C.Limit = K := by
  rw [show L.age C.Limit = ⋃ n, L.age (C.stage n) from
    age_directLimit (fun n => C.stage n) C.map]
  ext B
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, hB⟩
    exact hK.hereditary (C.stage n) (C.mem n) hB
  · intro hB
    obtain ⟨r, ⟨e⟩⟩ := hreps B hB
    obtain ⟨n, ⟨a⟩⟩ := huniv r
    exact ⟨n, hK.FG B hB, ⟨a.comp e.toEmbedding⟩⟩

/-- Factor the supplied finite map, complete its registered request, then return to the original B. -/
theorem fair_limit_extension_property [L.IsRelational] (hK : IsFraisse K)
    (A : ℕ → Bundled.{w} L.Structure)
    (hreps : ∀ B ∈ K, ∃ r, Nonempty (B ≃[L] A r)) (C : Chain K)
    (hfair : C.IsFair A) : ExtensionProperty K C.Limit := by
  intro B D hB hD f g
  have : Finite B := (hK.FG B hB).finite
  obtain ⟨i, fi, hfi⟩ := C.factor_finite_embedding B f
  obtain ⟨r, ⟨e⟩⟩ := hreps D hD
  let S := fi.toHom.range
  let req : S ↪[L] A r := (e.toEmbedding.comp g).comp fi.equivRange.symm.toEmbedding
  obtain ⟨n, hin, h, hh⟩ := hfair i S r req
  refine ⟨(C.intoLimit n).comp (h.comp e.toEmbedding), ?_⟩
  ext a
  have hc := congrArg (fun q : S ↪[L] C.stage n => q (fi.equivRange a)) hh
  change h (e (g (fi.equivRange.symm (fi.equivRange a)))) =
    C.map i n hin (fi a) at hc
  rw [Language.Equiv.symm_apply_apply] at hc
  change C.intoLimit n (h (e (g a))) = f a
  rw [hc]
  exact (Language.DirectLimit.of_f (G := fun n => C.stage n) (f := C.map)
      (i := i) (j := n) (hij := hin) (x := fi a)).trans
    (congrArg (fun q : B ↪[L] C.Limit => q a) hfi)

/-- Existence includes the age and extension property for one and the same countable witness. -/
theorem exists_limit [L.IsRelational] (hK : IsFraisse K) :
    ∃ M : Bundled.{w} L.Structure,
      Countable M ∧ L.age M = K ∧ ExtensionProperty K M := by
  obtain ⟨A, hA, hreps⟩ := exists_representatives hK
  obtain ⟨C, huniv, hfair⟩ := exists_fair_chain hK A hA
  exact ⟨Bundled.of C.Limit, C.limit_countable hK,
    fair_limit_age hK A hA hreps C huniv,
    fair_limit_extension_property hK A hreps C hfair⟩

variable {M N : Type w} [L.Structure M] [L.Structure N]

/-- The extension property gives the forth requirement for actual finite-substructure maps. -/
theorem isExtensionPair_of_extension_property
    (hage : L.age M ⊆ K) (hEP : ExtensionProperty K N) : L.IsExtensionPair M N := by
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S hS f m
  let T : L.Substructure M := Substructure.closure L {m} ⊔ S
  have hT : T.FG := (Substructure.fg_closure_singleton m).sup hS
  obtain ⟨g, hg⟩ := hEP (Bundled.of S) (Bundled.of T)
    (hage ⟨(S.fg_iff_structure_fg).1 hS, ⟨S.subtype⟩⟩)
    (hage ⟨(T.fg_iff_structure_fg).1 hT, ⟨T.subtype⟩⟩)
    f (Substructure.inclusion le_sup_right)
  exact ⟨g, hg.symm⟩

/-- One-sided extension embeds every compatible countable structure, including empty structures. -/
theorem countable_universality [Countable N]
    (hageM : L.age M = K) (hEP : ExtensionProperty K M) (hageN : L.age N ⊆ K) :
    Nonempty (N ↪[L] M) := by
  let S : L.Substructure N := ⊥
  have hS : S.FG := Substructure.fg_bot
  have hSK : (⟨S, inferInstance⟩ : Bundled L.Structure) ∈ L.age M := by
    rw [hageM]
    exact hageN ⟨(S.fg_iff_structure_fg).1 hS, ⟨S.subtype⟩⟩
  obtain ⟨a⟩ := hSK.2
  let p : L.FGEquiv N M := ⟨⟨S, a.toHom.range, a.equivRange⟩, hS⟩
  obtain ⟨f, _⟩ := embedding_from_cg Structure.cg_of_countable p
    (isExtensionPair_of_extension_property hageN hEP)
  exact ⟨f⟩

/-- Back and forth preserves the specified initial embedding of a finite induced substructure. -/
theorem extend_prescribed_isomorphism [Countable M] [Countable N]
    (hageM : L.age M = K) (hM : ExtensionProperty K M)
    (hageN : L.age N = K) (hN : ExtensionProperty K N)
    (S : L.Substructure M) (hS : S.FG) (f : S ↪[L] N) :
    ∃ e : M ≃[L] N, e.toEmbedding.comp S.subtype = f := by
  obtain ⟨e, ⟨_, he⟩⟩ := equiv_between_cg Structure.cg_of_countable Structure.cg_of_countable
    ⟨⟨S, f.toHom.range, f.equivRange⟩, hS⟩
    (isExtensionPair_of_extension_property hageM.le hN)
    (isExtensionPair_of_extension_property hageN.le hM)
  refine ⟨e, ?_⟩
  simp only [Embedding.subtype_equivRange] at he
  rw [← he]
  ext
  rfl

/-- For countable structures with a fixed age, the finite extension and symmetry formulations agree. -/
theorem extension_property_iff_ultrahomogeneous [Countable M] (hage : L.age M = K) :
    ExtensionProperty K M ↔ L.IsUltrahomogeneous M := by
  constructor
  · intro h
    exact (isUltrahomogeneous_iff_IsExtensionPair Structure.cg_of_countable).mpr
      (isExtensionPair_of_extension_property hage.le h)
  · intro h A B hA hB f g
    have hA' : A ∈ L.age M := hage ▸ hA
    have hB' : B ∈ L.age M := hage ▸ hB
    obtain ⟨j, hj⟩ := h.extend_embedding hA'.1 f g (h := hB'.2)
    exact ⟨j, hj.symm⟩

/-- Necessity and construction, with the nonempty-class requirement retained in IsFraisse. -/
theorem exists_limit_iff [L.IsRelational] :
    (∃ M : Bundled.{w} L.Structure,
      Countable M ∧ L.age M = K ∧ ExtensionProperty K M) ↔ IsFraisse K := by
  constructor
  · rintro ⟨M, hcount, hage, hEP⟩
    have : Countable M := hcount
    have hhom := (extension_property_iff_ultrahomogeneous hage).mp hEP
    simpa only [hage] using hhom.age_isFraisse
  · exact exists_limit

/-- Finite equality structures extend every bijection between their finite subsets. -/
theorem finite_equality_ultrahomogeneous (M : Type) [Finite M] [Language.empty.Structure M] :
    Language.empty.IsUltrahomogeneous M := by
  classical
  intro S _ f
  let e : M ≃ M := f.equivRange.toEquiv.extendSubtype
  refine ⟨StrongHomClass.toEquiv e, ?_⟩
  ext a
  exact (Equiv.extendSubtype_apply_of_mem f.equivRange.toEquiv a a.2).symm

/-- The equality structure with m elements has exactly the sets of size at most m as its age. -/
theorem finite_equality_age (m : ℕ) [Language.empty.Structure (Fin m)] :
    Language.empty.age (Fin m) =
      {S : Bundled.{0} Language.empty.Structure | Nonempty (S ↪ Fin m)} := by
  ext S
  change (Structure.FG Language.empty S ∧ Nonempty (S ↪[Language.empty] Fin m)) ↔ _
  constructor
  · rintro ⟨_, ⟨e⟩⟩
    exact ⟨e.toEmbedding⟩
  · rintro ⟨e⟩
    have : Finite S := Finite.of_injective e e.injective
    exact ⟨Structure.FG.of_finite, ⟨StrongHomClass.toEmbedding e⟩⟩

/-- The finite equality example satisfies both the exact age and the finite extension property. -/
theorem finite_equality_limit (m : ℕ) [Language.empty.Structure (Fin m)] :
    let Km : Set (Bundled.{0} Language.empty.Structure) := {S | Nonempty (S ↪ Fin m)}
    Language.empty.age (Fin m) = Km ∧ ExtensionProperty Km (Fin m) := by
  exact ⟨finite_equality_age m,
    (extension_property_iff_ultrahomogeneous (finite_equality_age m)).mpr
      (finite_equality_ultrahomogeneous (Fin m))⟩

end Lemmatheca.ModelTheory.FraisseLimits
