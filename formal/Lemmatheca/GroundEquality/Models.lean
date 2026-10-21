import Lemmatheca.GroundEquality.Closure

/-! A finite quotient model whose function values use represented applications. -/

namespace Lemmatheca.MathematicalLogic.GroundEquality

open FirstOrder FirstOrder.Language

universe u v

variable {L : Language.{u, v}} [∀ n, DecidableEq (L.Functions n)]

/-- A retained application has the prescribed input classes. -/
structure ApplicationWitness (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    {n : ℕ} (f : L.Functions n) (xs : Fin n → Carrier S E hE) where
  terms : Fin n → GroundTerm L
  retained : Term.func f terms ∈ S
  arguments_match : ∀ i, classOf S E hE (terms i) (hS f terms retained i) = xs i

theorem represented_output_unique (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    {n : ℕ} (f : L.Functions n) (xs : Fin n → Carrier S E hE)
    (a b : ApplicationWitness S E hE hS f xs) :
    classOf S E hE (.func f a.terms) a.retained =
      classOf S E hE (.func f b.terms) b.retained := by
  apply (classOf_eq_iff S E hE _ _ _ _).mpr
  apply (closure_congruence S E hE).func f a.terms b.terms a.retained b.retained
  intro i
  apply (classOf_eq_iff S E hE _ _ _ _).mp
  exact (a.arguments_match i).trans (b.arguments_match i).symm

/-- Search for any retained application with the required input classes, rather than
applying the symbol to arbitrary representatives of those classes. -/
noncomputable def functionMap (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    {n : ℕ} (f : L.Functions n) (xs : Fin n → Carrier S E hE) : Carrier S E hE := by
  classical
  exact if h : Nonempty (ApplicationWitness S E hE hS f xs) then
    let a := Classical.choice h
    classOf S E hE (.func f a.terms) a.retained
  else none

/-- This structure interprets all relation symbols as false. -/
@[instance_reducible] noncomputable def modelStructure (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S) : L.Structure (Carrier S E hE) where
  funMap := functionMap S E hE hS
  RelMap := fun _ _ => False

theorem functionMap_of_represented (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    {n : ℕ} (f : L.Functions n) (xs : Fin n → Carrier S E hE)
    (a : ApplicationWitness S E hE hS f xs) :
    functionMap S E hE hS f xs = classOf S E hE (.func f a.terms) a.retained := by
  classical
  unfold functionMap
  rw [dite_eq_left (Nonempty.intro a)]
  exact represented_output_unique S E hE hS f xs (Classical.choice _) a

theorem functionMap_of_unrepresented (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    {n : ℕ} (f : L.Functions n) (xs : Fin n → Carrier S E hE)
    (h : IsEmpty (ApplicationWitness S E hE hS f xs)) :
    functionMap S E hE hS f xs = none := by
  classical
  have hn : ¬ Nonempty (ApplicationWitness S E hE hS f xs) :=
    fun ⟨a⟩ => h.false a
  simp only [functionMap, dite_eq_right hn]

theorem model_term_value (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S) (t : GroundTerm L) (ht : t ∈ S) :
    letI := modelStructure S E hE hS
    t.realize Empty.elim = classOf S E hE t ht := by
  let : L.Structure (Carrier S E hE) := modelStructure S E hE hS
  induction t with
  | var e => exact e.elim
  | func f ts ih =>
    change functionMap S E hE hS f (fun i => (ts i).realize Empty.elim) = _
    exact functionMap_of_represented S E hE hS f _
      ⟨ts, ht, fun i => (ih i (hS f ts ht i)).symm⟩

theorem model_equality_iff (S : Finset (GroundTerm L)) (E : Finset (TermPair L))
    (hE : E ⊆ S.product S) (hS : SubtermClosed S)
    (t s : GroundTerm L) (ht : t ∈ S) (hs : s ∈ S) :
    letI := modelStructure S E hE hS
    t.realize Empty.elim = s.realize (Empty.elim : Empty → Carrier S E hE) ↔
      (t, s) ∈ closure S E := by
  let : L.Structure (Carrier S E hE) := modelStructure S E hE hS
  rw [model_term_value S E hE hS t ht, model_term_value S E hE hS s hs]
  exact classOf_eq_iff S E hE t s ht hs

theorem model_satisfies (P : Problem L) (S : Finset (GroundTerm L))
    (hE : P.equations ⊆ S.product S) (hD : P.disequations ⊆ S.product S)
    (hS : SubtermClosed S) (hcheck : ∀ p ∈ P.disequations, p ∉ closure S P.equations) :
    letI := modelStructure S P.equations hE hS
    Satisfies P (Carrier S P.equations hE) := by
  let : L.Structure (Carrier S P.equations hE) := modelStructure S P.equations hE hS
  constructor
  · intro p hp
    obtain ⟨ht, hs⟩ := Finset.mem_product.mp (hE hp)
    exact (model_equality_iff S P.equations hE hS p.1 p.2 ht hs).mpr
      (equations_subset_closure S P.equations hp)
  · intro p hp heq
    obtain ⟨ht, hs⟩ := Finset.mem_product.mp (hD hp)
    exact hcheck p hp ((model_equality_iff S P.equations hE hS p.1 p.2 ht hs).mp heq)

/-- The executable test performs exactly the canonical bounded saturation. -/
def accepts (P : Problem L) : Bool :=
  decide (∀ p ∈ P.disequations, p ∉ closure (support P) P.equations)

theorem hasModel_iff (P : Problem L) :
    HasModel P ↔ ∀ p ∈ P.disequations, p ∉ closure (support P) P.equations := by
  constructor
  · rintro ⟨M, inst, _, hM⟩
    let : L.Structure M := inst
    intro p hp hc
    exact hM.2 p hp (closure_sound (support P) P.equations (equations_supported P) M
      hM.1 p hc)
  · intro hcheck
    exact ⟨Carrier (support P) P.equations (equations_supported P),
      modelStructure (support P) P.equations (equations_supported P) (support_closed P),
      inferInstance, model_satisfies P (support P) (equations_supported P)
        (disequations_supported P) (support_closed P) hcheck⟩

theorem accepts_correct (P : Problem L) : accepts P = true ↔ HasModel P := by
  simp only [accepts, decide_eq_true_eq]
  exact (hasModel_iff P).symm

end Lemmatheca.MathematicalLogic.GroundEquality
