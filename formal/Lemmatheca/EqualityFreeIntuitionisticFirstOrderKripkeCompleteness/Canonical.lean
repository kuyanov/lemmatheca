import Lemmatheca.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories.Extensions
import Lemmatheca.IntuitionisticFirstOrderKripkeSemantics.Soundness

namespace Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a
noncomputable section
variable {L : Language.{u,v}}

/-- The actual parameter universe and actual accepted native formulas of a world. -/
structure World (L : Language.{u,v}) where
  parameters : PrimeHenkin.Universe
  theory : Set (PrimeHenkin.Fml L)
  prime : PrimeHenkin.Theory parameters theory

instance worldPreorder : Preorder (World L) where
  le w z := PrimeHenkin.Extends w.parameters w.theory z.parameters z.theory
  le_refl _ := ⟨Set.Subset.rfl,Set.Subset.rfl⟩
  le_trans _ _ _ hwz hzt := ⟨Set.Subset.trans hwz.1 hzt.1,Set.Subset.trans hwz.2 hzt.2⟩

/-- Domains are literal term trees labelled by the parameters available at the world. -/
abbrev Domain (w : World L) := L.Term w.parameters.carrier

/-- Erasure removes only the subtype proof on each available numerical name. -/
def erase {w : World L} (t : Domain w) : L.Term ℕ := t.relabel Subtype.val

def transition {w z : World L} (h : w ≤ z) (t : Domain w) : Domain z :=
  t.relabel (fun c => ⟨c.val,h.1 c.property⟩)

@[instance_reducible]
def termStructure (w : World L) : L.Structure (Domain w) where
  funMap := fun f ts => .func f ts
  RelMap := fun R ts => (.rel R (fun i => (erase (ts i)).relabel Sum.inl) : PrimeHenkin.Fml L) ∈ w.theory

theorem erase_injective (w : World L) : Function.Injective (@erase L w) := by
  classical
  let c : w.parameters.carrier := ⟨Classical.choose w.parameters.nonempty,Classical.choose_spec w.parameters.nonempty⟩
  let f : ℕ → w.parameters.carrier := fun n => if h : n ∈ w.parameters.carrier then ⟨n,h⟩ else c
  have he : f ∘ Subtype.val = id := by
    funext x
    simp [f,x.property]
  intro x y h
  have hm := congrArg (Term.relabel f) h
  simpa only [erase,Term.relabel_relabel,he,Term.relabel_id] using hm

theorem erase_supported {w : World L} (t : Domain w) :
    PrimeHenkin.TermSupported w.parameters.carrier (erase t) := by
  induction t with
  | var c =>
      intro n hn
      have he := Finset.mem_singleton.mp hn
      exact he ▸ c.property
  | func f ts ih =>
      intro c hc
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc
      exact ih i c hi

theorem erase_transition {w z : World L} (h : w ≤ z) (t : Domain w) :
    erase (transition h t) = erase t := by
  simp only [erase,transition,Term.relabel_relabel]
  rfl

theorem transition_injective {w z : World L} (h : w ≤ z) :
    Function.Injective (transition h) := by
  intro x y hxy
  apply erase_injective w
  simpa only [erase_transition] using congrArg erase hxy

theorem transition_function {w z : World L} (h : w ≤ z) {n} (f : L.Functions n)
    (ts : Fin n → Domain w) :
    transition h (.func f ts) = .func f (transition h ∘ ts) := by
  rfl

theorem transition_relation {w z : World L} (h : w ≤ z) {n} (R : L.Relations n)
    (ts : Fin n → Domain w) :
    @Structure.RelMap L (Domain w) (termStructure w) n R ts →
      @Structure.RelMap L (Domain z) (termStructure z) n R (transition h ∘ ts) := by
  change (.rel R (fun i => (erase (ts i)).relabel Sum.inl) : PrimeHenkin.Fml L) ∈ w.theory →
    (.rel R (fun i => (erase (transition h (ts i))).relabel Sum.inl) : PrimeHenkin.Fml L) ∈ z.theory
  simp only [erase_transition]
  exact fun ht => h.2 ht

def transitionHom {w z : World L} (h : w ≤ z) :
    @Language.Hom L (Domain w) (Domain z) (termStructure w) (termStructure z) :=
  letI := termStructure w
  letI := termStructure z
  ⟨transition h, transition_function h, transition_relation h⟩

theorem transition_refl (w : World L) (t : Domain w) : transition (le_refl w) t = t := by
  unfold transition
  have he : (fun c : w.parameters.carrier => (⟨c.val,(le_refl w).1 c.property⟩ : w.parameters.carrier)) = id := by
    funext c
    rfl
  rw [he,Term.relabel_id]

theorem transition_trans {w z t : World L} (hwz : w ≤ z) (hzt : z ≤ t) (x : Domain w) :
    transition hzt (transition hwz x) = transition (le_trans hwz hzt) x := by
  simp only [transition,Term.relabel_relabel]
  rfl

theorem domain_nonempty (w : World L) : Nonempty (Domain w) := by
  obtain ⟨c,hc⟩ := w.parameters.nonempty
  exact ⟨.var ⟨c,hc⟩⟩

theorem seed_infinite_compl : ({0} : Set ℕ)ᶜ.Infinite := by
  exact (Set.finite_singleton 0).infinite_compl

/-- A supplied nonempty parameter seed with an infinite unused complement. -/
def seed : PrimeHenkin.Universe where
  carrier := {0}
  nonempty := ⟨0,Set.mem_singleton 0⟩
  infinite_compl := seed_infinite_compl

theorem seed_consistent [_countableSymbols : Countable L.Symbols] : ¬ PrimeHenkin.Provable (L := L) ∅ .falsum := by
  rintro ⟨p⟩
  have he : p.assumptions = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    exact p.allowed A hA
  apply NaturalDeduction.public_consistent L ℕ false false
  exact ⟨he ▸ p.derivation⟩

variable [Countable L.Symbols]

def initialWorld : World L where
  parameters := PrimeHenkin.enlargement seed
  theory := PrimeHenkin.extension seed ∅ .falsum
  prime := PrimeHenkin.extension_prime seed ∅ .falsum (Set.empty_subset _) ⟨trivial,fun _ h => False.elim (Finset.notMem_empty _ h)⟩ seed_consistent

/-- One fixed genuine native Kripke model, chosen independently of premises or conclusion. -/
def canonicalModel : Kripke.Model.{u,v,max u v,u} L (World L) where
  world_nonempty := ⟨initialWorld⟩
  Domain := Domain
  domain_nonempty := domain_nonempty
  structureAt := termStructure
  map := transitionHom
  map_refl := transition_refl
  map_trans := fun h k x => transition_trans h k x

end
end Lemmatheca.ProofTheory.FirstOrder.KripkeCompleteness
