import Lemmatheca.ForcingAndGenericFilters.BoundedTests

namespace Lemmatheca.SetTheory.ForcingAndGenericFilters
open Set Order
open Lemmatheca.SetTheory.FinitePartialMaps
universe u

abbrev Cohen := BinaryMap ℕ


private theorem graph_lookup (p : Cohen) (n : ℕ) (b : Bool) :
    (n,b) ∈ graph p ↔ p.lookup n = some b :=
  Finmap.lookup_eq_some_iff.symm

private theorem graph_unique (p : Cohen) (n : ℕ) (b c : Bool)
    (hb : (n,b) ∈ graph p) (hc : (n,c) ∈ graph p) : b = c :=
  Option.some.inj ((graph_lookup p n b).mp hb |>.symm.trans ((graph_lookup p n c).mp hc))

theorem cohen_graph_injective : Function.Injective (graph : Cohen → Set (ℕ × Bool)) := by
  intro p q h
  apply Finmap.ext_lookup
  intro n
  apply Option.ext
  intro b
  simp only [←graph_lookup,h]

instance cohenPartialOrder : PartialOrder Cohen :=
  PartialOrder.lift (fun p : Cohen => OrderDual.toDual (graph p)) cohen_graph_injective

theorem empty_graph_subset (p : Cohen) : graph (∅ : Cohen) ⊆ graph p := by
  rintro ⟨n,b⟩ hn
  rw [graph_lookup,Finmap.lookup_empty] at hn
  cases hn

instance cohenOrderTop : OrderTop Cohen where
  top := ∅
  le_top := empty_graph_subset

theorem cohen_order (q p : Cohen) :
    (q ≤ p ↔ graph p ⊆ graph q) ∧ graph (⊤ : Cohen) = ∅ := by
  refine ⟨Iff.rfl,?_⟩
  ext ⟨n,b⟩
  simp only [Set.mem_empty_iff_false,iff_false]
  rw [graph_lookup]
  change (∅ : Cohen).lookup n ≠ some b
  simp

theorem cohen_compatibility (q p : Cohen) :
    Compatible q p ↔ Agree q p := by
  exact Lemmatheca.SetTheory.FinitePartialMaps.compatible_iff_agree q p

def cohenExtend (p : Cohen) (n : ℕ) (b : Bool) : Cohen := Finmap.insert n b p

theorem cohen_fresh (p : Cohen) : ∃ n : ℕ, n ∉ p.keys := by
  exact p.keys.exists_notMem

theorem cohen_extension (p : Cohen) (n : ℕ) (hn : n ∉ p.keys) (b : Bool) :
    cohenExtend p n b ≤ p ∧ graph (cohenExtend p n b) = insert (n,b) (graph p) := by
  have hgraph : graph (cohenExtend p n b) = insert (n,b) (graph p) := by
    ext ⟨k,c⟩
    by_cases hkn : k = n
    · subst k
      have hn' : p.lookup n = none := Finmap.lookup_eq_none.mpr hn
      simp [cohenExtend,graph_lookup,hn',eq_comm]
    · simp [cohenExtend,graph_lookup,Finmap.lookup_insert_of_ne p hkn,hkn]
  refine ⟨?_,hgraph⟩
  change graph p ⊆ graph (cohenExtend p n b)
  rw [hgraph]
  exact Set.subset_insert _ _

theorem cohen_split (p : Cohen) (n : ℕ) (hn : n ∉ p.keys) :
    cohenExtend p n false ≤ p ∧ cohenExtend p n true ≤ p ∧
      ¬Compatible (cohenExtend p n false) (cohenExtend p n true) := by
  refine ⟨(cohen_extension p n hn false).1,(cohen_extension p n hn true).1,?_⟩
  intro hc
  have h := (cohen_compatibility _ _).mp hc n false true
  have hf : (n,false) ∈ graph (cohenExtend p n false) := by
    rw [(cohen_extension p n hn false).2]; exact Set.mem_insert _ _
  have ht : (n,true) ∈ graph (cohenExtend p n true) := by
    rw [(cohen_extension p n hn true).2]; exact Set.mem_insert _ _
  exact Bool.false_ne_true (h hf ht)

theorem cohen_atomless : Atomless (P := Cohen) := by
  intro p
  obtain ⟨n,hn⟩ := cohen_fresh p
  exact ⟨cohenExtend p n false,cohenExtend p n true,cohen_split p n hn⟩

def coordinateDense (n : ℕ) : Set Cohen := {p | n ∈ p.keys}
def disagreementDense (f : ℕ → Bool) : Set Cohen :=
  {p | ∃ n b, (n,b) ∈ graph p ∧ b ≠ f n}

theorem coordinate_dense (n : ℕ) : Dense (coordinateDense n) := by
  intro p
  by_cases hn : n ∈ p.keys
  · exact ⟨p,hn,le_rfl⟩
  · refine ⟨cohenExtend p n false,?_,(cohen_extension p n hn false).1⟩
    change n ∈ Finmap.insert n false p
    simp

theorem disagreement_dense (f : ℕ → Bool) : Dense (disagreementDense f) := by
  intro p
  obtain ⟨n,hn⟩ := cohen_fresh p
  refine ⟨cohenExtend p n (!f n),?_,(cohen_extension p n hn _).1⟩
  refine ⟨n,!f n,?_,?_⟩
  · rw [(cohen_extension p n hn _).2]
    exact Set.mem_insert _ _
  · cases f n <;> decide

def cohenUnion (G : PFilter Cohen) : Set (ℕ × Bool) :=
  {nb | ∃ p ∈ G, nb ∈ graph p}

theorem cohen_union_single_valued (G : PFilter Cohen) {n : ℕ} {b c : Bool}
    (hb : (n,b) ∈ cohenUnion G) (hc : (n,c) ∈ cohenUnion G) : b = c := by
  obtain ⟨p,hp,hpb⟩ := hb
  obtain ⟨q,hq,hqc⟩ := hc
  obtain ⟨r,hr,hrp,hrq⟩ := G.directed p hp q hq
  exact graph_unique r n b c (hrp hpb) (hrq hqc)

theorem cohen_coordinate_exists (G : PFilter Cohen)
    (hG : ∀ n, Meets G (coordinateDense n)) (n : ℕ) :
    ∃ b, (n,b) ∈ cohenUnion G := by
  obtain ⟨p,hp,hpn⟩ := hG n
  obtain ⟨b,hb⟩ := Finmap.mem_iff.mp hpn
  exact ⟨b,p,hp,(graph_lookup p n b).mpr hb⟩

noncomputable def cohenReal (G : PFilter Cohen) (hG : ∀ n, Meets G (coordinateDense n)) :
    ℕ → Bool := fun n => Classical.choose (cohen_coordinate_exists G hG n)

theorem cohen_real_spec (G : PFilter Cohen) (hG : ∀ n, Meets G (coordinateDense n)) :
    cohenUnion G = {nb | nb.2 = cohenReal G hG nb.1} ∧
    ∀ p ∈ G, graph p ⊆ {nb | nb.2 = cohenReal G hG nb.1} := by
  have hgraph : cohenUnion G = {nb | nb.2 = cohenReal G hG nb.1} := by
    ext ⟨n,b⟩
    constructor
    · intro hb
      exact cohen_union_single_valued G hb (Classical.choose_spec (cohen_coordinate_exists G hG n))
    · intro hb
      change b = cohenReal G hG n at hb
      rw [hb]
      exact Classical.choose_spec (cohen_coordinate_exists G hG n)
  refine ⟨hgraph,?_⟩
  intro p hp nb hnb
  rw [←hgraph]
  exact ⟨p,hp,hnb⟩

theorem cohen_real_disagrees (G : PFilter Cohen)
    (hG : ∀ n, Meets G (coordinateDense n)) (f : ℕ → Bool)
    (hf : Meets G (disagreementDense f)) :
    ∃ n, cohenReal G hG n ≠ f n := by
  obtain ⟨p,hp,n,b,hnb,hbf⟩ := hf
  have hmem : (n,b) ∈ cohenUnion G := ⟨p,hp,hnb⟩
  rw [(cohen_real_spec G hG).1] at hmem
  exact ⟨n,fun he => hbf (hmem.trans he)⟩

theorem cohen_real_not_old (G : PFilter Cohen)
    (hG : ∀ n, Meets G (coordinateDense n)) (old : Set (ℕ → Bool))
    (hold : ∀ f ∈ old, Meets G (disagreementDense f)) :
    cohenReal G hG ∉ old := by
  intro hreal
  obtain ⟨n,hn⟩ := cohen_real_disagrees G hG _ (hold _ hreal)
  exact hn rfl

theorem cohen_generic_real (G : PFilter Cohen) (S : Set (Set Cohen))
    (hG : GenericFor G S) (hcoord : ∀ n, coordinateDense n ∈ S)
    (old : Set (ℕ → Bool)) (hold : ∀ f ∈ old, disagreementDense f ∈ S) :
    ∃ g : ℕ → Bool, cohenUnion G = {nb | nb.2 = g nb.1} ∧
      (∀ p ∈ G, graph p ⊆ {nb | nb.2 = g nb.1}) ∧ g ∉ old := by
  have hc : ∀ n, Meets G (coordinateDense n) := fun n => hG _ (hcoord n) (coordinate_dense n)
  refine ⟨cohenReal G hc,(cohen_real_spec G hc).1,(cohen_real_spec G hc).2,?_⟩
  exact cohen_real_not_old G hc old (fun f hf => hG _ (hold f hf) (disagreement_dense f))

end Lemmatheca.SetTheory.ForcingAndGenericFilters
