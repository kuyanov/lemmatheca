import Lemmatheca.ForcingChainConditions.BinaryMaps
import Mathlib.SetTheory.Cardinal.Continuum

/-! The actual finite-map order on rows and columns, its union and its specified columns. -/
namespace Lemmatheca.SetTheory.ManyCohenReals
open Set Order
open Lemmatheca.SetTheory.FinitePartialMaps
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Conditions (I : Type u) := BinaryMap (ℕ × I)

local instance arrayOrder (I : Type u) : PartialOrder (Conditions I) := binaryOrder (ℕ × I)
local instance arrayTop (I : Type u) : OrderTop (Conditions I) := binaryOrderTop (ℕ × I)

variable {I : Type u}

private theorem graph_lookup (p : Conditions I) (i : ℕ × I) (b : Bool) :
    (i,b) ∈ graph p ↔ p.lookup i = some b := Finmap.lookup_eq_some_iff.symm

private theorem graph_unique (p : Conditions I) (i : ℕ × I) (b c : Bool)
    (hb : (i,b) ∈ graph p) (hc : (i,c) ∈ graph p) : b = c :=
  Option.some.inj ((graph_lookup p i b).mp hb |>.symm.trans ((graph_lookup p i c).mp hc))

/-- The specified one-coordinate insertion. -/
def extendAt (p : Conditions I) (n : ℕ) (α : I) (b : Bool) : Conditions I :=
  Finmap.insert (n, α) b p

/-- Conditions deciding the indicated row and column. -/
def coordinateDense (n : ℕ) (α : I) : Set (Conditions I) :=
  {p | (n, α) ∈ p.keys}

/-- Conditions with an explicit row witnessing disagreement between two columns. -/
def separationDense (α β : I) : Set (Conditions I) :=
  {p | ∃ n b c, ((n, α), b) ∈ graph p ∧ ((n, β), c) ∈ graph p ∧ b ≠ c}

/-- Conditions with a column entry differing from the specified old binary real. -/
def disagreementDense (α : I) (f : ℕ → Bool) : Set (Conditions I) :=
  {p | ∃ n b, ((n, α), b) ∈ graph p ∧ b ≠ f n}

/-- The actual graph union of all finite conditions in the filter. -/
def arrayUnion (G : PFilter (Conditions I)) : Set ((ℕ × I) × Bool) :=
  {z | ∃ p ∈ G, z ∈ graph p}

/-- The two inserted coordinates used in the pair-separation proof. -/
def separateAt (p : Conditions I) (n : ℕ) (α β : I) : Conditions I :=
  extendAt (extendAt p n α false) n β true

theorem fresh_pair (p : Conditions I) (α β : I) :
    ∃ n : ℕ, (n, α) ∉ p.keys ∧ (n, β) ∉ p.keys := by
  classical
  obtain ⟨n,hn⟩ := (p.keys.image Prod.fst).exists_notMem
  refine ⟨n,?_,?_⟩
  · intro h
    exact hn (Finset.mem_image.mpr ⟨(n,α),h,rfl⟩)
  · intro h
    exact hn (Finset.mem_image.mpr ⟨(n,β),h,rfl⟩)

theorem extension_spec (p : Conditions I) (n : ℕ) (α : I)
    (hn : (n, α) ∉ p.keys) (b : Bool) :
    extendAt p n α b ≤ p ∧
      graph (extendAt p n α b) = insert ((n, α), b) (graph p) := by
  have hgraph : graph (extendAt p n α b) = insert ((n,α),b) (graph p) := by
    ext ⟨k,c⟩
    by_cases hkn : k = (n,α)
    · subst k
      have hn' : p.lookup (n,α) = none := Finmap.lookup_eq_none.mpr hn
      simp [extendAt,graph_lookup,hn',eq_comm]
    · simp [extendAt,graph_lookup,Finmap.lookup_insert_of_ne p hkn,hkn]
  refine ⟨?_,hgraph⟩
  change graph p ⊆ graph (extendAt p n α b)
  rw [hgraph]
  exact Set.subset_insert _ _

theorem coordinate_dense (n : ℕ) (α : I) : Dense (coordinateDense n α) := by
  intro p
  by_cases hn : (n,α) ∈ p.keys
  · exact ⟨p,hn,le_rfl⟩
  · refine ⟨extendAt p n α false,?_,(extension_spec p n α hn false).1⟩
    change (n,α) ∈ Finmap.insert (n,α) false p
    simp

theorem array_single_valued (G : PFilter (Conditions I)) {n : ℕ} {α : I} {b c : Bool}
    (hb : ((n, α), b) ∈ arrayUnion G) (hc : ((n, α), c) ∈ arrayUnion G) :
    b = c := by
  obtain ⟨p,hp,hpb⟩ := hb
  obtain ⟨q,hq,hqc⟩ := hc
  obtain ⟨r,_,hrp,hrq⟩ := G.directed p hp q hq
  exact graph_unique r (n,α) b c (hrp hpb) (hrq hqc)

theorem coordinate_exists (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) (n : ℕ) (α : I) :
    ∃ b, ((n, α), b) ∈ arrayUnion G := by
  obtain ⟨p,hp,hpn⟩ := hG n α
  obtain ⟨b,hb⟩ := Finmap.mem_iff.mp hpn
  exact ⟨b,p,hp,(graph_lookup p (n,α) b).mpr hb⟩

/-- The selected total column is defined from the actual coordinate witnesses. -/
def column (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) (α : I) : ℕ → Bool :=
  fun n => Classical.choose (coordinate_exists G hG n α)

theorem column_spec (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) :
    arrayUnion G = {z | z.2 = column G hG z.1.2 z.1.1} ∧
      ∀ p ∈ G, graph p ⊆ {z | z.2 = column G hG z.1.2 z.1.1} := by
  have hgraph : arrayUnion G = {z | z.2 = column G hG z.1.2 z.1.1} := by
    ext ⟨⟨n,α⟩,b⟩
    constructor
    · intro hb
      exact array_single_valued G hb (Classical.choose_spec (coordinate_exists G hG n α))
    · intro hb
      change b = column G hG α n at hb
      rw [hb]
      exact Classical.choose_spec (coordinate_exists G hG n α)
  refine ⟨hgraph,?_⟩
  intro p hp z hz
  rw [←hgraph]
  exact ⟨p,hp,hz⟩

theorem separation_extension (p : Conditions I) (n : ℕ) (α β : I) (hne : α ≠ β)
    (hα : (n, α) ∉ p.keys) (hβ : (n, β) ∉ p.keys) :
    separateAt p n α β ≤ p ∧
      graph (separateAt p n α β) =
        insert ((n, β), true) (insert ((n, α), false) (graph p)) ∧
      separateAt p n α β ∈ separationDense α β := by
  have ha := extension_spec p n α hα false
  have hb' : (n,β) ∉ (extendAt p n α false).keys := by
    simp only [Finmap.mem_keys,extendAt,Finmap.mem_insert,not_or]
    exact ⟨fun h => hne (Prod.mk.inj h).2.symm,hβ⟩
  have hb := extension_spec (extendAt p n α false) n β hb' true
  have hg : graph (separateAt p n α β) =
      insert ((n,β),true) (insert ((n,α),false) (graph p)) := by
    rw [separateAt,hb.2,ha.2]
  refine ⟨hb.1.trans ha.1,hg,?_⟩
  refine ⟨n,false,true,?_,?_,Bool.false_ne_true⟩
  · rw [hg]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · rw [hg]
    exact Set.mem_insert _ _

theorem separation_dense (α β : I) (hne : α ≠ β) :
    Dense (separationDense α β) := by
  intro p
  obtain ⟨n,ha,hb⟩ := fresh_pair p α β
  have hs := separation_extension p n α β hne ha hb
  exact ⟨separateAt p n α β,hs.2.2,hs.1⟩

theorem columns_ne (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) (α β : I)
    (hsep : Meets G (separationDense α β)) : column G hG α ≠ column G hG β := by
  obtain ⟨p,hp,n,b,c,hb,hc,hbc⟩ := hsep
  have hb' : b = column G hG α n := (column_spec G hG).2 p hp hb
  have hc' : c = column G hG β n := (column_spec G hG).2 p hp hc
  intro he
  exact hbc (hb'.trans ((congrFun he n).trans hc'.symm))

theorem column_injective (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α))
    (hsep : ∀ α β, α ≠ β → Meets G (separationDense α β)) :
    Function.Injective (column G hG) := by
  intro α β he
  by_contra hn
  exact columns_ne G hG α β (hsep α β hn) he

theorem disagreement_dense (α : I) (f : ℕ → Bool) :
    Dense (disagreementDense α f) := by
  intro p
  obtain ⟨n,hn,_⟩ := fresh_pair p α α
  refine ⟨extendAt p n α (!f n),?_,(extension_spec p n α hn _).1⟩
  refine ⟨n,!f n,?_,?_⟩
  · rw [(extension_spec p n α hn _).2]
    exact Set.mem_insert _ _
  · cases f n <;> decide

theorem column_disagrees (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) (α : I) (f : ℕ → Bool)
    (hf : Meets G (disagreementDense α f)) :
    ∃ n, column G hG α n ≠ f n := by
  obtain ⟨p,hp,n,b,hb,hbf⟩ := hf
  have he : b = column G hG α n := (column_spec G hG).2 p hp hb
  exact ⟨n,fun hn => hbf (he.trans hn)⟩

theorem column_not_old (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α)) (old : Set (ℕ → Bool))
    (hold : ∀ α f, f ∈ old → Meets G (disagreementDense α f)) :
    ∀ α, column G hG α ∉ old := by
  intro α hα
  obtain ⟨n,hn⟩ := column_disagrees G hG α _ (hold α _ hα)
  exact hn rfl

/-- Genericity supplies the coordinate and pair requirements used by the specified columns. -/
theorem generic_injective_columns (G : PFilter (Conditions I)) (S : Set (Set (Conditions I)))
    (hG : GenericFor G S) (hcoord : ∀ n α, coordinateDense n α ∈ S)
    (hsep : ∀ α β, α ≠ β → separationDense α β ∈ S) :
    let hc : ∀ n α, Meets G (coordinateDense n α) :=
      fun n α => hG _ (hcoord n α) (coordinate_dense n α)
    Function.Injective (column G hc) := by
  exact column_injective G
    (fun n α => hG _ (hcoord n α) (coordinate_dense n α))
    (fun α β hne => hG _ (hsep α β hne) (separation_dense α β hne))

/-- The cardinal comparison concerns exactly the specified family of columns. -/
theorem column_cardinality (G : PFilter (Conditions I))
    (hG : ∀ n α, Meets G (coordinateDense n α))
    (hsep : ∀ α β, α ≠ β → Meets G (separationDense α β)) :
    Cardinal.mk I ≤ Cardinal.lift.{u} (Cardinal.mk (ℕ → Bool)) := by
  simpa using Cardinal.lift_mk_le_lift_mk_of_injective (column_injective G hG hsep)

end
end Lemmatheca.SetTheory.ManyCohenReals
