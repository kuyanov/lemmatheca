import Lemmatheca.ForcingAndGenericFilters.Orders

namespace Lemmatheca.SetTheory.DenseForcingPresentations
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
universe u v
noncomputable section
local instance denseOrdersPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]

/-- A dense order embedding includes order reflection through its type. -/
def DenseEmbedding (j : Q ↪o P) : Prop := ∀ p, ∃ q, j q ≤ p

theorem dense_subtype_iff (D : Set P) : DenseEmbedding (P := P) (Q := D) (OrderEmbedding.subtype D) ↔ Dense D := by
  constructor
  · intro h p
    obtain ⟨d,hd⟩ := h p
    exact ⟨d.val,d.property,hd⟩
  · intro h p
    obtain ⟨d,hd,hpd⟩ := h p
    exact ⟨⟨d,hd⟩,hpd⟩

theorem dense_compatibility (j : Q ↪o P) (hj : DenseEmbedding j) (q r : Q) :
    Compatible (j q) (j r) ↔ Compatible q r := by
  constructor
  · rintro ⟨p,hpq,hpr⟩
    obtain ⟨s,hs⟩ := hj p
    exact ⟨s,j.le_iff_le.mp (hs.trans hpq),j.le_iff_le.mp (hs.trans hpr)⟩
  · rintro ⟨s,hsq,hsr⟩
    exact ⟨j s,j.monotone hsq,j.monotone hsr⟩

def imageCone (j : Q ↪o P) (p : P) : Set P :=
  {s | (∃ q, s = j q ∧ s ≤ p) ∨ ¬Compatible s p}

theorem image_cone_dense (j : Q ↪o P) (hj : DenseEmbedding j) (p : P) :
    Dense (imageCone j p) := by
  intro r
  by_cases h : Compatible r p
  · obtain ⟨s,hsr,hsp⟩ := h
    obtain ⟨q,hq⟩ := hj s
    exact ⟨j q,Or.inl ⟨q,rfl,hq.trans hsp⟩,hq.trans hsr⟩
  · exact ⟨r,Or.inr h,le_rfl⟩

def CofinalTrace (j : Q ↪o P) (G : PFilter P) : Prop :=
  ∀ p ∈ G, ∃ q, j q ∈ G ∧ j q ≤ p

theorem generic_cofinal_trace (j : Q ↪o P) (hj : DenseEmbedding j)
    (G : PFilter P) (S : Set (Set P)) (hG : GenericFor G S)
    (hcones : ∀ p, imageCone j p ∈ S) : CofinalTrace j G := by
  intro p hp
  obtain ⟨r,hr,hrcone⟩ := hG _ (hcones p) (image_cone_dense j hj p)
  rcases hrcone with ⟨q,rfl,hqp⟩ | hrp
  · exact ⟨q,hr,hqp⟩
  · exact False.elim (hrp (filter_compatible G hr hp))

def traceSet (j : Q ↪o P) (G : PFilter P) : Set Q := {q | j q ∈ G}

theorem trace_is_filter (j : Q ↪o P) (G : PFilter P) (hc : CofinalTrace j G) :
    IsPFilter (traceSet j G) := by
  apply IsPFilter.of_def
  · obtain ⟨p,hp⟩ := G.nonempty
    obtain ⟨q,hq,_⟩ := hc p hp
    exact ⟨q,hq⟩
  · intro q hq r hr
    obtain ⟨p,hp,hpq,hpr⟩ := G.directed (j q) hq (j r) hr
    obtain ⟨s,hs,hsp⟩ := hc p hp
    exact ⟨s,hs,j.le_iff_le.mp (hsp.trans hpq),j.le_iff_le.mp (hsp.trans hpr)⟩
  · intro q r hqr hq
    exact PFilter.mem_of_le (j.monotone hqr) hq

def traceFilter (j : Q ↪o P) (G : PFilter P) (hc : CofinalTrace j G) : PFilter Q :=
  (trace_is_filter j G hc).toPFilter

theorem trace_filter_members (j : Q ↪o P) (G : PFilter P) (hc : CofinalTrace j G) (q : Q) :
    q ∈ traceFilter j G hc ↔ j q ∈ G := by rfl

def liftSet (j : Q ↪o P) (H : PFilter Q) : Set P := {p | ∃ q ∈ H, j q ≤ p}

theorem lift_is_filter (j : Q ↪o P) (H : PFilter Q) : IsPFilter (liftSet j H) := by
  apply IsPFilter.of_def
  · obtain ⟨q,hq⟩ := H.nonempty
    exact ⟨j q,q,hq,le_rfl⟩
  · rintro p ⟨q,hq,hqp⟩ r ⟨s,hs,hsr⟩
    obtain ⟨t,ht,htq,hts⟩ := H.directed q hq s hs
    exact ⟨j t,⟨t,ht,le_rfl⟩,(j.monotone htq).trans hqp,(j.monotone hts).trans hsr⟩
  · rintro p r hpr ⟨q,hq,hqp⟩
    exact ⟨q,hq,hqp.trans hpr⟩

def liftFilter (j : Q ↪o P) (H : PFilter Q) : PFilter P := (lift_is_filter j H).toPFilter

theorem lift_filter_members (j : Q ↪o P) (H : PFilter Q) (p : P) :
    p ∈ liftFilter j H ↔ ∃ q ∈ H, j q ≤ p := by rfl

theorem trace_lift_members (j : Q ↪o P) (H : PFilter Q) (q : Q) :
    j q ∈ liftFilter j H ↔ q ∈ H := by
  rw [lift_filter_members]
  constructor
  · rintro ⟨r,hr,hrq⟩
    exact PFilter.mem_of_le (j.le_iff_le.mp hrq) hr
  · intro hq
    exact ⟨q,hq,le_rfl⟩

theorem lift_trace_inverse (j : Q ↪o P) (G : PFilter P) (hc : CofinalTrace j G) :
    liftFilter j (traceFilter j G hc) = G := by
  apply PFilter.ext
  ext p
  change p ∈ liftFilter j (traceFilter j G hc) ↔ p ∈ G
  rw [lift_filter_members]
  constructor
  · rintro ⟨q,hq,hqp⟩
    exact PFilter.mem_of_le hqp ((trace_filter_members j G hc q).mp hq)
  · intro hp
    obtain ⟨q,hq,hqp⟩ := hc p hp
    exact ⟨q,(trace_filter_members j G hc q).mpr hq,hqp⟩

theorem lift_cofinal_trace (j : Q ↪o P) (H : PFilter Q) :
    CofinalTrace j (liftFilter j H) := by
  intro p hp
  obtain ⟨q,hq,hqp⟩ := (lift_filter_members j H p).mp hp
  exact ⟨q,(trace_lift_members j H q).mpr hq,hqp⟩

theorem trace_lift_inverse (j : Q ↪o P) (H : PFilter Q) :
    traceFilter j (liftFilter j H) (lift_cofinal_trace j H) = H := by
  apply PFilter.ext
  ext q
  change q ∈ traceFilter j (liftFilter j H) (lift_cofinal_trace j H) ↔ q ∈ H
  rw [trace_filter_members,trace_lift_members]

theorem dense_image_of_dense (j : Q ↪o P) (hj : DenseEmbedding j) (A : Set Q)
    (hA : Dense A) : Dense (j '' A) := by
  intro p
  obtain ⟨q,hq⟩ := hj p
  obtain ⟨r,hr,hrq⟩ := hA q
  exact ⟨j r,⟨r,hr,rfl⟩,(j.monotone hrq).trans hq⟩

theorem trace_generic (j : Q ↪o P) (hj : DenseEmbedding j)
    (G : PFilter P) (hc : CofinalTrace j G) (S : Set (Set P)) (T : Set (Set Q))
    (hG : GenericFor G S) (himages : ∀ A ∈ T, j '' A ∈ S) :
    GenericFor (traceFilter j G hc) T := by
  intro A hAT hA
  obtain ⟨p,hp,q,hq,rfl⟩ := hG _ (himages A hAT) (dense_image_of_dense j hj A hA)
  exact ⟨q,(trace_filter_members j G hc q).mpr hp,hq⟩

def densePullback (j : Q ↪o P) (E : Set P) : Set Q := {q | ∃ e ∈ E, j q ≤ e}

theorem dense_pullback_dense (j : Q ↪o P) (hj : DenseEmbedding j) (E : Set P)
    (hE : Dense E) : Dense (densePullback j E) := by
  intro q
  obtain ⟨e,he,heq⟩ := hE (j q)
  obtain ⟨r,hr⟩ := hj e
  exact ⟨r,⟨e,he,hr⟩,j.le_iff_le.mp (hr.trans heq)⟩

theorem lift_generic (j : Q ↪o P) (hj : DenseEmbedding j)
    (H : PFilter Q) (S : Set (Set P)) (T : Set (Set Q))
    (hH : GenericFor H T) (hpull : ∀ E ∈ S, densePullback j E ∈ T) :
    GenericFor (liftFilter j H) S := by
  intro E hES hE
  obtain ⟨q,hq,e,he,hqe⟩ := hH _ (hpull E hES) (dense_pullback_dense j hj E hE)
  exact ⟨e,(lift_filter_members j H e).mpr ⟨q,hq,hqe⟩,he⟩

/-- Factor through the actual image with the inherited order. -/
def imageOrderIso (j : Q ↪o P) : Q ≃o Set.range j where
  toEquiv := Equiv.ofInjective j j.injective
  map_rel_iff' := j.map_rel_iff

theorem image_order_iso_value (j : Q ↪o P) (q : Q) :
    (imageOrderIso j q).val = j q := by rfl

theorem image_density_transport (j : Q ↪o P) (A : Set Q) :
    Dense A ↔ Dense ((imageOrderIso j) '' A) := by
  constructor
  · intro h p
    obtain ⟨q,hq,hqp⟩ := h ((imageOrderIso j).symm p)
    exact ⟨imageOrderIso j q,⟨q,hq,rfl⟩,
      by simpa using (imageOrderIso j).monotone hqp⟩
  · intro h q
    obtain ⟨r,⟨s,hs,rfl⟩,hrq⟩ := h (imageOrderIso j q)
    exact ⟨s,hs,(imageOrderIso j).le_iff_le.mp hrq⟩

end
end Lemmatheca.SetTheory.DenseForcingPresentations
