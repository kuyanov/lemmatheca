import Lemmatheca.Absoluteness.Absoluteness

namespace Lemmatheca.SetTheory.Absoluteness
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
universe u

/-- All arguments are supplied candidates; the pair's two internal components
are bounded by the candidate ordered pair itself. -/
def orderedPairTest {n} (z x y : Fin n) : DeltaZero n :=
  .bex z (.bex z.castSucc
    (.conj (pairTest z.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))
      (.conj (pairTest (Fin.last n).castSucc x.castSucc.castSucc x.castSucc.castSucc)
        (pairTest (Fin.last (n+1)) x.castSucc.castSucc y.castSucc.castSucc))))

def relationTest {n} (x y R : Fin n) : DeltaZero n :=
  .bex R (orderedPairTest (Fin.last n) x.castSucc y.castSucc)


private theorem holds_conj {n} (p q : DeltaZero n) (a : Fin n → ZFSet.{u}) :
    (p.conj q).Holds (fun x y => x ∈ y) a ↔
      p.Holds (fun x y => x ∈ y) a ∧ q.Holds (fun x y => x ∈ y) a := by
  classical
  simp [DeltaZero.conj,DeltaZero.neg,DeltaZero.Holds]

private theorem holds_pair {n} (x y z : Fin n) (a : Fin n → ZFSet.{u}) :
    (pairTest x y z).Holds (fun x y => x ∈ y) a ↔ a x = {a y,a z} :=
  (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
    (pairTest_correct x y z a)

theorem orderedPairTest_correct {n} (z x y : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (orderedPairTest z x y).toShared a ↔
      a z = ZFSet.pair (a x) (a y) := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  simp only [orderedPairTest,DeltaZero.bex_realize,holds_conj,holds_pair,
    Fin.snoc_castSucc,Fin.snoc_last]
  constructor
  · rintro ⟨r,hr,s,hs,hz,hr',hs'⟩
    rw [hz,hr',hs',ZFSet.pair_eq_singleton]
    rfl
  · intro hz
    refine ⟨{a x},?_,{a x,a y},?_,?_,?_,rfl⟩
    · rw [hz]
      simp [ZFSet.pair]
    · rw [hz]
      simp [ZFSet.pair]
    · exact hz
    · exact (ZFSet.pair_eq_singleton _).symm

theorem relationTest_correct {n} (x y R : Fin n) (a : Fin n → ZFSet.{u}) :
    universeSatisfies (relationTest x y R).toShared a ↔
      ZFSet.pair (a x) (a y) ∈ a R := by
  classical
  apply (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).trans
  have hp {n} (z x y : Fin n) (a : Fin n → ZFSet.{u}) :
      (orderedPairTest z x y).Holds (fun x y => x ∈ y) a ↔ a z = ZFSet.pair (a x) (a y) :=
    (DeltaZero.toShared_realize (fun x y : ZFSet.{u} => x ∈ y) _ a).symm.trans
      (orderedPairTest_correct z x y a)
  simp only [relationTest,DeltaZero.bex_realize,hp,Fin.snoc_castSucc,Fin.snoc_last]
  simp only [exists_eq_right]


end Lemmatheca.SetTheory.Absoluteness
