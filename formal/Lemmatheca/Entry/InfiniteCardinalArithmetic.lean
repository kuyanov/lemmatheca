import Lemmatheca.SetTheory.InfiniteCardinalArithmetic
import Lemmatheca.SetTheory.Choice

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.InfiniteCardinalArithmetic
open Lemmatheca.SetTheory.InfiniteCardinalArithmetic
open Set Function Ordinal Order
open scoped Ordinal
universe u

theorem shellRank_figure :
    (List.range 5).map (fun i => (List.range 5).map (fun j => shellRank (i, j))) =
      [[0, 1, 4, 9, 16], [2, 3, 5, 10, 17], [6, 7, 8, 11, 18],
       [12, 13, 14, 15, 19], [20, 21, 22, 23, 24]] := by decide +kernel

end Lemmatheca.Entry.InfiniteCardinalArithmetic
