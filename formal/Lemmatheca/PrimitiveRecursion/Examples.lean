import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion

namespace Lemmatheca.Entry.PrimitiveRecursion

theorem power_trace :
    (List.range 5).map (fun n => (3 : ℕ) ^ n) = [1, 3, 9, 27, 81] := by
  norm_num [List.range_succ]

end Lemmatheca.Entry.PrimitiveRecursion
