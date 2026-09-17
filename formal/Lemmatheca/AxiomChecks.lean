import Lemmatheca.Combinatorics.Additive.Sumsets

/-!
These checks fail the build if the reported axiom dependencies change. They are
checks for the three example theorems, not the planned full dependency auditor.
-/

/-- info: 'Lemmatheca.translate_mem_sumset' does not depend on any axioms -/
#guard_msgs in
#print axioms Lemmatheca.translate_mem_sumset

/-- info: 'Lemmatheca.translate_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lemmatheca.translate_injective

/-- info: 'Lemmatheca.example_sumset' does not depend on any axioms -/
#guard_msgs in
#print axioms Lemmatheca.example_sumset
