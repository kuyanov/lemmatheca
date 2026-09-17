# A lower bound for a triple sumset

Let \(A,B,C\) be finite nonempty subsets of an additive abelian group. With
\(A+B+C=(A+B)+C\), we have

\[
|A+B+C|\geq\max\{|A|,|B|,|C|\}.
\]

Apply [Sumset lower bound](lower-bound.md) twice. The full
[human proof](proofs/triple-lower-bound.md) follows the same steps as
`Lemmatheca.triple_sumset_card_lower_bound` in Lean.

Each nonemptiness assumption matters: an empty summand makes the triple sumset
empty, even if one of the other summands is nonempty.
