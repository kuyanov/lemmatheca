# Apply the sumset lemma twice

Set \(D=A+B\). It is finite, and it is nonempty: choose \(a\in A\) and
\(b\in B\), so that \(a+b\in D\).

Applying [Sumset lower bound](../lower-bound.md) to \(A,B\) gives

\[
|D|\geq\max\{|A|,|B|\}.
\]

Apply the same lemma again, this time to \(D,C\):

\[
|D+C|\geq\max\{|D|,|C|\}.
\]

Thus \(|D+C|\) is at least \(|D|\), hence at least each of \(|A|\) and
\(|B|\), and it is also at least \(|C|\). Since \(D+C=A+B+C\),

\[
|A+B+C|\geq\max\{|A|,|B|,|C|\}.
\]
