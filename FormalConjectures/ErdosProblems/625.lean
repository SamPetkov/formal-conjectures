/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 625

*References:*
- [erdosproblems.com/625](https://www.erdosproblems.com/625)
- [ErGi93] P. Erdős and J. Gimbel, *Some problems and results in cochromatic theory*.
  Annals of Discrete Mathematics 55 (1993), 261–264.
- [Bo88] B. Bollobás, *The chromatic number of random graphs*. Combinatorica (1988),
  49–55.
- [Gi16] J. Gimbel, *Some of my favorite coloring problems for graphs and digraphs*.
  Graph Theory: Favorite Conjectures and Open Problems 1 (2016), 95–108.
- [He24] A. Heckel, *On a question of Erdős and Gimbel on the cochromatic number* (2024),
  [arXiv:2408.13839](https://arxiv.org/abs/2408.13839).
- [He24c] A. Heckel, *The difference between the chromatic and the cochromatic number of a
  random graph* (2024), [arXiv:2409.17614](https://arxiv.org/abs/2409.17614).
- [St24b] R. Steiner, *On the difference between the chromatic and cochromatic number* (2024),
  [arXiv:2408.02400](https://arxiv.org/abs/2408.02400).
-/

open Filter
open scoped Topology

namespace Erdos625

/-- The event that the chromatic number exceeds the cochromatic number by at
least `M`.  Writing the inequality as `M + ζ(G) ≤ χ(G)` avoids truncated
natural-number subtraction. -/
def GapAtLeast {V : Type*} (G : SimpleGraph V) (M : ℕ) : Prop :=
  (M : ℕ∞) + G.cochromaticNumber ≤ G.chromaticNumber

/-- Under `G(n, 1 / 2)`, the probability that the chromatic–cochromatic gap is
at least `M`.  At edge probability `1 / 2`, all labelled simple graphs on
`Fin n` are equally likely, so this counting ratio is exactly the desired
probability. -/
noncomputable def gapProbability (M n : ℕ) : ℝ := by
  classical
  exact
    ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => GapAtLeast G M)).card : ℝ) /
      (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/--
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed
to colour the vertices of $G$ such that each colour class induces either a complete graph or
empty graph. Let $\chi(G)$ denote the chromatic number.

If $G$ is a random graph with $n$ vertices and each edge included independently with probability
$1/2$ then is it true that almost surely
\[
\chi(G) - \zeta(G) \to \infty
\]
as $n\to\infty$?

The formal statement interprets "almost surely" in the standard asymptotic random-graph sense:
for every fixed natural number $M$, the probability of
$M + \zeta(G) \leq \chi(G)$ tends to one along the full sequence of natural numbers.

This is [Erdős Problem 625](https://www.erdosproblems.com/625) [ErGi93].
-/
@[category research open, AMS 5 60]
theorem erdos_625 : answer(sorry) ↔
    ∀ M : ℕ, Tendsto (gapProbability M) atTop (𝓝 1) := by
  sorry

end Erdos625
