/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StabilityGraph
import GromovWitten.AlgebraicGeometry.Curves.StableMaps.DecoratedGraph

/-!
# The numerical `2g - 2 + n > 0` stability criterion

This file removes the redundant `arithmeticGenus` conjuncts from the unpointed stability
criteria of `StabilityGraph.lean`: since the total canonical degree is `2g - 2` and the vertex
set is nonempty, the genus bound is *derivable* from pointwise positivity (resp.
nonnegativity) of the canonical degree, rather than needing to be assumed separately. This is
exactly the classical "`2g - 2 + n > 0`" numerical stability test, phrased combinatorially.

We also connect the pointed (`DecoratedGraph`) log-canonical degree to the unpointed one:
`sum_logCanonicalDegree` already shows the vertex sum is `2g - 2 + (number of legs)`
(`StableMaps/DecoratedGraph.lean`), and here we show it agrees with the unpointed canonical
degree whenever there are no legs, so that `IsPointedStable` specialises to `DualGraph.IsStable`
in that case.
-/

namespace GromovWitten.AlgebraicGeometry.Curves

namespace DualGraph

/-- A dual graph is (unpointed) stable iff every component has positive canonical degree.
The `2 ≤ arithmeticGenus` conjunct of `IsStable` is derivable from pointwise positivity via
`sum_canonicalDegree` and the nonemptiness of the vertex set, so it need not be assumed. -/
theorem isStable_iff_forall_canonicalDegree_pos (G : DualGraph) :
    G.IsStable ↔ ∀ v, 0 < G.canonicalDegree v := by
  rw [G.isStable_iff_canonicalDegree_pos]
  refine ⟨fun h ↦ h.2, fun hdeg ↦ ⟨?_, hdeg⟩⟩
  have h1 : ∀ v ∈ (Finset.univ : Finset G.Vertex), (1 : ℤ) ≤ G.canonicalDegree v :=
    fun v _ ↦ hdeg v
  have hsum_le : (Fintype.card G.Vertex : ℤ) ≤ ∑ v, G.canonicalDegree v := by
    have h2 := Finset.sum_le_sum h1
    simpa [Finset.card_univ] using h2
  rw [G.sum_canonicalDegree] at hsum_le
  have hcard : 0 < Fintype.card G.Vertex := Fintype.card_pos
  omega

/-- A dual graph is (unpointed) semistable iff every component has nonnegative canonical
degree. The `1 ≤ arithmeticGenus` conjunct of `IsSemistable` is derivable from pointwise
nonnegativity via `sum_canonicalDegree`, so it need not be assumed. -/
theorem isSemistable_iff_forall_canonicalDegree_nonneg (G : DualGraph) :
    G.IsSemistable ↔ ∀ v, 0 ≤ G.canonicalDegree v := by
  rw [G.isSemistable_iff_canonicalDegree_nonneg]
  refine ⟨fun h ↦ h.2, fun hdeg ↦ ⟨?_, hdeg⟩⟩
  have h1 : ∀ v ∈ (Finset.univ : Finset G.Vertex), (0 : ℤ) ≤ G.canonicalDegree v :=
    fun v _ ↦ hdeg v
  have hsum_le : (0 : ℤ) ≤ ∑ v, G.canonicalDegree v := by
    have h2 := Finset.sum_le_sum h1
    simpa using h2
  rw [G.sum_canonicalDegree] at hsum_le
  omega

/-- A stable dual graph is semistable. -/
theorem isSemistable_of_isStable (G : DualGraph) (h : G.IsStable) : G.IsSemistable :=
  ⟨le_trans (by norm_num) h.1, fun v ↦ (h.2 v).1⟩

end DualGraph

end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves.StableMaps

open GromovWitten.AlgebraicGeometry.Curves

namespace DecoratedGraph

/-- With no marking legs, the log-canonical degree agrees with the unpointed canonical
degree of the underlying dual graph. -/
theorem logCanonicalDegree_eq_canonicalDegree_of_isEmpty_leg (G : DecoratedGraph)
    [IsEmpty G.Leg] (v : G.toDualGraph.Vertex) :
    G.logCanonicalDegree v = G.toDualGraph.canonicalDegree v := by
  have hmarking : G.markingCount v = 0 := by
    simp [markingCount, markingsAt, Finset.univ_eq_empty]
  simp [logCanonicalDegree, specialFlagCount, DualGraph.canonicalDegree, hmarking]

/-- With no marking legs, pointed stability specialises to the unpointed numerical criterion
on the underlying dual graph. -/
theorem isPointedStable_iff_isStable_of_isEmpty_leg (G : DecoratedGraph) [IsEmpty G.Leg] :
    G.IsPointedStable ↔ G.toDualGraph.IsStable := by
  rw [G.toDualGraph.isStable_iff_forall_canonicalDegree_pos]
  unfold IsPointedStable
  refine ⟨fun h v ↦ ?_, fun h v ↦ ?_⟩
  · rw [← G.logCanonicalDegree_eq_canonicalDegree_of_isEmpty_leg v]
    exact h v
  · rw [G.logCanonicalDegree_eq_canonicalDegree_of_isEmpty_leg v]
    exact h v

end DecoratedGraph

end GromovWitten.AlgebraicGeometry.Curves.StableMaps
