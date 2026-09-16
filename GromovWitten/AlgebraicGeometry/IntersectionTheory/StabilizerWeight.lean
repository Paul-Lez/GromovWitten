/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.EquivFin

/-!
# Rational stabilizer weights

For a finite constant group `G`, the fundamental zero-cycle of `BG` has degree `1 / |G|`.
This elementary normalization is the reason the first stack-Chow theory is rational rather than
integral.  The definition here is used as the numerical acceptance test for future pushforward
from Deligne--Mumford stacks.
-/

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-
Retired numerical placeholder.  Defining the degree of `BG` to be `1 / |G|` and proving the
formula by reflexivity is not a construction of a Chow-theoretic degree map.  The statement will
return with the stack Chow and proper-degree construction.

/-- Degree of the rational fundamental class of the classifying stack of a finite constant
group. -/
def classifyingStackDegree (G : Type u) [Group G] [Fintype G] : ℚ :=
  1 / (Fintype.card G : ℚ)

theorem classifyingStackDegree_formula (G : Type u) [Group G] [Fintype G] :
    classifyingStackDegree G = 1 / (Fintype.card G : ℚ) :=
  rfl

theorem classifyingStackDegree_ne_zero (G : Type u) [Group G] [Fintype G] :
    classifyingStackDegree G ≠ 0 := by
  have hcard : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  exact div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr hcard)

/-- Multiplying by the stabilizer order removes the stack weight. -/
theorem card_mul_classifyingStackDegree (G : Type u) [Group G] [Fintype G] :
    (Fintype.card G : ℚ) * classifyingStackDegree G = 1 := by
  rw [classifyingStackDegree, one_div]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- A classifying stack with trivial stabilizer has ordinary degree one. -/
theorem classifyingStackDegree_eq_one_of_subsingleton
    (G : Type u) [Group G] [Fintype G] [Subsingleton G] :
    classifyingStackDegree G = 1 := by
  have hcard : Fintype.card G = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨1, fun g ↦ Subsingleton.elim g 1⟩
  simp [classifyingStackDegree, hcard]

-/

end GromovWitten.AlgebraicGeometry.IntersectionTheory
