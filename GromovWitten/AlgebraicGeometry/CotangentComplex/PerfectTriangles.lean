/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectRank

/-!
# Perfect objects and distinguished triangles

The affine definition of `IsPerfect` in `PerfectComplex` is represented by a bounded complex of
finite free modules.  This file records the derived triangulated closure of that definition.  The
mapping-cone argument is already available in `PerfectDual`: K-projectivity realises the first map
of a distinguished triangle by a chain map, and the comparison theorem identifies its cone with the
third vertex.  Here we use the unconditional rank-independence theorem from `PerfectRank` to turn
the corresponding representative-level cone calculation into additivity for perfect objects.

This is the global strictly-perfect affine model.  It does not claim that an arbitrary locally
perfect object has a global finite free representative.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

section Derived

attribute [local instance] HasDerivedCategory.standard

/-! ## Rank additivity -/

/-- The rank of perfect objects is additive in a distinguished triangle.  The first two vertices
are represented by strictly perfect complexes `K` and `L`; K-projectivity realises the derived
morphism by a chain map `φ`, and the mapping cone of `φ` represents the third vertex.  The
representative-level identity `rank (Cone φ) = rank L - rank K` is then transported to the three
perfect-object ranks using `IsPerfect.rank_eq_of_rep'`. -/
theorem IsPerfect.rank_add_of_distTriang [Nontrivial R]
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    h₂.rank = h₁.rank + h₃.rank := by
  let h₁' := h₁
  let h₂' := h₂
  obtain ⟨K, hK, ⟨e⟩⟩ := h₁'
  obtain ⟨L, hL, ⟨e'⟩⟩ := h₂'
  obtain ⟨φ, ⟨f⟩⟩ := exists_mappingCone_iso_of_distTriang T hT hK e e'
  have hCone : IsStrictlyPerfect (CochainComplex.mappingCone φ) :=
    isStrictlyPerfect_mappingCone φ hK hL
  have hKrank : PerfectComplex.rank K = h₁.rank :=
    IsPerfect.rank_eq_of_rep' h₁ hK e
  have hLrank : PerfectComplex.rank L = h₂.rank :=
    IsPerfect.rank_eq_of_rep' h₂ hL e'
  have hConerank : PerfectComplex.rank (CochainComplex.mappingCone φ) = h₃.rank :=
    IsPerfect.rank_eq_of_rep' h₃ hCone f
  rw [← hLrank, ← hKrank, ← hConerank]
  rw [rank_mappingCone φ hK hL]
  ring

end Derived

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
