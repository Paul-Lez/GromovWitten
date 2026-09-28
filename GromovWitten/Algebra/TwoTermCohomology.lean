/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.ProjectiveKernels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Projectivity of two-term cohomology

For a map between finite projective modules, flatness of its cokernel implies that its
kernel is finite projective. The cokernel is finitely presented, hence projective; splitting
the cokernel and image sequences makes the kernel a direct summand of the source.

The short-complex corollary uses actual categorical homology. It is the algebraic
local-freeness step for two-term finite-projective cohomology models; the geometric
construction and comparison of such models are separate requirements.
-/

namespace LinearMap
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- A map between finite projective modules with flat cokernel has finite projective kernel. -/
lemma finite_projective_ker_of_flat_cokernel (f : M →ₗ[R] N)
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Flat R (N ⧸ LinearMap.range f)] :
    Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  have : Module.FinitePresentation R (N ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_surjective (LinearMap.range f).mkQ
      (LinearMap.range f).mkQ_surjective (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range f)
  have : Module.Projective R (N ⧸ LinearMap.range f) :=
    Module.Flat.projective_of_finitePresentation
  have hproj := projective_ker_of_surjective (LinearMap.range f).mkQ
    (LinearMap.range f).mkQ_surjective
  rw [Submodule.ker_mkQ] at hproj
  have : Module.Projective R (LinearMap.range f) := hproj
  have hfin' := finite_ker_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have hproj' := projective_ker_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  rw [f.ker_rangeRestrict] at hfin' hproj'
  exact ⟨hfin', hproj'⟩

end LinearMap

open CategoryTheory Limits
namespace CategoryTheory.ShortComplex
variable {R : Type*} [CommRing R] (S : ShortComplex (ModuleCat R))

noncomputable section

/-- The degree-zero homology of a two-term finite-projective complex is finite projective
when its degree-one cohomology is flat. -/
lemma finite_projective_homology_of_flat_cokernel (hf : S.f = 0)
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    [Module.Flat R ((cokernel S.g : ModuleCat R) : Type _)] :
    Module.Finite R S.homology ∧ Module.Projective R S.homology := by
  have : Module.Flat R (S.X₃ ⧸ LinearMap.range S.g.hom) :=
    Module.Flat.of_linearEquiv (ModuleCat.cokernelIsoRangeQuotient S.g).toLinearEquiv.symm
  obtain ⟨hfin, hproj⟩ := S.g.hom.finite_projective_ker_of_flat_cokernel
  have := hfin
  have := hproj
  let e : S.homology ≅ ModuleCat.of R (LinearMap.ker S.g.hom) :=
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer S.g
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
    Module.Projective.of_equiv e.toLinearEquiv.symm⟩

end
end CategoryTheory.ShortComplex
