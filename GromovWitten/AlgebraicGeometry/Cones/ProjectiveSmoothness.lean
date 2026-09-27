/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.SymmetricFunctoriality
import GromovWitten.Algebra.FinitePresentationRetract
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Smoothness of symmetric cones for projective modules

The symmetric algebra of an arbitrary projective module is formally smooth: a lift on the
degree-one module generators is supplied by projectivity and then extended by the universal
property of the symmetric algebra.  A finite projective module is a retract of a finite free
module, so its symmetric algebra is finitely presented as well.  The final section transports
this result across the scalar-extension equivalence from `SymmetricFunctoriality`.
-/

open CategoryTheory AlgebraicGeometry Polynomial
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.GradedCone

universe u v

section FormallySmooth

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]

/-- The symmetric algebra on a projective module has the infinitesimal lifting property.

Indeed, a map out of `SymmetricAlgebra R M` is determined by its restriction to `M`.  The
restriction can be lifted through a square-zero quotient because `M` is projective, and the
universal property of the symmetric algebra extends that linear lift to an algebra map.  Notice
that no finiteness, nilpotence, or freeness assumption on `M` is used here. -/
theorem formallySmooth_symmetricAlgebra :
    Algebra.FormallySmooth R (SymmetricAlgebra R M) := by
  rw [Algebra.FormallySmooth.iff_comp_surjective]
  intro B _ _ I hI f
  let q : B →ₗ[R] (B ⧸ I) := (Ideal.Quotient.mkₐ R I).toLinearMap
  let g : M →ₗ[R] (B ⧸ I) := f.toLinearMap.comp (SymmetricAlgebra.ι R M)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property q g
    (fun b => Ideal.Quotient.mk_surjective b)
  let F : SymmetricAlgebra R M →ₐ[R] B := SymmetricAlgebra.lift l
  refine ⟨F, ?_⟩
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  simpa [F, q, g, LinearMap.comp_apply] using LinearMap.congr_fun hl m

end FormallySmooth

section FiniteProjective

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The symmetric algebra of a finite projective module is a retract of a polynomial algebra.

The retraction is induced by a finite free presentation of the projective module.  This exposes
the finite-presentation part of smoothness without choosing a basis for `M` itself. -/
theorem finitePresentation_symmetricAlgebra [Module.Finite R M] [Module.Projective R M] :
    Algebra.FinitePresentation R (SymmetricAlgebra R M) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let p : SymmetricAlgebra R (Fin n → R) →ₐ[R] SymmetricAlgebra R M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp f)
  let i : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (Fin n → R) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (Fin n → R)).comp g)
  have hpi : p.comp i = AlgHom.id R (SymmetricAlgebra R M) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    dsimp [p, i]
    simp only [LinearMap.comp_apply, SymmetricAlgebra.lift_ι_apply]
    exact congrArg (SymmetricAlgebra.ι R M) (congrArg (fun k => k m) hfg)
  let _ : Algebra.Smooth R (SymmetricAlgebra R (Fin n → R)) :=
    smooth_symmetricAlgebra R (Fin n → R)
  exact GromovWitten.Algebra.finitePresentation_of_retraction p i hpi

/-- The symmetric algebra of a finite projective module is formally smooth and finitely
presented, hence smooth, over the base ring. -/
theorem smooth_symmetricAlgebra_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    Algebra.Smooth R (SymmetricAlgebra R M) where
  formallySmooth := formallySmooth_symmetricAlgebra
  finitePresentation := finitePresentation_symmetricAlgebra

end FiniteProjective

section SchemeProjection

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The affine cone attached to a finite projective module is a smooth scheme over the affine
base. -/
theorem smooth_projection_of_finite_projective
    [Module.Finite R M] [Module.Projective R M] :
    AlgebraicGeometry.Smooth (projection R (SymmetricAlgebra R M)) := by
  refine AlgebraicGeometry.HasRingHomProperty.Spec_iff.2 ?_
  exact RingHom.smooth_algebraMap.2
    (smooth_symmetricAlgebra_of_finite_projective (R := R) (M := M))

end SchemeProjection

section ScalarExtension

variable {R B M : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [AddCommGroup M] [Module R M]

/-- Smoothness of the symmetric cone is preserved by scalar extension.  The proof uses the
canonical algebra equivalence `B ⊗ Sym_R(M) ≃ Sym_B(B ⊗ M)` from `SymmetricFunctoriality` and the
base-change instance for algebraic smoothness. -/
theorem smooth_scalarExtension_symmetricAlgebra [Module.Finite R M] [Module.Projective R M] :
    Algebra.Smooth B (SymmetricAlgebra B (B ⊗[R] M)) := by
  let _ : Algebra.Smooth R (SymmetricAlgebra R M) :=
    smooth_symmetricAlgebra_of_finite_projective (R := R) (M := M)
  exact Algebra.Smooth.of_equiv (SymmetricFunctoriality.scalarExtensionEquiv R B M)

end ScalarExtension

end GromovWitten.AlgebraicGeometry.GradedCone
