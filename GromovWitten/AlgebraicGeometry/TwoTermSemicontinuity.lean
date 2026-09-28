/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus
import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.Algebra.ModuleCatScalarExtension
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Semicontinuity for finite two-term complexes

The fibre dimension of a finitely presented module is upper semicontinuous.  For a
flat two-term complex with finite kernel and cokernel over a Noetherian ring, the
finite projective replacement reduces the corresponding fibre-kernel statement to
the finite-projective homology locus theorem.
-/

open CategoryTheory Limits
open scoped TensorProduct
open GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus
open GromovWitten.AlgebraicGeometry.FiniteProjectiveHomologyLocus

universe u
noncomputable section

namespace GromovWitten.AlgebraicGeometry

variable {R : Type u} [CommRing R]
variable {A B : ModuleCat.{u} R} (d : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveKernelSemicont [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (kernel (C := ModuleCat.{u} p.asIdeal.ResidueField)
          ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map d) : Type u)) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (0 : ModuleCat.of R PUnit ⟶ A) d (by simp)
  have h := upperSemicontinuous_fibreHomologyFinrank_of_finite_projective (S := S)
  convert h using 1
  funext p
  let E := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  let T := S.map E
  have hf : T.f = 0 := E.map_zero _ _
  let e : T.homology ≅ kernel (E.map d) :=
    (ShortComplex.LeftHomologyData.ofHasKernel T hf).homologyIso
  exact e.toLinearEquiv.finrank_eq.symm

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveCokerSemicont [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (cokernel (C := ModuleCat.{u} p.asIdeal.ResidueField)
          ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map d) : Type u)) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk d (0 : B ⟶ ModuleCat.of R PUnit) (by simp)
  have h := upperSemicontinuous_fibreHomologyFinrank_of_finite_projective (S := S)
  convert h using 1
  funext p
  let E := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  let T := S.map E
  have hg : T.g = 0 := E.map_zero _ _
  let e : T.homology ≅ cokernel (E.map d) :=
    (ShortComplex.LeftHomologyData.ofHasCokernel T hg).homologyIso
  exact e.toLinearEquiv.finrank_eq.symm

set_option backward.isDefEq.respectTransparency false in
/-- Fibre dimensions of a finitely presented module are upper semicontinuous. -/
theorem upperSemicontinuous_fibreFinrank_of_finitePresentation
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] M)) := by
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let d : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom g
  let e : cokernel d ≅ M :=
    ModuleCat.cokernelIsoRangeQuotient d ≪≫
      LinearEquiv.toModuleIso ((Submodule.quotEquivOfEq _ _
        (LinearMap.exact_iff.mp hgf).symm).trans (f.quotKerEquivOfSurjective hf))
  have h := projectiveCokerSemicont d
  convert h using 1
  funext p
  let E := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  let e' : cokernel (E.map d) ≅ ModuleCat.of p.asIdeal.ResidueField
      (p.asIdeal.ResidueField ⊗[R] M) :=
    (PreservesCokernel.iso E d).symm ≪≫ E.mapIso e ≪≫ ModuleCat.extendScalarsAlgebraIso M
  exact e'.toLinearEquiv.finrank_eq.symm

set_option backward.isDefEq.respectTransparency false in
/-- Fibre kernel dimensions are upper semicontinuous for flat finite-cohomology complexes. -/
theorem upperSemicontinuous_fibreKernelFinrank_of_flat_finite_cohomology
    [IsNoetherianRing R] [Module.Flat R A] [Module.Flat R B]
    [Module.Finite R d.hom.ker] [Module.Finite R (B ⧸ d.hom.range)] :
    UpperSemicontinuous (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (kernel (C := ModuleCat.{u} p.asIdeal.ResidueField)
          ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map d) : Type u)) := by
  obtain ⟨n, q, hq, hflat, hfinite, hproj⟩ := d.hom.exists_finiteFlatTwoTerm
  let K := LinearMap.ker (LinearMap.finiteFlatTwoTermMap d.hom q)
  let : Module.Finite R K := hfinite
  let : Module.Projective R K := hproj
  let d' := ModuleCat.ofHom (LinearMap.finiteFlatTwoTermDifferential d.hom q)
  have h := projectiveKernelSemicont d'
  convert h using 1
  funext p
  let E := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  let c := kernel.map (E.map d') (E.map d)
    (E.map (ModuleCat.ofHom (LinearMap.finiteFlatTwoTermLeft d.hom q)))
    (E.map (ModuleCat.ofHom q))
    (LinearMap.finiteFlatTwoTerm_extendScalars_isPullback
      (algebraMap R p.asIdeal.ResidueField) d.hom q hq).w
  have : IsIso c := LinearMap.finiteFlatTwoTerm_extendScalars_kernel_map_isIso
    (algebraMap R p.asIdeal.ResidueField) d.hom q hq
  exact (asIso c).toLinearEquiv.finrank_eq.symm

end GromovWitten.AlgebraicGeometry
