/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.FiniteProjectiveCohomologyModel
import GromovWitten.AlgebraicGeometry.TwoTermSemicontinuity

/-!
# Semicontinuity of fibre homology of bounded flat complexes

Compressing a bounded flat complex exact above degree one to a flat two-term
complex identifies its degree-zero homology after arbitrary scalar extension
with the kernel of the extended differential. Finite H⁰ and H¹ over a Noetherian
ring then give upper semicontinuity through the finite projective replacement.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry

open CochainComplex

/-- Degree-zero fibre homology is upper semicontinuous for a bounded flat complex
supported in nonnegative degrees, exact above one, with finite H⁰ and H¹. -/
theorem upperSemicontinuous_boundedFlat_fibreHomology_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [CochainComplex.IsStrictlyGE K 0]
    (hflat : ∀ n : ℕ, Module.Flat R (K.X n))
    (N : ℕ) (htail : ∀ n : ℕ, N ≤ n → IsZero (K.X n))
    (hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt n)
    (hfinite0 : Module.Finite R (K.homology 0 : ModuleCat R))
    (hfinite1 : Module.Finite R (K.homology 1 : ModuleCat R)) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R q.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj K).homology 0)) := by
  let d := bounded_int_flat_compression_d K
  let dcat := ModuleCat.ofHom d
  let : Module.Flat R (K.X 0) := hflat 0
  let : Module.Flat R (LinearMap.ker (K.d 1 2).hom) :=
    bounded_int_flat_compression_d_flat_target K hflat N htail hexact
  let : Module.Finite R (K.homology 0 : ModuleCat R) := hfinite0
  let : Module.Finite R (K.homology 1 : ModuleCat R) := hfinite1
  let : Module.Finite R (LinearMap.ker d) :=
    Module.Finite.equiv (bounded_int_flat_compression_kernel_homology_iso K).toLinearEquiv
  let e := bounded_int_flat_compression_cokernel_homology_iso K
  let : Module.Finite R (cokernel dcat : ModuleCat R) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Module.Finite R ((LinearMap.ker (K.d 1 2).hom) ⧸ LinearMap.range d) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient dcat).toLinearEquiv
  have h := upperSemicontinuous_fibreKernelFinrank_of_flat_finite_cohomology dcat
  convert h using 1
  funext q
  let E := ModuleCat.extendScalars (algebraMap R q.asIdeal.ResidueField)
  let e' := ModuleCat.kernelIsoKer (E.map dcat) ≪≫
    bounded_int_flat_compression_baseChange_h0Iso
      (algebraMap R q.asIdeal.ResidueField) K hflat N htail hexact
  exact e'.toLinearEquiv.finrank_eq.symm

end GromovWitten.AlgebraicGeometry
