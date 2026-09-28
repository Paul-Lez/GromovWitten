/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.TensorKernel
import GromovWitten.Algebra.ReducedFibreFlatness
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Flat and projective terms in a two-term Grauert calculation

For a two-term complex of flat modules over a reduced Noetherian ring, locally
constant residue-field dimension of the finite cokernel gives flatness of the
cokernel.  The flat-kernel lemma then gives the same conclusion for the kernel,
and finite presentation upgrades the kernel to a projective module.  The
scalar-extension statement is recorded separately under its weaker hypotheses.
-/

noncomputable section

namespace GromovWitten.Algebra

open TensorProduct

universe u v w

variable {R : Type u} [CommRing R] [IsReduced R]
variable {A : Type v} [AddCommGroup A] [Module R A]
variable {B : Type v} [AddCommGroup B] [Module R B]

namespace LinearMap

/-- Locally constant finite cokernel fibres make the kernel flat. -/
theorem kernel_flat_of_locallyConstant_fibre
    (d : A →ₗ[R] B)
    [Module.Flat R A] [Module.Flat R B]
    [Module.Finite R (B ⧸ LinearMap.range d)]
    (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (B ⧸ LinearMap.range d)))) :
    Module.Flat R (LinearMap.ker d) := by
  let _ : Module.Flat R (B ⧸ LinearMap.range d) :=
    reduced_fibre_flat hd
  exact d.kernel_flat_of_flat_source_of_flat_target_of_flat_cokernel

/-- Under Noetherianity and finite kernel, the flat kernel is projective. -/
theorem kernel_projective_of_locallyConstant_fibre
    [IsNoetherianRing R]
    (d : A →ₗ[R] B)
    [Module.Flat R A] [Module.Flat R B]
    [Module.Finite R (LinearMap.ker d)]
    [Module.Finite R (B ⧸ LinearMap.range d)]
    (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (B ⧸ LinearMap.range d)))) :
    Module.Projective R (LinearMap.ker d) := by
  let _ : Module.Flat R (LinearMap.ker d) :=
    kernel_flat_of_locallyConstant_fibre d hd
  let _ : Module.FinitePresentation R (LinearMap.ker d) :=
    Module.finitePresentation_of_finite R (LinearMap.ker d)
  exact Module.Flat.projective_of_finitePresentation

/-- The canonical tensor-kernel comparison is bijective over every `R`-algebra.

Only flatness of the target and finite locally constant cokernel fibres are
needed here; no assumptions on the source, its kernel, or Noetherianity enter.
-/
theorem tensorKer_bijective_of_locallyConstant_cokernel_fibre
    {T : Type w} [CommRing T] [Algebra R T]
    (d : A →ₗ[R] B)
    [Module.Flat R B]
    [Module.Finite R (B ⧸ LinearMap.range d)]
    (hd : IsLocallyConstant (fun p : PrimeSpectrum R =>
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (B ⧸ LinearMap.range d)))) :
    Function.Bijective (LinearMap.tensorKer T T d) := by
  let _ : Module.Flat R (B ⧸ LinearMap.range d) :=
    reduced_fibre_flat hd
  exact LinearMap.tensorKer_bijective_of_target_flat_of_cokernel_flat d

end LinearMap

end GromovWitten.Algebra
