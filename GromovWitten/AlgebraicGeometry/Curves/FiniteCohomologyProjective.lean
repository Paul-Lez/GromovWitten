/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyVanishing
import GromovWitten.AlgebraicGeometry.Curves.FiniteAffineCechCohomology
import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyGrauert
import GromovWitten.CategoryTheory.BoundedFlatBaseChange

/-!
# Projective cohomology with finite cohomology

A relatively flat quasi-coherent module on a curve family over a Noetherian
affine base has projective H⁰ if H⁰ is finite, H¹ is flat, and its actual higher
cohomology is finite. Over a reduced base, locally constant actual fibre H¹
dimensions give projectivity of both H⁰ and H¹ under finite cohomology.
Proper-family finite generation remains an explicit input.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} {X : Scheme.{u}}

/-- Actual degree-zero cohomology is projective when actual degree-one cohomology is flat,
provided actual degree-zero cohomology is finite and actual cohomology is finite in all
degrees at least two. -/
theorem family_projective_cohomology_zero_of_flat_one
    [CommRing R] [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteZero : Module.Finite R (cohomologyModuleCat R s M 0))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1)) :
    Module.Projective R (cohomologyModuleCat R s M 0) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨U, hU, hcover⟩ := exists_list_affine_cover (X := X)
  let K := baseFiniteCechComplex s M U
  let : CochainComplex.IsStrictlyGE K 0 := baseFiniteCechComplex_strictlyGE s M U
  have hflatK : ∀ n : ℕ, Module.Flat R (K.X n) := by
    intro n
    exact baseFiniteCechComplex_flat s M U hU hflat (n : ℤ)
  have htail : ∀ n : ℕ, U.length ≤ n → IsZero (K.X n) := by
    intro n hn
    apply baseFiniteCechComplex_bounded s M U (n : ℤ)
    right
    exact_mod_cast hn
  have hexact : ∀ n : ℕ, 2 ≤ n → K.ExactAt (n : ℤ) := by
    intro n hn
    exact (K.exactAt_iff_isZero_homology (n : ℤ)).2
      (IsZero.of_iso (family_cohomology_isZero_of_finite s M hflat hfiniteTail n hn)
        (baseFiniteCechHomologyIso s M U hU hcover n))
  let : Module.Flat R (cohomologyModuleCat R s M 1) := hflatOne
  let : Module.Flat R (K.homology (1 : ℤ)) :=
    Module.Flat.of_linearEquiv
      (baseFiniteCechHomologyIso s M U hU hcover 1).toLinearEquiv
  have hflatZeroK : Module.Flat R (K.homology (0 : ℤ)) :=
    CochainComplex.bounded_int_zero_homology_flat_of_flat_one
      K hflatK U.length htail hexact
  let : Module.Flat R (K.homology (0 : ℤ)) := hflatZeroK
  let : Module.Flat R (cohomologyModuleCat R s M 0) :=
    Module.Flat.of_linearEquiv
      (baseFiniteCechHomologyIso s M U hU hcover 0).symm.toLinearEquiv
  let : Module.Finite R (cohomologyModuleCat R s M 0) := hfiniteZero
  have : Module.FinitePresentation R (cohomologyModuleCat R s M 0) :=
    Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

/-- Under the same finite-cohomology and relative-flatness hypotheses, locally constant
actual fibre H¹ dimension over a reduced base makes both actual base H⁰ and H¹ projective. -/
theorem family_projective_cohomology_zero_and_one_of_locallyConstant_fibre
    [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfiniteTail : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hfiniteZero : Module.Finite R (cohomologyModuleCat R s M 0))
    (hfiniteOne : Module.Finite R (cohomologyModuleCat R s M 1))
    (hd : IsLocallyConstant (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 1))) :
    Module.Projective R (cohomologyModuleCat R s M 0) ∧
      Module.Projective R (cohomologyModuleCat R s M 1) := by
  have hp1 := family_projective_cohomology_one_of_locallyConstant_fibre
    s M hflat hfiniteTail hfiniteOne hd
  let : Module.Projective R (cohomologyModuleCat R s M 1) := hp1
  exact ⟨family_projective_cohomology_zero_of_flat_one
    s M hflat hfiniteTail hfiniteZero inferInstance, hp1⟩

end GromovWitten.AlgebraicGeometry.Curves

end
