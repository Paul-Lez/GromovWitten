/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyVanishing
import GromovWitten.AlgebraicGeometry.Curves.FiniteCechBaseChangeCohomology
import GromovWitten.CategoryTheory.BoundedFlatBaseChange

/-!
# Base change with finite cohomology

For a relatively flat quasi-coherent module on a curve family over a Noetherian
ring, finite actual cohomology above degree one gives positive-degree base-change
isomorphisms. Flat actual degree-one cohomology also gives a degree-zero
isomorphism. The target scheme is assumed locally Noetherian.

These are object isomorphisms constructed through finite affine Čech complexes.
Identification with the canonical sheaf or derived comparison is separate, as is
proper-family finite generation.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}

private theorem finiteCech_exactAt_ge_two_of_finite_actual_cohomology
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hcover : coverUnion U = ⊤) :
    ∀ n : ℕ, 2 ≤ n → (baseFiniteCechComplex s M U).ExactAt (n : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  intro n hn
  exact ((baseFiniteCechComplex s M U).exactAt_iff_isZero_homology (n : ℤ)).2
    (IsZero.of_iso (family_cohomology_isZero_of_finite s M hflat hfinite n hn)
      (baseFiniteCechHomologyIso s M U hU hcover n))

/-- In positive degrees, scalar extension of actual cohomology is isomorphic to
actual cohomology on a base change. This is an object isomorphism; it does not assert
that this isomorphism is induced by a canonical sheaf or derived base-change map. -/
noncomputable def family_cohomology_baseChangeIso_pos
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    [IsLocallyNoetherian Y] (n : ℕ) (hn : 1 ≤ n) :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M n) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) n := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hcoverExists := exists_list_affine_cover (X := X)
  let U := Classical.choose hcoverExists
  have hcoverSpec := Classical.choose_spec hcoverExists
  have hU : ∀ W ∈ U, IsAffineOpen W := hcoverSpec.1
  have hcover : coverUnion U = ⊤ := hcoverSpec.2
  let K := baseFiniteCechComplex s M U
  have hflatK : ∀ i : ℕ, Module.Flat R (K.X i) := by
    intro i
    exact baseFiniteCechComplex_flat s M U hU hflat (i : ℤ)
  have htail : ∀ i : ℕ, U.length ≤ i → IsZero (K.X i) := by
    intro i hi
    apply baseFiniteCechComplex_bounded s M U (i : ℤ)
    right
    exact_mod_cast hi
  have hexact : ∀ i : ℕ, 2 ≤ i → K.ExactAt (i : ℤ) :=
    finiteCech_exactAt_ge_two_of_finite_actual_cohomology
      s M hflat hfinite U hU hcover
  have hcmp : IsIso
      (K.homologyComparison (ModuleCat.extendScalars φ.hom) (n : ℤ)) :=
    CochainComplex.bounded_int_positive_homologyComparison_isIso
      φ.hom K hflatK U.length htail hexact n hn
  let : IsIso (K.homologyComparison (ModuleCat.extendScalars φ.hom) (n : ℤ)) := hcmp
  exact (ModuleCat.extendScalars φ.hom).mapIso
      (baseFiniteCechHomologyIso s M U hU hcover n).symm ≪≫
    asIso (K.homologyComparison (ModuleCat.extendScalars φ.hom) (n : ℤ)) ≪≫
    finiteCechBaseChangeHomologyIso s φ p g h M U hU hcover n

/-- Degree-zero actual cohomology commutes with base change if actual degree-one
cohomology is flat over the original Noetherian base. This is again only an object
isomorphism, with no asserted identification with a canonical sheaf or derived comparison. -/
noncomputable def family_cohomology_baseChangeIso_zero_of_flat_one
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (φ : R ⟶ T) (p : Y ⟶ X) (g : Y ⟶ Spec T)
    (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n))
    (hflatOne : Module.Flat R (cohomologyModuleCat R s M 1))
    [IsLocallyNoetherian Y] :
    (ModuleCat.extendScalars φ.hom).obj (cohomologyModuleCat R s M 0) ≅
      cohomologyModuleCat T g ((Scheme.Modules.pullback p).obj M) 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hcoverExists := exists_list_affine_cover (X := X)
  let U := Classical.choose hcoverExists
  have hcoverSpec := Classical.choose_spec hcoverExists
  have hU : ∀ W ∈ U, IsAffineOpen W := hcoverSpec.1
  have hcover : coverUnion U = ⊤ := hcoverSpec.2
  let K := baseFiniteCechComplex s M U
  have hflatK : ∀ i : ℕ, Module.Flat R (K.X i) := by
    intro i
    exact baseFiniteCechComplex_flat s M U hU hflat (i : ℤ)
  have htail : ∀ i : ℕ, U.length ≤ i → IsZero (K.X i) := by
    intro i hi
    apply baseFiniteCechComplex_bounded s M U (i : ℤ)
    right
    exact_mod_cast hi
  have hexact : ∀ i : ℕ, 2 ≤ i → K.ExactAt (i : ℤ) :=
    finiteCech_exactAt_ge_two_of_finite_actual_cohomology
      s M hflat hfinite U hU hcover
  let : Module.Flat R (cohomologyModuleCat R s M 1) := hflatOne
  let : Module.Flat R (K.homology (1 : ℤ)) :=
    Module.Flat.of_linearEquiv
      (baseFiniteCechHomologyIso s M U hU hcover 1).toLinearEquiv
  have hcmp : IsIso (K.homologyComparison (ModuleCat.extendScalars φ.hom) (0 : ℤ)) := by
    exact CochainComplex.bounded_int_zero_homologyComparison_isIso_of_flat_one
      φ.hom K hflatK U.length htail hexact
  let : IsIso (K.homologyComparison (ModuleCat.extendScalars φ.hom) (0 : ℤ)) := hcmp
  exact (ModuleCat.extendScalars φ.hom).mapIso
      (baseFiniteCechHomologyIso s M U hU hcover 0).symm ≪≫
    asIso (K.homologyComparison (ModuleCat.extendScalars φ.hom) (0 : ℤ)) ≪≫
    finiteCechBaseChangeHomologyIso s φ p g h M U hU hcover 0

end GromovWitten.AlgebraicGeometry.Curves

end
