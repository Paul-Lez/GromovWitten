/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCechBaseChangeCohomology
import GromovWitten.CategoryTheory.FibrewiseExactComplex
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreVanishing

/-!
# Vanishing for curve families with finite cohomology

A relatively flat quasi-coherent module on a curve family has cohomology zero
above degree one when its actual cohomology modules in those degrees are finite.
The proof uses a bounded flat finite affine Čech complex, its residue-field
comparison, and descending fibrewise exactness. Proper-family finite generation
is an explicit hypothesis here; it is not supplied by this theorem.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- If the actual base-linear cohomology modules of a family of curves are finite in
all degrees at least two and the relative stalks of a quasi-coherent module are flat,
then those cohomology modules vanish in those degrees. -/
theorem family_cohomology_isZero_of_finite
    [IsNoetherianRing R]
    (s : X ⟶ Spec R) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, 2 ≤ n →
      Module.Finite R (cohomologyModuleCat R s M n)) :
    ∀ n : ℕ, 2 ≤ n → IsZero (cohomologyModuleCat R s M n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨U, hU, hcover⟩ := exists_list_affine_cover (X := X)
  let K := baseFiniteCechComplex s M U
  have hflatK : ∀ n : ℕ, Module.Flat R (K.X n) := by
    intro n
    exact baseFiniteCechComplex_flat s M U hU hflat (n : ℤ)
  have htail : ∀ n : ℕ, U.length ≤ n → IsZero (K.X n) := by
    intro n hn
    apply baseFiniteCechComplex_bounded s M U (n : ℤ)
    right
    exact_mod_cast hn
  have hfiniteK : ∀ n : ℕ, 2 ≤ n → Module.Finite R (K.homology (n : ℤ)) := by
    intro n hn
    let : Module.Finite R (cohomologyModuleCat R s M n) := hfinite n hn
    exact Module.Finite.equiv
      (baseFiniteCechHomologyIso s M U hU hcover n).symm.toLinearEquiv
  have hfibres : ∀ q : PrimeSpectrum R, ∀ n : ℕ, 2 ≤ n →
      (((ModuleCat.extendScalars (algebraMap R q.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt (n : ℤ) := by
    intro q n hn
    let φ : R ⟶ CommRingCat.of q.asIdeal.ResidueField :=
      CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
    let p := Limits.pullback.fst s (Spec.map φ)
    let g := Limits.pullback.snd s (Spec.map φ)
    let h : IsPullback p g s (Spec.map φ) := IsPullback.of_hasPullback _ _
    let : IsLocallyNoetherian (Limits.pullback s (Spec.map φ)) :=
      LocallyOfFiniteType.isLocallyNoetherian g
    let Mq := (Scheme.Modules.pullback p).obj M
    have hzeroFibreCohom : IsZero
        (cohomologyModuleCat q.asIdeal.ResidueField g Mq n) := by
      have hn' : n - 2 + 2 = n := by omega
      simpa [affineBaseFibreCohomology, p, g, Mq, hn'] using
        (affineBaseFibreCohomology_isZero s M q (n - 2))
    have hzeroSource : IsZero
        ((((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology (n : ℤ)) :=
      IsZero.of_iso hzeroFibreCohom
        (finiteCechBaseChangeHomologyIso s φ p g h M U hU hcover n)
    exact ((((ModuleCat.extendScalars φ.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).exactAt_iff_isZero_homology (n : ℤ)).2 hzeroSource
  have hexact := CochainComplex.bounded_flat_fibrewise_exact_tail
    K hflatK U.length htail 2 hfiniteK hfibres
  intro n hn
  have hzeroK : IsZero (K.homology (n : ℤ)) :=
    (K.exactAt_iff_isZero_homology (n : ℤ)).1 (hexact n hn)
  exact IsZero.of_iso hzeroK (baseFiniteCechHomologyIso s M U hU hcover n).symm

end GromovWitten.AlgebraicGeometry.Curves

end
