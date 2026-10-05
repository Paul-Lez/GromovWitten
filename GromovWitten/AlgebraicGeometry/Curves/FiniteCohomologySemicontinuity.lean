/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FiniteCohomologyVanishing
import GromovWitten.AlgebraicGeometry.Curves.FiniteCechBaseChangeCohomology
import GromovWitten.AlgebraicGeometry.Curves.AffineBaseFibreCohomology
import GromovWitten.AlgebraicGeometry.BoundedCohomologySemicontinuity

/-!
# Degree-zero semicontinuity with finite cohomology

The dimensions of actual H⁰ on the scheme-theoretic fibres of a curve family
are upper semicontinuous when the module is relatively flat and actual base
cohomology is finite. A bounded flat Čech complex supplies the finite two-term
calculation; no flatness of H¹ is required. Proper-family finite generation
is an explicit hypothesis, not a conclusion here.
-/

open CategoryTheory Limits HomologicalComplex Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- For a flat quasi-coherent module on a curve family, actual degree-zero cohomology
of the scheme-theoretic fibres has upper semicontinuous dimension, assuming actual
base cohomology is finite in every degree. -/
theorem upperSemicontinuous_familyAffineBaseFibreCohomology_zero
    [IsNoetherianRing R]
    (s : X ⟶ Spec (CommRingCat.of R)) [FamilyOfCurves s]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x))
    (hfinite : ∀ n : ℕ, Module.Finite R (cohomologyModuleCat R s M n)) :
    UpperSemicontinuous (fun q : PrimeSpectrum R =>
      Module.finrank q.asIdeal.ResidueField (affineBaseFibreCohomology s M q 0)) := by
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
      (IsZero.of_iso (family_cohomology_isZero_of_finite s M hflat
        (fun k _ => hfinite k) n hn)
        (baseFiniteCechHomologyIso s M U hU hcover n))
  have hfinite0 : Module.Finite R (K.homology 0 : ModuleCat R) := by
    let : Module.Finite R (cohomologyModuleCat R s M 0) := hfinite 0
    exact Module.Finite.equiv
      (baseFiniteCechHomologyIso s M U hU hcover 0).symm.toLinearEquiv
  have hfinite1 : Module.Finite R (K.homology 1 : ModuleCat R) := by
    let : Module.Finite R (cohomologyModuleCat R s M 1) := hfinite 1
    exact Module.Finite.equiv
      (baseFiniteCechHomologyIso s M U hU hcover 1).symm.toLinearEquiv
  have h := GromovWitten.AlgebraicGeometry.upperSemicontinuous_boundedFlat_fibreHomology_zero
    K hflatK U.length htail hexact hfinite0 hfinite1
  convert h using 1
  funext q
  let φ : CommRingCat.of R ⟶ CommRingCat.of q.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)
  let p := Limits.pullback.fst s (Spec.map φ)
  let g := Limits.pullback.snd s (Spec.map φ)
  let h : IsPullback p g s (Spec.map φ) := IsPullback.of_hasPullback _ _
  let : IsLocallyNoetherian (Limits.pullback s (Spec.map φ)) :=
    affineBaseFibre_isLocallyNoetherian s q
  exact (finiteCechBaseChangeHomologyIso s φ p g h M U hU hcover 0).toLinearEquiv.finrank_eq.symm

end GromovWitten.AlgebraicGeometry.Curves

end
