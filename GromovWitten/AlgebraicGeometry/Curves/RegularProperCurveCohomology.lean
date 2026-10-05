/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import GromovWitten.AlgebraicGeometry.Curves.ProperCurveTopology
import GromovWitten.AlgebraicGeometry.Curves.RationalFunctionToProjectiveLine
import GromovWitten.AlgebraicGeometry.Curves.FiniteToProjectiveLineCohomology
import GromovWitten.AlgebraicGeometry.Curves.CoherentHigherDirectImage
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Coherent cohomology of regular proper curves

A regular proper integral one-dimensional scheme over a field admits a finite morphism to the
projective line. This gives finite coherent cohomology in every degree, finite presentation of all
higher direct images to the field, and vanishing of higher direct images above degree one.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry

namespace RegularProperCurve

variable {k : Type u} [Field k] (C : RegularProperCurve k)

/-- A regular proper integral curve admits a finite morphism to the projective line over its base
field. -/
theorem exists_finite_to_projectiveLine :
    ∃ (p : C.W ⟶ ProjectiveLine.scheme k), IsFinite p ∧
      p ≫ ProjectiveLine.structureMap k = C.f := by
  let η := genericPoint C.W
  let κ : Type u := C.W.residueField η
  let φ : k →+* κ := IntersectionTheory.FiniteTypeDimension.residueMap C.f η
  let _ : Algebra k κ := φ.toAlgebra
  have htrdeg : Algebra.trdeg k κ ≠ 0 := by
    intro hzero
    have hdim := C.dim_eq_one
    change Cardinal.toENat (Algebra.trdeg k κ) = 1 at hdim
    rw [hzero] at hdim
    norm_num at hdim
  have htrans : Algebra.Transcendental k κ :=
    (trdeg_ne_zero_iff).mp htrdeg
  obtain ⟨x, hx⟩ := htrans.transcendental
  obtain ⟨r, hrx⟩ := C.W.residue_surjective η x
  have htop : C.f.appLE ⊤ ⊤ (by simp) = C.f.appTop := by
    unfold Scheme.Hom.appLE
    change C.f.appTop ≫ C.W.presheaf.map (𝟙 _) = C.f.appTop
    rw [C.W.presheaf.map_id, Category.comp_id]
  have hscalar : (C.W.residue η).hom.comp
      (RationalFunction.kFunctionField C.f).hom = φ := by
    ext c
    unfold RationalFunction.kFunctionField RationalFunction.kSection
    rw [htop]
    rfl
  have heval : (C.W.residue η).hom.comp
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r) =
        Polynomial.eval₂RingHom φ x := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        using RingHom.congr_fun hscalar a
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        using hrx
  have haeval (p : Polynomial k) :
      Polynomial.eval₂RingHom φ x p = Polynomial.aeval x p := by
    change Polynomial.eval₂ φ x p = Polynomial.aeval x p
    rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]
  have htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r) := by
    intro p q hpq
    have hmap := congrArg (C.W.residue η).hom hpq
    change ((C.W.residue η).hom.comp
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r)) p =
      ((C.W.residue η).hom.comp
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r)) q at hmap
    rw [heval] at hmap
    have hinj := (transcendental_iff_injective.mp hx)
    exact hinj (by rw [← haeval p, ← haeval q]; exact hmap)
  have hr : r ≠ 0 := by
    have hxne : x ≠ 0 := by
      intro hx0
      have hinj := (transcendental_iff_injective.mp hx)
      have hX : Polynomial.aeval x (Polynomial.X : Polynomial k) =
          Polynomial.aeval x (0 : Polynomial k) := by simp [hx0]
      exact Polynomial.X_ne_zero (hinj hX)
    intro hr0
    apply hxne
    calc x = (C.W.residue η).hom r := hrx.symm
      _ = (C.W.residue η).hom 0 := by rw [hr0]
      _ = 0 := map_zero _
  let hv : ∀ y : C.W, ValuationRing (C.W.presheaf.stalk y) := C.valuationRing_stalk
  let p : C.W ⟶ ProjectiveLine.scheme k :=
    RationalFunction.toProjectiveLine C.f hv r hr
  have hp : IsFinite p := by
    dsimp [p]
    exact RationalFunction.isFinite_toProjectiveLine C.f hv r hr
      C.finite_of_isClosed C.isClosed_singleton htr
  exact ⟨p, hp, by
    dsimp [p]
    exact RationalFunction.toProjectiveLine_comp_structureMap C.f hv r hr⟩

/-- Every cohomology module of a finitely presented module on a regular proper curve is finite over
the base field. -/
theorem finite_cohomology
    (M : C.W.Modules) [M.IsFinitePresentation] (n : ℕ) :
    Module.Finite k (Curves.cohomologyModuleCat k C.f M n) := by
  obtain ⟨p, hp, hcomp⟩ := C.exists_finite_to_projectiveLine
  have _ : IsFinite p := hp
  have h := Curves.finite_cohomology_of_finite_to_projectiveLine k p M n
  rw [hcomp] at h
  exact h

/-- Every higher direct image of a finitely presented module on a regular proper curve is
finitely presented over the base field. -/
theorem isFinitePresentation_higherDirectImageModule
    (M : C.W.Modules) [M.IsFinitePresentation] (n : ℕ) :
    (Curves.higherDirectImageModule C.f M n).IsFinitePresentation := by
  let _ : IsLocallyNoetherian C.W := C.isNoetherian.toIsLocallyNoetherian
  let _ : M.IsQuasicoherent :=
    SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  exact (Curves.isFinitePresentation_higherDirectImageModule_iff_finite_cohomology
      (s := C.f) M n).2 (C.finite_cohomology M n)

/-- Higher direct images of a quasi-coherent module on a regular proper curve vanish in degrees
strictly greater than one. -/
theorem isZero_higherDirectImageModule
    (M : C.W.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (Curves.higherDirectImageModule C.f M (n + 2)) := by
  obtain ⟨p, hp, hcomp⟩ := C.exists_finite_to_projectiveLine
  have _ : IsFinite p := hp
  have _ : IsLocallyNoetherian C.W := C.isNoetherian.toIsLocallyNoetherian
  have hzero := Curves.isZero_higherDirectImageModule_of_affine_to_projectiveLine k p M n
  rw [hcomp] at hzero
  exact hzero

end RegularProperCurve

end GromovWitten.AlgebraicGeometry
