/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesGradedBaseChange
import GromovWitten.AlgebraicGeometry.GradedBaseChangeAlong
import GromovWitten.AlgebraicGeometry.RelativeProj
import GromovWitten.AlgebraicGeometry.RelativeProjective

/-!
# Global graded Rees data

The affine Rees algebras of an ideal sheaf form graded affine data.  On an
affine restriction, the ideal sheaf compatibility and flatness of restriction
maps give the degreewise base-change witness needed by relative `Proj`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial
namespace GromovWitten.AlgebraicGeometry.GlobalBlowup
open ReesBlowup ReesBlowupOfEq
open ReesGradedBaseChange
open RelativeProj
universe u
noncomputable section

/-- The graded affine data of the Rees algebras of an ideal sheaf. -/
def gradedData (X : Scheme.{u}) (I : X.IdealSheafData) : GradedAlgebraData X where
  ring U := reesAlgebra (I.ideal U)
  commRing U := inferInstance
  algebra U := inferInstance
  grading U := gradeSubmodule (I.ideal U)
  gradedAlgebra U := inferInstance
  map := by
    intro U V h
    exact gradedMapSubmoduleOfEq (I.ideal V) (res X h) (I.ideal U) (I.map_ideal h)
  map_id U := by
    apply GradedRingHom.ext
    intro p
    apply Subtype.ext
    simp [res_refl, gradedMapSubmoduleOfEq, ReesBlowupOfEq.reesMapOfEq]
  map_comp := by
    intro U V W hUV hVW
    apply GradedRingHom.ext
    intro p
    apply Subtype.ext
    change (((p : reesAlgebra (I.ideal W)) : Polynomial (Γ(X, W.1))).map
        (res X (hUV.trans hVW))) = _
    change (((p : reesAlgebra (I.ideal W)) : Polynomial (Γ(X, W.1))).map
        (res X (hUV.trans hVW))) =
      (((p : reesAlgebra (I.ideal W)) : Polynomial (Γ(X, W.1))).map (res X hVW)).map
        (res X hUV)
    rw [res_comp, Polynomial.map_map]
  isBaseChange := by
    intro U V h
    let _ := (res X h).toAlgebra
    let _ : Module.Flat Γ(X, V.1) Γ(X, U.1) := by
      exact res_flat X h
    have hres : algebraMap (Γ(X, V.1)) (Γ(X, U.1)) = res X h :=
      RingHom.algebraMap_toAlgebra (res X h)
    have hideal : (I.ideal V).map (algebraMap (Γ(X, V.1)) (Γ(X, U.1))) = I.ideal U := by
      rw [hres]
      exact I.map_ideal h
    change ProjBaseChange.IsGradedBaseChangeAlong
      (algebraMap (Γ(X, V.1)) (Γ(X, U.1)))
      (gradeSubmodule (I.ideal V)) (gradeSubmodule (I.ideal U))
      (gradedMapSubmoduleOfEq (I.ideal V) (algebraMap (Γ(X, V.1)) (Γ(X, U.1)))
        (I.ideal U) hideal)
    exact ReesGradedBaseChange.isBaseChangeOfEq
      (I.ideal V) (I.ideal U) hideal

/-- The Rees relative `Proj` attached to a quasi-coherent ideal sheaf. -/
abbrev relativeBlowup (X : Scheme.{u}) (I : X.IdealSheafData) : Scheme :=
  RelativeProj.relativeProj X (gradedData X I)

/-- The structure morphism of the Rees relative `Proj`. -/
def relativeBlowupToBase (X : Scheme.{u}) (I : X.IdealSheafData) :
    relativeBlowup X I ⟶ X :=
  RelativeProj.toBase X (gradedData X I)

private theorem gradedData_finiteType (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    Algebra.FiniteType ((gradedData X I).grading U 0) ((gradedData X I).ring U) := by
  change Algebra.FiniteType (gradeSubmodule (I.ideal U) 0) (reesAlgebra (I.ideal U))
  let _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsScalarTower Γ(X, U.1) (gradeSubmodule (I.ideal U) 0)
      (reesAlgebra (I.ideal U)) :=
    IsScalarTower.of_algebraMap_eq (R := Γ(X, U.1))
      (S := gradeSubmodule (I.ideal U) 0) (A := reesAlgebra (I.ideal U)) (fun _ ↦ rfl)
  apply Algebra.FiniteType.of_restrictScalars_finiteType
    Γ(X, U.1) (gradeSubmodule (I.ideal U) 0) (reesAlgebra (I.ideal U))

private theorem gradedData_degreeZero (X : Scheme.{u}) (I : X.IdealSheafData)
    (U : X.affineOpens) :
    Function.Bijective (algebraMap Γ(X, U.1) ((gradedData X I).grading U 0)) := by
  change Function.Bijective (algebraMap Γ(X, U.1) (gradeSubmodule (I.ideal U) 0))
  constructor
  · intro a b hab
    have hpoly :
        ((algebraMap Γ(X, U.1) (gradeSubmodule (I.ideal U) 0) a :
          gradeSubmodule (I.ideal U) 0) : reesAlgebra (I.ideal U)) =
          ((algebraMap Γ(X, U.1) (gradeSubmodule (I.ideal U) 0) b :
            gradeSubmodule (I.ideal U) 0) : reesAlgebra (I.ideal U)) := by
      exact congrArg Subtype.val hab
    have hcoeff := congrArg
      (fun p : reesAlgebra (I.ideal U) =>
        ((p : Polynomial (Γ(X, U.1))).coeff 0)) hpoly
    simpa [Polynomial.algebraMap_apply] using hcoeff
  · intro p
    let p' : reesAlgebra (I.ideal U) := p.1
    refine ⟨(((p' : reesAlgebra (I.ideal U)) : Polynomial (Γ(X, U.1))).coeff 0), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Polynomial.C (((p' : reesAlgebra (I.ideal U)) :
      Polynomial (Γ(X, U.1))).coeff 0) = (p' : Polynomial (Γ(X, U.1)))
    symm
    exact p.property

theorem relativeBlowupToBase_isProper (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsProper (relativeBlowupToBase X I) := by
  let _ : ∀ U, Algebra.FiniteType ((gradedData X I).grading U 0) ((gradedData X I).ring U) :=
    fun U ↦ gradedData_finiteType X I U
  apply RelativeProj.toBase_isProper
  exact fun U ↦ gradedData_degreeZero X I U

/-- The Rees relative `Proj` carries a genuine relative-projective witness. -/
def relativeProjective (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    RelativeProjective (relativeBlowupToBase X I) :=
  RelativeProjective.ofRelativeProj X (gradedData X I)
    (fun U ↦ gradedData_finiteType X I U) (fun U ↦ gradedData_degreeZero X I U)

end
end GromovWitten.AlgebraicGeometry.GlobalBlowup
