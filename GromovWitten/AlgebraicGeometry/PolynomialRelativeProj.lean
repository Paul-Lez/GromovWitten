/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.PolynomialProjBaseChange
import GromovWitten.AlgebraicGeometry.GradedBaseChangeAlong
import GromovWitten.AlgebraicGeometry.RelativeProjBaseChange
import GromovWitten.AlgebraicGeometry.RelativeProjective

/-!
# Polynomial relative Proj over an arbitrary scheme

Polynomial coefficient restriction supplies the affine-local graded data for relative Proj.
For finitely many variables the resulting morphism has a relative-projective presentation
and is proper. The degreewise polynomial tensor theorem supplies the graded base-change
witnesses, giving a scheme-level pullback square over every affine original base.
-/

open CategoryTheory Limits AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.PolynomialRelativeProj
open ProjBaseChange GlobalBlowup RelativeProj
variable (σ : Type u)

/-- Coefficient extension preserves homogeneous degree. -/
def coefficientMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    MvPolynomial.homogeneousSubmodule σ A →+*ᵍ MvPolynomial.homogeneousSubmodule σ B where
  __ := MvPolynomial.map f
  map_mem := by
    intro n x hx
    exact hx.map f

/-- Polynomial homogeneous pieces commute with any coefficient-ring map. -/
lemma coefficientMap_isBaseChange {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    IsGradedBaseChangeAlong f (MvPolynomial.homogeneousSubmodule σ A)
      (MvPolynomial.homogeneousSubmodule σ B) (coefficientMap σ f) := by
  let _ := f.toAlgebra
  exact IsGradedBaseChangeAlong.of_isBaseChange (Polynomial.gradedMapOver σ)
    (Polynomial.isBaseChange σ)

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial graded algebras and their coefficient restriction maps. -/
def data (X : Scheme.{u}) : GradedAlgebraData X where
  ring U := MvPolynomial σ Γ(X, U.1)
  commRing _ := inferInstance
  algebra _ := inferInstance
  grading U := MvPolynomial.homogeneousSubmodule σ Γ(X, U.1)
  gradedAlgebra _ := MvPolynomial.gradedAlgebra
  map h := coefficientMap σ (res X h)
  map_id U := by
    ext p : 1
    change MvPolynomial.map (res X (le_refl U)) p = p
    rw [res_refl, MvPolynomial.map_id]
  map_comp hUV hVW := by
    ext p : 1
    change MvPolynomial.map (res X _) p =
      MvPolynomial.map (res X hUV) (MvPolynomial.map (res X hVW) p)
    rw [MvPolynomial.map_map, res_comp]
  isBaseChange h := coefficientMap_isBaseChange σ (res X h)

/-- The degree-zero part is canonically the base section ring. -/
lemma degreeZero (X : Scheme.{u}) (U : X.affineOpens) :
    Function.Bijective (algebraMap Γ(X, U.1) ((data σ X).grading U 0)) := by
  change Function.Bijective
    (algebraMap Γ(X, U.1) (MvPolynomial.homogeneousSubmodule σ Γ(X, U.1) 0))
  constructor
  · intro a b h
    apply MvPolynomial.C_injective
    exact congrArg Subtype.val h
  · intro p
    have hp := p.property
    change p.val ∈ MvPolynomial.homogeneousSubmodule σ Γ(X, U.1) 0 at hp
    obtain ⟨a, ha⟩ := (show ∃ a : Γ(X, U.1),
        algebraMap Γ(X, U.1) (MvPolynomial σ Γ(X, U.1)) a = p.val by
      simpa only [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] using hp)
    exact ⟨a, Subtype.ext ha⟩

/-- Finitely many variables give finite type over the degree-zero part. -/
lemma finiteType [Finite σ] (X : Scheme.{u}) (U : X.affineOpens) :
    Algebra.FiniteType ((data σ X).grading U 0) ((data σ X).ring U) := by
  have : Algebra.FiniteType Γ(X, U.1) ((data σ X).ring U) :=
    inferInstanceAs (Algebra.FiniteType Γ(X, U.1) (MvPolynomial σ Γ(X, U.1)))
  have : IsScalarTower Γ(X, U.1) ((data σ X).grading U 0) ((data σ X).ring U) :=
    IsScalarTower.of_algebraMap_eq (R := Γ(X, U.1))
      (S := (data σ X).grading U 0) (A := (data σ X).ring U) (fun _ => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType Γ(X, U.1)
    ((data σ X).grading U 0) ((data σ X).ring U)

/-- A relative-projective presentation built from polynomial coefficients. -/
def projective [Finite σ] (X : Scheme.{u}) :
    RelativeProjective (RelativeProj.toBase X (data σ X)) :=
  RelativeProjective.ofRelativeProj X (data σ X) (finiteType σ X) (degreeZero σ X)


set_option backward.isDefEq.respectTransparency false in
/-- Polynomial coefficients give all the scalar-extension data used by the gluing theorem. -/
def baseChangeData {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X) :
    RelativeProj.AffineBaseChangeData b (data σ X) (data σ X') where
  app U := coefficientMap σ (b.appLE ⊤ U.1 (by simp)).hom
  naturality {U V} h := by
    ext p : 1
    change MvPolynomial.map (res X' h)
      (MvPolynomial.map (b.appLE ⊤ V.1 (by simp)).hom p) =
      MvPolynomial.map (b.appLE ⊤ U.1 (by simp)).hom p
    rw [MvPolynomial.map_map]
    exact congrArg (fun q : Γ(X, ⊤) →+* Γ(X', U.1) => MvPolynomial.map q p)
      (congrArg CommRingCat.Hom.hom
        (b.appLE_map (show V.1 ≤ b ⁻¹ᵁ ⊤ by simp) (homOfLE h).op))
  isBaseChange U := coefficientMap_isBaseChange σ (b.appLE ⊤ U.1 (by simp)).hom


/-- The polynomial relative Proj over a scheme. With variables `Fin (n + 1)`, this is
projective `n`-space over the base. -/
abbrev scheme (X : Scheme.{u}) : Scheme.{u} := RelativeProj.relativeProj X (data σ X)

/-- The structure morphism of polynomial relative Proj. -/
abbrev toBase (X : Scheme.{u}) : scheme σ X ⟶ X := RelativeProj.toBase X (data σ X)

instance [Finite σ] (X : Scheme.{u}) : IsProper (toBase σ X) :=
  (projective σ X).isProper

/-- The polynomial base-change morphism over an affine original base. -/
def baseChangeMap {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X) :
    scheme σ X' ⟶ scheme σ X :=
  (baseChangeData σ b).map

/-- Polynomial relative Proj commutes with arbitrary base change from an affine base;
no flatness or affineness of the new base is required. -/
lemma isPullback_baseChangeMap {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X) :
    IsPullback (baseChangeMap σ b) (toBase σ X') (toBase σ X) b :=
  (baseChangeData σ b).isPullback_map

/-- The canonical polynomial relative-Proj base-change isomorphism. -/
def baseChangeIso {X X' : Scheme.{u}} [IsAffine X] (b : X' ⟶ X) :
    scheme σ X' ≅ pullback (toBase σ X) b :=
  (baseChangeData σ b).pullbackIso

end GromovWitten.AlgebraicGeometry.PolynomialRelativeProj
