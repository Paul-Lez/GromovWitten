/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.MatrixHomologyLocus
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Homology loci for finite free short complexes

For a short complex of finite free modules over a commutative ring, this file identifies the
dimension of the actual categorical homology after reduction to a residue field with the
dimension of a matrix homology. The matrix homology locus theorem then gives openness of the
locus where the fibre homology dimension is bounded above.
-/

open CategoryTheory
open CategoryTheory.ShortComplex
open _root_.AlgebraicGeometry
open scoped TensorProduct ChangeOfRings
open GromovWitten.AlgebraicGeometry.Matrix

namespace GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus

universe u
noncomputable section
variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{u} R)}
variable [Module.Free R (S.X₁ : Type u)] [Module.Finite R (S.X₁ : Type u)]
variable [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)]
variable [Module.Free R (S.X₃ : Type u)] [Module.Finite R (S.X₃ : Type u)]

private abbrev I₁ := Module.Free.ChooseBasisIndex R (S.X₁ : Type u)
private abbrev I₂ := Module.Free.ChooseBasisIndex R (S.X₂ : Type u)
private abbrev I₃ := Module.Free.ChooseBasisIndex R (S.X₃ : Type u)

private noncomputable def b₁ : Module.Basis (I₁ (S := S)) R (S.X₁ : Type u) :=
  Module.Free.chooseBasis R _
private noncomputable def b₂ : Module.Basis (I₂ (S := S)) R (S.X₂ : Type u) :=
  Module.Free.chooseBasis R _
private noncomputable def b₃ : Module.Basis (I₃ (S := S)) R (S.X₃ : Type u) :=
  Module.Free.chooseBasis R _

noncomputable def matrix₁₂ : Matrix (I₂ (S := S)) (I₁ (S := S)) R :=
  LinearMap.toMatrix (b₁ (S := S)) (b₂ (S := S)) S.f.hom
noncomputable def matrix₂₃ : Matrix (I₃ (S := S)) (I₂ (S := S)) R :=
  LinearMap.toMatrix (b₂ (S := S)) (b₃ (S := S)) S.g.hom

omit [Module.Free R (S.X₁ : Type u)] [Module.Finite R (S.X₁ : Type u)]
  [Module.Free R (S.X₂ : Type u)] [Module.Finite R (S.X₂ : Type u)]
  [Module.Free R (S.X₃ : Type u)] [Module.Finite R (S.X₃ : Type u)] in
lemma comp_zero : S.g.hom.comp S.f.hom = 0 := by
  exact congrArg ModuleCat.Hom.hom S.zero

lemma matrix_comp_zero : matrix₂₃ (S := S) * matrix₁₂ (S := S) = 0 := by
  dsimp [matrix₁₂, matrix₂₃]
  rw [← LinearMap.toMatrix_comp (b₁ (S := S)) (b₂ (S := S)) (b₃ (S := S)) S.g.hom S.f.hom]
  rw [comp_zero]
  simp

noncomputable def fibreShortComplex (p : PrimeSpectrum R) :
    ShortComplex (ModuleCat.{u} p.asIdeal.ResidueField) :=
  S.map (ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField))

noncomputable def fibreHomologyFinrank (p : PrimeSpectrum R) : ℕ :=
  Module.finrank p.asIdeal.ResidueField ((fibreShortComplex (S := S) p).homology)

private noncomputable def baseChangeBasis {K : Type u} [CommRing K] (f : R →+* K)
    (M : ModuleCat.{u} R) [Module.Free R (M : Type u)] [Module.Finite R (M : Type u)]
    (b : Module.Basis (Module.Free.ChooseBasisIndex R (M : Type u)) R (M : Type u)) :
    Module.Basis (Module.Free.ChooseBasisIndex R (M : Type u)) K
      ((ModuleCat.extendScalars f).obj M : Type u) := by
  letI : Algebra R K := f.toAlgebra
  change Module.Basis (Module.Free.ChooseBasisIndex R (M : Type u)) K (K ⊗[R] (M : Type u))
  exact Algebra.TensorProduct.basis K b

private noncomputable def bp₁ (p : PrimeSpectrum R) :
    Module.Basis (I₁ (S := S)) p.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).obj S.X₁ : Type u) :=
  baseChangeBasis (algebraMap R p.asIdeal.ResidueField) S.X₁ (b₁ (S := S))

private noncomputable def bp₂ (p : PrimeSpectrum R) :
    Module.Basis (I₂ (S := S)) p.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).obj S.X₂ : Type u) :=
  baseChangeBasis (algebraMap R p.asIdeal.ResidueField) S.X₂ (b₂ (S := S))

private noncomputable def bp₃ (p : PrimeSpectrum R) :
    Module.Basis (I₃ (S := S)) p.asIdeal.ResidueField
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).obj S.X₃ : Type u) :=
  baseChangeBasis (algebraMap R p.asIdeal.ResidueField) S.X₃ (b₃ (S := S))

omit [Module.Free R (S.X₃ : Type u)] [Module.Finite R (S.X₃ : Type u)] in
private lemma toMatrix_ext_map (p : PrimeSpectrum R) (φ : S.X₁ ⟶ S.X₂) :
    LinearMap.toMatrix (bp₁ (S := S) p) (bp₂ (S := S) p)
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map φ).hom =
      (LinearMap.toMatrix (b₁ (S := S)) (b₂ (S := S)) φ.hom).map
        (algebraMap R p.asIdeal.ResidueField) := by
  let _ : Algebra R p.asIdeal.ResidueField :=
    (algebraMap R p.asIdeal.ResidueField).toAlgebra
  change LinearMap.toMatrix (Algebra.TensorProduct.basis p.asIdeal.ResidueField (b₁ (S := S)))
      (Algebra.TensorProduct.basis p.asIdeal.ResidueField (b₂ (S := S)))
      (LinearMap.baseChange p.asIdeal.ResidueField φ.hom) = _
  exact LinearMap.toMatrix_baseChange p.asIdeal.ResidueField φ.hom (b₁ (S := S)) (b₂ (S := S))

private noncomputable def e₁ (p : PrimeSpectrum R) :
    ((ModuleCat.extendScalars
      (algebraMap R p.asIdeal.ResidueField)).obj S.X₁ : Type u) ≃ₗ[p.asIdeal.ResidueField]
      (I₁ (S := S) → p.asIdeal.ResidueField) :=
  (bp₁ (S := S) p).equivFun

private noncomputable def e₂ (p : PrimeSpectrum R) :
    ((ModuleCat.extendScalars
      (algebraMap R p.asIdeal.ResidueField)).obj S.X₂ : Type u) ≃ₗ[p.asIdeal.ResidueField]
      (I₂ (S := S) → p.asIdeal.ResidueField) :=
  (bp₂ (S := S) p).equivFun

private noncomputable def e₃ (p : PrimeSpectrum R) :
    ((ModuleCat.extendScalars
      (algebraMap R p.asIdeal.ResidueField)).obj S.X₃ : Type u) ≃ₗ[p.asIdeal.ResidueField]
      (I₃ (S := S) → p.asIdeal.ResidueField) :=
  (bp₃ (S := S) p).equivFun

omit [Module.Free R (S.X₃ : Type u)] [Module.Finite R (S.X₃ : Type u)] in
private lemma coordinate_f_apply (p : PrimeSpectrum R) (x : (fibreShortComplex (S := S) p).X₁) :
    e₂ (S := S) p ((fibreShortComplex (S := S) p).f x) =
      (residueMatrix (matrix₁₂ (S := S)) p).mulVec (e₁ (S := S) p x) := by
  have hm := toMatrix_ext_map (S := S) p S.f
  have hrepr := LinearMap.toMatrix_mulVec_repr (bp₁ (S := S) p) (bp₂ (S := S) p)
    ((fibreShortComplex (S := S) p).f.hom) x
  change (LinearMap.toMatrix (bp₁ (S := S) p) (bp₂ (S := S) p)
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map S.f).hom).mulVec
      ((bp₁ (S := S) p).repr x) = _ at hrepr
  rw [hm] at hrepr
  change ⇑((bp₂ (S := S) p).repr ((fibreShortComplex (S := S) p).f.hom x)) =
    (residueMatrix (matrix₁₂ (S := S)) p).mulVec
      ⇑((bp₁ (S := S) p).repr x)
  have hres :
      ((LinearMap.toMatrix (b₁ (S := S)) (b₂ (S := S)) S.f.hom).map
          (algebraMap R p.asIdeal.ResidueField)) = residueMatrix (matrix₁₂ (S := S)) p := by
    ext i j
    rfl
  rw [hres] at hrepr
  exact hrepr.symm

omit [Module.Free R (S.X₁ : Type u)] [Module.Finite R (S.X₁ : Type u)] in
private lemma coordinate_g_apply (p : PrimeSpectrum R) (x : (fibreShortComplex (S := S) p).X₂) :
    e₃ (S := S) p ((fibreShortComplex (S := S) p).g x) =
      (residueMatrix (matrix₂₃ (S := S)) p).mulVec (e₂ (S := S) p x) := by
  have hm :
      LinearMap.toMatrix (bp₂ (S := S) p) (bp₃ (S := S) p)
          ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map S.g).hom =
        (LinearMap.toMatrix (b₂ (S := S)) (b₃ (S := S)) S.g.hom).map
          (algebraMap R p.asIdeal.ResidueField) := by
    let _ : Algebra R p.asIdeal.ResidueField :=
      (algebraMap R p.asIdeal.ResidueField).toAlgebra
    change LinearMap.toMatrix (Algebra.TensorProduct.basis p.asIdeal.ResidueField (b₂ (S := S)))
        (Algebra.TensorProduct.basis p.asIdeal.ResidueField (b₃ (S := S)))
        (LinearMap.baseChange p.asIdeal.ResidueField S.g.hom) = _
    exact LinearMap.toMatrix_baseChange p.asIdeal.ResidueField S.g.hom
      (b₂ (S := S)) (b₃ (S := S))
  have hrepr := LinearMap.toMatrix_mulVec_repr (bp₂ (S := S) p) (bp₃ (S := S) p)
    ((fibreShortComplex (S := S) p).g.hom) x
  change (LinearMap.toMatrix (bp₂ (S := S) p) (bp₃ (S := S) p)
      ((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).map S.g).hom).mulVec
      ((bp₂ (S := S) p).repr x) = _ at hrepr
  rw [hm] at hrepr
  change ⇑((bp₃ (S := S) p).repr ((fibreShortComplex (S := S) p).g.hom x)) =
    (residueMatrix (matrix₂₃ (S := S)) p).mulVec
      ⇑((bp₂ (S := S) p).repr x)
  have hres :
      ((LinearMap.toMatrix (b₂ (S := S)) (b₃ (S := S)) S.g.hom).map
          (algebraMap R p.asIdeal.ResidueField)) = residueMatrix (matrix₂₃ (S := S)) p := by
    ext i j
    rfl
  rw [hres] at hrepr
  exact hrepr.symm

private noncomputable def coordinateShortComplex (p : PrimeSpectrum R) :
    ShortComplex (ModuleCat.{u} p.asIdeal.ResidueField) :=
  ShortComplex.moduleCatMk
    (residueMatrix (matrix₁₂ (S := S)) p).mulVecLin
    (residueMatrix (matrix₂₃ (S := S)) p).mulVecLin
    (residueMatrix_comp_eq_zero (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
      (matrix_comp_zero (S := S)) p)

private noncomputable def fibreToCoordinateIso (p : PrimeSpectrum R) :
    fibreShortComplex (S := S) p ≅ coordinateShortComplex (S := S) p := by
  refine ShortComplex.isoMk (e₁ (S := S) p).toModuleIso
    (e₂ (S := S) p).toModuleIso (e₃ (S := S) p).toModuleIso
    ?_ ?_
  · apply ModuleCat.hom_ext
    ext x
    exact (coordinate_f_apply (S := S) p x).symm
  · apply ModuleCat.hom_ext
    ext x
    exact (coordinate_g_apply (S := S) p x).symm

lemma fibreHomologyFinrank_eq_matrix (p : PrimeSpectrum R) :
    fibreHomologyFinrank (S := S) p =
      residueHomologyFinrank (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
        (matrix_comp_zero (S := S)) p := by
  have hi :=
    (ShortComplex.homologyMapIso (fibreToCoordinateIso (S := S) p)).toLinearEquiv.finrank_eq
  calc
    fibreHomologyFinrank (S := S) p =
        Module.finrank p.asIdeal.ResidueField
          ((coordinateShortComplex (S := S) p).homology) := hi
    _ = moduleHomologyFinrank
        (residueMatrix (matrix₁₂ (S := S)) p).mulVecLin
        (residueMatrix (matrix₂₃ (S := S)) p).mulVecLin
        (residueMatrix_comp_eq_zero (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
          (matrix_comp_zero (S := S)) p) := by
      change Module.finrank p.asIdeal.ResidueField
          ((ShortComplex.moduleCatMk
            (residueMatrix (matrix₁₂ (S := S)) p).mulVecLin
            (residueMatrix (matrix₂₃ (S := S)) p).mulVecLin
            (residueMatrix_comp_eq_zero (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
              (matrix_comp_zero (S := S)) p)).homology) = _
      rw [moduleHomologyFinrank]
    _ = residueHomologyFinrank (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
        (matrix_comp_zero (S := S)) p :=
      (residueHomologyFinrank_eq_moduleHomologyFinrank
        (matrix₁₂ (S := S)) (matrix₂₃ (S := S)) (matrix_comp_zero (S := S)) p).symm

def fibreHomologyLocus (d : ℕ) : Set (PrimeSpectrum R) :=
  {p | fibreHomologyFinrank (S := S) p ≤ d}

theorem fibreHomologyLocus_eq_matrixLocus (d : ℕ) :
    fibreHomologyLocus (S := S) d =
      homologyLocus (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
        (matrix_comp_zero (S := S)) d := by
  ext p
  change fibreHomologyFinrank (S := S) p ≤ d ↔
    residueHomologyFinrank (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
      (matrix_comp_zero (S := S)) p ≤ d
  rw [fibreHomologyFinrank_eq_matrix (S := S) p]

theorem isOpen_fibreHomologyLocus (d : ℕ) :
    IsOpen (fibreHomologyLocus (S := S) d) := by
  rw [fibreHomologyLocus_eq_matrixLocus]
  exact isOpen_homologyLocus (matrix₁₂ (S := S)) (matrix₂₃ (S := S))
    (matrix_comp_zero (S := S)) d

theorem upperSemicontinuous_fibreHomologyFinrank :
    UpperSemicontinuous (fibreHomologyFinrank (S := S)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro y
  cases y with
  | zero =>
      simp
  | succ d =>
      have hopen := isOpen_fibreHomologyLocus (S := S) d
      convert hopen using 1
      ext p
      simp [fibreHomologyLocus]

end
end GromovWitten.AlgebraicGeometry.FiniteFreeHomologyLocus
