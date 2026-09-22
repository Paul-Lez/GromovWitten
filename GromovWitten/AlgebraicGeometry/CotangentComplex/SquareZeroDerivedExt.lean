/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Derived morphisms from a two-term complex with one projective term

For a complex `[C ⟶ F]` in degrees `-1,0`, we construct the distinguished triangle
coming from the degreewise short exact sequence `F[0] ⟶ [C ⟶ F] ⟶ C[1]`.
If `F` is projective, every derived morphism to a module in degree `-1` is represented
by a chain map. No projectivity of `C` is required. Identifying the kernel with the
image of `Hom(F,M) ⟶ Hom(C,M)` is a separate remaining step; this file does not claim
the resulting cokernel equivalence.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace SquareZero

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

universe u

attribute [local instance] HasDerivedCategory.standard

section TwoTerm

variable {A : Type u} [CommRing A]

namespace TwoTerm

variable {E : LinearTwoTermComplex A}

/-! ### Morphisms between single complexes in degree `-1`

The derived single functor is fully faithful in every integer degree.  This is the precise
identification used below; no homotopy-to-derived identification is being assumed. -/

noncomputable def singleNegHomEquiv {X Y : ModuleCat A} :
    ((DerivedCategory.singleFunctor (ModuleCat A) (-1)).obj X ⟶
      (DerivedCategory.singleFunctor (ModuleCat A) (-1)).obj Y) ≃ (X ⟶ Y) := by
  exact (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor (ModuleCat A) (-1))).homEquiv.symm

/-! ### The canonical short exact sequence of complexes -/

/-- The inclusion of the degree-zero term into a two-term complex. -/
noncomputable def inclusion (E : LinearTwoTermComplex A) :
    (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A E.degreeOne) ⟶
      E.toCochainComplex :=
  mkHomFromSingle (𝟙 _) (fun i hi => by
    have hi' : i = 1 := by
      simp only [ComplexShape.up_Rel] at hi
      omega
    subst hi'
    exact (E.toCochainComplex_X_isZero 1 (by omega) (by omega)).eq_of_tgt _ _)

/-- The projection from a two-term complex to its degree-minus-one term. -/
noncomputable def projection (E : LinearTwoTermComplex A) :
    E.toCochainComplex ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-1)).obj (ModuleCat.of A E.degreeZero) :=
  mkHomToSingle (𝟙 _) (fun i hi => by
    have hi' : i = -2 := by
      simp only [ComplexShape.up_Rel] at hi
      omega
    subst hi'
    exact (E.toCochainComplex_X_isZero (-2) (by omega) (by omega)).eq_of_src _ _)

@[simp]
theorem inclusion_f_zero (E : LinearTwoTermComplex A) :
    (inclusion E).f 0 = 𝟙 _ := by
  dsimp [inclusion]
  apply ModuleCat.hom_ext
  rfl

@[simp]
theorem projection_f_negOne (E : LinearTwoTermComplex A) :
    (projection E).f (-1) = 𝟙 _ := by
  dsimp [projection]
  apply ModuleCat.hom_ext
  rfl

/-!
The componentwise exactness proof is deliberately kept at the cochain-complex level.  In
particular, no projectivity of `E.degreeZero` occurs here.
-/

noncomputable def shortComplex (E : LinearTwoTermComplex A) :
    ShortComplex (CochainComplex (ModuleCat A) ℤ) :=
  ShortComplex.mk (inclusion E) (projection E) (by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    by_cases hi : i = -1
    · subst hi
      exact (isZero_single_obj_X _ _ _ (-1) (by omega)).eq_of_src _ _
    · by_cases hi0 : i = 0
      · subst hi0
        exact (isZero_single_obj_X _ _ _ 0 (by omega)).eq_of_tgt _ _
      · exact (isZero_single_obj_X _ _ _ i (by omega)).eq_of_src _ _)

theorem shortExact (E : LinearTwoTermComplex A) :
    (shortComplex E).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : i = -1
  · subst hi
    have hs : IsZero (((CochainComplex.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A E.degreeOne)).X (-1)) :=
      isZero_single_obj_X _ _ _ (-1) (by omega)
    exact { exact := by
              apply (ShortComplex.moduleCat_exact_iff _).2
              intro x hx
              have hx' : x = 0 := by
                change (projection E).f (-1) x = 0 at hx
                rw [projection_f_negOne] at hx
                exact hx
              subst x
              refine ⟨0, ?_⟩
              change (inclusion E).f (-1) 0 = 0
              simp
            mono_f := hs.mono _
            epi_g := by
              rw [ModuleCat.epi_iff_surjective]
              intro x
              refine ⟨x, ?_⟩
              change (projection E).f (-1) x = x
              rw [projection_f_negOne]
              rfl }
  · by_cases hi0 : i = 0
    · subst hi0
      have ht : IsZero (((CochainComplex.singleFunctor (ModuleCat A) (-1)).obj
          (ModuleCat.of A E.degreeZero)).X 0) :=
        isZero_single_obj_X _ _ _ 0 (by omega)
      have hexact : ((shortComplex E).map (eval (ModuleCat A) (ComplexShape.up ℤ) 0)).Exact := by
        apply (ShortComplex.moduleCat_exact_iff _).2
        intro x hx
        refine ⟨x, ?_⟩
        change (inclusion E).f 0 x = x
        rw [inclusion_f_zero]
        rfl
      exact {
            exact := hexact
            mono_f := by
              apply (ModuleCat.mono_iff_injective _).2
              intro x y h
              change x = y at h
              exact h
            epi_g := ht.epi _ }
    · exact { exact := ShortComplex.exact_of_isZero_X₂ _
                (E.toCochainComplex_X_isZero i hi hi0)
              mono_f := (isZero_single_obj_X (ComplexShape.up ℤ) 0
                (ModuleCat.of A E.degreeOne) i hi0).mono _
              epi_g := (isZero_single_obj_X (ComplexShape.up ℤ) (-1)
                (ModuleCat.of A E.degreeZero) i hi).epi _ }

/-! ### The derived triangle and its first exactness consequences -/

noncomputable def derivedTriangle (E : LinearTwoTermComplex A) :
    Triangle (DerivedCategory (ModuleCat A)) :=
  DerivedCategory.triangleOfSES (shortExact E)

theorem derivedTriangle_distinguished (E : LinearTwoTermComplex A) :
    derivedTriangle E ∈ distTriang (DerivedCategory (ModuleCat A)) :=
  DerivedCategory.triangleOfSES_distinguished (shortExact E)

theorem factorThroughDegreeMinusOne {L : CochainComplex (ModuleCat A) ℤ}
    (E : LinearTwoTermComplex A) (f :
      DerivedCategory.Q.obj E.toCochainComplex ⟶ DerivedCategory.Q.obj L)
    (hf : DerivedCategory.Q.map (inclusion E) ≫ f = 0) :
    ∃ g : DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat A) (-1)).obj
          (ModuleCat.of A E.degreeZero)) ⟶ DerivedCategory.Q.obj L,
      f = (derivedTriangle E).mor₂ ≫ g := by
  exact Triangle.yoneda_exact₂ (derivedTriangle E) (derivedTriangle_distinguished E) f hf

theorem firstMap_eq_zero_of_projective {L : CochainComplex (ModuleCat A) ℤ}
    [Projective (ModuleCat.of A E.degreeOne)] (hL : L.IsStrictlyLE (-1 : ℤ))
    (f : (derivedTriangle E).obj₁ ⟶ DerivedCategory.Q.obj L) : f = 0 := by
  change DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A E.degreeOne)) ⟶ DerivedCategory.Q.obj L at f
  exact DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective f (-1 : ℤ) (by omega)

/-- A derived morphism to a module in degree `-1` has a chain-map representative if
the degree-zero term of the source is projective. The conormal term may be arbitrary. -/
theorem q_map_surjective_to_single_negOne (E : LinearTwoTermComplex A)
    [Projective (ModuleCat.of A E.degreeOne)] (N : ModuleCat A) :
    Function.Surjective (fun f : E.toCochainComplex ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-1)).obj N ↦ DerivedCategory.Q.map f) := by
  intro f
  obtain ⟨g, hg⟩ := factorThroughDegreeMinusOne E f
    (firstMap_eq_zero_of_projective (E := E) (by infer_instance) _)
  change (DerivedCategory.singleFunctor (ModuleCat A) (-1)).obj
    (ModuleCat.of A E.degreeZero) ⟶
    (DerivedCategory.singleFunctor (ModuleCat A) (-1)).obj N at g
  obtain ⟨k, hk⟩ := (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map_surjective g
  refine ⟨projection E ≫ (CochainComplex.singleFunctor (ModuleCat A) (-1)).map k, ?_⟩
  dsimp only
  rw [Functor.map_comp]
  change (derivedTriangle E).mor₂ ≫
    (DerivedCategory.singleFunctor (ModuleCat A) (-1)).map k = f
  rw [hk]
  exact hg.symm

end TwoTerm

end TwoTerm

section AffinePresentation

universe v

variable (R : Type u) {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
variable (M : Ideal B) {A : Type v} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)]
variable [IsScalarTower R A (B ⧸ M)] [IsSquareZero M]
variable (P : Algebra.Extension.{v} R A)

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- The canonical map from the presentation obstruction group to derived degree-one Hom.
It exists without any projectivity assumption. Injectivity is not asserted here. -/
noncomputable def obstructionToDerivedHom (ξ : ObstructionGroup R M P) :
    DerivedCategory.Q.obj (AffinePresentation.cochainComplex R A P) ⟶
      DerivedCategory.Q.obj (coeffComplex M A) :=
  DerivedCategory.Qh.map (homotopyExtOneEquiv R M P ξ)

/-- Every derived obstruction class has a representative in the explicit presentation
cokernel when the cotangent-space term is projective. The conormal term is arbitrary. -/
theorem obstructionToDerivedHom_surjective
    [Projective (ModuleCat.of A P.CotangentSpace)] :
    Function.Surjective (obstructionToDerivedHom R M P) := by
  intro f
  let : Projective (ModuleCat.of A (AffinePresentation.twoTerm R A P).degreeOne) := by
    change Projective (ModuleCat.of A P.CotangentSpace)
    infer_instance
  obtain ⟨g, hg⟩ := TwoTerm.q_map_surjective_to_single_negOne
    (AffinePresentation.twoTerm R A P) (ModuleCat.of A (Coeff M)) f
  refine ⟨(homotopyExtOneEquiv R M P).symm
    ((HomotopyCategory.quotient _ _).map g), ?_⟩
  simp only [obstructionToDerivedHom, Equiv.apply_symm_apply]
  exact hg

@[simp]
theorem obstructionToDerivedHom_zero : obstructionToDerivedHom R M P 0 = 0 := by
  rw [obstructionToDerivedHom, homotopyExtOneEquiv_zero]
  exact (DerivedCategory.Qh (C := ModuleCat.{v} A)).map_zero _ _

end AffinePresentation

end SquareZero

end GromovWitten.AlgebraicGeometry.CotangentComplex
