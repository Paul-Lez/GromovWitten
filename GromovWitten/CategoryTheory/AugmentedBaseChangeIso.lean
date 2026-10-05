/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.CategoryTheory.HomologyBaseChange
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.QuasiIso
/-!
# Detecting base-change isomorphisms through augmentations

A commutative square between augmented complexes identifies the map on their
augmented objects with a homology comparison. If the augmentations and complex
comparison are quasi-isomorphisms in the augmentation degree and the functor's
homology comparison is invertible there, the map on the objects is invertible.
-/
open CategoryTheory Limits
namespace HomologicalComplex
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
/-- An augmentation-compatible base-change comparison with invertible homology
comparison detects invertibility of the map on the augmented objects. -/
lemma isIso_of_single_augmentation_baseChange
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (n : ℤ) {M : C} {N : D} {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}
    (a : (single C (.up ℤ) n).obj M ⟶ K)
    (b : (single D (.up ℤ) n).obj N ⟶ L)
    (f : F.obj M ⟶ N)
    (c : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
    (hsq : (F.mapHomologicalComplex (.up ℤ)).map a ≫ c =
      (singleMapHomologicalComplex F (.up ℤ) n).hom.app M ≫
        (single D (.up ℤ) n).map f ≫ b)
    [QuasiIsoAt a n] [QuasiIsoAt b n] [QuasiIsoAt c n]
    [IsIso (K.homologyComparison F n)] : IsIso f := by
  let S := (single C (.up ℤ) n).obj M
  let FC := F.mapHomologicalComplex (.up ℤ)
  have : IsIso (S.homologyComparison F n) :=
    S.isIso_homologyComparison_of_d_eq_zero F n (by simp [S])
  have heq := S.homologyComparison_naturality F n a
  have hcomp : IsIso (S.homologyComparison F n ≫ homologyMap (FC.map a) n) := by
    rw [← heq]
    infer_instance
  have : IsIso (homologyMap (FC.map a) n) :=
    IsIso.of_isIso_comp_left (S.homologyComparison F n) _
  have : QuasiIsoAt (FC.map a) n := (quasiIsoAt_iff_isIso_homologyMap _ _).2 inferInstance
  have hq : QuasiIsoAt (FC.map a ≫ c) n := inferInstance
  rw [hsq] at hq
  have hq' : QuasiIsoAt ((single D (.up ℤ) n).map f ≫ b) n :=
    (quasiIsoAt_iff_comp_left ((singleMapHomologicalComplex F (.up ℤ) n).hom.app M) _ n).mp hq
  have : QuasiIsoAt ((single D (.up ℤ) n).map f) n :=
    (quasiIsoAt_iff_comp_right _ b n).mp hq'
  have : IsIso ((single D (.up ℤ) n ⋙ homologyFunctor D (.up ℤ) n).map f) :=
    inferInstanceAs (IsIso (homologyMap ((single D (.up ℤ) n).map f) n))
  exact (NatIso.isIso_map_iff (homologyFunctorSingleIso D (.up ℤ) n) f).mp inferInstance
end HomologicalComplex
