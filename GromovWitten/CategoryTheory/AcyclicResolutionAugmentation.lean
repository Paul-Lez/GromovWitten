/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Acyclicity of the canonical resolution augmentation

An additive left exact functor sends an injective resolution to a complex whose
canonical augmentation is a quasi-isomorphism whenever all positive right-derived
objects of the input vanish.
-/

open CategoryTheory Limits HomologicalComplex
noncomputable section

namespace CategoryTheory.Functor

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/-- If the positive right-derived objects of `A` under an additive left exact functor
vanish, then the canonical augmentation of the mapped injective resolution is a
quasi-isomorphism. -/
lemma quasiIso_resolutionAug_of_isZero_rightDerived_succ
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] (A : C)
    (h : ∀ n : ℕ, IsZero ((L.rightDerived (n + 1)).obj A)) :
    QuasiIso
      ((singleMapHomologicalComplex L (.up ℕ) 0).inv.app A ≫
        (L.mapHomologicalComplex (.up ℕ)).map (injectiveResolution A).ι) := by
  let I := injectiveResolution A
  let a : (CochainComplex.single₀ D).obj (L.obj A) ⟶
      (L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    (singleMapHomologicalComplex L (.up ℕ) 0).inv.app A ≫
      (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have ha : QuasiIso a := by
    rw [quasiIso_iff]
    intro n
    by_cases hn : n = 0
    · subst n
      let e := singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (L.obj A)
      have hcycles : e.inv ≫ HomologicalComplex.cyclesMap a 0 =
          I.toRightDerivedZero' L := by
        apply (cancel_mono
          (((L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles 0)).mp
        rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
          singleObjCyclesSelfIso_inv_iCycles]
        dsimp [a]
        simp only [singleMapHomologicalComplex_inv_app_self, CochainComplex.single₀ObjXSelf,
          Iso.refl_hom, Iso.refl_inv, Category.id_comp,
          Functor.mapHomologicalComplex_map_f,
          InjectiveResolution.toRightDerivedZero'_comp_iCycles]
        change L.map (𝟙 A) ≫ L.map (I.ι.f 0) = L.map (I.ι.f 0)
        rw [L.map_id, Category.id_comp]
      have hcycles' : IsIso (HomologicalComplex.cyclesMap a 0) := by
        have hc : IsIso (e.inv ≫ HomologicalComplex.cyclesMap a 0) := by
          rw [hcycles]
          infer_instance
        exact IsIso.of_isIso_comp_left e.inv _
      have hhom : IsIso (HomologicalComplex.homologyMap a 0) := by
        have hcomp : IsIso
            (HomologicalComplex.homologyMap a 0 ≫
              (CochainComplex.isoHomologyπ₀
                ((L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).inv) := by
          rw [CochainComplex.isoHomologyπ₀_inv_naturality]
          infer_instance
        exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap a 0)
          (CochainComplex.isoHomologyπ₀ ((L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).inv
      exact (quasiIsoAt_iff_isIso_homologyMap a 0).2 hhom
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [quasiIsoAt_iff_exactAt a (n + 1)
        (CochainComplex.exactAt_succ_single_obj (L.obj A) n)]
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact IsZero.of_iso (h n) (I.isoRightDerivedObj L (n + 1)).symm
  exact ha

end CategoryTheory.Functor
