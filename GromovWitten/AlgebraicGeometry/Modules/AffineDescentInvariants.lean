/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Modules.AffineDescent
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Concrete affine descent invariants

This file identifies the categorical Beck equalizer with the actual module of
elements satisfying `δ n = 1 ⊗ n`, and records its faithfully flat reconstruction.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Comonad CategoryTheory.Comonad.ComonadicityInternal
open ModuleCat
open scoped ChangeOfRings TensorProduct

namespace GromovWitten.AlgebraicGeometry.Modules

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

private noncomputable def coactionA (D : AffineDescent f) :
    (restrictScalars f).obj D.A ⟶
      (extendScalars f ⋙ restrictScalars f).obj ((restrictScalars f).obj D.A) :=
  (restrictScalars f).map D.a

private noncomputable def unitA (D : AffineDescent f) :
    (restrictScalars f).obj D.A ⟶
      (extendScalars f ⋙ restrictScalars f).obj ((restrictScalars f).obj D.A) :=
  (extendRestrictScalarsAdj.{u, u, u} f).unit.app ((restrictScalars f).obj D.A)

/-- The usual module of invariant elements of an affine descent datum.

The two maps in the kernel are the coaction and the unit of extension and restriction
of scalars.  Thus this is the concrete module
`{n | δ n = 1 ⊗ n}`.
-/
noncomputable def invariantSubmodule (D : AffineDescent f) :
  Submodule A ((restrictScalars f).obj D.A) :=
  LinearMap.ker ((coactionA f D - unitA f D).hom)

/-- The inclusion of the concrete invariants into the restricted underlying module. -/
noncomputable def invariantSubtype (D : AffineDescent f) :
    ModuleCat.of A (invariantSubmodule f D) ⟶ (restrictScalars f).obj D.A :=
  ModuleCat.ofHom (Y := (restrictScalars f).obj D.A) (invariantSubmodule f D).subtype

private theorem mem_invariantSubmodule_iff_maps (D : AffineDescent f)
    (n : (restrictScalars f).obj D.A) :
    n ∈ invariantSubmodule f D ↔
      (coactionA f D) n = (unitA f D) n := by
  rw [invariantSubmodule, LinearMap.mem_ker]
  exact sub_eq_zero

@[simp]
theorem mem_invariantSubmodule_iff (D : AffineDescent f)
    (n : (restrictScalars f).obj D.A) :
    n ∈ invariantSubmodule f D ↔
      D.a n = (1 : B) ⊗ₜ[A, f] n := by
  rw [mem_invariantSubmodule_iff_maps]
  rw [← extension_unit_apply f ((restrictScalars f).obj D.A) n]
  change (coactionA f D) n = (unitA f D) n ↔
    (coactionA f D) n = (unitA f D) n
  rfl

@[simp]
theorem invariantSubmodule_coaction_eq (D : AffineDescent f)
    (n : invariantSubmodule f D) :
    D.a (n : (restrictScalars f).obj D.A) =
      (1 : B) ⊗ₜ[A, f] (n : (restrictScalars f).obj D.A) := by
  rw [← extension_unit_apply f ((restrictScalars f).obj D.A) (n : (restrictScalars f).obj D.A)]
  exact (mem_invariantSubmodule_iff_maps f D n).mp n.property

private noncomputable def equalizerToInvariant (D : AffineDescent f) :
    (descentFunctor f).obj D ⟶ ModuleCat.of A (invariantSubmodule f D) :=
  ModuleCat.ofHom <|
    LinearMap.codRestrict (invariantSubmodule f D) (descentEqualizerι f D).hom <| by
      intro x
      apply (mem_invariantSubmodule_iff_maps f D _).2
      have hcond : descentEqualizerι f D ≫ coactionA f D =
          descentEqualizerι f D ≫ unitA f D :=
        descentEqualizerι_condition f D
      have h := congrArg (fun g => g.hom) hcond
      have hx := congrArg (fun g => g x) h
      change ((coactionA f D).hom.comp (descentEqualizerι f D).hom) x =
        ((unitA f D).hom.comp (descentEqualizerι f D).hom) x
      exact hx

private noncomputable def invariantToEqualizer (D : AffineDescent f) :
    ModuleCat.of A (invariantSubmodule f D) ⟶ (descentFunctor f).obj D :=
  equalizer.lift (invariantSubtype f D) (by
    apply ModuleCat.hom_ext
    ext n
    change (coactionA f D) ((invariantSubtype f D) n) =
      (unitA f D) ((invariantSubtype f D) n)
    exact (mem_invariantSubmodule_iff_maps f D n).mp n.property)

@[simp]
private theorem equalizerToInvariant_comp_ι (D : AffineDescent f) :
    equalizerToInvariant f D ≫ invariantSubtype f D =
      descentEqualizerι f D := by
  apply ModuleCat.hom_ext
  rfl

@[simp]
private theorem invariantToEqualizer_comp_ι (D : AffineDescent f) :
    invariantToEqualizer f D ≫ descentEqualizerι f D =
      invariantSubtype f D := by
  exact equalizer.lift_ι _ _

/-- The categorical descent equalizer is the concrete invariant submodule. -/
noncomputable def invariantEqualizerIso (D : AffineDescent f) :
    (descentFunctor f).obj D ≅ ModuleCat.of A (invariantSubmodule f D) :=
  { hom := equalizerToInvariant f D
    inv := invariantToEqualizer f D
    hom_inv_id := by
      apply descentHom_ext f D D
      rw [Category.assoc, invariantToEqualizer_comp_ι, equalizerToInvariant_comp_ι,
        Category.id_comp]
    inv_hom_id := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      apply Subtype.ext
      have h := congrArg (fun g => g n) (invariantToEqualizer_comp_ι f D)
      change descentEqualizerι f D ((invariantToEqualizer f D) n) =
        (n : (restrictScalars f).obj D.A)
      exact h }

@[simp]
theorem invariantEqualizerIso_hom_comp_ι (D : AffineDescent f) :
    (invariantEqualizerIso f D).hom ≫ invariantSubtype f D =
      descentEqualizerι f D := by
  exact equalizerToInvariant_comp_ι f D

@[simp]
theorem invariantEqualizerIso_inv_comp_ι (D : AffineDescent f) :
    (invariantEqualizerIso f D).inv ≫ descentEqualizerι f D =
      invariantSubtype f D := by
  exact invariantToEqualizer_comp_ι f D

/-- A morphism of descent data restricts to a map of invariant modules. -/
noncomputable def invariantMap (D E : AffineDescent f) (φ : D ⟶ E) :
    ModuleCat.of A (invariantSubmodule f D) ⟶ ModuleCat.of A (invariantSubmodule f E) :=
  (invariantEqualizerIso f D).inv ≫ descendedHom f D E φ ≫
    (invariantEqualizerIso f E).hom

@[simp]
theorem invariantMap_comp_subtype (D E : AffineDescent f) (φ : D ⟶ E) :
    invariantMap f D E φ ≫ invariantSubtype f E =
      invariantSubtype f D ≫
        (restrictScalars f).map φ.f := by
  simp only [invariantMap, Category.assoc, invariantEqualizerIso_hom_comp_ι,
    descendedHom_comp_ι]
  rw [← Category.assoc, invariantEqualizerIso_inv_comp_ι]

@[simp]
theorem invariantMap_apply (D E : AffineDescent f) (φ : D ⟶ E)
    (n : invariantSubmodule f D) :
    ((invariantMap f D E φ) n : (restrictScalars f).obj E.A) =
      φ.f (n : (restrictScalars f).obj D.A) := by
  have h := congrArg (fun g => g n) (invariantMap_comp_subtype f D E φ)
  change (invariantSubtype f E) ((invariantMap f D E φ) n) =
    φ.f ((invariantSubtype f D) n)
  exact h

/-- The descended module, extended back to `B`, is canonically the original module. -/
noncomputable def invariantExtensionDescentIso (hf : f.FaithfullyFlat)
    (D : AffineDescent f) :
    (extendScalars f).obj (ModuleCat.of A (invariantSubmodule f D)) ≅ D.A := by
  let i : (affineDescentComparison f).obj (ModuleCat.of A (invariantSubmodule f D)) ≅ D :=
    (affineDescentComparison f).mapIso (invariantEqualizerIso f D).symm ≪≫
      extensionDescentIso f hf D
  exact (Comonad.forget ((extendRestrictScalarsAdj.{u, u, u} f).toComonad)).mapIso i

@[simp]
theorem invariantExtensionDescentIso_hom_one_tmul (hf : f.FaithfullyFlat)
    (D : AffineDescent f) (n : invariantSubmodule f D) :
    (invariantExtensionDescentIso f hf D).hom
        ((1 : B) ⊗ₜ[A, f] n) =
      (n : (restrictScalars f).obj D.A) := by
  change (extensionDescentIso f hf D).hom.f
    ((extendScalars f).map (invariantEqualizerIso f D).inv
      ((1 : B) ⊗ₜ[A, f] n)) =
      (n : (restrictScalars f).obj D.A)
  rw [ModuleCat.ExtendScalars.map_tmul]
  have h₁ := extensionDescentIso_hom_apply_one_tmul f hf D
    ((invariantEqualizerIso f D).inv n)
  have h₂ : descentEqualizerι f D ((invariantEqualizerIso f D).inv n) =
      (n : (restrictScalars f).obj D.A) := by
    have h := congrArg (fun k => k n) (invariantEqualizerIso_inv_comp_ι f D)
    change descentEqualizerι f D ((invariantEqualizerIso f D).inv n) = _
    exact h
  exact h₁.trans h₂

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem invariantExtensionDescentIso_hom_tmul (hf : f.FaithfullyFlat)
    (D : AffineDescent f) (b : B) (n : invariantSubmodule f D) :
    (invariantExtensionDescentIso f hf D).hom
        (b ⊗ₜ[A, f] n) = b • (n : (restrictScalars f).obj D.A) := by
  have hb :
      b • ((1 : B) ⊗ₜ[A, f] n :
        (extendScalars f).obj (ModuleCat.of A (invariantSubmodule f D))) =
      (b ⊗ₜ[A, f] n :
        (extendScalars f).obj (ModuleCat.of A (invariantSubmodule f D))) := by
    simpa only [mul_one] using
      (ModuleCat.ExtendScalars.smul_tmul f
        (M := ModuleCat.of A (invariantSubmodule f D)) b (1 : B) n)
  rw [← hb, map_smul, invariantExtensionDescentIso_hom_one_tmul]

/-! The preceding isomorphism transports finite generation along faithfully flat descent. -/

/-- A faithfully flat affine descent datum with finite underlying `B`-module has finite
invariants over `A`. -/
theorem module_finite_invariant_of_finite (hf : f.FaithfullyFlat)
    (D : AffineDescent f) [Module.Finite B D.A] :
    Module.Finite A (invariantSubmodule f D) := by
  algebraize [f]
  have hfinite :
      Module.Finite B ((extendScalars f).obj (ModuleCat.of A (invariantSubmodule f D))) := by
    rw [Module.Finite.equiv_iff (invariantExtensionDescentIso f hf D).toLinearEquiv]
    infer_instance
  exact @Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A _ B _ _
    (ModuleCat.of A (invariantSubmodule f D)) _ _ _ hfinite

end GromovWitten.AlgebraicGeometry.Modules
