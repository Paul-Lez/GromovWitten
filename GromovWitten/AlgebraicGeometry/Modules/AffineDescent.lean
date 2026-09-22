/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Affine faithfully flat descent for modules

This file keeps the affine stage of descent concrete.  Descent data are the genuine
Eilenberg–Moore coalgebras for extension and restriction of scalars, and the descended
module is the equalizer of the two maps occurring in Beck's construction.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Comonad CategoryTheory.Comonad.ComonadicityInternal
open ModuleCat
open scoped ChangeOfRings

namespace GromovWitten.AlgebraicGeometry.Modules

universe u

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The honest category of affine descent data for `f`.

An object is a `B`-module equipped with a coaction for the comonad induced by
extension and restriction of scalars.  Thus the counit and coassociativity laws are
part of the descent datum itself.
-/
abbrev AffineDescent :=
  (extendRestrictScalarsAdj.{u, u, u} f).toComonad.Coalgebra

/-- The comparison functor sends an `A`-module to its scalar extension with canonical
descent coaction. -/
noncomputable def affineDescentComparison : ModuleCat A ⥤ AffineDescent f :=
  Comonad.comparison (extendRestrictScalarsAdj.{u, u, u} f)

/-- The descended module is the equalizer of the coaction and the unit.

For `D : AffineDescent f`, this is literally
`equalizer ((restrictScalars f).map D.a) ((extendRestrictScalarsAdj f).unit.app _)`.
-/
noncomputable def descentFunctor : AffineDescent f ⥤ ModuleCat A :=
  Comonad.ComonadicityInternal.rightAdjointComparison (extendRestrictScalarsAdj.{u, u, u} f)

@[simp]
theorem descentFunctor_obj (D : AffineDescent f) :
    (descentFunctor f).obj D =
      equalizer ((restrictScalars f).map D.a)
        ((extendRestrictScalarsAdj.{u, u, u} f).unit.app ((restrictScalars f).obj D.A)) :=
  rfl

/-- The inclusion of the invariant module into the underlying restricted module. -/
noncomputable def descentEqualizerι (D : AffineDescent f) :
    (descentFunctor f).obj D ⟶ (restrictScalars f).obj D.A :=
  equalizer.ι ((restrictScalars f).map D.a)
    ((extendRestrictScalarsAdj.{u, u, u} f).unit.app ((restrictScalars f).obj D.A))

@[simp]
theorem descentEqualizerι_condition (D : AffineDescent f) :
    descentEqualizerι f D ≫ (restrictScalars f).map D.a =
      descentEqualizerι f D ≫
        (extendRestrictScalarsAdj.{u, u, u} f).unit.app ((restrictScalars f).obj D.A) :=
  equalizer.condition _ _

/-- The unit of extension and restriction is evaluation at `1`, i.e. `m ↦ 1 ⊗ m`. -/
theorem extension_unit_apply (M : ModuleCat A) (m : M) :
    ((extendRestrictScalarsAdj.{u, u, u} f).unit.app M) m =
      (1 : B) ⊗ₜ[A,f] m := by
  exact extendRestrictScalarsAdj_unit_app_apply f M m

/-- Equalizer morphisms into a descended module are determined by their underlying map into
the restricted carrier.  This is the uniqueness part of descent for arrows. -/
theorem descentHom_ext (D E : AffineDescent f)
    (g h : (descentFunctor f).obj D ⟶ (descentFunctor f).obj E)
    (w : g ≫ descentEqualizerι f E = h ≫ descentEqualizerι f E) :
    g = h := by
  apply equalizer.hom_ext
  exact w

/-- Explicitly descend a coalgebra morphism by lifting its underlying map through the two
equalizers. -/
noncomputable def descendedHom (D E : AffineDescent f) (φ : D ⟶ E) :
    (descentFunctor f).obj D ⟶ (descentFunctor f).obj E :=
  equalizer.lift (descentEqualizerι f D ≫ (restrictScalars f).map φ.f) (by
    rw [Category.assoc, ← Functor.map_comp, ← φ.h]
    rw [Functor.map_comp, ← Category.assoc, descentEqualizerι_condition]
    exact congrArg (fun k => descentEqualizerι f D ≫ k)
      ((extendRestrictScalarsAdj.{u, u, u} f).unit.naturality
        ((restrictScalars f).map φ.f))
  )

@[simp]
theorem descendedHom_comp_ι (D E : AffineDescent f) (φ : D ⟶ E) :
    descendedHom f D E φ ≫ descentEqualizerι f E =
      descentEqualizerι f D ≫ (restrictScalars f).map φ.f :=
  equalizer.lift_ι _ _

theorem descendedHom_unique (D E : AffineDescent f) (φ : D ⟶ E)
    (g : (descentFunctor f).obj D ⟶ (descentFunctor f).obj E)
    (w : g ≫ descentEqualizerι f E =
      descentEqualizerι f D ≫ (restrictScalars f).map φ.f) :
    g = descendedHom f D E φ := by
  apply descentHom_ext f D E
  rw [w, descendedHom_comp_ι]

/-- The adjunction whose left adjoint is the comparison and whose right adjoint is the
equalizer descent functor. -/
noncomputable def descentAdjunction :
    affineDescentComparison f ⊣ descentFunctor f :=
  Comonad.ComonadicityInternal.comparisonAdjunction (extendRestrictScalarsAdj.{u, u, u} f)

section FaithfullyFlat

variable (hf : f.FaithfullyFlat)

/-- Faithfully flat extension makes the affine comparison an equivalence. -/
theorem affineDescentComparison_isEquivalence (hf : f.FaithfullyFlat) :
    (affineDescentComparison f).IsEquivalence := by
  let h : ComonadicLeftAdjoint (extendScalars f) := comonadicExtendScalars hf
  exact h.eqv

/-- The effective affine descent equivalence, with inverse the equalizer descent functor. -/
noncomputable def affineDescentEquivalence (hf : f.FaithfullyFlat) :
    ModuleCat A ≌ AffineDescent f := by
  letI := comonadicExtendScalars hf
  letI : (affineDescentComparison f).IsEquivalence :=
    affineDescentComparison_isEquivalence f hf
  exact (descentAdjunction f).toEquivalence

@[simp]
theorem affineDescentEquivalence_functor (hf : f.FaithfullyFlat) :
    (affineDescentEquivalence f hf).functor = affineDescentComparison f := by
  rfl

@[simp]
theorem affineDescentEquivalence_inverse (hf : f.FaithfullyFlat) :
    (affineDescentEquivalence f hf).inverse = descentFunctor f := by
  rfl

/-- The unit identifies an `A`-module with the equalizer recovered from its canonical
descent data. -/
noncomputable def reconstructionIso (hf : f.FaithfullyFlat) (M : ModuleCat A) :
    M ≅ (descentFunctor f).obj ((affineDescentComparison f).obj M) :=
  by
    letI := comonadicExtendScalars hf
    letI : (affineDescentComparison f).IsEquivalence :=
      affineDescentComparison_isEquivalence f hf
    exact
      { hom := (descentAdjunction f).unit.app M
        inv := inv ((descentAdjunction f).unit.app M)
        hom_inv_id := IsIso.hom_inv_id _
        inv_hom_id := IsIso.inv_hom_id _ }

/-- The counit identifies the extension of a descended module with its original module. -/
noncomputable def extensionDescentIso (hf : f.FaithfullyFlat) (D : AffineDescent f) :
    (affineDescentComparison f).obj ((descentFunctor f).obj D) ≅ D :=
  by
    letI := comonadicExtendScalars hf
    letI : (affineDescentComparison f).IsEquivalence :=
      affineDescentComparison_isEquivalence f hf
    exact
      { hom := (descentAdjunction f).counit.app D
        inv := inv ((descentAdjunction f).counit.app D)
        hom_inv_id := IsIso.hom_inv_id _
        inv_hom_id := IsIso.inv_hom_id _ }

@[simp]
theorem reconstructionIso_hom (M : ModuleCat A) :
    (reconstructionIso f hf M).hom = (descentAdjunction f).unit.app M :=
  by
    rfl

@[simp]
theorem extensionDescentIso_hom (D : AffineDescent f) :
    (extensionDescentIso f hf D).hom = (descentAdjunction f).counit.app D :=
  by
    rfl

/-- On pure tensors, the reconstruction map is the expected action map.  In particular its
value on `1 ⊗ x` is the underlying invariant element. -/
theorem extensionDescentIso_hom_apply_one_tmul (hf : f.FaithfullyFlat) (D : AffineDescent f)
    (x : (descentFunctor f).obj D) :
    (extensionDescentIso f hf D).hom.f.hom ((1 : B) ⊗ₜ[A,f] x) =
      descentEqualizerι f D x := by
  rw [extensionDescentIso_hom f hf D]
  change ((descentAdjunction f).counit.app D).f ((1 : B) ⊗ₜ[A,f] x) = _
  change ((Comonad.ComonadicityInternal.comparisonAdjunction
      (extendRestrictScalarsAdj.{u, u, u} f)).counit.app D).f
      ((1 : B) ⊗ₜ[A,f] x) = _
  rw [Comonad.ComonadicityInternal.comparisonAdjunction_counit_f_aux]
  exact extendRestrictScalarsAdj_counit_app_apply_one_tmul f D.A
    (descentEqualizerι f D x)

end FaithfullyFlat

end GromovWitten.AlgebraicGeometry.Modules
