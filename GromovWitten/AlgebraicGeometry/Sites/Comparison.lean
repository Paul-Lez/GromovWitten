/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Ring.ULift
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# The étale and fppf sites

The Behrend--Fantechi construction uses different sites for derived coherent complexes and for
torsors/cone stacks.  This file records that distinction at the type level.  It also proves that
the big étale topology is weaker than the big fppf topology and constructs the resulting
restriction functor on sheaves.  In particular, the comparison is an explicit functor and not a
definitional identification of sites.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Sites

universe u v w w'

abbrev Scheme := _root_.AlgebraicGeometry.Scheme

/-- Objects of the big fppf site. -/
abbrev BigFppfSite := Scheme.{u}

/-- Objects of the small étale site of `X`. -/
abbrev SmallEtaleSite (X : Scheme.{u}) := X.Etale

/-- The big fppf topology. -/
abbrev bigFppfTopology : GrothendieckTopology BigFppfSite.{u} :=
  Scheme.fppfTopology

/-- The small étale topology of `X`. -/
abbrev smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology (SmallEtaleSite X) :=
  Scheme.smallEtaleTopology X

/-- The forgetful functor from the small étale site to all schemes. -/
abbrev smallEtaleToBig (X : Scheme.{u}) : SmallEtaleSite X ⥤ BigFppfSite.{u} :=
  Scheme.Etale.forget X ⋙ Over.forget X

set_option linter.style.haveILetI false in
/-- Every étale covering family is an fppf covering family. -/
theorem etalePrecoverage_le_fppfPrecoverage :
    Scheme.etalePrecoverage.{u} ≤ Scheme.fppfPrecoverage.{u} := by
  apply Scheme.precoverage_mono
  intro X Y f hf
  let : _root_.AlgebraicGeometry.Etale f := hf
  exact ⟨inferInstance, inferInstance⟩

/-- The big étale topology is weaker than the big fppf topology. -/
theorem etaleTopology_le_fppfTopology :
    Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

/-- Restrict a sheaf for a stronger topology to a weaker topology on the same category. -/
def restrictTopology
    {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (h : J ≤ K)
    (A : Type w) [Category.{w'} A] : Sheaf K A ⥤ Sheaf J A where
  obj F := ⟨F.obj, F.property.of_le h⟩
  map f := ⟨f.hom⟩

@[simp]
theorem restrictTopology_obj_obj
    {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (h : J ≤ K)
    (A : Type w) [Category.{w'} A] (F : Sheaf K A) :
    ((restrictTopology h A).obj F).obj = F.obj :=
  rfl

/-- Restriction of big fppf sheaves to big étale sheaves. -/
def restrictFppfToEtale (A : Type w) [Category.{w'} A] :
    Sheaf Scheme.fppfTopology A ⥤ Sheaf Scheme.etaleTopology A :=
  restrictTopology etaleTopology_le_fppfTopology A

/-! ## The structure sheaf on the big sites -/

noncomputable section

/-- A one-element index type in the scheme universe. -/
abbrev RegularFunctionIndex : Type u := ULift.{u} Unit

/-- The absolute affine line, used to represent the functor of global regular functions. -/
abbrev absoluteAffineLine : Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec
    (.of (MvPolynomial RegularFunctionIndex (ULift.{u} ℤ)))

/-- A regular function on a scheme is the same thing as a morphism to the absolute affine line. -/
def globalSectionsEquiv (X : Scheme.{u}) :
    (X ⟶ absoluteAffineLine) ≃ Γ(X, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv RegularFunctionIndex).trans
    (Equiv.funUnique RegularFunctionIndex Γ(X, ⊤))

/-- The representing isomorphism for the presheaf of global regular functions. -/
def regularFunctionsYonedaIso :
    yoneda.obj absoluteAffineLine ≅ Scheme.Γ ⋙ forget CommRingCat.{u} :=
  NatIso.ofComponents (fun X ↦ (globalSectionsEquiv (Opposite.unop X)).toIso) (by
    intro X Y f
    ext g
    exact AffineSpace.toSpecMvPolyIntEquiv_comp
      (n := RegularFunctionIndex) (X := Opposite.unop Y)
      (Y := Opposite.unop X) f.unop g default)

/-- Global regular functions form an actual fppf sheaf of types because they are represented by
the absolute affine line. -/
theorem regularFunctions_isFppfSheaf :
    Presheaf.IsSheaf Scheme.fppfTopology
      (Scheme.Γ ⋙ forget CommRingCat.{u}) := by
  rw [← Presheaf.isSheaf_of_iso_iff regularFunctionsYonedaIso]
  exact Scheme.fppfTopology.yoneda.obj absoluteAffineLine |>.property

/-- Universe lift on rings.  The target universe supplies the limits required to regard regular
functions as a ring-valued sheaf on the large category of schemes. -/
def ringUliftFunctor : Functor RingCat.{u} RingCat.{u + 1} where
  obj R := RingCat.of (ULift.{u + 1} R)
  map {X Y} f := RingCat.ofHom
    ((ULift.ringEquiv (R := Y)).symm.toRingHom.comp
      (f.hom.comp (ULift.ringEquiv (R := X)).toRingHom))
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- Universe lift on commutative rings.  Unlike `ringUliftFunctor`, this retains the
commutativity needed for tensor products and symmetric powers of module sheaves. -/
def commRingUliftFunctor : Functor CommRingCat.{u} CommRingCat.{u + 1} where
  obj R := CommRingCat.of (ULift.{u + 1} R)
  map {X Y} f := CommRingCat.ofHom
    ((ULift.ringEquiv (R := Y)).symm.toRingHom.comp
      (f.hom.comp (ULift.ringEquiv (R := X)).toRingHom))
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- The ring-valued regular-function presheaf in a universe large enough for big-site descent. -/
def regularFunctionsRingPresheaf :
    Functor Scheme.{u}ᵒᵖ RingCat.{u + 1} :=
  Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙ ringUliftFunctor

/-- The commutative-ring-valued regular-function presheaf in the enlarged universe. -/
def regularFunctionsCommRingPresheaf :
    Functor Scheme.{u}ᵒᵖ CommRingCat.{u + 1} :=
  Scheme.Γ ⋙ commRingUliftFunctor

/-- Forgetting the lifted ring structure gives the ordinary regular-function presheaf followed
by universe lift. -/
def regularFunctionsRingForgetIso :
    regularFunctionsRingPresheaf ⋙ forget RingCat.{u + 1} ≅
      (Scheme.Γ ⋙ forget CommRingCat.{u}) ⋙ uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun X ↦ (Equiv.refl (ULift.{u + 1} Γ(Opposite.unop X, ⊤))).toIso)
    (by intros; rfl)

/-- Forgetting the lifted commutative-ring structure gives the represented regular-function
presheaf followed by universe lift. -/
def regularFunctionsCommRingForgetIso :
    regularFunctionsCommRingPresheaf ⋙ forget CommRingCat.{u + 1} ≅
      (Scheme.Γ ⋙ forget CommRingCat.{u}) ⋙ uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun X ↦ (Equiv.refl (ULift.{u + 1} Γ(Opposite.unop X, ⊤))).toIso)
    (by intros; rfl)

/-- The lifted ring-valued presheaf of regular functions is an actual fppf sheaf. -/
theorem regularFunctionsRing_isFppfSheaf :
    Presheaf.IsSheaf Scheme.fppfTopology regularFunctionsRingPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget RingCat)]
  rw [Presheaf.isSheaf_of_iso_iff regularFunctionsRingForgetIso]
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ _).mp regularFunctions_isFppfSheaf)

/-- Lifted regular functions are an actual commutative-ring-valued fppf sheaf. -/
theorem regularFunctionsCommRing_isFppfSheaf :
    Presheaf.IsSheaf Scheme.fppfTopology regularFunctionsCommRingPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)]
  rw [Presheaf.isSheaf_of_iso_iff regularFunctionsCommRingForgetIso]
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_comp_uliftFunctor _
    ((isSheaf_iff_isSheaf_of_type _ _).mp regularFunctions_isFppfSheaf)

/-- Regular functions are also a sheaf for the weaker big étale topology. -/
theorem regularFunctionsRing_isEtaleSheaf :
    Presheaf.IsSheaf Scheme.etaleTopology regularFunctionsRingPresheaf :=
  regularFunctionsRing_isFppfSheaf.of_le etaleTopology_le_fppfTopology

/-- Lifted commutative regular functions are also a sheaf for the big étale topology. -/
theorem regularFunctionsCommRing_isEtaleSheaf :
    Presheaf.IsSheaf Scheme.etaleTopology regularFunctionsCommRingPresheaf :=
  regularFunctionsCommRing_isFppfSheaf.of_le etaleTopology_le_fppfTopology

/-- Pull the actual regular-function sheaf back to a site whose topology is induced from a
scheme topology.  This is the common construction behind the big fppf and lisse-étale
structure sheaves of a stack. -/
def inducedRegularFunctionsRingSheaf
    {C : Type v} [Category.{w} C] (toScheme : Functor C Scheme.{u})
    (K : GrothendieckTopology Scheme.{u})
    (h : Presheaf.IsSheaf K regularFunctionsRingPresheaf) :
    Sheaf (toScheme.inducedTopology K) RingCat.{u + 1} where
  obj := toScheme.op ⋙ regularFunctionsRingPresheaf
  property := toScheme.op_comp_isSheaf_of_isSheaf
    (toScheme.inducedTopology K) K regularFunctionsRingPresheaf h

/-- Pull the commutative regular-function sheaf back to a site whose topology is induced from
a scheme topology. -/
def inducedRegularFunctionsCommRingSheaf
    {C : Type v} [Category.{w} C] (toScheme : Functor C Scheme.{u})
    (K : GrothendieckTopology Scheme.{u})
    (h : Presheaf.IsSheaf K regularFunctionsCommRingPresheaf) :
    Sheaf (toScheme.inducedTopology K) CommRingCat.{u + 1} where
  obj := toScheme.op ⋙ regularFunctionsCommRingPresheaf
  property := toScheme.op_comp_isSheaf_of_isSheaf
    (toScheme.inducedTopology K) K regularFunctionsCommRingPresheaf h

end

end GromovWitten.AlgebraicGeometry.Sites
