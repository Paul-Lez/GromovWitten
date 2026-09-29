/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.OpenPullbackSections

/-!
# Base-linear sections on an affine open immersion

This file restricts the canonical open-immersion section comparison to a base
ring. The scalar identity is expressed through the structure morphism and the
global section maps, so the resulting equivalence is an honest linear
equivalence over the base ring.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R A : CommRingCat.{u}} {X : Scheme.{u}}

/-- The scalar map from the base ring to sections on an open of `X`. -/
def baseToSections (s : X ⟶ Spec R) (U : X.Opens) :
    R ⟶ CommRingCat.of Γ(X, U) :=
  (Scheme.ΓSpecIso R).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op

/-- The scalar map induced by an affine open immersion. -/
def openSectionsRingHom (f : Spec A ⟶ X) [IsOpenImmersion f] :
    A ⟶ CommRingCat.of Γ(X, f.opensRange) :=
  (Scheme.ΓSpecIso A).inv ≫ (IsOpenImmersion.ΓIsoTop f).hom

/-- The affine-open scalar map agrees with the structure-morphism scalar map. -/
lemma openSectionsRingHom_base (s : X ⟶ Spec R) (f : Spec A ⟶ X)
    [IsOpenImmersion f] (φ : R ⟶ A) (hcomp : f ≫ s = Spec.map φ) :
    φ ≫ openSectionsRingHom f = baseToSections s f.opensRange := by
  dsimp [openSectionsRingHom, baseToSections]
  rw [← Category.assoc]
  rw [Scheme.ΓSpecIso_inv_naturality, ← hcomp, Scheme.Hom.comp_appTop]
  have hfi :
      Scheme.Hom.appTop f ≫ (IsOpenImmersion.ΓIsoTop f).hom =
        X.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op := by
    dsimp [AlgebraicGeometry.IsOpenImmersion.ΓIsoTop]
    have hfi0 :
        Scheme.Hom.app f (⊤ : X.Opens) ≫
            (Scheme.Hom.appIso f (⊤ : (Spec A).Opens)).inv =
          X.presheaf.map
            (homOfLE (show f ''ᵁ (⊤ : (Spec A).Opens) ≤ ⊤ from le_top)).op := by
      exact Scheme.Hom.app_appIso_inv f (⊤ : X.Opens)
    change (Scheme.Hom.app f (⊤ : X.Opens) ≫
      (Scheme.Hom.appIso f (⊤ : (Spec A).Opens)).inv) ≫
        X.presheaf.map (eqToIso (Scheme.Hom.image_top_eq_opensRange f).symm).op.hom = _
    rw [hfi0]
    rw [← X.presheaf.map_comp]
    rfl
  simp only [Category.assoc]
  rw [hfi]

/-- Sections on an open, viewed as a module over the base ring. -/
abbrev baseSectionModule (s : X ⟶ Spec R) (U : X.Opens) (M : X.Modules) :
    ModuleCat R :=
  (ModuleCat.restrictScalars (baseToSections s U).hom).obj
    (ModuleCat.of (Γ(X, U)) Γ(M, U))

@[instance_reducible]
def baseSectionModuleStructure (s : X ⟶ Spec R) (U : X.Opens) (M : X.Modules) :
    Module R Γ(M, U) :=
  Module.compHom _ (baseToSections s U).hom

/-- The open-immersion section comparison as a linear equivalence over the base. -/
def openPullbackSectionsLinearEquiv (s : X ⟶ Spec R) (f : Spec A ⟶ X)
    [IsOpenImmersion f] (φ : R ⟶ A) (hcomp : f ≫ s = Spec.map φ)
    (M : X.Modules) :
    (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.pullback f).obj M)) ≃ₗ[R]
      baseSectionModule s f.opensRange M := by
  letI : Module R
      ((moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.pullback f).obj M)) :=
    Module.compHom
      ((moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.pullback f).obj M))
      φ.hom
  let eMap :
      ((moduleSpecΓFunctor (R := A)).obj ((Scheme.Modules.pullback f).obj M)) →ₗ[R]
        (baseSectionModule s f.opensRange M) :=
    { toFun := fun x => (openPullbackSectionsIso f M).hom x
      map_add' := by
        intro x y
        exact map_add (ConcreteCategory.hom (openPullbackSectionsIso f M).hom) x y
      map_smul' := by
        intro r x
        change (openPullbackSectionsIso f M).hom (φ.hom r • x) =
          (baseToSections s f.opensRange).hom r •
            (openPullbackSectionsIso f M).hom x
        rw [openPullbackSectionsIso_smul]
        have hring := congrArg CommRingCat.Hom.hom
          (openSectionsRingHom_base s f φ hcomp)
        have hring' (r : R) :
            (openSectionsRingHom f).hom (φ.hom r) =
              (baseToSections s f.opensRange).hom r := by
          have h := congrArg (fun g => g r) hring
          simpa only [CommRingCat.comp_apply] using h
        change (openSectionsRingHom f).hom (φ.hom r) •
            (openPullbackSectionsIso f M).hom x =
          (baseToSections s f.opensRange).hom r •
            (openPullbackSectionsIso f M).hom x
        rw [hring' r] }
  exact LinearEquiv.ofBijective eMap
    (ConcreteCategory.bijective_of_isIso (openPullbackSectionsIso f M).hom)

@[simp]
lemma openPullbackSectionsLinearEquiv_apply (s : X ⟶ Spec R) (f : Spec A ⟶ X)
    [IsOpenImmersion f] (φ : R ⟶ A) (hcomp : f ≫ s = Spec.map φ)
    (M : X.Modules) (x : (moduleSpecΓFunctor (R := A)).obj
      ((Scheme.Modules.pullback f).obj M)) :
    openPullbackSectionsLinearEquiv s f φ hcomp M x =
      (openPullbackSectionsIso f M).hom x := rfl

/-- Restriction of sections, viewed as a linear map over the base ring. -/
def baseSectionRestrictionLinear (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    @LinearMap R R _ _ (RingHom.id R) Γ(M, U) Γ(M, V) _ _
      (baseSectionModuleStructure s U M) (baseSectionModuleStructure s V M) := by
  letI : Module R Γ(M, U) := baseSectionModuleStructure s U M
  letI : Module R Γ(M, V) := baseSectionModuleStructure s V M
  exact LinearMap.mk
    (AddMonoidHom.mk' (fun x : Γ(M, U) => M.presheaf.map i.op x) (by simp)) (by
      intro r x
      change M.presheaf.map i.op ((baseToSections s U).hom r • x) =
        (baseToSections s V).hom r • M.presheaf.map i.op x
      rw [M.map_smul]
      have hbase (r : R) :
          X.presheaf.map i.op ((baseToSections s U).hom r) =
            (baseToSections s V).hom r := by
        change X.presheaf.map i.op
            (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
              (s.appTop ((Scheme.ΓSpecIso R).inv r))) =
          X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
            (s.appTop ((Scheme.ΓSpecIso R).inv r))
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
        congr 2
      rw [hbase r])

@[simp]
lemma baseSectionRestrictionLinear_apply (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    baseSectionRestrictionLinear s M i x = M.presheaf.map i.op x := by rfl

/-- The restriction map on base-linear section modules. -/
def baseSectionRestrictionMap (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :
    baseSectionModule s U M ⟶ baseSectionModule s V M := by
  letI : Module R Γ(M, U) := baseSectionModuleStructure s U M
  letI : Module R Γ(M, V) := baseSectionModuleStructure s V M
  exact ModuleCat.ofHom (baseSectionRestrictionLinear s M i)

@[simp]
lemma baseSectionRestrictionMap_apply (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) (x : baseSectionModule s U M) :
    baseSectionRestrictionMap s M i x = M.presheaf.map i.op x := by rfl

@[simp]
lemma baseSectionRestrictionMap_id (s : X ⟶ Spec R) (M : X.Modules)
    (U : X.Opens) :
    baseSectionRestrictionMap s M (𝟙 U) = 𝟙 (baseSectionModule s U M) := by
  apply ModuleCat.hom_ext
  ext x
  change Γ(M, U) at x
  change M.presheaf.map (𝟙 U).op x = x
  simpa only [op_id, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom (M.presheaf.map_id (op U)) x

@[simp]
lemma baseSectionRestrictionMap_comp (s : X ⟶ Spec R) (M : X.Modules)
    {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) :
    baseSectionRestrictionMap s M i ≫ baseSectionRestrictionMap s M j =
      baseSectionRestrictionMap s M (j ≫ i) := by
  apply ModuleCat.hom_ext
  ext x
  change Γ(M, U) at x
  change M.presheaf.map j.op (M.presheaf.map i.op x) =
    M.presheaf.map (j ≫ i).op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

/-- Transport base-linear sections across an equality of opens. -/
def baseSectionCongr (s : X ⟶ Spec R) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    baseSectionModule s U M ≃ₗ[R] baseSectionModule s V M :=
  LinearEquiv.ofBijective (baseSectionRestrictionLinear s M (eqToHom h.symm))
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom h.symm).op))

@[simp]
lemma baseSectionCongr_apply (s : X ⟶ Spec R) (M : X.Modules)
    {U V : X.Opens} (h : U = V) (x : baseSectionModule s U M) :
    baseSectionCongr s M h x = M.presheaf.map (eqToHom h.symm).op x := rfl

end GromovWitten.AlgebraicGeometry.Curves
