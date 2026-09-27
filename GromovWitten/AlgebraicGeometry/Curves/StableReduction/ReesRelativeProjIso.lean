/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesRelativeProj

/-!
# The old and new global Rees constructions

The original global blowup gluing uses the polynomial-valued grading
`ReesBlowup.grade`, while `RelativeProj` uses the submodule-valued grading
`gradeSubmodule`.  They have the same homogeneous elements.  This file gives
the resulting chartwise and global scheme isomorphisms, including the
transition compatibility needed for the colimit.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Polynomial

namespace GromovWitten.AlgebraicGeometry.GlobalBlowup

open ReesBlowup ReesBlowupOfEq ReesGradedBaseChange RelativeProj

universe u

noncomputable section

variable {R : Type u} [CommRing R]

/-- The identity map between the two presentations of the Rees grading. -/
def submoduleToGrade (I : Ideal R) :
    gradeSubmodule I →+*ᵍ ReesBlowup.grade I where
  toRingHom :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  map_mem := by
    intro n x hx
    exact hx

/-- The inverse identity map between the two presentations of the Rees grading. -/
def gradeToSubmodule (I : Ideal R) :
    ReesBlowup.grade I →+*ᵍ gradeSubmodule I where
  toRingHom :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  map_mem := by
    intro n x hx
    exact hx

theorem submoduleToGrade_comp_gradeToSubmodule (I : Ideal R) :
    (submoduleToGrade I).comp (gradeToSubmodule I) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro x
  rfl

theorem gradeToSubmodule_comp_submoduleToGrade (I : Ideal R) :
    (gradeToSubmodule I).comp (submoduleToGrade I) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro x
  rfl

theorem submoduleToGrade_irr (I : Ideal R) :
    HomogeneousIdeal.irrelevant (ReesBlowup.grade I) ≤
      HomogeneousIdeal.map (submoduleToGrade I)
        (HomogeneousIdeal.irrelevant (gradeSubmodule I)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn x hx
  change x ∈ gradeSubmodule I n at hx
  exact Ideal.mem_map_of_mem (submoduleToGrade I)
    (HomogeneousIdeal.mem_irrelevant_of_mem (gradeSubmodule I) hn hx)

theorem gradeToSubmodule_irr (I : Ideal R) :
    HomogeneousIdeal.irrelevant (gradeSubmodule I) ≤
      HomogeneousIdeal.map (gradeToSubmodule I)
        (HomogeneousIdeal.irrelevant (ReesBlowup.grade I)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn x hx
  change x ∈ ReesBlowup.grade I n at hx
  exact Ideal.mem_map_of_mem (gradeToSubmodule I)
    (HomogeneousIdeal.mem_irrelevant_of_mem (ReesBlowup.grade I) hn hx)

/-- The affine Proj isomorphism between the two Rees grading presentations. -/
def affineRelativeProjIso (I : Ideal R) :
    AlgebraicGeometry.Proj (ReesBlowup.grade I) ≅
      AlgebraicGeometry.Proj (gradeSubmodule I) where
  hom := Proj.map (submoduleToGrade I) (submoduleToGrade_irr I)
  inv := Proj.map (gradeToSubmodule I) (gradeToSubmodule_irr I)
  hom_inv_id := by
    calc
      _ = Proj.map ((submoduleToGrade I).comp (gradeToSubmodule I)) _ := by
        symm
        exact Proj.map_comp (gradeToSubmodule I) (submoduleToGrade I)
          (gradeToSubmodule_irr I) (submoduleToGrade_irr I)
      _ = Proj.map (GradedRingHom.id _) _ := by
        congr 1
      _ = _ := Proj.map_id
  inv_hom_id := by
    calc
      _ = Proj.map ((gradeToSubmodule I).comp (submoduleToGrade I)) _ := by
        symm
        exact Proj.map_comp (submoduleToGrade I) (gradeToSubmodule I)
          (submoduleToGrade_irr I) (gradeToSubmodule_irr I)
      _ = Proj.map (GradedRingHom.id _) _ := by
        congr 1
      _ = _ := Proj.map_id

/-- The affine comparison respects the maps to the affine base. -/
theorem affineRelativeProjIso_hom_projection (I : Ideal R) :
    (affineRelativeProjIso I).hom ≫ ProjBaseChange.projection (gradeSubmodule I) =
      ReesBlowup.projection I := by
  refine (Proj.mapAffineOpenCover (submoduleToGrade I) (submoduleToGrade_irr I)).openCover.hom_ext
    _ _ ?_
  rintro ⟨⟨d, hd⟩, s, hs⟩
  let _ : Algebra R (gradeSubmodule I 0) := inferInstance
  let _ : Algebra R (HomogeneousLocalization.Away (gradeSubmodule I)
      (s : reesAlgebra I)) := ProjBaseChange.awayAlgebra (s : reesAlgebra I)
  let si : gradeSubmodule I d := ⟨s, hs⟩
  let chartO : Spec (.of (HomogeneousLocalization.Away (ReesBlowup.grade I)
      (submoduleToGrade I si))) ⟶ Proj (ReesBlowup.grade I) :=
    Proj.awayι (ReesBlowup.grade I) (submoduleToGrade I si)
      (show submoduleToGrade I si ∈ ReesBlowup.grade I d from si.property) hd
  let chartN : Spec (.of (HomogeneousLocalization.Away (gradeSubmodule I)
      (si : reesAlgebra I))) ⟶ Proj (gradeSubmodule I) :=
    Proj.awayι (gradeSubmodule I) (si : reesAlgebra I) si.property hd
  change chartO ≫ Proj.map (submoduleToGrade I) (submoduleToGrade_irr I) ≫
      ProjBaseChange.projection (gradeSubmodule I) =
    chartO ≫ ReesBlowup.projection I
  have haway : chartO ≫ Proj.map (submoduleToGrade I) (submoduleToGrade_irr I) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (submoduleToGrade I) (si : reesAlgebra I))) ≫ chartN := by
    exact Proj.awayι_comp_map (f := submoduleToGrade I)
      (hf := submoduleToGrade_irr I) (i := d) hd (si : reesAlgebra I) si.property
  calc
    _ = (chartO ≫ Proj.map (submoduleToGrade I) (submoduleToGrade_irr I)) ≫
        ProjBaseChange.projection (gradeSubmodule I) := by
      simp only [Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (submoduleToGrade I) (si : reesAlgebra I))) ≫ chartN) ≫
        ProjBaseChange.projection (gradeSubmodule I) := by
      rw [haway]
    _ = _ := by
      calc
        _ = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
            (submoduleToGrade I) (si : reesAlgebra I))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R
                (HomogeneousLocalization.Away (gradeSubmodule I)
                  (si : reesAlgebra I)))) := by
          simp only [Category.assoc]
          rw [ProjBaseChange.awayι_projection]
        _ = Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.Away.map
            (submoduleToGrade I) (si : reesAlgebra I)).comp (algebraMap R
              (HomogeneousLocalization.Away (gradeSubmodule I)
                (si : reesAlgebra I))))) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        _ = Spec.map (CommRingCat.ofHom
            (ReesBlowup.awayBaseHom I (submoduleToGrade I si))) := by
          congr 2
          apply RingHom.ext
          intro a
          change (HomogeneousLocalization.Away.map (submoduleToGrade I)
              (si : reesAlgebra I)
              ((HomogeneousLocalization.fromZeroRingHom (gradeSubmodule I)
                (Submonoid.powers (si : reesAlgebra I)))
                (algebraMap R (gradeSubmodule I 0) a))) =
            (HomogeneousLocalization.fromZeroRingHom (ReesBlowup.grade I)
              (Submonoid.powers (submoduleToGrade I si)))
              ((ReesBlowup.zeroEquiv I).symm.toRingHom a)
          apply HomogeneousLocalization.val_injective
          have h1 : ∀ y : gradeSubmodule I 0,
              HomogeneousLocalization.fromZeroRingHom (gradeSubmodule I)
                  (Submonoid.powers (si : reesAlgebra I)) y =
                HomogeneousLocalization.mk ⟨0, y, 1, one_mem _⟩ := fun _ ↦ rfl
          have h2 : ∀ y : ReesBlowup.grade I 0,
              HomogeneousLocalization.fromZeroRingHom (ReesBlowup.grade I)
                  (Submonoid.powers (submoduleToGrade I si)) y =
                HomogeneousLocalization.mk ⟨0, y, 1, one_mem _⟩ := fun _ ↦ rfl
          rw [HomogeneousLocalization.Away.map, h1, h2,
            HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mk]
          congr 1
          apply Subtype.ext
          simp [ReesBlowup.zeroEquiv, ReesBlowup.component, submoduleToGrade]
        _ = chartO ≫ ReesBlowup.projection I := by
          rw [ReesBlowup.awayι_comp_projection]

section Global

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} (𝓘 : X.IdealSheafData)

private def oldTransition {U V : X.affineOpens} (h : U ≤ V) :
    ReesBlowup.grade (𝓘.ideal V) →+*ᵍ ReesBlowup.grade (𝓘.ideal U) :=
  ReesBlowupOfEq.gradedMapOfEq (𝓘.ideal V) (GlobalBlowup.res X h) (𝓘.ideal U)
    (𝓘.map_ideal h)

private def newTransition {U V : X.affineOpens} (h : U ≤ V) :
    gradeSubmodule (𝓘.ideal V) →+*ᵍ gradeSubmodule (𝓘.ideal U) :=
  ReesGradedBaseChange.gradedMapSubmoduleOfEq (𝓘.ideal V) (GlobalBlowup.res X h)
    (𝓘.ideal U) (𝓘.map_ideal h)

private theorem transition_comm {U V : X.affineOpens} (h : U ≤ V) :
    (oldTransition 𝓘 h).comp (submoduleToGrade (𝓘.ideal V)) =
      (submoduleToGrade (𝓘.ideal U)).comp (newTransition 𝓘 h) := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  change ((p : reesAlgebra (𝓘.ideal V)) : Polynomial (Γ(X, V.1))).map
        (GlobalBlowup.res X h) =
      ((p : reesAlgebra (𝓘.ideal V)) : Polynomial (Γ(X, V.1))).map
        (GlobalBlowup.res X h)
  rfl

private def functorIso (U : X.affineOpens) :
    (GlobalBlowup.gluingFunctor X 𝓘).obj U ≅
      (RelativeProj.gluingFunctor X (GlobalBlowup.gradedData X 𝓘)).obj U :=
  affineRelativeProjIso (𝓘.ideal U)

private theorem functorIso_hom_gluingApp (U : X.affineOpens) :
    (affineRelativeProjIso (𝓘.ideal U)).hom ≫
        RelativeProj.gluingApp X (GlobalBlowup.gradedData X 𝓘) U =
      GlobalBlowup.gluingApp X 𝓘 U := by
  change (affineRelativeProjIso (𝓘.ideal U)).hom ≫
      ProjBaseChange.projection (gradeSubmodule (𝓘.ideal U)) ≫
        (GlobalBlowup.isAffineOpen X U).isoSpec.inv =
    ReesBlowup.projection (𝓘.ideal U) ≫
      (GlobalBlowup.isAffineOpen X U).isoSpec.inv
  rw [← Category.assoc, affineRelativeProjIso_hom_projection]

private theorem functorIso_naturality {U V : X.affineOpens} (h : U ⟶ V) :
    (GlobalBlowup.gluingFunctor X 𝓘).map h ≫ (functorIso 𝓘 V).hom =
      (functorIso 𝓘 U).hom ≫
        (RelativeProj.gluingFunctor X (GlobalBlowup.gradedData X 𝓘)).map h := by
  change Proj.map (oldTransition 𝓘 (leOfHom h)) _ ≫
      Proj.map (submoduleToGrade (𝓘.ideal V)) _ =
    Proj.map (submoduleToGrade (𝓘.ideal U)) _ ≫
      Proj.map (newTransition 𝓘 (leOfHom h)) _
  calc
    _ = Proj.map ((oldTransition 𝓘 (leOfHom h)).comp
        (submoduleToGrade (𝓘.ideal V))) _ := by
      symm
      apply Proj.map_comp
    _ = Proj.map ((submoduleToGrade (𝓘.ideal U)).comp
        (newTransition 𝓘 (leOfHom h))) _ := by
      exact ReesBlowupOfEq.projMap_congr (transition_comm 𝓘 (leOfHom h)) _
    _ = _ := by
      apply Proj.map_comp

private def gluingNatIso :
    (GlobalBlowup.gluingData X 𝓘).functor ≅
      (RelativeProj.gluingData X (GlobalBlowup.gradedData X 𝓘)).functor :=
  NatIso.ofComponents (functorIso 𝓘) (functorIso_naturality 𝓘)

/-- The old global Rees blowup is canonically isomorphic to the relative `Proj`
construction based on the submodule-valued Rees grading. -/
def relativeBlowupIso : GlobalBlowup.blowup X 𝓘 ≅
    GlobalBlowup.relativeBlowup X 𝓘 :=
  HasColimit.isoOfNatIso (gluingNatIso 𝓘)

theorem relativeBlowupIso_hom_toBase :
    (relativeBlowupIso 𝓘).hom ≫
        RelativeProj.toBase X (GlobalBlowup.gradedData X 𝓘) =
      GlobalBlowup.toBase X 𝓘 := by
  apply colimit.hom_ext
  intro U
  unfold relativeBlowupIso
  rw [← Category.assoc, HasColimit.isoOfNatIso_ι_hom]
  rw [Category.assoc]
  rw [RelativeProj.toBase, GlobalBlowup.toBase]
  rw [(RelativeProj.gluingData X (GlobalBlowup.gradedData X 𝓘)).ι_toBase U,
    (GlobalBlowup.gluingData X 𝓘).ι_toBase U]
  change (affineRelativeProjIso (𝓘.ideal U)).hom ≫
      RelativeProj.gluingApp X (GlobalBlowup.gradedData X 𝓘) U ≫
        X.directedAffineCover.f U =
    GlobalBlowup.gluingApp X 𝓘 U ≫ X.directedAffineCover.f U
  rw [← Category.assoc]
  have hlocal := functorIso_hom_gluingApp (𝓘 := 𝓘) (show X.affineOpens from U)
  exact congrArg (fun q ↦ q ≫ X.directedAffineCover.f U) hlocal

end Global

end
end GromovWitten.AlgebraicGeometry.GlobalBlowup
