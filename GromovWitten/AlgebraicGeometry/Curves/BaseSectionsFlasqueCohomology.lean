/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheaf
import GromovWitten.AlgebraicGeometry.Curves.ModuleFlasqueSections
import GromovWitten.CategoryTheory.MapComplexExtension
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Base-linear cohomology from flasque resolutions

The section complexes agree with derived global sections as modules over the base
ring. Extension from natural to integer degrees preserves the comparison.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.SheafCohomology

universe u v

noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
noncomputable def baseSectionsTopIsoPushforward (s : X ⟶ Spec R) :
    baseSectionsFunctor s ⊤ ≅ Scheme.Modules.pushforward s ⋙ moduleSpecΓFunctor := by
  let e (M : X.Modules) : baseSectionModule s ⊤ M ≃ₗ[R] sectionsModuleCat R s M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change (baseToSections s ⊤).hom r • x = baseRingHom R s r • x
        have htop : baseToSections s ⊤ = (Scheme.ΓSpecIso R).inv ≫ s.appTop := by
          unfold baseToSections
          change (Scheme.ΓSpecIso R).inv ≫ s.appTop ≫ X.presheaf.map (𝟙 _) = _
          rw [X.presheaf.map_id, Category.comp_id]
        rw [htop]
        rfl }
  refine NatIso.ofComponents (fun M =>
    (e M).toModuleIso ≪≫ (pushforwardSectionsBaseLinearEquiv s M).toModuleIso.symm) ?_
  intro M N f
  apply ModuleCat.hom_ext
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def baseSectionsTopComplexIsoPushforward (s : X ⟶ Spec R)
    (K : CochainComplex X.Modules ℕ) :
    ((baseSectionsFunctor s ⊤).mapHomologicalComplex (.up ℕ)).obj K ≅
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℕ)).obj
      (((Scheme.Modules.pushforward s).mapHomologicalComplex (.up ℕ)).obj K) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (baseSectionsTopIsoPushforward s).app (K.X i)) ?_
  intro i j hij
  exact (baseSectionsTopIsoPushforward s).hom.naturality (K.d i j)

noncomputable def baseSectionsFlasqueHomologyIso (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) (n : ℕ) :
    (((baseSectionsFunctor s ⊤).mapHomologicalComplex (.up ℕ)).obj K).homology (n + 1) ≅
      cohomologyModuleCat R s M (n + 1) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) (n + 1)).mapIso
    (baseSectionsTopComplexIsoPushforward s K) ≪≫
      moduleFlasqueResolutionSectionsIsoCohomology s a hK n

noncomputable def cohomologyZeroDerivedSectionsLinearEquiv (M : X.Modules) :
    cohomology X M 0 ≃ₗ[Γ(X, ⊤)] (derivedSectionsModuleCat M (⊤ : X.Opens) 0 : Type u) := by
  let e : (cohomology X M 0 : Type u) ≃+
      (derivedSectionsModuleCat M (⊤ : X.Opens) 0 : Type u) :=
    sheafHRightDerivedSectionsAddEquiv_zero
      (F := ((moduleToSheafAb X).obj M :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  let f : cohomology X M 0 →ₗ[Γ(X, ⊤)]
      (derivedSectionsModuleCat M (⊤ : X.Opens) 0 : Type u) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro r x
        change e (Sheaf.H.map (sectionSMul M r) 0 x) =
          ((sections (⊤ : X.Opens)).rightDerived 0).map (sectionSMul M r) (e x)
        exact sheafHRightDerivedSectionsAddEquiv_zero_naturality (sectionSMul M r) x }
  exact LinearEquiv.ofBijective f e.bijective

noncomputable def baseSectionsFlasqueHomologyIsoAll (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) (n : ℕ) :
    (((baseSectionsFunctor s ⊤).mapHomologicalComplex (.up ℕ)).obj K).homology n ≅
      cohomologyModuleCat R s M n := by
  cases n with
  | zero =>
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) 0).mapIso
        (baseSectionsTopComplexIsoPushforward s K) ≪≫
        moduleFlasqueResolutionSectionsIsoDerived s a hK 0 ≪≫
        ((ModuleCat.restrictScalars (baseRingHom R s)).mapIso
          (cohomologyZeroDerivedSectionsLinearEquiv M).toModuleIso).symm
  | succ n => exact baseSectionsFlasqueHomologyIso s a hK n

/-- Integer-indexed global sections of a flasque resolution compute the actual
base-linear sheaf cohomology groups, including degree zero. -/
noncomputable def intBaseSectionsFlasqueHomologyIso (s : X ⟶ Spec R)
    {M : X.Modules} {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ _).obj M ⟶ K) [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) (n : ℕ) :
    (((baseSectionsFunctor s ⊤).mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ≅
      cohomologyModuleCat R s M n :=
  CategoryTheory.Functor.mapExtendHomologyIso (baseSectionsFunctor s ⊤)
    ComplexShape.embeddingUpNat K n ≪≫ baseSectionsFlasqueHomologyIsoAll s a hK n

lemma moduleFlasque_extend_nat (K : CochainComplex X.Modules ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n))) (i : ℤ) :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj
      ((K.extend ComplexShape.embeddingUpNat).X i)) := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have := hK n
    exact TopCat.Sheaf.isFlasque_of_iso
      ((moduleToSheafAb X).mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)).symm
  · have hz : IsZero ((K.extend ComplexShape.embeddingUpNat).X i) :=
      K.isZero_extend_X ComplexShape.embeddingUpNat i (by
        intro n hn
        change (n : ℤ) = i at hn
        omega)
    have : Injective ((moduleToSheafAb X).obj
        ((K.extend ComplexShape.embeddingUpNat).X i)) :=
      ((moduleToSheafAb X).map_isZero hz).injective
    exact TopCat.Sheaf.isFlasque_of_injective _ _

end GromovWitten.AlgebraicGeometry.Curves
