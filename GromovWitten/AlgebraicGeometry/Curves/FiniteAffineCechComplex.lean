/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ResolutionSectionsAugmentation
import GromovWitten.AlgebraicGeometry.Curves.AffineResolutionSections
import GromovWitten.AlgebraicGeometry.Curves.BaseSectionsPresheafBaseChange
import GromovWitten.AlgebraicGeometry.Curves.OpenAffineSectionsFlat
import GromovWitten.AlgebraicGeometry.FiniteAffineCover
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechFlat
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechQuasiIso
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechAugmentation

/-!
# Finite affine Čech complexes over an affine base

For a finite affine cover of a separated scheme, the section presheaf gives a
bounded nonnegative complex. Relative stalkwise flatness makes its terms flat.
Affine acyclicity and affine base change give local comparison quasi-isomorphisms.
These statements do not assert finite generation of cohomology for proper schemes.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry
noncomputable section
universe u
namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech HomologicalComplex
variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- The base-linear section presheaf concentrated in degree zero. -/
noncomputable def baseSectionsSingle (s : X ⟶ Spec R) (M : X.Modules) :
    PresheafComplex X.toTopCat R :=
  (single (Presheaves X.toTopCat R) (.up ℤ) 0).obj (baseSectionsPresheaf s M)

/-- Global sections of the finite Čech complex of the base-linear section presheaf. -/
noncomputable def baseFiniteCechComplex (s : X ⟶ Spec R) (M : X.Modules)
    (U : List X.Opens) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (finiteCechComplex (baseSectionsSingle s M) U).obj (op ⊤)

lemma baseFiniteCechComplex_bounded (s : X ⟶ Spec R) (M : X.Modules)
    (U : List X.Opens) (i : ℤ) (hi : i < 0 ∨ (U.length : ℤ) ≤ i) :
    IsZero ((baseFiniteCechComplex s M U).X i) := by
  apply Functor.map_isZero ((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op ⊤))
  apply finiteCechData_bounded_support _ _ U i hi
  intro j hj
  exact isZero_single_obj_X (.up ℤ) 0 (baseSectionsPresheaf s M) j hj

lemma baseFiniteCechComplex_flat (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    [X.IsSeparated] (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W)
    (hflat : ∀ x : X, Module.Flat R (relativeStalkBase s M x)) (i : ℤ) :
    Module.Flat R ((baseFiniteCechComplex s M U).X i) := by
  apply finiteCechData_flat_at (baseSectionsSingle s M) IsAffineOpen
    (fun V W hV hW => hV.inf hW) _ U ⊤ _ i
  · intro W hW j
    by_cases hj : j = 0
    · subst j
      have : Module.Flat R (baseSectionModule s W M) :=
        baseSections_flat_of_relative_stalks s M W hW hflat
      let e : ((baseSectionsSingle s M).X 0).obj (op W) ≅ baseSectionModule s W M :=
        ((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)).mapIso
          (singleObjXSelf (.up ℤ) 0 (baseSectionsPresheaf s M))
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    · have hz := isZero_single_obj_X (.up ℤ) 0 (baseSectionsPresheaf s M) j hj
      have hzero := Functor.map_isZero
        ((evaluation X.Opensᵒᵖ (ModuleCat R)).obj (op W)) hz
      have : Subsingleton (((baseSectionsSingle s M).X j).obj (op W)) :=
        ModuleCat.subsingleton_of_isZero hzero
      let _ : Module.Free R (((baseSectionsSingle s M).X j).obj (op W)) :=
        Module.Free.of_subsingleton _ _
      exact Module.Flat.of_free
  · intro W hW
    simpa only [top_inf_eq] using hU W hW
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
variable {R : CommRingCat.{u}} {X : Scheme.{u}}
/-- On a finite list of affine opens, the resolution augmentation induces a
quasi-isomorphism of finite Čech complexes. -/
lemma resolutionFiniteCechMap_quasiIso
    [IsLocallyNoetherian X] [X.IsSeparated]
    (s : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    {K : CochainComplex X.Modules ℕ} (a : (CochainComplex.single₀ _).obj M ⟶ K)
    [QuasiIso a]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (U : List X.Opens) (hU : ∀ W ∈ U, IsAffineOpen W) :
    QuasiIso ((evaluatePresheafComplexMap
      (finiteCechMap (resolutionSectionsAugmentation s a) U)).app (op ⊤)) := by
  refine finiteCechMap_quasiIso_at _ IsAffineOpen
    (fun V W hV hW => hV.inf hW) ?_ ⊤ U ?_
  · intro W hW
    have := affineOpen_sections_augmentation_quasiIso s W hW M a hK
    exact resolutionSectionsAugmentation_quasiIso_at s a W
  · intro W hW
    simpa only [top_inf_eq] using hU W hW
end GromovWitten.AlgebraicGeometry.Curves
namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
/-- The canonical base-change presheaf map induces a finite Čech quasi-isomorphism
for a list of affine opens. -/
lemma finiteCech_single_baseChange_quasiIso_at
    [X.IsSeparated] (s : X ⟶ Spec R) (φ : R ⟶ T)
    (p : Y ⟶ X) (g : Y ⟶ Spec T) (h : IsPullback p g s (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (U : List X.Opens)
    (hU : ∀ W ∈ U, IsAffineOpen W) :
    QuasiIso ((evaluatePresheafComplexMap
      (finiteCechMap ((HomologicalComplex.single (X.Opensᵒᵖ ⥤ ModuleCat T)
        (.up ℤ) 0).map (baseSectionsPresheafBaseChange s φ p g h M)) U)).app (op ⊤)) := by
  refine finiteCechMap_quasiIso_at _ IsAffineOpen
    (fun V W hV hW => hV.inf hW)
    (fun W hW => single_baseSectionsPresheafBaseChange_quasiIso_at s φ p g h M W hW)
    ⊤ U ?_
  intro W hW
  simpa only [top_inf_eq] using hU W hW
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology
open GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
variable {R : CommRingCat.{u}} {X : Scheme.{u}}
lemma coverUnion_eq_affineUnion (U : List X.Opens) : coverUnion U = affineUnion U := by
  induction U with
  | nil => rfl
  | cons W tail ih => exact congrArg (W ⊔ ·) ih

lemma exists_list_affine_cover [CompactSpace X] :
    ∃ U : List X.Opens, (∀ W ∈ U, IsAffineOpen W) ∧ coverUnion U = ⊤ := by
  obtain ⟨m, U, hU, hcover⟩ := exists_fin_affine_cover (X := X)
  refine ⟨List.ofFn U, ?_, ?_⟩
  · intro W hW
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
    exact hU i
  · rw [coverUnion_eq_affineUnion, affineUnion_ofFn, hcover]

lemma baseFiniteCechComplex_strictlyGE (s : X ⟶ Spec R) (M : X.Modules)
    (U : List X.Opens) : (baseFiniteCechComplex s M U).IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ _).mpr fun i hi =>
    baseFiniteCechComplex_bounded s M U i (Or.inl hi)
end GromovWitten.AlgebraicGeometry.Curves
