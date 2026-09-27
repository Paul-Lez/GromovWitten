/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange

/-!
# Affine pullback of associated module sheaves

The affine pullback statement is obtained from uniqueness of left adjoints.  The
right adjoints are identified by the fact that sections of a pushforward over
the top open are the sections over the inverse image of the top open; the
restriction of scalars records the resulting change of coefficient ring.
-/

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Global sections identify affine pushforward with restriction of scalars. -/
def affineGammaIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom := by
  let e := AlgebraicGeometry.pushforwardCompModulesSpecToSheafIso φ
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R).toTopCat ⋙
    (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj (.op ⊤)
  dsimp [moduleSpecΓFunctor]
  exact Functor.isoWhiskerRight e H

def affinePullbackAdjunction :
    tilde.functor (R := R) ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))

def affineExtendAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))

/-- Pullback of an affine associated module is associated to scalar extension. -/
def affinePullbackTildeIso :
    tilde.functor (R := R) ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S) := by
  exact
    ((conjugateIsoEquiv (affinePullbackAdjunction φ) (affineExtendAdjunction φ)).symm
      (affineGammaIso φ)).symm

/-- The affine pullback isomorphism is compatible with the two adjunction counits. -/
theorem affinePullbackTildeIso_counit {N : (Spec S).Modules} :
    (affinePullbackTildeIso φ).hom.app
        ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≫
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S)).map
        ((affineGammaIso φ).hom.app N) ≫
      (affineExtendAdjunction φ).counit.app N =
    (affinePullbackAdjunction φ).counit.app N := by
  let adj₁ := affinePullbackAdjunction φ
  let adj₂ := affineExtendAdjunction φ
  let e := affineGammaIso φ
  let i := ((conjugateIsoEquiv adj₁ adj₂).symm e).symm
  have h := conjugateEquiv_counit_symm adj₁ adj₂ e.hom N
  change i.hom.app
      ((moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) ≫
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor (R := S)).map
        (e.hom.app N) ≫ adj₂.counit.app N = adj₁.counit.app N
  rw [h]
  change i.hom.app _ ≫ i.inv.app _ ≫ adj₁.counit.app N = _
  simp

/-- On an affine scheme, a morphism is an isomorphism when its global-sections map
is an isomorphism and both `fromTildeΓ` counits are isomorphisms. -/
theorem isIso_of_isIso_fromTildeΓ {R : CommRingCat.{u}}
    {N P : (Spec R).Modules} (f : N ⟶ P)
    [hN : IsIso N.fromTildeΓ] [hP : IsIso P.fromTildeΓ]
    [hΓ : IsIso ((moduleSpecΓFunctor (R := R)).map f)] : IsIso f := by
  have hn := (tilde.adjunction (R := R)).counit.naturality f
  change (tilde.functor (R := R)).map ((moduleSpecΓFunctor (R := R)).map f) ≫
      P.fromTildeΓ = N.fromTildeΓ ≫ f at hn
  refine @IsIso.of_isIso_comp_left _ _ _ _ _ N.fromTildeΓ f hN ?_
  rw [← hn]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) hP

section TensorBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable (M : ModuleCat (CommRingCat.of B))

local notation "P" => B ⊗[A] C

local instance : Algebra B P := Algebra.TensorProduct.leftAlgebra
local instance : Algebra C P := Algebra.TensorProduct.rightAlgebra
local instance : Module A M :=
  Module.compHom M (algebraMap A B)
local instance : IsScalarTower A B M :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance : SMulCommClass A B M := by
  infer_instance

abbrev affineTensorBaseChange_cancel (M : ModuleCat (CommRingCat.of B)) :
    (M ⊗[B] P) ≃ₗ[B] (M ⊗[A] C) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M C

abbrev affineTensorBaseChange_reorder₁ (M : ModuleCat (CommRingCat.of B)) :
    (P ⊗[B] M) ≃ₗ[B] (M ⊗[B] P) :=
  TensorProduct.comm B P M

abbrev affineTensorBaseChange_reorder₂ (M : ModuleCat (CommRingCat.of B)) :
    (M ⊗[A] C) ≃ₗ[A] (C ⊗[A] M) :=
  TensorProduct.comm A M C

private def affineTensorBaseChange_fun (M : ModuleCat (CommRingCat.of B)) :
    P ⊗[B] M → C ⊗[A] M := fun z =>
  (affineTensorBaseChange_reorder₂ M)
    ((affineTensorBaseChange_cancel M)
      ((affineTensorBaseChange_reorder₁ M) z))

private def affineTensorBaseChange_map (M : ModuleCat (CommRingCat.of B)) :
    P ⊗[B] M →ₗ[C] C ⊗[A] M :=
  { toFun := affineTensorBaseChange_fun M
    map_add' := by
      intro x y
      simp [affineTensorBaseChange_fun]
    map_smul' := by
      intro c z
      have back_add (x y : P ⊗[B] M) :
          affineTensorBaseChange_fun M (x + y) =
            affineTensorBaseChange_fun M x + affineTensorBaseChange_fun M y := by
        simp [affineTensorBaseChange_fun]
      induction z using TensorProduct.induction_on with
      | zero => simp [affineTensorBaseChange_fun]
      | tmul p m =>
        induction p using TensorProduct.induction_on with
        | zero => simp [affineTensorBaseChange_fun]
        | tmul b d =>
          change affineTensorBaseChange_fun M
              ((c • (b ⊗ₜ[A] d)) ⊗ₜ[B] m) = _
          have hcd : c • (b ⊗ₜ[A] d) = b ⊗ₜ[A] (c * d) := by
            rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            simp
          rw [hcd]
          simp [affineTensorBaseChange_fun, TensorProduct.smul_tmul']
        | add p q hp hq =>
          change affineTensorBaseChange_fun M
              ((c • (p + q)) ⊗ₜ[B] m) = _
          have hpq : c • (p + q) = c • p + c • q := smul_add c p q
          calc
            affineTensorBaseChange_fun M ((c • (p + q)) ⊗ₜ[B] m) =
                affineTensorBaseChange_fun M
                  ((c • p) ⊗ₜ[B] m + (c • q) ⊗ₜ[B] m) := by
              rw [hpq, add_tmul]
            _ = affineTensorBaseChange_fun M ((c • p) ⊗ₜ[B] m) +
                affineTensorBaseChange_fun M ((c • q) ⊗ₜ[B] m) := back_add _ _
            _ = c • affineTensorBaseChange_fun M (p ⊗ₜ[B] m) +
                c • affineTensorBaseChange_fun M (q ⊗ₜ[B] m) := by
              have hp' : affineTensorBaseChange_fun M ((c • p) ⊗ₜ[B] m) =
                  c • affineTensorBaseChange_fun M (p ⊗ₜ[B] m) := by
                simpa only [TensorProduct.smul_tmul', RingHom.id_apply] using hp
              have hq' : affineTensorBaseChange_fun M ((c • q) ⊗ₜ[B] m) =
                  c • affineTensorBaseChange_fun M (q ⊗ₜ[B] m) := by
                simpa only [TensorProduct.smul_tmul', RingHom.id_apply] using hq
              rw [hp', hq']
            _ = c • affineTensorBaseChange_fun M ((p + q) ⊗ₜ[B] m) := by
              rw [add_tmul]
              rw [back_add]
              exact (smul_add c (affineTensorBaseChange_fun M (p ⊗ₜ[B] m))
                (affineTensorBaseChange_fun M (q ⊗ₜ[B] m))).symm
      | add x y hx hy =>
        change affineTensorBaseChange_fun M (c • (x + y)) = _
        have hxy : c • (x + y) = c • x + c • y := smul_add c x y
        calc
          affineTensorBaseChange_fun M (c • (x + y)) =
              affineTensorBaseChange_fun M (c • x + c • y) := by rw [hxy]
          _ = affineTensorBaseChange_fun M (c • x) +
              affineTensorBaseChange_fun M (c • y) := back_add _ _
          _ = c • affineTensorBaseChange_fun M x +
              c • affineTensorBaseChange_fun M y := by
            have hx' : affineTensorBaseChange_fun M (c • x) =
                c • affineTensorBaseChange_fun M x := by simpa using hx
            have hy' : affineTensorBaseChange_fun M (c • y) =
                c • affineTensorBaseChange_fun M y := by simpa using hy
            rw [hx', hy']
          _ = c • affineTensorBaseChange_fun M (x + y) := by
            rw [back_add]
            exact (smul_add c (affineTensorBaseChange_fun M x)
              (affineTensorBaseChange_fun M y)).symm }

/-- The canonical tensor identity underlying affine module base change. -/
def affineTensorBaseChangeIso (M : ModuleCat (CommRingCat.of B)) :
    (P ⊗[B] M) ≃ₗ[C] (C ⊗[A] M) :=
  LinearEquiv.ofBijective (affineTensorBaseChange_map M) (by
    exact (affineTensorBaseChange_reorder₂ M).bijective.comp
      ((affineTensorBaseChange_cancel M).bijective.comp
        (affineTensorBaseChange_reorder₁ M).bijective))

@[simp]
theorem affineTensorBaseChangeIso_tmul (b : B) (c : C) (m : M) :
    affineTensorBaseChangeIso M ((b ⊗ₜ[A] c) ⊗ₜ[B] m) = c ⊗ₜ[A] (b • m) := by
  rfl

/-- The same affine tensor identity as an isomorphism in `ModuleCat C`. -/
def affineTensorBaseChangeModuleIso :
    ModuleCat.of C (P ⊗[B] M) ≅ ModuleCat.of C (C ⊗[A] M) :=
  (affineTensorBaseChangeIso M).toModuleIso

end TensorBaseChange

end
end GromovWitten.AlgebraicGeometry.Curves
