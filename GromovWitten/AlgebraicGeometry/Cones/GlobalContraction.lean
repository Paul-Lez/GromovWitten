/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeSpecFunctoriality
import GromovWitten.AlgebraicGeometry.RelativeSpecAffineLine
import GromovWitten.AlgebraicGeometry.Cones.Graded
import GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus

/-!
# Global contractions from affine graded algebra data

`AlgebraData` contains only affine pieces and their quasi-coherent transition maps.  The structure
below adds genuine polynomial coactions and their transition equations.  Thus the global
contractions are constructed as compatible `RelativeSpec.Hom`s and then glued by the colimit.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

open RelativeSpec GradedCone GlobalBlowup
open VectorBundleTotalSpace
open Curves

universe u

noncomputable section

section Compatibility

variable {R R' S T : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R' T]

/-- A compatible ring map commutes with scalar contraction. -/
theorem contraction_natural_of_coaction
    (g : R →+* R') (f : S →+* T)
    (hbase : f.comp (algebraMap R S) = (algebraMap R' T).comp g)
    (ψ : S →ₐ[R] Polynomial S) (ψ' : T →ₐ[R'] Polynomial T)
    (hψ : ∀ s, Polynomial.map f (ψ s) = ψ' (f s)) (r : R) (s : S) :
    f (contraction ψ r s) = contraction ψ' (g r) (f s) := by
  change f (Polynomial.eval₂ (RingHom.id S) (algebraMap R S r) (ψ s)) = _
  have heval : Polynomial.eval₂ (RingHom.id S) (algebraMap R S r) (ψ s) =
      Polynomial.eval (algebraMap R S r) (ψ s) := by
    exact Polynomial.eval₂_at_apply (RingHom.id S) (algebraMap R S r)
  rw [heval, ← Polynomial.eval₂_hom f (algebraMap R S r)]
  change Polynomial.eval₂ f (f (algebraMap R S r)) (ψ s) = _
  have hb := congrArg (fun k => k r) hbase
  change f (algebraMap R S r) = algebraMap R' T (g r) at hb
  rw [hb, contraction]
  change Polynomial.eval₂ f (algebraMap R' T (g r)) (ψ s) =
    Polynomial.eval₂ (RingHom.id T) (algebraMap R' T (g r)) (ψ' (f s))
  rw [← hψ s, Polynomial.eval₂_map]
  rfl

end Compatibility

structure ConeAlgebraData (X : Scheme.{u}) extends AlgebraData X where
  /-- The polynomial coaction on each affine coordinate algebra. -/
  coaction : ∀ U : X.affineOpens, ring U →ₐ[Γ(X, U.1)] Polynomial (ring U)
  /-- The augmentation defining the local vertex. -/
  vertex : ∀ U : X.affineOpens, ring U →ₐ[Γ(X, U.1)] Γ(X, U.1)
  /-- The local coactions satisfy the counit and coassociativity laws. -/
  coaction_law : ∀ U, IsConeCoaction (coaction U)
  /-- The local augmentation is the zero-contraction vertex. -/
  vertex_law : ∀ U, IsConeVertex (coaction U) (vertex U)
  /-- Coactions commute with every affine restriction, coefficientwise. -/
  coaction_natural : ∀ {U V : X.affineOpens} (h : U ≤ V) (a : ring V),
    Polynomial.map (map h) (coaction V a) = coaction U (map h a)
  /-- Augmentations commute with every affine restriction. -/
  vertex_natural : ∀ {U V : X.affineOpens} (h : U ≤ V),
    (vertex U).toRingHom.comp (map h) = (res X h).comp (vertex V).toRingHom

namespace ConeAlgebraData

variable {X : Scheme.{u}} (𝒜 : ConeAlgebraData X)

private theorem base_natural {U V : X.affineOpens} (h : U ≤ V) :
    (𝒜.map h).comp (algebraMap Γ(X, V.1) (𝒜.ring V)) =
      (algebraMap Γ(X, U.1) (𝒜.ring U)).comp (res X h) := by
  ext a
  exact RelativeSpec.map_algebraMap X 𝒜.toAlgebraData h a

private theorem contraction_natural {U V : X.affineOpens} (h : U ≤ V)
    (r : Γ(X, V.1)) (a : 𝒜.ring V) :
    𝒜.map h (contraction (𝒜.coaction V) r a) =
      contraction (𝒜.coaction U) (res X h r) (𝒜.map h a) := by
  apply contraction_natural_of_coaction (res X h) (𝒜.map h)
    (base_natural 𝒜 h) (𝒜.coaction V) (𝒜.coaction U)
  · intro x
    exact 𝒜.coaction_natural h x

/-- The compatible affine algebra map contracting by the restriction of a global scalar. -/
def contractionHom (r : Γ(X, ⊤)) : RelativeSpec.Hom X 𝒜.toAlgebraData 𝒜.toAlgebraData where
  app U := contraction (𝒜.coaction U) (restrictTop X U.1 r)
  naturality {U V} h := by
    apply RingHom.ext
    intro a
    change contraction (𝒜.coaction U) (restrictTop X U.1 r) (𝒜.map h a) =
      𝒜.map h (contraction (𝒜.coaction V) (restrictTop X V.1 r) a)
    have hr : res X h (restrictTop X V.1 r) = restrictTop X U.1 r := by
      change (X.presheaf.map (homOfLE (h : U.1 ≤ V.1)).op).hom
          (restrictTop X V.1 r) = restrictTop X U.1 r
      exact @restrictTop_map X V.1 U.1 (homOfLE h) r
    rw [← hr]
    exact (contraction_natural 𝒜 h (restrictTop X V.1 r) a).symm

/-- The global contraction endomorphism of the relative spectrum. -/
noncomputable def contractionMap (r : Γ(X, ⊤)) :
    relativeSpec X 𝒜.toAlgebraData ⟶ relativeSpec X 𝒜.toAlgebraData :=
  (contractionHom 𝒜 r).map

@[simp]
theorem contractionMap_affineι (r : Γ(X, ⊤)) (U : X.affineOpens) :
    affineι X 𝒜.toAlgebraData U ≫ contractionMap 𝒜 r =
      Spec.map (CommRingCat.ofHom
        (contraction (𝒜.coaction U) (restrictTop X U.1 r)).toRingHom) ≫
        affineι X 𝒜.toAlgebraData U :=
  RelativeSpec.Hom.affineι_map (contractionHom 𝒜 r) U

theorem contractionMap_one : contractionMap 𝒜 (1 : Γ(X, ⊤)) = 𝟙 _ := by
  apply RelativeSpec.hom_ext
  intro U
  rw [contractionMap_affineι]
  rw [map_one, GradedCone.contraction_one (𝒜.coaction_law U)]
  have hid : (AlgHom.id Γ(X, U.1) (𝒜.ring U)).toRingHom = RingHom.id _ := rfl
  rw [hid, CommRingCat.ofHom_id, Spec.map_id]
  simp

theorem contractionMap_mul (r s : Γ(X, ⊤)) :
    contractionMap 𝒜 (r * s) = contractionMap 𝒜 r ≫ contractionMap 𝒜 s := by
  have hh : contractionHom 𝒜 (r * s) =
      (contractionHom 𝒜 r).comp (contractionHom 𝒜 s) := by
    apply RelativeSpec.Hom.ext
    intro U
    apply AlgHom.ext
    intro a
    change contraction (𝒜.coaction U) (restrictTop X U.1 (r * s)) a =
      contraction (𝒜.coaction U) (restrictTop X U.1 r)
        (contraction (𝒜.coaction U) (restrictTop X U.1 s) a)
    rw [map_mul]
    simpa using DFunLike.congr_fun
      (GradedCone.contraction_mul (𝒜.coaction_law U)
        (restrictTop X U.1 r) (restrictTop X U.1 s)) a
  change (contractionHom 𝒜 (r * s)).map =
    (contractionHom 𝒜 r).map ≫ (contractionHom 𝒜 s).map
  rw [← RelativeSpec.Hom.map_comp, hh]

/-- The compatible family of local augmentations, as a morphism from the relative structure sheaf
to the cone algebra. -/
def vertexHom : RelativeSpec.Hom X (structureData X) 𝒜.toAlgebraData where
  app U := 𝒜.vertex U
  naturality {_U _V} h := 𝒜.vertex_natural h

/-- The vertex section of the global cone, transported through `Spec_X O_X ≅ X`. -/
noncomputable def vertexMap : X ⟶ relativeSpec X 𝒜.toAlgebraData :=
  (baseIso X).inv ≫ (vertexHom 𝒜).map

theorem vertexMap_affineι (U : X.affineOpens) :
    affineι X (structureData X) U ≫ (vertexHom 𝒜).map =
      Spec.map (CommRingCat.ofHom (𝒜.vertex U).toRingHom) ≫
        affineι X 𝒜.toAlgebraData U :=
  RelativeSpec.Hom.affineι_map (vertexHom 𝒜) U

/-- The zero contraction factors through the local vertex augmentation. -/
def zeroHom : RelativeSpec.Hom X 𝒜.toAlgebraData 𝒜.toAlgebraData where
  app U := (Algebra.ofId Γ(X, U.1) (𝒜.ring U)).comp (𝒜.vertex U)
  naturality {U V} h := by
    apply RingHom.ext
    intro a
    change algebraMap Γ(X, U.1) (𝒜.ring U) (𝒜.vertex U (𝒜.map h a)) =
      𝒜.map h (algebraMap Γ(X, V.1) (𝒜.ring V) (𝒜.vertex V a))
    rw [RelativeSpec.map_algebraMap]
    exact congrArg (algebraMap Γ(X, U.1) (𝒜.ring U))
      (congrArg (fun f => f a) (𝒜.vertex_natural h))

theorem contractionMap_zero_hom :
    contractionMap 𝒜 (0 : Γ(X, ⊤)) = (zeroHom 𝒜).map := by
  have hh : contractionHom 𝒜 (0 : Γ(X, ⊤)) = zeroHom 𝒜 := by
    apply RelativeSpec.Hom.ext
    intro U
    apply AlgHom.ext
    intro a
    change contraction (𝒜.coaction U) (restrictTop X U.1 0) a =
      algebraMap Γ(X, U.1) (𝒜.ring U) (𝒜.vertex U a)
    rw [map_zero, 𝒜.vertex_law U]
    rfl
  exact congrArg RelativeSpec.Hom.map hh

theorem zeroHom_map_eq_toBase_comp_vertexMap :
    (zeroHom 𝒜).map = toBase X 𝒜.toAlgebraData ≫ vertexMap 𝒜 := by
  have hzero : zeroHom 𝒜 = (AlgebraData.toStructure 𝒜.toAlgebraData).comp
      (vertexHom 𝒜) := by
    apply RelativeSpec.Hom.ext
    intro U
    apply AlgHom.ext
    intro a
    rfl
  rw [hzero, RelativeSpec.Hom.map_comp]
  change (AlgebraData.toStructure 𝒜.toAlgebraData).map ≫ (vertexHom 𝒜).map =
    toBase X 𝒜.toAlgebraData ≫ (baseIso X).inv ≫ (vertexHom 𝒜).map
  rw [← AlgebraData.toStructure_map 𝒜.toAlgebraData]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem contractionMap_zero :
    contractionMap 𝒜 (0 : Γ(X, ⊤)) =
      toBase X 𝒜.toAlgebraData ≫ vertexMap 𝒜 := by
  rw [contractionMap_zero_hom, zeroHom_map_eq_toBase_comp_vertexMap]

theorem vertexMap_comp_toBase :
    vertexMap 𝒜 ≫ toBase X 𝒜.toAlgebraData = 𝟙 X := by
  rw [vertexMap, Category.assoc, RelativeSpec.Hom.map_toBase, ← baseIso_hom]
  exact (baseIso X).inv_hom_id

/-! ### The genuine polynomial coaction -/

/-- The local coactions form a morphism of quasi-coherent algebras
`A → A[t]`, hence a morphism `Spec_X A[t] → Spec_X A`. -/
def coactionHom : RelativeSpec.Hom X 𝒜.toAlgebraData.polynomial 𝒜.toAlgebraData where
  app U := 𝒜.coaction U
  naturality {U V} h := by
    apply RingHom.ext
    intro a
    exact (𝒜.coaction_natural h a).symm

/- The evaluation-at-one map is the counit on coordinate rings. -/
def counitHom : RelativeSpec.Hom X 𝒜.toAlgebraData 𝒜.toAlgebraData.polynomial where
  app U := evalHom (AlgHom.id Γ(X, U.1) (𝒜.ring U)) (1 : 𝒜.ring U)
  naturality {U V} h := by
    apply Polynomial.ringHom_ext
    · intro a
      change evalHom (AlgHom.id Γ(X, U.1) (𝒜.ring U)) 1
          (Polynomial.map (𝒜.map h) (Polynomial.C a)) =
        𝒜.map h (evalHom (AlgHom.id Γ(X, V.1) (𝒜.ring V)) 1 (Polynomial.C a))
      rw [Polynomial.map_C, evalHom_C, evalHom_C]
      rfl
    · change evalHom (AlgHom.id Γ(X, U.1) (𝒜.ring U)) 1
          (Polynomial.map (𝒜.map h) Polynomial.X) =
        𝒜.map h (evalHom (AlgHom.id Γ(X, V.1) (𝒜.ring V)) 1 Polynomial.X)
      rw [Polynomial.map_X, evalHom_X, evalHom_X]
      simp

/- The polynomial comultiplication `A[t] → A[t][u]`. -/
def comulHom : RelativeSpec.Hom X 𝒜.toAlgebraData.polynomial.polynomial
    𝒜.toAlgebraData.polynomial where
  app U := comul (R := Γ(X, U.1)) (S := 𝒜.ring U)
  naturality {U V} h := by
    apply Polynomial.ringHom_ext
    · intro a
      change comul (R := Γ(X, U.1)) (S := 𝒜.ring U)
          (Polynomial.map (𝒜.map h) (Polynomial.C a)) =
        Polynomial.map (Polynomial.mapRingHom (𝒜.map h))
          (comul (R := Γ(X, V.1)) (S := 𝒜.ring V) (Polynomial.C a))
      simp [comul]
    · change comul (R := Γ(X, U.1)) (S := 𝒜.ring U)
          (Polynomial.map (𝒜.map h) Polynomial.X) =
        Polynomial.map (Polynomial.mapRingHom (𝒜.map h))
          (comul (R := Γ(X, V.1)) (S := 𝒜.ring V) Polynomial.X)
      simp [comul]

noncomputable def coactionMap :
    relativeSpec X 𝒜.toAlgebraData.polynomial ⟶ relativeSpec X 𝒜.toAlgebraData :=
  (coactionHom 𝒜).map

noncomputable def counitMap :
    relativeSpec X 𝒜.toAlgebraData ⟶ relativeSpec X 𝒜.toAlgebraData.polynomial :=
  (counitHom 𝒜).map

noncomputable def comulMap :
    relativeSpec X 𝒜.toAlgebraData.polynomial.polynomial ⟶
      relativeSpec X 𝒜.toAlgebraData.polynomial :=
  (comulHom 𝒜).map

/-- The coaction is an actual morphism from the affine-line extension of the cone. -/
noncomputable def actionMap :
    pullback (toBase X 𝒜.toAlgebraData)
      (toBase X (structureData X).polynomial) ⟶
      relativeSpec X 𝒜.toAlgebraData :=
  (AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).inv ≫ coactionMap 𝒜

@[simp]
theorem polynomialIsoPullback_hom_comp_actionMap :
    (AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).hom ≫ actionMap 𝒜 =
      coactionMap 𝒜 := by
  simp [actionMap]

theorem actionMap_toBase :
    actionMap 𝒜 ≫ toBase X 𝒜.toAlgebraData =
      pullback.fst (toBase X 𝒜.toAlgebraData)
        (toBase X (structureData X).polynomial) ≫ toBase X 𝒜.toAlgebraData := by
  apply (cancel_epi (AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).hom).1
  change ((AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).hom ≫ actionMap 𝒜) ≫
      toBase X 𝒜.toAlgebraData =
    ((AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).hom ≫
      pullback.fst (toBase X 𝒜.toAlgebraData)
        (toBase X (structureData X).polynomial)) ≫ toBase X 𝒜.toAlgebraData
  rw [polynomialIsoPullback_hom_comp_actionMap]
  change (coactionHom 𝒜).map ≫ toBase X 𝒜.toAlgebraData = _
  rw [RelativeSpec.Hom.map_toBase]
  change toBase X 𝒜.toAlgebraData.polynomial =
    ((𝒜.toAlgebraData.isPullback_affineLine).isoPullback.hom ≫
      pullback.fst (toBase X 𝒜.toAlgebraData)
        (toBase X (structureData X).polynomial)) ≫ toBase X 𝒜.toAlgebraData
  rw [
    (𝒜.toAlgebraData.isPullback_affineLine).isoPullback_hom_fst]
  change toBase X 𝒜.toAlgebraData.polynomial =
    (𝒜.toAlgebraData.polynomialInclusion).map ≫ toBase X 𝒜.toAlgebraData
  rw [RelativeSpec.Hom.map_toBase]

theorem actionMap_toBase_snd :
    actionMap 𝒜 ≫ toBase X 𝒜.toAlgebraData =
      pullback.snd (toBase X 𝒜.toAlgebraData)
        (toBase X (structureData X).polynomial) ≫
        toBase X (structureData X).polynomial := by
  rw [actionMap_toBase]
  exact pullback.condition

theorem coactionMap_affineι (U : X.affineOpens) :
    affineι X 𝒜.toAlgebraData.polynomial U ≫ coactionMap 𝒜 =
      Spec.map (CommRingCat.ofHom (𝒜.coaction U).toRingHom) ≫
        affineι X 𝒜.toAlgebraData U :=
  RelativeSpec.Hom.affineι_map (coactionHom 𝒜) U

theorem coaction_counit_hom :
    (counitHom 𝒜).comp (coactionHom 𝒜) = RelativeSpec.Hom.id 𝒜.toAlgebraData := by
  apply RelativeSpec.Hom.ext
  intro U
  exact (𝒜.coaction_law U).counit

theorem coaction_coassoc_hom :
    (coactionHom 𝒜).polynomial.comp (coactionHom 𝒜) =
      (comulHom 𝒜).comp (coactionHom 𝒜) := by
  apply RelativeSpec.Hom.ext
  intro U
  change (Polynomial.mapAlgHom (𝒜.coaction U)).comp (𝒜.coaction U) =
    (comul (R := Γ(X, U.1)) (S := 𝒜.ring U)).comp (𝒜.coaction U)
  exact (𝒜.coaction_law U).coassoc

theorem counitMap_comp_coactionMap :
    counitMap 𝒜 ≫ coactionMap 𝒜 = 𝟙 _ := by
  change (counitHom 𝒜).map ≫ (coactionHom 𝒜).map = _
  rw [← RelativeSpec.Hom.map_comp, coaction_counit_hom, RelativeSpec.Hom.map_id]

/-- The scalar-one section of the polynomial presentation, transported to the product. -/
noncomputable def actionUnitMap :
    relativeSpec X 𝒜.toAlgebraData ⟶
      pullback (toBase X 𝒜.toAlgebraData)
        (toBase X (structureData X).polynomial) :=
  counitMap 𝒜 ≫ (AlgebraData.polynomialIsoPullback 𝒜.toAlgebraData).hom

theorem actionUnitMap_comp_actionMap : actionUnitMap 𝒜 ≫ actionMap 𝒜 = 𝟙 _ := by
  rw [actionUnitMap, Category.assoc, polynomialIsoPullback_hom_comp_actionMap,
    counitMap_comp_coactionMap]

theorem coactionPolynomialMap_comp_coactionMap :
    (coactionHom 𝒜).polynomial.map ≫ coactionMap 𝒜 =
      comulMap 𝒜 ≫ coactionMap 𝒜 := by
  change (coactionHom 𝒜).polynomial.map ≫ (coactionHom 𝒜).map =
    (comulHom 𝒜).map ≫ (coactionHom 𝒜).map
  rw [← RelativeSpec.Hom.map_comp, ← RelativeSpec.Hom.map_comp, coaction_coassoc_hom]

end ConeAlgebraData

end
end GromovWitten.AlgebraicGeometry
