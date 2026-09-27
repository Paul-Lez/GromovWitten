/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroExt

/-!
# Contravariance in the source of a square-zero lifting problem

The coefficient square-zero extension is kept fixed while the source algebra is changed by an
algebra map.  `SourceMap` records the one compatibility equation needed to make this operation
well-typed when both source algebras have their own algebra structures on the quotient.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace SquareZero

universe u v w w' w'' w''' t

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
variable (M : Ideal B)

section Source

variable {A : Type w} {A' : Type w'} {A'' : Type w''} {A''' : Type w'''}
variable [CommRing A] [CommRing A'] [CommRing A'']
variable [CommRing A''']
variable [Algebra R A] [Algebra R A'] [Algebra R A'']
variable [Algebra R A''']
variable [Algebra A (B ⧸ M)] [Algebra A' (B ⧸ M)] [Algebra A'' (B ⧸ M)]
variable [Algebra A''' (B ⧸ M)]
/-- A map of source algebras over `R` which preserves the fixed map to the quotient. -/
structure SourceMap (R : Type u) {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (M : Ideal B) (A A' : Type*) [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] [Algebra A (B ⧸ M)] [Algebra A' (B ⧸ M)] where
  /-- The map in the source direction. -/
  hom : A →ₐ[R] A'
  /-- The two maps from `A` to the quotient agree. -/
  commutes : (algebraMap A' (B ⧸ M)).comp hom = algebraMap A (B ⧸ M)

namespace SourceMap

variable {M}

@[ext]
theorem ext {f g : SourceMap R M A A'} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity source map. -/
def id : SourceMap R M A A where
  hom := AlgHom.id R A
  commutes := by
    ext a
    simp

/-- Composition of source maps. -/
def comp (g : SourceMap R M A' A'') (f : SourceMap R M A A') : SourceMap R M A A'' where
  hom := g.hom.comp f.hom
  commutes := by
    ext a
    calc
      algebraMap A'' (B ⧸ M) (g.hom (f.hom a)) =
          algebraMap A' (B ⧸ M) (f.hom a) := congrArg (fun k => k (f.hom a)) g.commutes
      _ = algebraMap A (B ⧸ M) a := congrArg (fun k => k a) f.commutes

@[simp]
theorem hom_id : (id (M := M) (A := A)).hom = AlgHom.id R A :=
  rfl

@[simp]
theorem hom_comp (g : SourceMap R M A' A'') (f : SourceMap R M A A') :
    (g.comp f).hom = g.hom.comp f.hom :=
  rfl

@[simp]
theorem comp_id (f : SourceMap R M A A') :
    f.comp (id (M := M) (A := A)) = f := by
  apply ext
  simp [hom_comp]

@[simp]
theorem id_comp (f : SourceMap R M A A') :
    (id (M := M) (A := A')).comp f = f := by
  apply ext
  simp [hom_comp]

@[simp]
theorem comp_assoc (h : SourceMap R M A'' A''') (g : SourceMap R M A' A'')
    (f : SourceMap R M A A') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  simp [hom_comp, AlgHom.comp_assoc]

end SourceMap

variable {M} [IsSquareZero M]

/-! ### Restriction of lifts and derivations -/

variable [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)]
  [IsScalarTower R A'' (B ⧸ M)]

namespace SourceMap

/-- Restrict a lift along a compatible map of source algebras. -/
def restrictLift (f : SourceMap R M A A') (F : Lift R M A') : Lift R M A :=
  ⟨F.hom.comp f.hom, by
    ext a
    change Ideal.Quotient.mk M (F.hom (f.hom a)) = algebraMap A (B ⧸ M) a
    rw [Lift.mk_hom]
    exact congrArg (fun k => k a) f.commutes⟩

omit [IsSquareZero M] in
@[simp]
theorem restrictLift_hom (f : SourceMap R M A A') (F : Lift R M A') (a : A) :
    (restrictLift f F).hom a = F.hom (f.hom a) :=
  rfl

/-- Precompose a derivation with a compatible map of source algebras. -/
def restrictDer (f : SourceMap R M A A') (d : Derivation R A' (Coeff M)) :
    Derivation R A (Coeff M) where
  toLinearMap := d.toLinearMap.comp f.hom.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by
    have h := d.leibniz (f.hom a) (f.hom b)
    have ha : algebraMap A' (B ⧸ M) (f.hom a) = algebraMap A (B ⧸ M) a :=
      congrArg (fun k => k a) f.commutes
    have hb : algebraMap A' (B ⧸ M) (f.hom b) = algebraMap A (B ⧸ M) b :=
      congrArg (fun k => k b) f.commutes
    change d (f.hom (a * b)) = _
    rw [map_mul, h]
    change algebraMap A' (B ⧸ M) (f.hom a) • d (f.hom b) +
      algebraMap A' (B ⧸ M) (f.hom b) • d (f.hom a) = _
    rw [ha, hb]
    rfl

omit [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)] in
@[simp]
theorem restrictDer_apply (f : SourceMap R M A A') (d : Derivation R A' (Coeff M)) (a : A) :
    restrictDer f d a = d (f.hom a) :=
  rfl

omit [IsSquareZero M] in
@[simp]
theorem restrictLift_id (F : Lift R M A) :
    restrictLift (SourceMap.id (R := R) (M := M) (A := A)) F = F := by
  apply Lift.ext
  intro a
  change F.hom ((AlgHom.id R A) a) = F.hom a
  simp

omit [IsSquareZero M] in
@[simp]
theorem restrictLift_comp (g : SourceMap R M A' A'') (f : SourceMap R M A A')
    (F : Lift R M A'') :
    restrictLift f (restrictLift g F) = restrictLift (g.comp f) F := by
  apply Lift.ext
  intro a
  rfl

omit [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem restrictDer_id (d : Derivation R A (Coeff M)) :
    restrictDer (SourceMap.id (R := R) (M := M) (A := A)) d = d := by
  apply Derivation.ext
  intro a
  rfl

omit [IsScalarTower R A (B ⧸ M)] [IsScalarTower R A' (B ⧸ M)]
  [IsScalarTower R A'' (B ⧸ M)] in
@[simp]
theorem restrictDer_comp (g : SourceMap R M A' A'') (f : SourceMap R M A A')
    (d : Derivation R A'' (Coeff M)) :
    restrictDer f (restrictDer g d) = restrictDer (g.comp f) d := by
  apply Derivation.ext
  intro a
  rfl

@[simp]
theorem restrictLift_vsub (f : SourceMap R M A A') (F G : Lift R M A') :
    restrictLift f F -ᵥ restrictLift f G = restrictDer f (F -ᵥ G) := by
  apply Derivation.ext
  intro a
  rfl

@[simp]
theorem restrictLift_vadd (f : SourceMap R M A A') (d : Derivation R A' (Coeff M))
    (F : Lift R M A') :
    restrictLift f (d +ᵥ F) = restrictDer f d +ᵥ restrictLift f F := by
  apply Lift.ext
  intro a
  change (d (f.hom a)).val + F.hom (f.hom a) =
    (restrictDer f d a).val + F.hom (f.hom a)
  rfl

end SourceMap

end Source

/-! ### Naturality for a map of presentations of the same algebra -/

section Presentation

variable {A : Type w} [CommRing A] [Algebra R A] [Algebra A (B ⧸ M)]
  [IsScalarTower R A (B ⧸ M)] [IsSquareZero M]
variable {P P' : Algebra.Extension.{t} R A}

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- A map of presentations is a compatible source map after both ambient rings act through `A`. -/
noncomputable def presentationSourceMap (f : P.Hom P') :
    SourceMap R M P.Ring P'.Ring where
  hom := f.toAlgHom
  commutes := by
    ext p
    change algebraMap A (B ⧸ M) (algebraMap P'.Ring A (f.toAlgHom p)) =
      algebraMap A (B ⧸ M) (algebraMap P.Ring A p)
    change algebraMap A (B ⧸ M) (algebraMap P'.Ring A (f.toRingHom p)) =
      algebraMap A (B ⧸ M) (algebraMap P.Ring A p)
    rw [f.algebraMap_toRingHom]
    simp

/-- Precomposition with the conormal map of a presentation morphism. -/
noncomputable def presentationConormalPrecomp (f : P.Hom P') :
    (P'.Cotangent →ₗ[A] Coeff M) →ₗ[A] (P.Cotangent →ₗ[A] Coeff M) where
  toFun θ := θ.comp (Algebra.Extension.Cotangent.map f)
  map_add' θ η := by
    ext x
    simp
  map_smul' a θ := by
    ext x
    simp

omit [Algebra R B] [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem presentationConormalPrecomp_apply (f : P.Hom P')
    (θ : P'.Cotangent →ₗ[A] Coeff M) (x : P.Cotangent) :
    presentationConormalPrecomp M f θ x = θ (Algebra.Extension.Cotangent.map f x) :=
  rfl

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction of an ambient derivation commutes with restriction to the conormal module. -/
theorem presentationRestrictDer (f : P.Hom P')
    (d : Derivation R P'.Ring (Coeff M)) :
    restrictDer R M P (SourceMap.restrictDer (presentationSourceMap M f) d) =
      presentationConormalPrecomp M f (restrictDer R M P' d) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  rfl

/-- The obstruction cocycle commutes with restricting an ambient lift along a presentation map. -/
theorem presentationObstructionMap (f : P.Hom P') (F : Lift R M P'.Ring) :
    obstructionMap R M P (SourceMap.restrictLift (presentationSourceMap M f) F) =
      presentationConormalPrecomp M f (obstructionMap R M P' F) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  refine Coeff.ext M ?_
  rfl

/-- Precomposition with a presentation morphism descends to obstruction cokernels. -/
noncomputable def presentationObstructionGroupMap (f : P.Hom P') :
    ObstructionGroup R M P' →ₗ[A] ObstructionGroup R M P :=
  Submodule.mapQ _ _ (presentationConormalPrecomp M f) (by
    rintro _ ⟨d, rfl⟩
    refine ⟨SourceMap.restrictDer (presentationSourceMap M f) d, ?_⟩
    exact presentationRestrictDer M f d)

omit [IsScalarTower R A (B ⧸ M)] in
@[simp]
theorem presentationObstructionGroupMap_mk (f : P.Hom P')
    (θ : P'.Cotangent →ₗ[A] Coeff M) :
    presentationObstructionGroupMap M f (Submodule.Quotient.mk θ) =
      Submodule.Quotient.mk (presentationConormalPrecomp M f θ) :=
  rfl

/-- The difference of precomposition maps for two presentation morphisms is a coboundary. -/
theorem presentationConormalPrecomp_sub_mem_coboundary (f g : P.Hom P')
    (θ : P'.Cotangent →ₗ[A] Coeff M) :
    presentationConormalPrecomp M f θ - presentationConormalPrecomp M g θ ∈
      coboundary R M P := by
  rw [mem_coboundary_iff_comp_cotangentComplex]
  refine ⟨θ.comp (Algebra.Extension.Hom.sub f g), ?_⟩
  refine LinearMap.ext fun x => ?_
  symm
  change θ (Algebra.Extension.Cotangent.map f x) -
      θ (Algebra.Extension.Cotangent.map g x) =
    θ (Algebra.Extension.Hom.sub f g (P.cotangentComplex x))
  rw [← map_sub]
  change θ ((Algebra.Extension.Cotangent.map f - Algebra.Extension.Cotangent.map g) x) = _
  rw [Algebra.Extension.Cotangent.map_sub_map]
  rfl

/-- The obstruction cokernel map depends only on the map of presented algebras. -/
theorem presentationObstructionGroupMap_eq (f g : P.Hom P') :
    presentationObstructionGroupMap M f = presentationObstructionGroupMap M g := by
  apply LinearMap.ext
  intro x
  obtain ⟨θ, rfl⟩ := Submodule.Quotient.mk_surjective (coboundary R M P') x
  rw [presentationObstructionGroupMap_mk, presentationObstructionGroupMap_mk]
  apply (Submodule.Quotient.eq _).2
  exact presentationConormalPrecomp_sub_mem_coboundary M f g θ

/-- The obstruction class is natural under a map of presentations of the same algebra. -/
theorem presentationObstructionGroupMap_obstruction (f : P.Hom P')
    [Nonempty (Lift R M P'.Ring)] [Nonempty (Lift R M P.Ring)] :
    presentationObstructionGroupMap M f (obstruction R M P') = obstruction R M P := by
  obtain ⟨F⟩ := (inferInstance : Nonempty (Lift R M P'.Ring))
  let F₀ : Lift R M P.Ring := SourceMap.restrictLift (presentationSourceMap M f) F
  rw [obstruction_eq M F, presentationObstructionGroupMap_mk,
    ← presentationObstructionMap M f F,
    obstruction_eq M F₀]

end Presentation

end SquareZero

end GromovWitten.AlgebraicGeometry.CotangentComplex
