/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Affine
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# Affine normal-cone examples

This file fixes the strict nonregular affine test from the Behrend--Fantechi roadmap.  The
coordinate ring is the node `k[x,y]/(xy)`, and the centre is its origin ideal `(x,y)`.  The
definitions feed directly into `AffineNormalCone`, rather than introducing a second example-only
notion of normal cone.
-/

namespace GromovWitten.AlgebraicGeometry

universe u

namespace NodalNormalCone

variable (k : Type u) [Field k]

/-- The polynomial ring `k[x,y]`, with variables indexed by `Fin 2`. -/
abbrev PolynomialRing := MvPolynomial (Fin 2) k

/-- The nodal equation ideal `(xy)`. -/
noncomputable def relationIdeal : Ideal (PolynomialRing k) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The coordinate ring `k[x,y]/(xy)` of the affine node. -/
abbrev CoordinateRing := PolynomialRing k ⧸ relationIdeal k

/-- The image of the first coordinate in the nodal ring. -/
noncomputable def x : CoordinateRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X 0)

/-- The image of the second coordinate in the nodal ring. -/
noncomputable def y : CoordinateRing k :=
  Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.X 1)

/-- The ideal `(x,y)` defining the origin of the node. -/
noncomputable def originIdeal : Ideal (CoordinateRing k) :=
  Ideal.span {x k, y k}

@[simp]
theorem x_mul_y : x k * y k = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

theorem x_mem_origin : x k ∈ originIdeal k :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem y_mem_origin : y k ∈ originIdeal k :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Evaluation of the nodal ring at a pair `(a,b)` satisfying `ab=0`. -/
noncomputable def evalAt (a b : k) (h : a * b = 0) : CoordinateRing k →ₐ[k] k := by
  refine Ideal.Quotient.liftₐ (relationIdeal k) (MvPolynomial.aeval ![a, b]) ?_
  intro p hp
  have hpker := (show relationIdeal k ≤
      RingHom.ker (MvPolynomial.aeval ![a, b]).toRingHom by
    rw [relationIdeal, Ideal.span_le]
    rintro _ rfl
    simp [h]) hp
  change MvPolynomial.aeval ![a, b] p = 0 at hpker
  exact hpker

@[simp]
theorem evalAt_x (a b : k) (h : a * b = 0) : evalAt k a b h (x k) = a := by
  change ((evalAt k a b h).comp
    (Ideal.Quotient.mkₐ k (relationIdeal k))) (MvPolynomial.X 0) = a
  rw [evalAt, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

@[simp]
theorem evalAt_y (a b : k) (h : a * b = 0) : evalAt k a b h (y k) = b := by
  change ((evalAt k a b h).comp
    (Ideal.Quotient.mkₐ k (relationIdeal k))) (MvPolynomial.X 1) = b
  rw [evalAt, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

/-- The first branch coordinate is nonzero. -/
theorem x_ne_zero : x k ≠ 0 := by
  intro hx
  have h := congrArg (evalAt k 1 0 (by simp)) hx
  rw [evalAt_x, map_zero] at h
  exact one_ne_zero h

/-- The second branch coordinate is nonzero. -/
theorem y_ne_zero : y k ≠ 0 := by
  intro hy
  have h := congrArg (evalAt k 0 1 (by simp)) hy
  rw [evalAt_y, map_zero] at h
  exact one_ne_zero h

/-- The node ring has a genuine zero divisor in each branch direction. -/
theorem x_has_nonzero_annihilator :
    ∃ z : CoordinateRing k, z ≠ 0 ∧ x k * z = 0 :=
  ⟨y k, y_ne_zero k, x_mul_y k⟩

/-- The associated graded coordinate ring of the normal cone at the node's origin. -/
abbrev NormalConeCoordinateRing :=
  AffineNormalCone.associatedGradedRing (CoordinateRing k) (originIdeal k)

/-- The normal cone of the origin in the affine node. -/
noncomputable abbrev normalCone : _root_.AlgebraicGeometry.Scheme.{u} :=
  AffineNormalCone.scheme (CoordinateRing k) (originIdeal k)

/-- The conormal module of the origin in the affine node. -/
abbrev ConormalModule := (originIdeal k).Cotangent

/-- The normal sheaf of the origin in the affine node. -/
noncomputable abbrev normalSheaf : _root_.AlgebraicGeometry.Scheme.{u} :=
  AffineNormalCone.normalSheaf (CoordinateRing k) (originIdeal k)

/-- The polynomial plane `k[a,b]`, the coordinate ring of the normal sheaf model. -/
abbrev NormalSheafModelRing := MvPolynomial (Fin 2) k

/-- The nodal tangent cone model `k[a,b]/(ab)`. -/
abbrev NormalConeModelRing := NormalSheafModelRing k ⧸ relationIdeal k

/-- The closed immersion of the nodal cone into its two-dimensional normal-sheaf model is
induced by quotienting by `ab`. -/
noncomputable def normalConeModelQuotient :
    NormalSheafModelRing k →+* NormalConeModelRing k :=
  Ideal.Quotient.mk (relationIdeal k)

/-- The coordinate-ring map defining the nodal cone is surjective. -/
theorem normalConeModelQuotient_surjective :
    Function.Surjective (normalConeModelQuotient k) :=
  Ideal.Quotient.mk_surjective

/-- The equation `ab` is nonzero in the polynomial normal sheaf. -/
theorem normalSheaf_relation_ne_zero :
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ≠
      (0 : NormalSheafModelRing k) := by
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1)

/-- The equation `ab` vanishes on the nodal normal-cone model. -/
theorem normalCone_relation_eq_zero :
    normalConeModelQuotient k
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Consequently `Spec k[a,b]/(ab)` is a proper closed subcone of `Spec k[a,b]`. -/
theorem normalConeModelQuotient_not_injective :
    ¬ Function.Injective (normalConeModelQuotient k) := by
  intro h
  have heq :
      normalConeModelQuotient k
          (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) =
        normalConeModelQuotient k 0 := by
    rw [normalCone_relation_eq_zero, map_zero]
  exact normalSheaf_relation_ne_zero k (h heq)

/-- The explicit nodal tangent-cone model has equation `ab=0` and is a proper closed subcone of
the polynomial plane; this conclusion does not depend on separately supplied proof data. -/
theorem model_is_proper_closed_subcone :
    Function.Surjective (normalConeModelQuotient k) ∧
      ¬ Function.Injective (normalConeModelQuotient k) :=
  ⟨normalConeModelQuotient_surjective k, normalConeModelQuotient_not_injective k⟩

/-- The two coordinate directions as elements of the conormal module. -/
noncomputable def conormalX : ConormalModule k :=
  (originIdeal k).toCotangent ⟨x k, x_mem_origin k⟩

/-- The two coordinate directions as elements of the conormal module. -/
noncomputable def conormalY : ConormalModule k :=
  (originIdeal k).toCotangent ⟨y k, y_mem_origin k⟩

/-- The dual numbers used to test a tangent direction of the node. -/
abbrev DualNumbers := TrivSqZeroExt k k

/-- The two coordinates of the diagonal tangent vector. -/
def diagonalTangentPoint : Fin 2 → DualNumbers k :=
  ![TrivSqZeroExt.inr (1 : k), TrivSqZeroExt.inr (1 : k)]

/-- The tangent vector sending both branch coordinates to `ε`.  It factors through the nodal
quotient because `ε² = 0`. -/
noncomputable def diagonalTangentEval : CoordinateRing k →ₐ[k] DualNumbers k := by
  refine Ideal.Quotient.liftₐ (relationIdeal k)
    (MvPolynomial.aeval (diagonalTangentPoint k)) ?_
  intro p hp
  have hpker := (show relationIdeal k ≤ RingHom.ker
      (MvPolynomial.aeval
        (diagonalTangentPoint k)).toRingHom by
    rw [relationIdeal, Ideal.span_le]
    rintro _ rfl
    change MvPolynomial.aeval
      (diagonalTangentPoint k)
        (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) =
          (0 : DualNumbers k)
    rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact TrivSqZeroExt.inr_mul_inr k (1 : k) 1) hp
  change MvPolynomial.aeval
    (diagonalTangentPoint k) p = 0 at hpker
  exact hpker

@[simp]
theorem diagonalTangentEval_x :
    diagonalTangentEval k (x k) = TrivSqZeroExt.inr 1 := by
  change ((diagonalTangentEval k).comp
    (Ideal.Quotient.mkₐ k (relationIdeal k))) (MvPolynomial.X 0) = _
  rw [diagonalTangentEval, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

@[simp]
theorem diagonalTangentEval_y :
    diagonalTangentEval k (y k) = TrivSqZeroExt.inr 1 := by
  change ((diagonalTangentEval k).comp
    (Ideal.Quotient.mkₐ k (relationIdeal k))) (MvPolynomial.X 1) = _
  rw [diagonalTangentEval, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]
  rfl

/-- The residue homomorphism underlying the displayed tangent vector. -/
noncomputable def diagonalResidue : CoordinateRing k →+* k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom.comp
    (diagonalTangentEval k).toRingHom

/-- Both generators of the origin ideal vanish under the residue homomorphism. -/
theorem originIdeal_le_diagonalResidue_ker :
    originIdeal k ≤ RingHom.ker (diagonalResidue k) := by
  rw [originIdeal, Ideal.span_le]
  rintro z (rfl | rfl)
  · simp [diagonalResidue]
  · simp [diagonalResidue]

/-- The tangent-vector residue map factors through the closed point. -/
noncomputable def quotientResidue :
    CoordinateRing k ⧸ originIdeal k →+* k :=
  Ideal.Quotient.lift (originIdeal k) (diagonalResidue k)
    (originIdeal_le_diagonalResidue_ker k)

noncomputable local instance : Algebra (CoordinateRing k) k :=
  (diagonalResidue k).toAlgebra

noncomputable local instance : Algebra (CoordinateRing k ⧸ originIdeal k) k :=
  (quotientResidue k).toAlgebra

noncomputable local instance : Module (CoordinateRing k ⧸ originIdeal k) k :=
  Module.compHom k (quotientResidue k)

noncomputable local instance :
    IsScalarTower (CoordinateRing k) (CoordinateRing k ⧸ originIdeal k) k where
  smul_assoc a b c := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change diagonalResidue k (a * b) * c =
      diagonalResidue k a * (diagonalResidue k b * c)
    rw [map_mul, mul_assoc]

/-- The derivative along the diagonal tangent direction, restricted to the origin ideal. -/
noncomputable def diagonalTangentSnd : originIdeal k →ₗ[CoordinateRing k] k where
  toFun z := (diagonalTangentEval k z.1).snd
  map_add' a b := by
    change (diagonalTangentEval k (a.1 + b.1)).snd =
      (diagonalTangentEval k a.1).snd + (diagonalTangentEval k b.1).snd
    rw [map_add]
    rfl
  map_smul' a z := by
    change (diagonalTangentEval k (a * z.1)).snd =
      diagonalResidue k a * (diagonalTangentEval k z.1).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    have hz : (diagonalTangentEval k z.1).fst = 0 :=
      (originIdeal_le_diagonalResidue_ker k z.property)
    rw [hz]
    simp [diagonalResidue]

/-- Products of two elements of the origin ideal have zero diagonal derivative. -/
theorem diagonalTangentSnd_mul (a b : originIdeal k) :
    diagonalTangentSnd k (a * b) = 0 := by
  change (diagonalTangentEval k ((a * b : originIdeal k) : CoordinateRing k)).snd = 0
  change (diagonalTangentEval k (a.1 * b.1)).snd = 0
  rw [map_mul, TrivSqZeroExt.snd_mul]
  have ha : (diagonalTangentEval k a.1).fst = 0 :=
    originIdeal_le_diagonalResidue_ker k a.property
  have hb : (diagonalTangentEval k b.1).fst = 0 :=
    originIdeal_le_diagonalResidue_ker k b.property
  rw [ha, hb]
  simp

/-- The diagonal tangent derivative descends to `I/I²`. -/
noncomputable def conormalDiagonalTangentOverAmbient :
    ConormalModule k →ₗ[CoordinateRing k] k :=
  Ideal.Cotangent.lift (diagonalTangentSnd k) (diagonalTangentSnd_mul k)

/-- The descended derivative as a linear map over the residue ring. -/
noncomputable def conormalDiagonalTangent :
    ConormalModule k →ₗ[CoordinateRing k ⧸ originIdeal k] k :=
  (conormalDiagonalTangentOverAmbient k).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp]
theorem conormalDiagonalTangent_toCotangent (z : originIdeal k) :
    conormalDiagonalTangent k ((originIdeal k).toCotangent z) =
      diagonalTangentSnd k z := by
  unfold conormalDiagonalTangent conormalDiagonalTangentOverAmbient
  rw [LinearMap.extendScalarsOfSurjective_apply,
    Ideal.Cotangent.lift_toCotangent]

@[simp]
theorem conormalDiagonalTangent_x :
    conormalDiagonalTangent k (conormalX k) = 1 := by
  rw [conormalX, conormalDiagonalTangent_toCotangent]
  change (diagonalTangentEval k (x k)).snd = 1
  rw [diagonalTangentEval_x]
  rfl

@[simp]
theorem conormalDiagonalTangent_y :
    conormalDiagonalTangent k (conormalY k) = 1 := by
  rw [conormalY, conormalDiagonalTangent_toCotangent]
  change (diagonalTangentEval k (y k)).snd = 1
  rw [diagonalTangentEval_y]
  rfl

/-- The product of the two canonical conormal generators in `Sym(I/I²)`. -/
noncomputable def canonicalNodalRelation :
    AffineNormalCone.normalSheafCoordinateRing
      (CoordinateRing k) (originIdeal k) :=
  SymmetricAlgebra.ι (CoordinateRing k ⧸ originIdeal k) (ConormalModule k)
      (conormalX k) *
    SymmetricAlgebra.ι (CoordinateRing k ⧸ originIdeal k) (ConormalModule k)
      (conormalY k)

/-- The nodal quadratic relation is nonzero in the actual symmetric algebra. -/
theorem canonicalNodalRelation_ne_zero : canonicalNodalRelation k ≠ 0 := by
  intro h
  have hh := congrArg (SymmetricAlgebra.lift (conormalDiagonalTangent k)) h
  simp only [canonicalNodalRelation, map_mul, SymmetricAlgebra.lift_ι_apply,
    conormalDiagonalTangent_x, conormalDiagonalTangent_y, mul_one, map_zero] at hh
  exact one_ne_zero hh

/-- The canonical normal-sheaf map kills the nodal relation because `xy=0` in the node. -/
@[simp]
theorem normalSheafCoordinateMap_canonicalNodalRelation :
    AffineNormalCone.normalSheafCoordinateMap
        (CoordinateRing k) (originIdeal k) (canonicalNodalRelation k) = 0 := by
  simp only [canonicalNodalRelation, map_mul,
    AffineNormalCone.normalSheafCoordinateMap_ι]
  apply AffineNormalCone.conormalToAssociatedGraded_mul_eq_zero_of_mul_eq_zero
  exact x_mul_y k

/-- The actual canonical coordinate map of the nodal normal cone is not injective. -/
theorem normalSheafCoordinateMap_not_injective :
    ¬ Function.Injective
      (AffineNormalCone.normalSheafCoordinateMap
        (CoordinateRing k) (originIdeal k)) := by
  intro h
  apply canonicalNodalRelation_ne_zero k
  apply h
  rw [normalSheafCoordinateMap_canonicalNodalRelation, map_zero]

/-- Thus the actual Rees normal cone of the node's origin is a proper closed subcone of its
normal sheaf, not merely isomorphic to a separately declared model with that property. -/
theorem actual_is_proper_closed_subcone :
    Function.Surjective
        (AffineNormalCone.normalSheafCoordinateMap
          (CoordinateRing k) (originIdeal k)) ∧
      ¬ Function.Injective
        (AffineNormalCone.normalSheafCoordinateMap
          (CoordinateRing k) (originIdeal k)) :=
  ⟨AffineNormalCone.normalSheafCoordinateMap_surjective _ _,
    normalSheafCoordinateMap_not_injective k⟩

end NodalNormalCone

/-!
## A strict normal cone computed through the canonical map

The node above records the traditional presentation `k[a,b]/(ab)`.  The following square-zero
example additionally proves strictness for `AffineNormalCone.normalSheafCoordinateMap` itself,
without choosing an unrelated presentation of either coordinate ring.
-/

namespace DualNumberNormalCone

variable (k : Type u) [Field k]

/-- The split square-zero extension `k ⊕ kε`. -/
abbrev CoordinateRing := TrivSqZeroExt k k

/-- The square-zero ideal `(ε)`, defined as the kernel of the actual projection to `k`. -/
abbrev nilpotentIdeal : Ideal (CoordinateRing k) :=
  RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom

/-- The projection `k ⊕ kε → k` is surjective. -/
theorem fstHom_surjective :
    Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
  fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

/-- The quotient by `(ε)` is canonically the residue field. -/
noncomputable def quotientEquiv : (CoordinateRing k ⧸ nilpotentIdeal k) ≃+* k :=
  RingHom.quotientKerEquivOfSurjective (fstHom_surjective k)

@[simp]
theorem quotientEquiv_mk (x : CoordinateRing k) :
    quotientEquiv k (Ideal.Quotient.mk (nilpotentIdeal k) x) = x.fst := by
  unfold quotientEquiv
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

local instance : Algebra (CoordinateRing k) k :=
  TrivSqZeroExt.algebraBase k k

noncomputable local instance : Algebra (CoordinateRing k ⧸ nilpotentIdeal k) k :=
  (quotientEquiv k).toRingHom.toAlgebra

/- This module structure is restriction of scalars along the proved quotient equivalence.  It
is named explicitly because the target algebra structure is not Mathlib's default one. -/
noncomputable local instance : Module (CoordinateRing k ⧸ nilpotentIdeal k) k :=
  Module.compHom k (quotientEquiv k).toRingHom

noncomputable local instance :
    IsScalarTower (CoordinateRing k) (CoordinateRing k ⧸ nilpotentIdeal k) k where
  smul_assoc a b x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change
      quotientEquiv k (Ideal.Quotient.mk (nilpotentIdeal k) (a * b)) * x =
        a.fst *
          (quotientEquiv k (Ideal.Quotient.mk (nilpotentIdeal k) b) * x)
    rw [quotientEquiv_mk, quotientEquiv_mk, TrivSqZeroExt.fst_mul, mul_assoc]

/-- Extract the `ε` coefficient from an element of `(ε)`. -/
def idealSnd : nilpotentIdeal k →ₗ[CoordinateRing k] k where
  toFun z := z.1.snd
  map_add' _ _ := rfl
  map_smul' a z := by
    change (a * z.1).snd = a.fst * z.1.snd
    rw [TrivSqZeroExt.snd_mul]
    have hz : z.1.fst = 0 := z.property
    rw [hz]
    simp

/-- Products in `(ε)` have zero `ε` coefficient. -/
theorem idealSnd_mul (x y : nilpotentIdeal k) :
    idealSnd k (x * y) = 0 := by
  change (x.1 * y.1).snd = 0
  rw [TrivSqZeroExt.snd_mul]
  have hx : x.1.fst = 0 := x.property
  have hy : y.1.fst = 0 := y.property
  rw [hx, hy]
  simp

/-- The `ε` coefficient descends to the conormal module. -/
noncomputable def cotangentSndOverAmbient :
    (nilpotentIdeal k).Cotangent →ₗ[CoordinateRing k] k :=
  Ideal.Cotangent.lift (idealSnd k) (idealSnd_mul k)

/-- The same map, with its canonical residue-field linear structure. -/
noncomputable def cotangentSnd :
    (nilpotentIdeal k).Cotangent →ₗ[CoordinateRing k ⧸ nilpotentIdeal k] k :=
  (cotangentSndOverAmbient k).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- The generator `ε` as an element of its defining ideal. -/
noncomputable def epsilon : nilpotentIdeal k :=
  ⟨TrivSqZeroExt.inr 1, rfl⟩

@[simp]
theorem cotangentSnd_epsilon :
    cotangentSnd k ((nilpotentIdeal k).toCotangent (epsilon k)) = 1 := by
  rfl

/-- The quadratic element `ε²` in the symmetric algebra of `(ε)/(ε²)`. -/
noncomputable def quadraticRelation :
    AffineNormalCone.normalSheafCoordinateRing
      (CoordinateRing k) (nilpotentIdeal k) :=
  SymmetricAlgebra.ι (CoordinateRing k ⧸ nilpotentIdeal k)
      (nilpotentIdeal k).Cotangent
      ((nilpotentIdeal k).toCotangent (epsilon k)) *
    SymmetricAlgebra.ι (CoordinateRing k ⧸ nilpotentIdeal k)
      (nilpotentIdeal k).Cotangent
      ((nilpotentIdeal k).toCotangent (epsilon k))

/-- The quadratic relation is genuinely nonzero in the normal-sheaf coordinate ring. -/
theorem quadraticRelation_ne_zero : quadraticRelation k ≠ 0 := by
  intro h
  have hh := congrArg (SymmetricAlgebra.lift (cotangentSnd k)) h
  simp only [quadraticRelation, map_mul, SymmetricAlgebra.lift_ι_apply,
    cotangentSnd_epsilon, mul_one, map_zero] at hh
  exact one_ne_zero hh

/-- The actual canonical normal-sheaf coordinate map kills `ε²`, because multiplication in the
ambient square-zero extension kills `ε²`. -/
@[simp]
theorem normalSheafCoordinateMap_quadraticRelation :
    AffineNormalCone.normalSheafCoordinateMap
        (CoordinateRing k) (nilpotentIdeal k) (quadraticRelation k) = 0 := by
  simp only [quadraticRelation, map_mul,
    AffineNormalCone.normalSheafCoordinateMap_ι]
  apply AffineNormalCone.conormalToAssociatedGraded_mul_eq_zero_of_mul_eq_zero
  ext <;> simp [epsilon]

/-- Hence the canonical map `Sym(I/I²) → gr_I(A)` itself is not injective. -/
theorem normalSheafCoordinateMap_not_injective :
    ¬ Function.Injective
      (AffineNormalCone.normalSheafCoordinateMap
        (CoordinateRing k) (nilpotentIdeal k)) := by
  intro h
  apply quadraticRelation_ne_zero k
  apply h
  rw [normalSheafCoordinateMap_quadraticRelation, map_zero]

/-- The actual normal cone of the dual-number closed point is a proper closed subcone of its
normal sheaf: the canonical coordinate map is surjective but not injective. -/
theorem actual_is_proper_closed_subcone :
    Function.Surjective
        (AffineNormalCone.normalSheafCoordinateMap
          (CoordinateRing k) (nilpotentIdeal k)) ∧
      ¬ Function.Injective
        (AffineNormalCone.normalSheafCoordinateMap
          (CoordinateRing k) (nilpotentIdeal k)) :=
  ⟨AffineNormalCone.normalSheafCoordinateMap_surjective _ _,
    normalSheafCoordinateMap_not_injective k⟩

end DualNumberNormalCone

end GromovWitten.AlgebraicGeometry
