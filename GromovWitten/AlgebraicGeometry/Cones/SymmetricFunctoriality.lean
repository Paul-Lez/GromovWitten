/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Cones.Graded

/-!
# Functoriality and scalar extension of affine symmetric cones

This file records the functorial part of the construction `M ↦ Spec Sym(M)`.  A linear map
`M → N` gives an algebra map `Sym(M) → Sym(N)`, and this map is compatible with the contraction
coactions already constructed in `Cones/Graded.lean`.  The scalar-extension statements use the
universal-property equivalence `GradedCone.baseChangeEquiv`; no basis or finite-projectivity
hypothesis is introduced.

The coordinate-ring variance is deliberate: a linear map points from `M` to `N`, while the
induced affine-scheme map points from `Spec Sym(N)` to `Spec Sym(M)`.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

universe u

namespace GradedCone
namespace SymmetricFunctoriality

section Functoriality

variable {R : Type u} [CommRing R]
variable {M N P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The symmetric-algebra map induced by an `R`-linear map. -/
noncomputable def map (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)

@[simp]
theorem map_ι (f : M →ₗ[R] N) (m : M) :
    map f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (f m) :=
  SymmetricAlgebra.lift_ι_apply _ _

@[simp]
theorem map_id :
    map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R (SymmetricAlgebra R M) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  simp

theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (g.comp f) = (map g).comp (map f) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  simp

/-- The map induced by a linear map is a morphism of the actual contraction coactions. -/
theorem isConeHom_map (f : M →ₗ[R] N) :
    IsConeHom (symCoaction R M) (symCoaction R N) (map f) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change Polynomial.mapAlgHom (map f)
      (symCoaction R M (SymmetricAlgebra.ι R M m)) =
    symCoaction R N (map f (SymmetricAlgebra.ι R M m))
  rw [map_ι, symCoaction_ι, symCoaction_ι, map_mul]
  simp

/-- Cone maps induced by linear maps commute with every contraction parameter. -/
theorem map_contraction (f : M →ₗ[R] N) (r : R) :
    (map f).comp (contraction (symCoaction R M) r) =
      (contraction (symCoaction R N) r).comp (map f) :=
  (isConeHom_map f).comp_contraction r

/-- Cone maps induced by linear maps carry the canonical augmentation to the canonical
augmentation.  This is stated over the same base ring, where both augmentations have codomain
`R`. -/
theorem map_vertex (f : M →ₗ[R] N) :
    (SymmetricAlgebra.algebraMapInv (R := R) (M := N)).comp (map f) =
      SymmetricAlgebra.algebraMapInv (R := R) (M := M) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change (SymmetricAlgebra.algebraMapInv (R := R) (M := N))
      (map f (SymmetricAlgebra.ι R M m)) =
    SymmetricAlgebra.algebraMapInv (SymmetricAlgebra.ι R M m)
  rw [map_ι, SymmetricAlgebra.algebraMapInv_ι, SymmetricAlgebra.algebraMapInv_ι]

end Functoriality

section ScalarExtension

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The canonical orientation of the symmetric-algebra scalar-extension equivalence:
`B ⊗[R] Sym_R(M) ≃ Sym_B(B ⊗[R] M)`.  Its inverse is the equivalence constructed in
`GradedCone.baseChangeEquiv`. -/
noncomputable def scalarExtensionEquiv :
    B ⊗[R] SymmetricAlgebra R M ≃ₐ[B]
      SymmetricAlgebra B (B ⊗[R] M) :=
  (baseChangeEquiv R M B).symm

/-- The map from `Sym_R(M)` to the scalar-extended symmetric algebra. -/
noncomputable def scalarExtensionMap :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra B (B ⊗[R] M) :=
  SymmetricAlgebra.lift (baseChangeGen R M B)

@[simp]
theorem scalarExtensionMap_ι (m : M) :
    scalarExtensionMap R B M (SymmetricAlgebra.ι R M m) =
      SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m) := by
  rw [scalarExtensionMap, SymmetricAlgebra.lift_ι_apply]
  change (SymmetricAlgebra.ι B (B ⊗[R] M)) (1 ⊗ₜ[R] m) = _
  rfl

/-- The scalar-extension equivalence sends `1 ⊗ s` to the map induced by `m ↦ 1 ⊗ m`.
This is the universal-property compatibility needed to compare arbitrary test algebras. -/
theorem scalarExtensionEquiv_one_tmul (s : SymmetricAlgebra R M) :
    scalarExtensionEquiv R B M ((1 : B) ⊗ₜ[R] s) = scalarExtensionMap R B M s := by
  let e := baseChangeEquiv R M B
  have hkey : (e.toAlgHom.restrictScalars R).comp (SymmetricAlgebra.lift
      (baseChangeGen R M B)) =
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra R M →ₐ[R] B ⊗[R] SymmetricAlgebra R M) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    change baseChangeForward R M B (SymmetricAlgebra.lift (baseChangeGen R M B)
        (SymmetricAlgebra.ι R M m)) = (1 : B) ⊗ₜ[R] SymmetricAlgebra.ι R M m
    rw [SymmetricAlgebra.lift_ι_apply]
    change baseChangeForward R M B
      (SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m)) = _
    rw [baseChangeForward, SymmetricAlgebra.lift_ι_apply, LinearMap.baseChange_tmul]
  apply e.injective
  change e (e.symm ((1 : B) ⊗ₜ[R] s)) = e (scalarExtensionMap R B M s)
  rw [e.apply_symm_apply]
  exact (AlgHom.congr_fun hkey s).symm

/-- On generators, scalar extension is the expected map into `1 ⊗ M`. -/
theorem scalarExtensionEquiv_one_tmul_ι (m : M) :
    scalarExtensionEquiv R B M ((1 : B) ⊗ₜ[R] SymmetricAlgebra.ι R M m) =
      SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m) := by
  rw [scalarExtensionEquiv_one_tmul, scalarExtensionMap_ι]

@[simp]
theorem scalarExtensionEquiv_tmul (b : B) (s : SymmetricAlgebra R M) :
    scalarExtensionEquiv R B M (b ⊗ₜ[R] s) =
      algebraMap B (SymmetricAlgebra B (B ⊗[R] M)) b *
        scalarExtensionEquiv R B M ((1 : B) ⊗ₜ[R] s) := by
  have htmul : b ⊗ₜ[R] s =
      (b ⊗ₜ[R] (1 : SymmetricAlgebra R M)) * ((1 : B) ⊗ₜ[R] s) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp
  rw [htmul, map_mul]
  change scalarExtensionEquiv R B M (algebraMap B (B ⊗[R] SymmetricAlgebra R M) b) *
      scalarExtensionEquiv R B M ((1 : B) ⊗ₜ[R] s) = _
  rw [(scalarExtensionEquiv R B M).commutes]

/-- The augmentation after scalar extension agrees with the scalar extension of the original
augmentation. -/
theorem augmentation_comp_scalarExtensionMap :
    ((SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M)).restrictScalars R).comp
        (scalarExtensionMap R B M) =
      (Algebra.ofId R B).comp (SymmetricAlgebra.algebraMapInv (R := R) (M := M)) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change (SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M))
      (scalarExtensionMap R B M (SymmetricAlgebra.ι R M m)) =
    (Algebra.ofId R B) (SymmetricAlgebra.algebraMapInv (R := R) (M := M)
      (SymmetricAlgebra.ι R M m))
  rw [scalarExtensionMap_ι]
  rw [SymmetricAlgebra.algebraMapInv_ι, SymmetricAlgebra.algebraMapInv_ι, map_zero]

/-- The scalar-extension equivalence respects the actual symmetric-cone coaction on the target:
the map from the original symmetric algebra into the base-changed cone is equivariant. -/
theorem isConeHom_scalarExtensionMap :
    IsConeHom (symCoaction R M)
      ((symCoaction B (B ⊗[R] M)).restrictScalars R)
      (scalarExtensionMap R B M) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change Polynomial.mapAlgHom (scalarExtensionMap R B M)
      (symCoaction R M (SymmetricAlgebra.ι R M m)) =
    (symCoaction B (B ⊗[R] M)).restrictScalars R
      (scalarExtensionMap R B M (SymmetricAlgebra.ι R M m))
  rw [symCoaction_ι, scalarExtensionMap_ι]
  change Polynomial.mapAlgHom (scalarExtensionMap R B M)
      (Polynomial.C (SymmetricAlgebra.ι R M m) * Polynomial.X) =
    symCoaction B (B ⊗[R] M)
      (SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m))
  rw [symCoaction_ι]
  change Polynomial.mapAlgHom (scalarExtensionMap R B M)
      (Polynomial.C (SymmetricAlgebra.ι R M m) * Polynomial.X) =
    Polynomial.C (SymmetricAlgebra.ι B (B ⊗[R] M) (1 ⊗ₜ[R] m)) * Polynomial.X
  rw [map_mul, Polynomial.coe_mapAlgHom, Polynomial.map_C, Polynomial.map_X]
  change Polynomial.C (scalarExtensionMap R B M (SymmetricAlgebra.ι R M m)) *
      Polynomial.X = _
  rw [scalarExtensionMap_ι]

/-- Scalar extension commutes with contraction by a scalar from the old base ring. -/
theorem scalarExtensionMap_contraction (r : R) :
    (scalarExtensionMap R B M).comp (contraction (symCoaction R M) r) =
      ((contraction (symCoaction B (B ⊗[R] M)) (algebraMap R B r)).restrictScalars R).comp
        (scalarExtensionMap R B M) := by
  exact (isConeHom_scalarExtensionMap R B M).comp_contraction r

/-- Contraction on the tensor-product presentation, obtained by extending the contraction on
`Sym_R(M)` along the right tensor factor. -/
noncomputable def tensorContraction (r : R) :
    B ⊗[R] SymmetricAlgebra R M →ₐ[B] B ⊗[R] SymmetricAlgebra R M :=
  Algebra.TensorProduct.lift (Algebra.ofId B (B ⊗[R] SymmetricAlgebra R M))
    ((Algebra.TensorProduct.includeRight :
      SymmetricAlgebra R M →ₐ[R] B ⊗[R] SymmetricAlgebra R M).comp
      (contraction (symCoaction R M) r))
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorContraction_tmul (r : R) (b : B) (s : SymmetricAlgebra R M) :
    tensorContraction R B M r (b ⊗ₜ[R] s) =
      algebraMap B (B ⊗[R] SymmetricAlgebra R M) b *
        ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R M →ₐ[R] B ⊗[R] SymmetricAlgebra R M)
          (contraction (symCoaction R M) r s)) := by
  rw [tensorContraction, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The scalar-extension equivalence intertwines the tensor contraction with the actual
contraction of `Sym_B(B ⊗ M)`. -/
theorem scalarExtensionEquiv_contraction (r : R) :
    (scalarExtensionEquiv R B M).toAlgHom.comp (tensorContraction R B M r) =
      (contraction (symCoaction B (B ⊗[R] M)) (algebraMap R B r)).comp
        (scalarExtensionEquiv R B M).toAlgHom := by
  refine Algebra.TensorProduct.ext' fun b s => ?_
  change scalarExtensionEquiv R B M
      (tensorContraction R B M r (b ⊗ₜ[R] s)) =
    contraction (symCoaction B (B ⊗[R] M)) (algebraMap R B r)
      (scalarExtensionEquiv R B M (b ⊗ₜ[R] s))
  rw [tensorContraction_tmul, map_mul, (scalarExtensionEquiv R B M).commutes,
    Algebra.TensorProduct.includeRight_apply, scalarExtensionEquiv_one_tmul,
    scalarExtensionEquiv_tmul, map_mul,
    (contraction (symCoaction B (B ⊗[R] M)) (algebraMap R B r)).commutes]
  rw [scalarExtensionEquiv_one_tmul]
  have hcon := AlgHom.congr_fun (scalarExtensionMap_contraction R B M r) s
  change (scalarExtensionMap R B M) (contraction (symCoaction R M) r s) =
    contraction (symCoaction B (B ⊗[R] M)) (algebraMap R B r)
      (scalarExtensionMap R B M s) at hcon
  exact congrArg (fun z => algebraMap B (SymmetricAlgebra B (B ⊗[R] M)) b * z) hcon

/-- The augmentation of the base-changed symmetric algebra, viewed on the tensor-product
presentation, is the canonical `B`-algebra augmentation. -/
noncomputable def tensorAugmentation :
    B ⊗[R] SymmetricAlgebra R M →ₐ[B] B :=
  Algebra.TensorProduct.lift (AlgHom.id B B)
    ((Algebra.ofId R B).comp (SymmetricAlgebra.algebraMapInv (R := R) (M := M)))
    (fun _ _ => Commute.all _ _)

theorem scalarExtensionEquiv_augmentation :
    (SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M)).comp
        (scalarExtensionEquiv R B M).toAlgHom =
      tensorAugmentation R B M := by
  refine Algebra.TensorProduct.ext' fun b s => ?_
  change (SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M))
      (scalarExtensionEquiv R B M (b ⊗ₜ[R] s)) =
    tensorAugmentation R B M (b ⊗ₜ[R] s)
  rw [scalarExtensionEquiv_tmul, map_mul,
    (SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M)).commutes,
    scalarExtensionEquiv_one_tmul]
  have haug := AlgHom.congr_fun (augmentation_comp_scalarExtensionMap R B M) s
  change (SymmetricAlgebra.algebraMapInv (R := B) (M := B ⊗[R] M))
      (scalarExtensionMap R B M s) = _ at haug
  rw [haug, tensorAugmentation, Algebra.TensorProduct.lift_tmul]
  rfl

end ScalarExtension

section BaseChangeNaturality

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The `B`-algebra map obtained by extending a symmetric-algebra map over `R`. -/
noncomputable def tensorExtensionMap (f : M →ₗ[R] N) :
    B ⊗[R] SymmetricAlgebra R M →ₐ[B] B ⊗[R] SymmetricAlgebra R N :=
  Algebra.TensorProduct.lift (Algebra.ofId B (B ⊗[R] SymmetricAlgebra R N))
    ((Algebra.TensorProduct.includeRight :
      SymmetricAlgebra R N →ₐ[R] B ⊗[R] SymmetricAlgebra R N).comp (map f))
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorExtensionMap_tmul (f : M →ₗ[R] N) (b : B) (s : SymmetricAlgebra R M) :
    tensorExtensionMap R B f (b ⊗ₜ[R] s) =
      algebraMap B (B ⊗[R] SymmetricAlgebra R N) b *
        ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R N →ₐ[R] B ⊗[R] SymmetricAlgebra R N) (map f s)) := by
  rw [tensorExtensionMap, Algebra.TensorProduct.lift_tmul]
  rfl

theorem tensorExtensionMap_includeRight {P : Type u} [AddCommGroup P] [Module R P]
    (g : N →ₗ[R] P) (s : SymmetricAlgebra R N) :
    tensorExtensionMap R B g
        ((Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R N →ₐ[R] B ⊗[R] SymmetricAlgebra R N) s) =
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra R P →ₐ[R] B ⊗[R] SymmetricAlgebra R P) (map g s) := by
  simp [tensorExtensionMap]

@[simp]
theorem tensorExtensionMap_id :
    tensorExtensionMap R B (LinearMap.id : M →ₗ[R] M) =
      AlgHom.id B (B ⊗[R] SymmetricAlgebra R M) := by
  refine Algebra.TensorProduct.ext' fun b s => ?_
  rw [tensorExtensionMap_tmul, map_id, AlgHom.id_apply,
    Algebra.TensorProduct.includeRight_apply]
  change algebraMap B (B ⊗[R] SymmetricAlgebra R M) b *
      ((1 : B) ⊗ₜ[R] s) = b ⊗ₜ[R] s
  rw [Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp

theorem tensorExtensionMap_comp {P : Type u} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    tensorExtensionMap R B (g.comp f) =
      (tensorExtensionMap R B g).comp (tensorExtensionMap R B f) := by
  refine Algebra.TensorProduct.ext' fun b s => ?_
  change tensorExtensionMap R B (g.comp f) (b ⊗ₜ[R] s) =
    tensorExtensionMap R B g (tensorExtensionMap R B f (b ⊗ₜ[R] s))
  rw [tensorExtensionMap_tmul, tensorExtensionMap_tmul, map_mul,
    (tensorExtensionMap R B g).commutes, tensorExtensionMap_includeRight]
  change algebraMap B (B ⊗[R] SymmetricAlgebra R P) b *
      ((1 : B) ⊗ₜ[R] (map (g.comp f) s)) =
    algebraMap B (B ⊗[R] SymmetricAlgebra R P) b *
      ((1 : B) ⊗ₜ[R] (map g (map f s)))
  rw [map_comp]
  rfl

theorem scalarExtensionMap_naturality (f : M →ₗ[R] N) :
    ((map (f.baseChange B)).restrictScalars R).comp (scalarExtensionMap R B M) =
      (scalarExtensionMap R B N).comp
        (map f : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  change (map (f.baseChange B))
      (scalarExtensionMap R B M (SymmetricAlgebra.ι R M m)) =
    scalarExtensionMap R B N
      (map f (SymmetricAlgebra.ι R M m))
  rw [scalarExtensionMap_ι, map_ι, LinearMap.baseChange_tmul, map_ι,
    scalarExtensionMap_ι]

/-- Naturality of the scalar-extension equivalence in the module.  The square is proved on pure
tensors and on symmetric generators, so it does not rely on a basis of either module. -/
theorem scalarExtension_naturality (f : M →ₗ[R] N) :
    (map (f.baseChange B)).comp (scalarExtensionEquiv R B M).toAlgHom =
      (scalarExtensionEquiv R B N).toAlgHom.comp (tensorExtensionMap R B f) := by
  refine Algebra.TensorProduct.ext' fun b s => ?_
  change map (f.baseChange B) (scalarExtensionEquiv R B M (b ⊗ₜ[R] s)) =
    scalarExtensionEquiv R B N (tensorExtensionMap R B f (b ⊗ₜ[R] s))
  rw [scalarExtensionEquiv_tmul, map_mul, (map (f.baseChange B)).commutes,
    tensorExtensionMap_tmul, map_mul, (scalarExtensionEquiv R B N).commutes,
    Algebra.TensorProduct.includeRight_apply, scalarExtensionEquiv_one_tmul,
    scalarExtensionEquiv_one_tmul]
  have hnat := AlgHom.congr_fun (scalarExtensionMap_naturality R B f) s
  exact congrArg
    (fun z => algebraMap B (SymmetricAlgebra B (B ⊗[R] N)) b * z) hnat

end BaseChangeNaturality

section SchemeBaseChange

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The tensor-product presentation of the base-changed affine cone is genuinely cartesian.
The scalar-extension equivalence identifies its upper-left coordinate ring with
`SymmetricAlgebra B (B ⊗[R] M)`. -/
theorem isPullback_tensorScalarExtension :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          B →+* B ⊗[R] SymmetricAlgebra R M)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R M →ₐ[R] B ⊗[R] SymmetricAlgebra R M).toRingHom))
      (projection R B) (projection R (SymmetricAlgebra R M)) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R B (SymmetricAlgebra R M))

end SchemeBaseChange

end SymmetricFunctoriality
end GradedCone

end GromovWitten.AlgebraicGeometry
