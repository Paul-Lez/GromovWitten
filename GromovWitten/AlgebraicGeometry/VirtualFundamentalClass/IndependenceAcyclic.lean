/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Independence

/-!
# Acyclic summands and the virtual class

The second half of Behrend–Fantechi, Proposition 5.3, in the affine model of
`VirtualFundamentalClass/Construction.lean`: adding an acyclic direct summand `[F --id--> F]` to
a two-term complex `E` does not change the virtual class.

`VirtualFundamentalClass/Independence.lean` already provides the obstruction theory
`sumAcyclic φ F : E ⊕ [F = F] ⟶ L`, the coordinate-ring map `bundleInl φ F` of the bundle
projection `p : E'₁ ⟶ E₁` and the two inclusions `C(E') ⊆ p⁻¹(C(E))` and
`p(C(E')) ⊆ C(E)`.  Here these are upgraded to the scheme-theoretic equality
`C(E') = p⁻¹(C(E))` and carried through to cycles, classes and the virtual class itself.

## Contents

* Symmetric algebras: `symProdTensorEquiv : Sym(M × N) ≃ₐ Sym M ⊗ Sym N`, the decomposition of
  the symmetric algebra of a product, and `mem_map_includeLeft_of_tensorMap_eq_zero`, the
  flat-base-change description of the kernel of `f ⊗ id`.
* **`ideal_sumAcyclic : ideal (sumAcyclic φ F) = (ideal φ).map (bundleInl φ F)`**, that is
  `C(E') = p⁻¹(C(E))` as closed subschemes of `E'₁`.
* Fundamental cycles of bundles: `length_self_eq_of_flat_local` (the length is preserved by a
  flat local extension with extended maximal ideal, the length analogue of
  `Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal`), `genericLength_bundlePoint`,
  `isMax_bundlePoint_iff`, `mem_range_bundlePoint_of_isMax` and
  **`pullbackBundle_fundamentalCycle`**: the fundamental cycle of the total space of a
  trivialised affine vector bundle is the flat pullback of the fundamental cycle of the base.
* The restriction of a trivialised bundle to an arbitrary (not necessarily prime) closed
  subscheme: `quotHom`, `ker_quotHom`, `quotBundleImm` and `pullbackBundle_map_quotImm`, the
  general-ideal form of `VectorBundle.pullbackBundle_map_quotImmersion`.
* The bundle structure of `C(E') ⟶ C(E)`: `acyclicTrivialization` (the coordinate ring of `E'₁`
  is a polynomial ring over the coordinate ring of `E₁`), `coneRingEquiv`, `coneIso`,
  `toBundle_comp_coneIso` and **`pullbackBundle_map_toBundle`**, the equality of the
  resolved-cone cycles.
* Classes: `pullbackBundle_resolvedConeCycleAt`,
  **`chowPullbackBundle_eq_resolvedConeClassAt_sumAcyclic`**,
  `injective_chowPullbackBundle_of_sumAcyclic`, `principalDivisorsHomogeneous_of_sumAcyclic`,
  **`virtualClassAt_sumAcyclic`** and, for the canonical trivialisations,
  **`virtualClass_eq_virtualClassAt_sumAcyclic`**: adding an acyclic summand does not change
  the virtual fundamental class.

## Hypotheses

Besides the homogeneity and injectivity hypotheses inherited from
`VirtualFundamentalClass/Construction.lean` (which are *descended* from the larger bundle `E'₁`
to `E₁` rather than assumed twice), `virtualClassAt_sumAcyclic` carries one numerical
hypothesis `hcard`, saying that the rank of the trivialisation of `E'₁` is the rank of the
trivialisation of `E₁` plus the rank of `F`; it is discharged for the canonical trivialisations
by `card_chooseBasisIndex_sumAcyclic`.
-/

universe u

set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## The symmetric algebra of a product of modules -/

section SymProd

variable (S : Type*) [CommRing S] (M N : Type*) [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]

/-- The algebra map `Sym(M × N) → Sym M ⊗ Sym N` sending a generator `(m, n)` to
`ι m ⊗ 1 + 1 ⊗ ι n`. -/
noncomputable def symProdTensorHom :
    SymmetricAlgebra S (M × N) →ₐ[S] SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N :=
  SymmetricAlgebra.lift (LinearMap.coprod
    ((Algebra.TensorProduct.includeLeft :
        SymmetricAlgebra S M →ₐ[S]
          SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N).toLinearMap ∘ₗ
      SymmetricAlgebra.ι S M)
    ((Algebra.TensorProduct.includeRight :
        SymmetricAlgebra S N →ₐ[S]
          SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N).toLinearMap ∘ₗ
      SymmetricAlgebra.ι S N))

@[simp]
theorem symProdTensorHom_ι (x : M × N) :
    symProdTensorHom S M N (SymmetricAlgebra.ι S (M × N) x) =
      SymmetricAlgebra.ι S M x.1 ⊗ₜ[S] 1 + 1 ⊗ₜ[S] SymmetricAlgebra.ι S N x.2 := by
  rw [symProdTensorHom, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The algebra map `Sym M ⊗ Sym N → Sym(M × N)` induced by the two inclusions. -/
noncomputable def symProdTensorInv :
    SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N →ₐ[S] SymmetricAlgebra S (M × N) :=
  Algebra.TensorProduct.lift (symAlgHom (LinearMap.inl S M N))
    (symAlgHom (LinearMap.inr S M N)) fun _ _ => Commute.all _ _

@[simp]
theorem symProdTensorInv_tmul (a : SymmetricAlgebra S M) (b : SymmetricAlgebra S N) :
    symProdTensorInv S M N (a ⊗ₜ[S] b) =
      symAlgHom (LinearMap.inl S M N) a * symAlgHom (LinearMap.inr S M N) b :=
  Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- The composite `Sym M → Sym(M × N) → Sym M ⊗ Sym N` is the left inclusion. -/
theorem symProdTensorHom_comp_inl :
    (symProdTensorHom S M N).comp (symAlgHom (LinearMap.inl S M N)) =
      (Algebra.TensorProduct.includeLeft :
        SymmetricAlgebra S M →ₐ[S] SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro m
  change symProdTensorHom S M N (symAlgHom (LinearMap.inl S M N)
    (SymmetricAlgebra.ι S M m)) = _
  rw [symAlgHom_ι, symProdTensorHom_ι]
  change SymmetricAlgebra.ι S M m ⊗ₜ[S] 1 + 1 ⊗ₜ[S] SymmetricAlgebra.ι S N 0 = _
  rw [map_zero, TensorProduct.tmul_zero, add_zero]
  rfl

/-- The composite `Sym N → Sym(M × N) → Sym M ⊗ Sym N` is the right inclusion. -/
theorem symProdTensorHom_comp_inr :
    (symProdTensorHom S M N).comp (symAlgHom (LinearMap.inr S M N)) =
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra S N →ₐ[S] SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro n
  change symProdTensorHom S M N (symAlgHom (LinearMap.inr S M N)
    (SymmetricAlgebra.ι S N n)) = _
  rw [symAlgHom_ι, symProdTensorHom_ι]
  change SymmetricAlgebra.ι S M 0 ⊗ₜ[S] 1 + 1 ⊗ₜ[S] SymmetricAlgebra.ι S N n = _
  rw [map_zero, TensorProduct.zero_tmul, zero_add]
  rfl

theorem symProdTensorHom_comp_symProdTensorInv :
    (symProdTensorHom S M N).comp (symProdTensorInv S M N) =
      AlgHom.id S (SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N) := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    change symProdTensorHom S M N (symProdTensorInv S M N
      (SymmetricAlgebra.ι S M m ⊗ₜ[S] 1)) = SymmetricAlgebra.ι S M m ⊗ₜ[S] 1
    rw [symProdTensorInv_tmul, map_one, mul_one]
    exact congrArg (fun g : SymmetricAlgebra S M →ₐ[S]
      SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N => g (SymmetricAlgebra.ι S M m))
      (symProdTensorHom_comp_inl S M N)
  · apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro n
    change symProdTensorHom S M N (symProdTensorInv S M N
      ((1 : SymmetricAlgebra S M) ⊗ₜ[S] SymmetricAlgebra.ι S N n)) =
      (1 : SymmetricAlgebra S M) ⊗ₜ[S] SymmetricAlgebra.ι S N n
    rw [symProdTensorInv_tmul, map_one, one_mul]
    exact congrArg (fun g : SymmetricAlgebra S N →ₐ[S]
      SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N => g (SymmetricAlgebra.ι S N n))
      (symProdTensorHom_comp_inr S M N)

theorem symProdTensorInv_comp_symProdTensorHom :
    (symProdTensorInv S M N).comp (symProdTensorHom S M N) =
      AlgHom.id S (SymmetricAlgebra S (M × N)) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change symProdTensorInv S M N (symProdTensorHom S M N
    (SymmetricAlgebra.ι S (M × N) x)) = SymmetricAlgebra.ι S (M × N) x
  rw [symProdTensorHom_ι, map_add, symProdTensorInv_tmul, symProdTensorInv_tmul,
    map_one, map_one, mul_one, one_mul, symAlgHom_ι, symAlgHom_ι, ← map_add]
  congr 1
  simp

/-- **The symmetric algebra of a product is the tensor product of the symmetric algebras.** -/
noncomputable def symProdTensorEquiv :
    SymmetricAlgebra S (M × N) ≃ₐ[S] SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N :=
  AlgEquiv.ofAlgHom (symProdTensorHom S M N) (symProdTensorInv S M N)
    (symProdTensorHom_comp_symProdTensorInv S M N)
    (symProdTensorInv_comp_symProdTensorHom S M N)

@[simp]
theorem symProdTensorEquiv_ι (x : M × N) :
    symProdTensorEquiv S M N (SymmetricAlgebra.ι S (M × N) x) =
      SymmetricAlgebra.ι S M x.1 ⊗ₜ[S] 1 + 1 ⊗ₜ[S] SymmetricAlgebra.ι S N x.2 :=
  symProdTensorHom_ι S M N x

@[simp]
theorem symProdTensorEquiv_symm_tmul (a : SymmetricAlgebra S M) (b : SymmetricAlgebra S N) :
    (symProdTensorEquiv S M N).symm (a ⊗ₜ[S] b) =
      symAlgHom (LinearMap.inl S M N) a * symAlgHom (LinearMap.inr S M N) b :=
  symProdTensorInv_tmul S M N a b

/-- The inverse isomorphism carries the left inclusion of the tensor product to the map of
symmetric algebras induced by the inclusion `M → M × N`. -/
theorem symProdTensorEquiv_symm_comp_includeLeft :
    ((symProdTensorEquiv S M N).symm.toAlgHom.comp
        (Algebra.TensorProduct.includeLeft :
          SymmetricAlgebra S M →ₐ[S]
            SymmetricAlgebra S M ⊗[S] SymmetricAlgebra S N)) =
      symAlgHom (LinearMap.inl S M N) := by
  apply AlgHom.ext
  intro a
  change (symProdTensorEquiv S M N).symm (a ⊗ₜ[S] 1) = _
  rw [symProdTensorEquiv_symm_tmul, map_one, mul_one]

end SymProd

/-! ## Kernels of `f ⊗ id` for a flat second factor -/

section FlatKernel

variable {S A P T : Type*} [CommRing S] [CommRing A] [CommRing P] [CommRing T]
  [Algebra S A] [Algebra S P] [Algebra S T]

/-- The linear map underlying `f ⊗ id` is `rTensor`. -/
theorem tensorMap_toLinearMap (f : A →ₐ[S] P) :
    (Algebra.TensorProduct.map f (AlgHom.id S T)).toLinearMap =
      LinearMap.rTensor T f.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/-- Every element of the image of `ker f ⊗ T` lies in the ideal generated by `ker f` inside
`A ⊗ T`. -/
theorem rTensor_ker_subtype_mem_map (f : A →ₐ[S] P)
    (y : (LinearMap.ker f.toLinearMap) ⊗[S] T) :
    LinearMap.rTensor T (LinearMap.ker f.toLinearMap).subtype y ∈
      Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] T).toRingHom
        (RingHom.ker f) := by
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · rw [map_zero]
    exact Ideal.zero_mem _
  · rintro ⟨c, hc⟩ t
    have hmem : c ∈ RingHom.ker (f : A →+* P) := hc
    have hfac : LinearMap.rTensor T (LinearMap.ker f.toLinearMap).subtype
        ((⟨c, hc⟩ : LinearMap.ker f.toLinearMap) ⊗ₜ[S] t) =
        ((1 : A) ⊗ₜ[S] t) *
          (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] T) c := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
      rfl
    rw [hfac]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmem)
  · intro y₁ y₂ h₁ h₂
    rw [map_add]
    exact Ideal.add_mem _ h₁ h₂

/-- **The kernel of `f ⊗ id_T` for `T` flat** is the ideal generated by the kernel of `f`. -/
theorem mem_map_includeLeft_of_tensorMap_eq_zero [Module.Flat S T] (f : A →ₐ[S] P)
    (z : A ⊗[S] T)
    (hz : Algebra.TensorProduct.map f (AlgHom.id S T) z = 0) :
    z ∈ Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] T).toRingHom
      (RingHom.ker f) := by
  have hlin : LinearMap.rTensor T f.toLinearMap z = 0 := by
    rw [← hz]
    exact (congrArg (fun L => L z) (tensorMap_toLinearMap (T := T) f)).symm
  have hex := Module.Flat.rTensor_exact (R := S) (M := T)
    (LinearMap.exact_subtype_ker_map f.toLinearMap)
  obtain ⟨y, hy⟩ := (hex z).mp hlin
  rw [← hy]
  exact rTensor_ker_subtype_mem_map f y

end FlatKernel


/-! ## The resolved cone of a complex with an acyclic summand -/

section Acyclic

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (F : Type u) [AddCommGroup F] [Module (R ⧸ I) F]

/-- The coordinate ring `Sym(E⁻¹ ⊕ F)` of `E'₁ = E₁ ×_X F^∨` as a tensor product. -/
noncomputable abbrev bundleTensorEquiv :
    ResolvedCone.bundleRing (sumAcyclic φ F) ≃ₐ[R ⧸ I]
      ResolvedCone.bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) F :=
  symProdTensorEquiv (R ⧸ I) E.degreeZero F

/-- The coordinate ring `gr ⊗ Sym(E⁰ ⊕ F)` of `C ×_X E'₀` as a tensor product. -/
noncomputable abbrev productTensorEquiv :
    ResolvedCone.productRing (sumAcyclic φ F) ≃ₐ[R ⧸ I]
      ResolvedCone.productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) F :=
  (Algebra.TensorProduct.congr AlgEquiv.refl
      (symProdTensorEquiv (R ⧸ I) E.degreeOne F)).trans
    (Algebra.TensorProduct.assoc (R := R ⧸ I) (S := R ⧸ I) (T := R ⧸ I)
      (A := AffineNormalCone.associatedGradedRing R I)
      (C := SymmetricAlgebra (R ⧸ I) E.degreeOne) (D := SymmetricAlgebra (R ⧸ I) F)).symm

theorem productTensorEquiv_tmul (c : AffineNormalCone.associatedGradedRing R I)
    (s : SymmetricAlgebra (R ⧸ I) (E.degreeOne × F)) :
    productTensorEquiv φ F (c ⊗ₜ[R ⧸ I] s) =
      (Algebra.TensorProduct.assoc (R := R ⧸ I) (S := R ⧸ I) (T := R ⧸ I)
        (A := AffineNormalCone.associatedGradedRing R I)
        (C := SymmetricAlgebra (R ⧸ I) E.degreeOne)
        (D := SymmetricAlgebra (R ⧸ I) F)).symm
          (c ⊗ₜ[R ⧸ I] symProdTensorEquiv (R ⧸ I) E.degreeOne F s) :=
  rfl

theorem productTensorEquiv_tmul_one (c : AffineNormalCone.associatedGradedRing R I) :
    productTensorEquiv φ F (c ⊗ₜ[R ⧸ I]
        (1 : SymmetricAlgebra (R ⧸ I) (E.degreeOne × F))) =
      (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) ⊗ₜ[R ⧸ I]
        (1 : SymmetricAlgebra (R ⧸ I) F) := by
  rw [productTensorEquiv_tmul, map_one, Algebra.TensorProduct.one_def]
  rfl

theorem productTensorEquiv_tmul_ι (c : AffineNormalCone.associatedGradedRing R I)
    (y : E.degreeOne) (f : F) :
    productTensorEquiv φ F (c ⊗ₜ[R ⧸ I]
        SymmetricAlgebra.ι (R ⧸ I) (E.degreeOne × F) (y, f)) =
      (c ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y) ⊗ₜ[R ⧸ I]
          (1 : SymmetricAlgebra (R ⧸ I) F) +
        (c ⊗ₜ[R ⧸ I] (1 : SymmetricAlgebra (R ⧸ I) E.degreeOne)) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) F f := by
  rw [productTensorEquiv_tmul, symProdTensorEquiv_ι, TensorProduct.tmul_add, map_add]
  rfl

/-- **The coordinate-ring square of the bundle projection, in tensor-product form.**  Under the
decompositions `Sym(E⁻¹ ⊕ F) ≅ Sym(E⁻¹) ⊗ Sym F` and `gr ⊗ Sym(E⁰ ⊕ F) ≅ (gr ⊗ Sym E⁰) ⊗ Sym F`
the map `C ×_X E'₀ → E'₁` is `(C ×_X E₀ → E₁) ⊗ id`. -/
theorem productTensorEquiv_comp_productMap :
    (productTensorEquiv φ F).toAlgHom.comp (ResolvedCone.productMap (sumAcyclic φ F)) =
      (Algebra.TensorProduct.map (ResolvedCone.productMap φ)
          (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) F))).comp
        (bundleTensorEquiv φ F).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change productTensorEquiv φ F (ResolvedCone.productMap (sumAcyclic φ F)
      (SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) x)) =
    Algebra.TensorProduct.map (ResolvedCone.productMap φ)
      (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) F))
      (symProdTensorEquiv (R ⧸ I) E.degreeZero F
        (SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) x))
  have hL : ResolvedCone.productMap (sumAcyclic φ F)
      (SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) x) =
      AffineNormalCone.conormalToAssociatedGraded R I (φ.degreeZero x.1) ⊗ₜ[R ⧸ I]
          (1 : SymmetricAlgebra (R ⧸ I) (E.degreeOne × F)) +
        (1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
          SymmetricAlgebra.ι (R ⧸ I) (E.degreeOne × F) (E.differential x.1, x.2) := by
    rw [ResolvedCone.productMap_ι, sumAcyclic_degreeZero]
    rfl
  rw [hL, map_add, productTensorEquiv_tmul_one, productTensorEquiv_tmul_ι,
    symProdTensorEquiv_ι, map_add, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, ResolvedCone.productMap_ι, map_one]
  rw [TensorProduct.add_tmul, map_one, AlgHom.id_apply, Algebra.TensorProduct.one_def]
  abel

/-- **`C(E') = p⁻¹(C(E))`**: the ideal of the resolved cone of `E ⊕ [F = F]` is the extension of
the ideal of the resolved cone of `E` along the coordinate-ring map of the bundle projection
`p : E'₁ ⟶ E₁`.  The inclusion which is proved here (the other one is
`map_ideal_le_ideal_sumAcyclic`) uses the flatness of `Sym F` over `R ⧸ I`. -/
theorem ideal_sumAcyclic [Module.Free (R ⧸ I) F] :
    ResolvedCone.ideal (sumAcyclic φ F) =
      Ideal.map (bundleInl φ F).toRingHom (ResolvedCone.ideal φ) := by
  refine le_antisymm ?_ (map_ideal_le_ideal_sumAcyclic φ F)
  intro a ha
  have ha0 : ResolvedCone.productMap (sumAcyclic φ F) a = 0 := ha
  have h1 : Algebra.TensorProduct.map (ResolvedCone.productMap φ)
      (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) F)) (bundleTensorEquiv φ F a) = 0 := by
    have h := congrArg (fun g : ResolvedCone.bundleRing (sumAcyclic φ F) →ₐ[R ⧸ I]
        ResolvedCone.productRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) F => g a)
      (productTensorEquiv_comp_productMap φ F)
    change productTensorEquiv φ F (ResolvedCone.productMap (sumAcyclic φ F) a) =
      Algebra.TensorProduct.map (ResolvedCone.productMap φ)
        (AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) F)) (bundleTensorEquiv φ F a) at h
    rw [← h, ha0, map_zero]
  have h2 := mem_map_includeLeft_of_tensorMap_eq_zero (T := SymmetricAlgebra (R ⧸ I) F)
    (ResolvedCone.productMap φ) (bundleTensorEquiv φ F a) h1
  have h3 := Ideal.mem_map_of_mem (bundleTensorEquiv φ F).symm.toAlgHom.toRingHom h2
  rw [Ideal.map_map] at h3
  have hcomp : ((bundleTensorEquiv φ F).symm.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeLeft : ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
          ResolvedCone.bundleRing φ ⊗[R ⧸ I] SymmetricAlgebra (R ⧸ I) F).toRingHom) =
      (bundleInl φ F).toRingHom :=
    congrArg AlgHom.toRingHom
      (symProdTensorEquiv_symm_comp_includeLeft (R ⧸ I) E.degreeZero F)
  rw [hcomp] at h3
  have h4 : ((bundleTensorEquiv φ F).symm.toAlgHom.toRingHom) ((bundleTensorEquiv φ F) a) = a :=
    (bundleTensorEquiv φ F).symm_apply_apply a
  rw [h4] at h3
  exact h3

end Acyclic


/-! ## The fundamental cycle of a trivialised affine vector bundle -/

section FundamentalCycle

/-- **A flat local extension whose maximal ideal is the extension of the maximal ideal of the
base has the same length.**  This is the length analogue of
`Ring.ord_algebraMap_of_flat_local_of_map_maximalIdeal`: base change along a flat local map
multiplies the length by the length of the residue quotient, which is one here. -/
theorem length_self_eq_of_flat_local {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B]
    (h : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B) :
    Module.length B B = Module.length A A := by
  have hres : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    rw [Module.length_eq_one_iff,
      isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
        (S := B ⧸ IsLocalRing.maximalIdeal B) Ideal.Quotient.mk_surjective]
    let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal B)
    exact instIsSimpleModule _
  have h1 := IsLocalRing.length_baseChange A B A
  rw [h, hres, mul_one] at h1
  rw [← (TensorProduct.AlgebraTensorModule.rid A B B).length_eq]
  exact h1

/-- **The generic multiplicity is preserved along a morphism whose stalk map is flat and extends
the maximal ideal.** -/
theorem genericLength_of_flat_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat)
    (hm : Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    X.genericLength x = Y.genericLength (f.base x) := by
  let Rs := Y.presheaf.stalk (f.base x)
  let Ss := X.presheaf.stalk x
  let _ : IsLocalRing Rs := by dsimp [Rs]; infer_instance
  let _ : IsLocalRing Ss := by dsimp [Ss]; infer_instance
  let j : Rs →+* Ss := (f.stalkMap x).hom
  let _ : Algebra Rs Ss := j.toAlgebra
  let _ : IsLocalHom (algebraMap Rs Ss) := by
    change IsLocalHom j
    infer_instance
  let _ : Module.Flat Rs Ss := hf
  change (Module.length Ss Ss).toNat = (Module.length Rs Rs).toNat
  rw [length_self_eq_of_flat_local (A := Rs) (B := Ss) hm]

section Bundle

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R)

/-- The specialisation order of an affine scheme is the opposite of the inclusion order on
prime ideals. -/
theorem spec_le_iff {B : Type u} [CommRing B] (a b : ↥(Spec (CommRingCat.of B))) :
    a ≤ b ↔ (b : PrimeSpectrum B).asIdeal ≤ (a : PrimeSpectrum B).asIdeal :=
  Iff.trans Scheme.le_iff_specializes
    (((PrimeSpectrum.le_iff_specializes (b : PrimeSpectrum B) (a : PrimeSpectrum B)).symm).trans
      (PrimeSpectrum.asIdeal_le_asIdeal (b : PrimeSpectrum B) (a : PrimeSpectrum B)).symm)

/-- A point of an affine scheme is a generic point of the specialisation order exactly when the
corresponding prime ideal is minimal. -/
theorem isMax_iff_asIdeal {B : Type u} [CommRing B] (x : ↥(Spec (CommRingCat.of B))) :
    IsMax x ↔ ∀ y : PrimeSpectrum B, y.asIdeal ≤ (x : PrimeSpectrum B).asIdeal →
      (x : PrimeSpectrum B).asIdeal ≤ y.asIdeal := by
  constructor
  · intro hx y hy
    exact (spec_le_iff y x).1 (hx ((spec_le_iff x y).2 hy))
  · intro hx a ha
    exact (spec_le_iff a x).2 (hx a ((spec_le_iff x a).1 ha))

include e in
/-- The generic point of the preimage of a point of the base lies over that point. -/
theorem comap_asIdeal_bundlePrime (p : PrimeSpectrum R) :
    Ideal.comap (algebraMap R A) (VectorBundle.bundlePrime e p).asIdeal = p.asIdeal :=
  congrArg PrimeSpectrum.asIdeal (VectorBundle.comap_bundlePrime e p)

include e in
/-- A generic point of the total space of a trivialised affine vector bundle is the generic
point of the preimage of its image: a minimal prime contains, hence equals, the extension of its
contraction. -/
theorem mem_range_bundlePoint_of_isMax {q : ↥(Spec (CommRingCat.of A))} (hq : IsMax q) :
    q ∈ Set.range (VectorBundle.bundlePoint e) := by
  refine ⟨(GradedCone.projection R A).base q, ?_⟩
  have hle : (VectorBundle.bundlePrime e
        (PrimeSpectrum.comap (algebraMap R A) (q : PrimeSpectrum A))).asIdeal ≤
      (q : PrimeSpectrum A).asIdeal := Ideal.map_le_iff_le_comap.2 le_rfl
  have hmin := (isMax_iff_asIdeal q).1 hq _ hle
  exact PrimeSpectrum.ext (le_antisymm hle hmin)

include e in
/-- The generic point of the preimage of a point of the base is a generic point of the total
space exactly when the point of the base is a generic point. -/
theorem isMax_bundlePoint_iff (x : ↥(Spec (CommRingCat.of R))) :
    IsMax (VectorBundle.bundlePoint e x) ↔ IsMax x := by
  rw [isMax_iff_asIdeal, isMax_iff_asIdeal]
  constructor
  · intro h p hp
    have h1 : (VectorBundle.bundlePrime e p).asIdeal ≤
        (VectorBundle.bundlePrime e (x : PrimeSpectrum R)).asIdeal := Ideal.map_mono hp
    have h2 := h (VectorBundle.bundlePrime e p) h1
    have h3 : Ideal.comap (algebraMap R A)
          (VectorBundle.bundlePrime e (x : PrimeSpectrum R)).asIdeal ≤
        Ideal.comap (algebraMap R A) (VectorBundle.bundlePrime e p).asIdeal :=
      Ideal.comap_mono h2
    rwa [comap_asIdeal_bundlePrime e (x : PrimeSpectrum R),
      comap_asIdeal_bundlePrime e p] at h3
  · intro h Q hQ
    have h1 : Ideal.comap (algebraMap R A) Q.asIdeal ≤ (x : PrimeSpectrum R).asIdeal := by
      have h2 : Ideal.comap (algebraMap R A) Q.asIdeal ≤
          Ideal.comap (algebraMap R A)
            (VectorBundle.bundlePrime e (x : PrimeSpectrum R)).asIdeal := Ideal.comap_mono hQ
      rwa [comap_asIdeal_bundlePrime e (x : PrimeSpectrum R)] at h2
    exact Ideal.map_le_iff_le_comap.2 (h (PrimeSpectrum.comap (algebraMap R A) Q) h1)

include e in
/-- The generic multiplicity of the generic point of a fibre equals the generic multiplicity of
the point of the base: the stalk map of the projection is flat and local with extended maximal
ideal. -/
theorem genericLength_bundlePoint [IsNoetherianRing R] [IsNoetherianRing A]
    (x : ↥(Spec (CommRingCat.of R))) :
    (Spec (CommRingCat.of A)).genericLength (VectorBundle.bundlePoint e x) =
      (Spec (CommRingCat.of R)).genericLength x := by
  have hbase := VectorBundle.projection_base_bundlePoint e x
  have hq : (VectorBundle.bundlePoint e x : PrimeSpectrum A).asIdeal =
      Ideal.map (algebraMap R A)
        (((GradedCone.projection R A).base (VectorBundle.bundlePoint e x) :
          PrimeSpectrum R)).asIdeal :=
    congrArg (fun y : PrimeSpectrum R => Ideal.map (algebraMap R A) y.asIdeal) hbase.symm
  have key := genericLength_of_flat_stalkMap (GradedCone.projection R A)
    (VectorBundle.bundlePoint e x) (VectorBundle.flat_stalkMap_projection e _)
    (VectorBundle.map_maximalIdeal_stalkMap_projection _ hq)
  rw [key, hbase]

include e in
/-- **The fundamental cycle of the total space of a trivialised affine vector bundle is the flat
pullback of the fundamental cycle of the base.** -/
theorem pullbackBundle_fundamentalCycle [IsNoetherianRing R] [IsNoetherianRing A] :
    AlgebraicCycle.pullbackBundle e (Spec (CommRingCat.of R)).fundamentalCycle =
      (Spec (CommRingCat.of A)).fundamentalCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change AlgebraicCycle.pullbackBundle e (Spec (CommRingCat.of R)).fundamentalCycle q =
    (Spec (CommRingCat.of A)).fundamentalCycle q
  by_cases hq : q ∈ Set.range (VectorBundle.bundlePoint e)
  · obtain ⟨x, rfl⟩ := hq
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    by_cases hx : IsMax x
    · rw [(Spec (CommRingCat.of R)).fundamentalCycle_apply_of_isMax x hx,
        (Spec (CommRingCat.of A)).fundamentalCycle_apply_of_isMax _
          ((isMax_bundlePoint_iff e x).2 hx), genericLength_bundlePoint e x]
    · rw [(Spec (CommRingCat.of R)).fundamentalCycle_apply_of_not_isMax x hx,
        (Spec (CommRingCat.of A)).fundamentalCycle_apply_of_not_isMax _
          fun h => hx ((isMax_bundlePoint_iff e x).1 h)]
  · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hq,
      (Spec (CommRingCat.of A)).fundamentalCycle_apply_of_not_isMax q
        fun h => hq (mem_range_bundlePoint_of_isMax e h)]

include e in
/-- Flat pullback along an affine vector bundle commutes with the projection onto the cycles of
a fixed dimension, up to the shift by the rank. -/
theorem pullbackBundle_project [IsNoetherianRing R] [Finite ι]
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A))) (d : ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :
    AlgebraicCycle.pullbackBundle e
        ((cyclesOfDimension.project (dimension := dimX) (i := d) c :
          AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)) =
      (cyclesOfDimension.project (dimension := dimE) (i := d + (Nat.card ι : ℤ))
        (AlgebraicCycle.pullbackBundle e c) :
          AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change AlgebraicCycle.pullbackBundle e
      ((cyclesOfDimension.project (dimension := dimX) (i := d) c :
        AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)) q =
    ((cyclesOfDimension.project (dimension := dimE) (i := d + (Nat.card ι : ℤ))
      (AlgebraicCycle.pullbackBundle e c) :
        AlgebraicCycle (Spec (CommRingCat.of A)) ℚ)) q
  by_cases hq : q ∈ Set.range (VectorBundle.bundlePoint e)
  · obtain ⟨x, rfl⟩ := hq
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint, cyclesOfDimension.project_apply,
      cyclesOfDimension.project_apply, AlgebraicCycle.pullbackBundle_apply_bundlePoint,
      VectorBundle.dimension_bundlePoint e dimX dimE x]
    by_cases hd : dimX x = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (by omega)]
  · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hq, cyclesOfDimension.project_apply,
      AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hq, ite_self]


end Bundle

end FundamentalCycle


/-- The isomorphism of affine schemes induced by an isomorphism of rings. -/
noncomputable def specIsoOfRingEquiv {A B : Type u} [CommRing A] [CommRing B] (f : A ≃+* B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) where
  hom := Spec.map (CommRingCat.ofHom f.toRingHom)
  inv := Spec.map (CommRingCat.ofHom f.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by simp)

/-! ## The restriction of a trivialised affine bundle to an arbitrary closed subscheme

`IntersectionTheory/BundlePullbackChow.lean` proves the compatibility of the flat pullback along
a vector bundle with the pushforward along the closed immersion `Spec (R ⧸ p) ↪ Spec R` for a
*prime* ideal `p`.  The resolved cone is cut out by an ideal which is not prime, so the same
statements are re-proved here for an arbitrary ideal; the primality of `p` plays no role in the
arguments of that file.
-/

section Restriction

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {ι : Type u} (e : A ≃ₐ[R] MvPolynomial ι R) (J : Ideal R)

/-- The extension of an arbitrary ideal to the coordinate algebra of a trivialised affine vector
bundle is the contraction of its extension to the polynomial algebra. -/
theorem map_algebraMap_eq_comap_ideal :
    Ideal.map (algebraMap R A) J =
      Ideal.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
        (Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) J) := by
  have hcomap : Ideal.comap (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom
      (Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) J) =
      Ideal.map ((e.toRingEquiv : A ≃+* MvPolynomial ι R).symm :
        MvPolynomial ι R →+* A) (Ideal.map (MvPolynomial.C : R →+* MvPolynomial ι R) J) :=
    (Ideal.map_symm (e.toRingEquiv : A ≃+* MvPolynomial ι R)).symm
  rw [hcomap, Ideal.map_map]
  congr 1
  refine RingHom.ext fun r => ?_
  have hr : (e.symm) ((algebraMap R (MvPolynomial ι R)) r) = algebraMap R A r :=
    e.symm.commutes r
  simp [MvPolynomial.algebraMap_eq, hr.symm]

/-- The surjection of the coordinate algebra of a trivialised affine vector bundle onto the
coordinate algebra of its restriction over the closed subscheme `Spec (R ⧸ J)`. -/
noncomputable def quotHom : A →+* MvPolynomial ι (R ⧸ J) :=
  (MvPolynomial.map (Ideal.Quotient.mk J)).comp
    (e.toRingEquiv : A ≃+* MvPolynomial ι R).toRingHom

/-- The coordinate algebra of the restricted bundle is a quotient of the coordinate algebra of
the bundle. -/
theorem quotHom_surjective : Function.Surjective (quotHom e J) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (e.toRingEquiv : A ≃+* MvPolynomial ι R).surjective

/-- The base-change square commutes. -/
theorem quotHom_algebraMap (r : R) :
    quotHom e J (algebraMap R A r) =
      algebraMap (R ⧸ J) (MvPolynomial ι (R ⧸ J)) (Ideal.Quotient.mk J r) := by
  change MvPolynomial.map (Ideal.Quotient.mk J) (e (algebraMap R A r)) = _
  rw [e.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]

/-- **The kernel of the restriction map is the extended ideal `J · A`.** -/
theorem ker_quotHom : RingHom.ker (quotHom e J) = Ideal.map (algebraMap R A) J := by
  rw [quotHom, ← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker]
  exact (map_algebraMap_eq_comap_ideal e J).symm

/-- Contracting an extended ideal of the restricted bundle along the restriction map gives the
extension of the contracted ideal. -/
theorem comap_quotHom_map_algebraMap (P : Ideal (R ⧸ J)) :
    Ideal.comap (quotHom e J)
        (Ideal.map (algebraMap (R ⧸ J) (MvPolynomial ι (R ⧸ J))) P) =
      Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk J) P) := by
  have hPQ : Ideal.map (Ideal.Quotient.mk J) (Ideal.comap (Ideal.Quotient.mk J) P) = P :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have hcomp : (quotHom e J).comp (algebraMap R A) =
      (algebraMap (R ⧸ J) (MvPolynomial ι (R ⧸ J))).comp (Ideal.Quotient.mk J) :=
    RingHom.ext fun r ↦ quotHom_algebraMap e J r
  have hmapK : Ideal.map (quotHom e J)
      (Ideal.map (algebraMap R A) (Ideal.comap (Ideal.Quotient.mk J) P)) =
      Ideal.map (algebraMap (R ⧸ J) (MvPolynomial ι (R ⧸ J))) P := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hPQ]
  have hJQ : J ≤ Ideal.comap (Ideal.Quotient.mk J) P := by
    intro x hx
    change Ideal.Quotient.mk J x ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact P.zero_mem
  rw [← hmapK, Ideal.comap_map_of_surjective _ (quotHom_surjective e J),
    ← RingHom.ker_eq_comap_bot, ker_quotHom e J, sup_eq_left]
  exact Ideal.map_mono hJQ

/-- The closed immersion of the closed subscheme `Spec (R ⧸ J)` into the affine base. -/
noncomputable abbrev quotImm :
    Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

instance isClosedImmersion_quotImm :
    _root_.AlgebraicGeometry.IsClosedImmersion (quotImm J) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The closed immersion of the restricted bundle into the total space of the bundle. -/
noncomputable abbrev quotBundleImm :
    Spec (CommRingCat.of (MvPolynomial ι (R ⧸ J))) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (quotHom e J))

instance isClosedImmersion_quotBundleImm :
    _root_.AlgebraicGeometry.IsClosedImmersion (quotBundleImm e J) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ (quotHom_surjective e J)

/-- The generic point of the preimage of a point of the closed subscheme, computed inside the
restricted bundle, is the generic point of the preimage of its image. -/
theorem quotBundleImm_base_bundlePoint (x : ↥(Spec (CommRingCat.of (R ⧸ J)))) :
    (quotBundleImm e J).base (VectorBundle.bundlePoint
        (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)) x) =
      VectorBundle.bundlePoint e ((quotImm J).base x) :=
  PrimeSpectrum.ext
    (comap_quotHom_map_algebraMap e J (x : PrimeSpectrum (R ⧸ J)).asIdeal)

/-- The flat pullback of a cycle pushed forward from `Spec (R ⧸ J)` vanishes away from the
generic points of the fibres of the restricted bundle. -/
theorem pullbackBundle_map_quotImm_apply_eq_zero
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ J))) ℚ)
    {y : ↥(Spec (CommRingCat.of A))}
    (hy : ∀ x, y ≠ (quotBundleImm e J).base (VectorBundle.bundlePoint
      (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)) x)) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImm J)
          (fun z ↦ wX ((quotImm J).base z)) wX c) y = 0 := by
  by_cases hmem : y ∈ Set.range (VectorBundle.bundlePoint e)
  · obtain ⟨w, rfl⟩ := hmem
    rw [AlgebraicCycle.pullbackBundle_apply_bundlePoint]
    refine AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ _ _ _ ?_
    rintro ⟨x, rfl⟩
    exact hy x (quotBundleImm_base_bundlePoint e J x).symm
  · exact AlgebraicCycle.pullbackBundle_eq_zero_of_notMem e _ hmem

/-- **The flat pullback along an affine vector bundle commutes with the pushforward along the
closed immersion of `Spec (R ⧸ J)`**, for an arbitrary ideal `J`. -/
theorem pullbackBundle_map_quotImm
    (wX : ↥(Spec (CommRingCat.of R)) → ℤ) (wE : ↥(Spec (CommRingCat.of A)) → ℤ)
    (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ J))) ℚ) :
    AlgebraicCycle.pullbackBundle e
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (quotImm J)
          (fun z ↦ wX ((quotImm J).base z)) wX c) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (quotBundleImm e J)
        (fun z ↦ wE ((quotBundleImm e J).base z)) wE
        (AlgebraicCycle.pullbackBundle
          (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)) c) := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  dsimp only
  by_cases hy : y ∈ Set.range (quotBundleImm e J).base
  · obtain ⟨z, rfl⟩ := hy
    rw [AlgebraicCycle.map_closedImmersion_apply_image (quotBundleImm e J) wE
      (AlgebraicCycle.pullbackBundle
        (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)) c) z]
    by_cases hz : z ∈ Set.range (VectorBundle.bundlePoint
        (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)))
    · obtain ⟨x, rfl⟩ := hz
      rw [quotBundleImm_base_bundlePoint e J x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint e _ ((quotImm J).base x),
        AlgebraicCycle.map_closedImmersion_apply_image (quotImm J) wX c x,
        AlgebraicCycle.pullbackBundle_apply_bundlePoint
          (AlgEquiv.refl : MvPolynomial ι (R ⧸ J) ≃ₐ[R ⧸ J] MvPolynomial ι (R ⧸ J)) c x]
    · rw [AlgebraicCycle.pullbackBundle_eq_zero_of_notMem _ c hz]
      refine pullbackBundle_map_quotImm_apply_eq_zero e J wX c ?_
      intro x hx
      exact hz ⟨x, ((quotBundleImm e J).isClosedEmbedding.injective hx).symm⟩
  · rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      (quotBundleImm e J) wE _ y hy]
    exact pullbackBundle_map_quotImm_apply_eq_zero e J wX c fun x hx ↦ hy ⟨_, hx.symm⟩

end Restriction


/-! ## The bundle structure of `E'₁ ⟶ E₁` and of `C(E') ⟶ C(E)` -/

section AcyclicBundle

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (F : Type u) [AddCommGroup F] [Module (R ⧸ I) F] [Module.Free (R ⧸ I) F]
  [Module.Finite (R ⧸ I) F]

/-- `Sym(E⁻¹ ⊕ F)` as an algebra over `Sym(E⁻¹)`, through the coordinate-ring map of the bundle
projection `p : E'₁ ⟶ E₁`. -/
@[instance_reducible]
noncomputable def bundleInlAlgebra :
    Algebra (ResolvedCone.bundleRing φ) (ResolvedCone.bundleRing (sumAcyclic φ F)) :=
  (bundleInl φ F).toRingHom.toAlgebra

attribute [local instance] bundleInlAlgebra

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) F] [Module.Finite (R ⧸ I) F] in
/-- The algebra structure of the bundle projection is compatible with the base `R ⧸ I`. -/
theorem isScalarTower_bundleInl :
    IsScalarTower (R ⧸ I) (ResolvedCone.bundleRing φ)
      (ResolvedCone.bundleRing (sumAcyclic φ F)) :=
  IsScalarTower.of_algebraMap_eq fun s => ((bundleInl φ F).commutes s).symm

attribute [local instance] isScalarTower_bundleInl

/-- The trivialisation of the bundle projection `p : E'₁ ⟶ E₁`, as an `R ⧸ I`-algebra
isomorphism `Sym(E⁻¹ ⊕ F) ≅ Sym(E⁻¹)[y_j]`. -/
noncomputable def acyclicTrivializationAux :
    ResolvedCone.bundleRing (sumAcyclic φ F) ≃ₐ[R ⧸ I]
      MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.bundleRing φ) :=
  (bundleTensorEquiv φ F).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] _)
        (VectorBundle.symTrivialization (R ⧸ I) F)).trans
      ((MvPolynomial.algebraTensorAlgEquiv (R ⧸ I)
        (ResolvedCone.bundleRing φ)).restrictScalars (R ⧸ I)))

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] in
/-- The trivialisation is the identity on the coordinate ring of `E₁`. -/
theorem acyclicTrivializationAux_bundleInl (a : ResolvedCone.bundleRing φ) :
    acyclicTrivializationAux φ F (bundleInl φ F a) = MvPolynomial.C a := by
  have h : (acyclicTrivializationAux φ F).toAlgHom.comp (bundleInl φ F) =
      IsScalarTower.toAlgHom (R ⧸ I) (ResolvedCone.bundleRing φ)
        (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F)
          (ResolvedCone.bundleRing φ)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro m
    have h1 : symProdTensorEquiv (R ⧸ I) E.degreeZero F
        (SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) (m, 0)) =
        SymmetricAlgebra.ι (R ⧸ I) E.degreeZero m ⊗ₜ[R ⧸ I]
          (1 : SymmetricAlgebra (R ⧸ I) F) := by
      rw [symProdTensorEquiv_ι]
      change SymmetricAlgebra.ι (R ⧸ I) E.degreeZero m ⊗ₜ[R ⧸ I]
          (1 : SymmetricAlgebra (R ⧸ I) F) +
        (1 : ResolvedCone.bundleRing φ) ⊗ₜ[R ⧸ I] SymmetricAlgebra.ι (R ⧸ I) F 0 = _
      rw [map_zero, TensorProduct.tmul_zero, add_zero]
    change acyclicTrivializationAux φ F (bundleInl φ F
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero m)) = _
    rw [bundleInl_ι]
    change MvPolynomial.algebraTensorAlgEquiv (R ⧸ I) (ResolvedCone.bundleRing φ)
      (Algebra.TensorProduct.congr AlgEquiv.refl (VectorBundle.symTrivialization (R ⧸ I) F)
        (symProdTensorEquiv (R ⧸ I) E.degreeZero F
          (SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) (m, 0)))) = _
    rw [h1, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
      MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, MvPolynomial.smul_eq_C_mul, mul_one]
    rfl
  exact congrArg (fun g : ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
    MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.bundleRing φ) => g a) h

/-- **The trivialisation of the bundle projection `p : E'₁ ⟶ E₁`**: the coordinate ring of `E'₁`
is a polynomial algebra over the coordinate ring of `E₁`, with one variable for each basis
vector of `F`. -/
noncomputable def acyclicTrivialization :
    ResolvedCone.bundleRing (sumAcyclic φ F) ≃ₐ[ResolvedCone.bundleRing φ]
      MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.bundleRing φ) :=
  AlgEquiv.ofRingEquiv (f := (acyclicTrivializationAux φ F).toRingEquiv)
    fun a => acyclicTrivializationAux_bundleInl φ F a

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] in
@[simp]
theorem acyclicTrivialization_apply (a : ResolvedCone.bundleRing (sumAcyclic φ F)) :
    acyclicTrivialization φ F a = acyclicTrivializationAux φ F a :=
  rfl

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] in
/-- The kernel of the restriction of the trivialisation of `E'₁` to the resolved cone is the
ideal of `C(E')`: this is `ideal_sumAcyclic` in the form needed for the bundle structure. -/
theorem ker_quotHom_acyclicTrivialization :
    RingHom.ker (quotHom (acyclicTrivialization φ F) (ResolvedCone.ideal φ)) =
      ResolvedCone.ideal (sumAcyclic φ F) := by
  rw [ker_quotHom, ideal_sumAcyclic]
  rfl

/-- **The coordinate ring of `C(E')` is a polynomial ring over the coordinate ring of `C(E)`**:
`C(E') = C(E) ×_X F^∨` as a bundle over `C(E)`. -/
noncomputable def coneRingEquiv :
    ResolvedCone.ring (sumAcyclic φ F) ≃+*
      MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.ring φ) :=
  (Ideal.quotEquivOfEq (ker_quotHom_acyclicTrivialization φ F).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (quotHom_surjective (acyclicTrivialization φ F) (ResolvedCone.ideal φ)))

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] in
theorem coneRingEquiv_mk (a : ResolvedCone.bundleRing (sumAcyclic φ F)) :
    coneRingEquiv φ F (Ideal.Quotient.mk (ResolvedCone.ideal (sumAcyclic φ F)) a) =
      quotHom (acyclicTrivialization φ F) (ResolvedCone.ideal φ) a :=
  rfl

/-- The resolved cone `C(E')` is the restriction of the bundle `E'₁ ⟶ E₁` to `C(E)`. -/
noncomputable def coneIso :
    Spec (CommRingCat.of (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F)
        (ResolvedCone.ring φ))) ≅ ResolvedCone.scheme (sumAcyclic φ F) :=
  specIsoOfRingEquiv (coneRingEquiv φ F)

instance isClosedImmersion_coneIso_hom :
    _root_.AlgebraicGeometry.IsClosedImmersion (coneIso φ F).hom :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (coneRingEquiv φ F).surjective

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] in
/-- The identification of `C(E')` with the restricted bundle is compatible with the two closed
immersions into `E'₁`. -/
theorem toBundle_comp_coneIso :
    (coneIso φ F).hom ≫ ResolvedCone.toBundle (sumAcyclic φ F) =
      quotBundleImm (acyclicTrivialization φ F) (ResolvedCone.ideal φ) := by
  rw [ResolvedCone.toBundle, coneIso, specIsoOfRingEquiv, ← Spec.map_comp]
  congr 1

/-- The certified dimension grading of the restriction of the bundle `E'₁ ⟶ E₁` to `C(E)`. -/
noncomputable abbrev restrictedConeDimension
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (sumAcyclic φ F))) :
    DimensionFunction (Spec (CommRingCat.of (MvPolynomial
      (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.ring φ)))) :=
  DimensionFunction.comapClosedImmersion
    (quotBundleImm (acyclicTrivialization φ F) (ResolvedCone.ideal φ)) dimE'

/-- **The resolved-cone cycle of `E ⊕ [F = F]` is the flat pullback of the resolved-cone cycle
of `E` along the bundle projection `p : E'₁ ⟶ E₁`.**  Both sides are the pushforward of a
fundamental cycle along a closed immersion, and the two closed immersions form a bundle square
(`toBundle_comp_coneIso`). -/
theorem pullbackBundle_map_toBundle
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace (sumAcyclic φ F))) :
    AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
          (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle (sumAcyclic φ F))
        (coneDimension (sumAcyclic φ F) dimE') dimE'
        (ResolvedCone.scheme (sumAcyclic φ F)).fundamentalCycle := by
  have hstep := pullbackBundle_map_quotImm (acyclicTrivialization φ F) (ResolvedCone.ideal φ)
    (fun z => (dimE : ResolvedCone.bundleSpace φ → ℤ) z)
    (fun z => (dimE' : ResolvedCone.bundleSpace (sumAcyclic φ F) → ℤ) z)
    (ResolvedCone.scheme φ).fundamentalCycle
  rw [pullbackBundle_fundamentalCycle
    (AlgEquiv.refl : MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F) (ResolvedCone.ring φ)
      ≃ₐ[ResolvedCone.ring φ] _)] at hstep
  have hcomp := map_congr_hom (toBundle_comp_coneIso φ F)
    (restrictedConeDimension φ F dimE') dimE'
    (Spec (CommRingCat.of (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F)
      (ResolvedCone.ring φ)))).fundamentalCycle
  have hsplit := map_comp_closedImmersion (coneIso φ F).hom
    (ResolvedCone.toBundle (sumAcyclic φ F)) (restrictedConeDimension φ F dimE')
    (coneDimension (sumAcyclic φ F) dimE') dimE'
    (Spec (CommRingCat.of (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F)
      (ResolvedCone.ring φ)))).fundamentalCycle
  have hfund := map_fundamentalCycle_of_isIso (coneIso φ F) (restrictedConeDimension φ F dimE')
    (coneDimension (sumAcyclic φ F) dimE')
  change AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
      (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
        (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map
      (quotBundleImm (acyclicTrivialization φ F) (ResolvedCone.ideal φ))
      (restrictedConeDimension φ F dimE') dimE'
      (Spec (CommRingCat.of (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) F)
        (ResolvedCone.ring φ)))).fundamentalCycle at hstep
  rw [hstep, ← hcomp, hsplit, hfund]

end AcyclicBundle


/-! ## Rational equivalence through the quotient map -/

section QuotientHelpers

variable {X : Scheme.{u}} {dim : DimensionFunction X} {d : ℤ}

/-- Two dimension-graded cycles with the same class differ by a rational-equivalence
relation. -/
theorem mem_totalRationalRelations_of_quotientMap_eq (RS : RationalEquivalenceSystem X dim d)
    (a b : cyclesOfDimension X dim d) (h : RS.quotientMap a = RS.quotientMap b) :
    ((a : AlgebraicCycle X ℚ) - (b : AlgebraicCycle X ℚ)) ∈ totalRationalRelations X dim := by
  cases RS
  have h2 := (Submodule.Quotient.eq
    (RationalEquivalenceSystem.canonical :
      RationalEquivalenceSystem X dim d).relations).1 h
  exact h2

/-- Two dimension-graded cycles differing by a rational-equivalence relation have the same
class. -/
theorem quotientMap_eq_of_mem_totalRationalRelations (RS : RationalEquivalenceSystem X dim d)
    (a b : cyclesOfDimension X dim d)
    (h : ((a : AlgebraicCycle X ℚ) - (b : AlgebraicCycle X ℚ)) ∈
      totalRationalRelations X dim) :
    RS.quotientMap a = RS.quotientMap b := by
  cases RS
  exact (Submodule.Quotient.eq
    (RationalEquivalenceSystem.canonical :
      RationalEquivalenceSystem X dim d).relations).2 h

end QuotientHelpers

/-- The cycle underlying the dimension-graded flat pullback along an affine vector bundle. -/
theorem flatPullbackBundle_coe {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Type u}
    [CommRing A] [Algebra R A] {ι : Type u} [Finite ι] (e : A ≃ₐ[R] MvPolynomial ι R)
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of A))) (i : ℤ)
    (z : cyclesOfDimension (Spec (CommRingCat.of R)) dimX i) :
    (cyclesOfDimension.flatPullbackBundle e dimX dimE i z :
        AlgebraicCycle (Spec (CommRingCat.of A)) ℚ) =
      AlgebraicCycle.pullbackBundle e (z : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) :=
  rfl

/-! ## The virtual class of a complex with an acyclic summand -/

section AcyclicClass

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (F : Type u) [AddCommGroup F] [Module (R ⧸ I) F] [Module.Free (R ⧸ I) F]
  [Module.Finite (R ⧸ I) F]

attribute [local instance] bundleInlAlgebra isScalarTower_bundleInl

variable {κ ι' : Type u} [Finite κ] [Finite ι']
variable (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial κ (R ⧸ I))
variable (e' : ResolvedCone.bundleRing (sumAcyclic φ F) ≃ₐ[R ⧸ I] MvPolynomial ι' (R ⧸ I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
variable (dimE' : DimensionFunction (ResolvedCone.bundleSpace (sumAcyclic φ F))) (i : ℤ)
variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
  (i + (Nat.card κ : ℤ)))
variable (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace (sumAcyclic φ F)) dimE'
  (i + (Nat.card ι' : ℤ)))

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) F] [Finite κ] [Finite ι'] in
/-- The flat pullback along the bundle `E'₁ ⟶ X` is the flat pullback along `E₁ ⟶ X` followed by
the flat pullback along the bundle projection `p : E'₁ ⟶ E₁`, at the level of cycles. -/
theorem pullbackBundle_tower_acyclic (c : AlgebraicCycle (Spec (CommRingCat.of (R ⧸ I))) ℚ) :
    AlgebraicCycle.pullbackBundle e' c =
      AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
        (AlgebraicCycle.pullbackBundle e c) :=
  VectorBundle.pullbackBundle_tower e' (acyclicTrivialization φ F) e c

/-- Two classes on the base with the same flat pullback to `E₁` have the same flat pullback to
`E'₁`. -/
theorem chowPullbackBundle_sumAcyclic_congr (α β : RX.ChowGroup)
    (h : VectorBundle.chowPullbackBundle e dimX dimE i RX RE α =
      VectorBundle.chowPullbackBundle e dimX dimE i RX RE β) :
    VectorBundle.chowPullbackBundle e' dimX dimE' i RX RE' α =
      VectorBundle.chowPullbackBundle e' dimX dimE' i RX RE' β := by
  obtain ⟨zα, rfl⟩ : ∃ z, RX.quotientMap z = α := Submodule.mkQ_surjective _ α
  obtain ⟨zβ, rfl⟩ : ∃ z, RX.quotientMap z = β := Submodule.mkQ_surjective _ β
  rw [VectorBundle.chowPullbackBundle_quotientMap,
    VectorBundle.chowPullbackBundle_quotientMap] at h
  rw [VectorBundle.chowPullbackBundle_quotientMap, VectorBundle.chowPullbackBundle_quotientMap]
  have h1 := mem_totalRationalRelations_of_quotientMap_eq RE _ _ h
  have h2 := VectorBundle.totalRationalRelations_pullbackBundle (acyclicTrivialization φ F)
    dimE dimE' ⟨_, h1, rfl⟩
  have hkey : AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
      ((cyclesOfDimension.flatPullbackBundle e dimX dimE i zα :
          AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ) -
        (cyclesOfDimension.flatPullbackBundle e dimX dimE i zβ :
          AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)) =
      (cyclesOfDimension.flatPullbackBundle e' dimX dimE' i zα :
          AlgebraicCycle (ResolvedCone.bundleSpace (sumAcyclic φ F)) ℚ) -
        (cyclesOfDimension.flatPullbackBundle e' dimX dimE' i zβ :
          AlgebraicCycle (ResolvedCone.bundleSpace (sumAcyclic φ F)) ℚ) := by
    have hsub := map_sub (AlgebraicCycle.pullbackBundleLinear (acyclicTrivialization φ F))
      (cyclesOfDimension.flatPullbackBundle e dimX dimE i zα :
        AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)
      (cyclesOfDimension.flatPullbackBundle e dimX dimE i zβ :
        AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)
    simp only [AlgebraicCycle.pullbackBundleLinear_apply] at hsub
    rw [hsub]
    simp only [flatPullbackBundle_coe]
    rw [← pullbackBundle_tower_acyclic φ F e e', ← pullbackBundle_tower_acyclic φ F e e']
  simp only [AlgebraicCycle.pullbackBundleLinear_apply] at h2
  rw [hkey] at h2
  exact quotientMap_eq_of_mem_totalRationalRelations RE' _ _ h2

/-- Injectivity of the flat pullback along `E'₁ ⟶ X` implies injectivity of the flat pullback
along `E₁ ⟶ X`. -/
theorem injective_chowPullbackBundle_of_sumAcyclic
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e' dimX dimE' i RX RE')) :
    Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE) := fun _ _ h =>
  hinj (chowPullbackBundle_sumAcyclic_congr φ F e e' dimX dimE dimE' i RX RE RE' _ _ h)

omit [Finite κ] [Finite ι'] in
/-- Homogeneity of principal divisors descends from `E'₁` to `E₁`. -/
theorem principalDivisorsHomogeneous_of_sumAcyclic
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (sumAcyclic φ F)) dimE') :
    PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE :=
  VectorBundle.principalDivisorsHomogeneous_base (acyclicTrivialization φ F) dimE dimE' hhom

omit [Finite κ] [Finite ι'] in
/-- **The resolved-cone cycle of `E ⊕ [F = F]` is the flat pullback of the resolved-cone cycle
of `E`**, in the dimension-graded form. -/
theorem pullbackBundle_resolvedConeCycleAt
    (hcard : (Nat.card ι' : ℤ) =
      (Nat.card κ : ℤ) + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F) : ℤ)) :
    AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
        ((resolvedConeCycleAt φ dimE (i + (Nat.card κ : ℤ)) :
          AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)) =
      (resolvedConeCycleAt (sumAcyclic φ F) dimE' (i + (Nat.card ι' : ℤ)) :
        AlgebraicCycle (ResolvedCone.bundleSpace (sumAcyclic φ F)) ℚ) := by
  have hdeg : i + (Nat.card ι' : ℤ) =
      i + (Nat.card κ : ℤ) + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F) : ℤ) := by
    rw [hcard]
    ring
  rw [hdeg]
  change AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
      ((cyclesOfDimension.project (dimension := dimE) (i := i + (Nat.card κ : ℤ))
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
          (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) :
            AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)) = _
  rw [pullbackBundle_project (acyclicTrivialization φ F) dimE dimE' (i + (Nat.card κ : ℤ)),
    pullbackBundle_map_toBundle φ F dimE dimE']
  rfl

/-- **A class on the base which is a virtual class for `E` is a virtual class for
`E ⊕ [F = F]`.** -/
theorem chowPullbackBundle_eq_resolvedConeClassAt_sumAcyclic
    (hcard : (Nat.card ι' : ℤ) =
      (Nat.card κ : ℤ) + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F) : ℤ))
    (α : RX.ChowGroup)
    (hα : VectorBundle.chowPullbackBundle e dimX dimE i RX RE α =
      resolvedConeClassAt φ dimE i RE) :
    VectorBundle.chowPullbackBundle e' dimX dimE' i RX RE' α =
      resolvedConeClassAt (sumAcyclic φ F) dimE' i RE' := by
  obtain ⟨z, rfl⟩ : ∃ z, RX.quotientMap z = α := Submodule.mkQ_surjective _ α
  rw [VectorBundle.chowPullbackBundle_quotientMap] at hα
  rw [VectorBundle.chowPullbackBundle_quotientMap]
  have h1 := mem_totalRationalRelations_of_quotientMap_eq RE _ _ hα
  have h2 := VectorBundle.totalRationalRelations_pullbackBundle (acyclicTrivialization φ F)
    dimE dimE' ⟨_, h1, rfl⟩
  have hkey : AlgebraicCycle.pullbackBundle (acyclicTrivialization φ F)
      ((cyclesOfDimension.flatPullbackBundle e dimX dimE i z :
          AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ) -
        (resolvedConeCycleAt φ dimE (i + (Nat.card κ : ℤ)) :
          AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)) =
      (cyclesOfDimension.flatPullbackBundle e' dimX dimE' i z :
          AlgebraicCycle (ResolvedCone.bundleSpace (sumAcyclic φ F)) ℚ) -
        (resolvedConeCycleAt (sumAcyclic φ F) dimE' (i + (Nat.card ι' : ℤ)) :
          AlgebraicCycle (ResolvedCone.bundleSpace (sumAcyclic φ F)) ℚ) := by
    have hsub := map_sub (AlgebraicCycle.pullbackBundleLinear (acyclicTrivialization φ F))
      (cyclesOfDimension.flatPullbackBundle e dimX dimE i z :
        AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)
      (resolvedConeCycleAt φ dimE (i + (Nat.card κ : ℤ)) :
        AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ)
    simp only [AlgebraicCycle.pullbackBundleLinear_apply] at hsub
    rw [hsub, pullbackBundle_resolvedConeCycleAt φ F dimE dimE' i hcard]
    simp only [flatPullbackBundle_coe]
    rw [← pullbackBundle_tower_acyclic φ F e e']
  simp only [AlgebraicCycle.pullbackBundleLinear_apply] at h2
  rw [hkey] at h2
  exact quotientMap_eq_of_mem_totalRationalRelations RE' _ _ h2

/-- **Behrend–Fantechi, Proposition 5.3 (acyclic summands).**  Adding an acyclic direct summand
`[F --id--> F]` to a global resolution does not change the virtual fundamental class.  The
homogeneity and injectivity hypotheses are those of `VirtualFundamentalClass/Construction.lean`
for the larger bundle `E'₁`; they are *descended* to `E₁` rather than assumed twice.  The
hypothesis `hcard` says that the two trivialisations have the expected ranks. -/
theorem virtualClassAt_sumAcyclic
    (hcard : (Nat.card ι' : ℤ) =
      (Nat.card κ : ℤ) + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F) : ℤ))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (sumAcyclic φ F)) dimE')
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e' dimX dimE' i RX RE')) :
    virtualClassAt (sumAcyclic φ F) e' dimX dimE' i RX RE' hhom hinj =
      virtualClassAt φ e dimX dimE i RX RE
        (principalDivisorsHomogeneous_of_sumAcyclic φ F dimE dimE' hhom)
        (injective_chowPullbackBundle_of_sumAcyclic φ F e e' dimX dimE dimE' i RX RE RE'
          hinj) := by
  symm
  apply eq_virtualClassAt_of_pullback_eq
  exact chowPullbackBundle_eq_resolvedConeClassAt_sumAcyclic φ F e e' dimX dimE dimE' i RX RE RE'
    hcard _ (chowPullbackBundle_virtualClassAt φ e dimX dimE i RX RE
      (principalDivisorsHomogeneous_of_sumAcyclic φ F dimE dimE' hhom)
      (injective_chowPullbackBundle_of_sumAcyclic φ F e e' dimX dimE dimE' i RX RE RE' hinj))

end AcyclicClass


/-! ## The canonical trivialisations -/

section Canonical

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {I : Ideal R} [Nontrivial (R ⧸ I)]
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (F : Type u) [AddCommGroup F] [Module (R ⧸ I) F] [Module.Free (R ⧸ I) F]
  [Module.Finite (R ⧸ I) F]

attribute [local instance] bundleInlAlgebra isScalarTower_bundleInl

omit [IsNoetherianRing R] in
/-- The rank of `E'₁` is the rank of `E₁` plus the rank of `F`. -/
theorem card_chooseBasisIndex_sumAcyclic :
    (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I)
        (E.sum (acyclicComplex (R ⧸ I) F)).degreeZero) : ℤ) =
      (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) : ℤ) +
        (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I) F) : ℤ) := by
  rw [VectorBundle.card_chooseBasisIndex, VectorBundle.card_chooseBasisIndex,
    VectorBundle.card_chooseBasisIndex]
  change ((Module.finrank (R ⧸ I) (E.degreeZero × F) : ℤ)) = _
  rw [Module.finrank_prod]
  push_cast
  ring

variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
variable (dimE' : DimensionFunction (ResolvedCone.bundleSpace (sumAcyclic φ F)))
variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
  (virtualDimension φ))
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))
variable (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace (sumAcyclic φ F)) dimE'
  (virtualDimension φ + (Nat.card (Module.Free.ChooseBasisIndex (R ⧸ I)
    (E.sum (acyclicComplex (R ⧸ I) F)).degreeZero) : ℤ)))

/-- **Behrend–Fantechi, Proposition 5.3 (acyclic summands), for the canonical
trivialisations.**  The virtual class of `E ⊕ [F = F]`, computed in the canonical
trivialisation of `E'₁` and in the degree `vd = virtualDimension φ`, is the virtual class
`VirtualClass.virtualClass φ` of `VirtualFundamentalClass/Construction.lean`. -/
theorem virtualClass_eq_virtualClassAt_sumAcyclic
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace (sumAcyclic φ F)) dimE')
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle
      (trivialization (sumAcyclic φ F)) dimX dimE' (virtualDimension φ) RX RE')) :
    virtualClassAt (sumAcyclic φ F) (trivialization (sumAcyclic φ F)) dimX dimE'
        (virtualDimension φ) RX RE' hhom hinj =
      virtualClass φ dimX dimE RX RE
        (principalDivisorsHomogeneous_of_sumAcyclic φ F dimE dimE' hhom)
        (injective_chowPullbackBundle_of_sumAcyclic φ F (trivialization φ)
          (trivialization (sumAcyclic φ F)) dimX dimE dimE' (virtualDimension φ) RX RE RE'
          hinj) := by
  rw [← virtualClassAt_trivialization]
  exact virtualClassAt_sumAcyclic φ F (trivialization φ) (trivialization (sumAcyclic φ F))
    dimX dimE dimE' (virtualDimension φ) RX RE RE' (card_chooseBasisIndex_sumAcyclic (E := E) F)
    hhom hinj

end Canonical

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass
