/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Modules.Derived
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duals, tensors, triangles and base change of perfect complexes

This file completes the affine model of `CotangentComplex/PerfectComplex.lean` with the
operations that were still missing there: the termwise dual of a bounded complex of finite free
modules, the termwise tensor product with a finite free module, two-out-of-three for
perfectness in a distinguished triangle of `DerivedCategory (ModuleCat R)`, and the derived
base change of a global two-term resolution.

Everything below is a construction or a theorem; no field of any structure asserts a
conclusion, and there is no `sorry` and no new axiom.

## Main definitions

* `dualObj M`, `dualHom g`, `evalHom M` : the `R`-linear dual of a module object, the transpose
  of a morphism, and the evaluation map into the double dual.
* `dualComplex K` : the termwise dual, `(K^∨)^i = (K^{-i})^∨` with the differential the
  transpose of the differential of `K` carrying the usual sign `(-1)^{i+1}`.
* `dualComplexMap φ` : the transpose of a morphism of complexes, making `dualComplex`
  contravariantly functorial.
* `tensorSingle K M n` : the tensor product of `K` with the finite free module `M` placed in
  cohomological degree `n`.
* `GlobalTwoTermResolution.dual`, `.tensorRight`, `.baseChange` : the shifted dual, the tensor
  product with a finite free module, and the extension of scalars of a global two-term
  resolution, each again an honest global two-term resolution.

## Main results

* `IsStrictlyPerfect.dual`, `IsStrictlyPerfect.tensorRight` : strict perfectness is stable
  under the termwise dual and under the termwise tensor product with a finite free module.
* `rank_dual` : `rank (K^∨) = rank K` for the honest alternating sum of ranks, the indexing
  `(K^∨)^i = (K^{-i})^∨` reversing both the sign and the degree.
* `bidualityIso` : a complex of finite free modules is isomorphic to its double dual, through
  evaluation twisted by `(-1)^i`; the twist is what compensates the sign convention.
* `rank_tensorRight`, `rank_tensorSingle` : `rank (K ⊗ M) = rank K * finrank M`, and the same
  with the sign `(-1)^n` when `M` sits in degree `n`.
* `exists_chainMap_of_derivedMap` : every derived morphism out of a strictly perfect complex is
  the image of an actual chain map, by K-projectivity.
* `IsPerfect.of_distTriang₁`, `of_distTriang₂`, `of_distTriang₃` : **two-out-of-three** for
  perfectness in a distinguished triangle, together with
  `exists_isStrictlyPerfect_rank_of_distTriang`, which produces a strictly perfect
  representative of the third vertex with `rank E' = rank E + rank E''`.
* `rank_baseChange`, `GlobalTwoTermResolution.baseChange_virtualRank` : base change along a
  ring homomorphism preserves ranks.
* `GlobalTwoTermResolution.nonempty_baseChange_iso` : the base change of a resolution does not
  depend on the resolution, so derived base change is well defined on the resolved object.

## What is not proved

The tensor product of two strictly perfect complexes is only constructed when the second factor
is a finite free module in a single degree.  Mathlib's `HomologicalComplex.tensorObj` produces
the term `⨁_{p + q = n} K^p ⊗ L^q` as a coproduct over the infinite index set `{(p,q) | p+q=n}`,
and identifying such a coproduct with the finite biproduct of its finitely many nonzero
summands is not available; that identification, not the tensor product itself, is what is
missing for the general case.

The dual is not proved to be homotopy invariant: `dualComplexMap` is functorial, but
transporting a `Homotopy` through the sign convention of `dualComplex` is not carried out, so
the dual of a perfect *object* of the derived category is not shown to be independent of the
chosen strictly perfect representative.  Derived base change is likewise only constructed on
complexes and on resolutions; there is no base change functor on `DerivedCategory (ModuleCat R)`
itself, since `Modules/Derived.lean` supplies base change only up to quasi-isomorphism of
bounded above complexes of projectives.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## The dual of a module object -/

/-- The `R`-linear dual of a module object of `ModuleCat R`. -/
abbrev dualObj (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (Module.Dual R M)

/-- The transpose of a morphism of module objects. -/
noncomputable def dualHom {M N : ModuleCat.{u} R} (g : M ⟶ N) : dualObj N ⟶ dualObj M :=
  ModuleCat.ofHom g.hom.dualMap

@[simp]
theorem dualHom_apply {M N : ModuleCat.{u} R} (g : M ⟶ N) (φ : dualObj N) (x : M) :
    (dualHom g).hom φ x = φ (g.hom x) :=
  rfl

/-- The transpose of the identity is the identity. -/
@[simp]
theorem dualHom_id (M : ModuleCat.{u} R) : dualHom (𝟙 M) = 𝟙 (dualObj M) := by
  ext φ
  rfl

/-- Dualising reverses composition. -/
theorem dualHom_comp {M N L : ModuleCat.{u} R} (g : M ⟶ N) (h : N ⟶ L) :
    dualHom (g ≫ h) = dualHom h ≫ dualHom g := by
  ext φ
  rfl

/-- The transpose of the zero morphism is zero. -/
@[simp]
theorem dualHom_zero {M N : ModuleCat.{u} R} : dualHom (0 : M ⟶ N) = 0 := by
  ext φ x
  simp [dualHom]

/-- Dualising is compatible with the integer scalar action on morphisms. -/
theorem dualHom_zsmul {M N : ModuleCat.{u} R} (g : M ⟶ N) (c : ℤ) :
    dualHom (c • g) = c • dualHom g := by
  ext φ x
  simp [dualHom]

/-- The dual of a zero module object is a zero module object. -/
theorem isZero_dualObj {M : ModuleCat.{u} R} (h : IsZero M) : IsZero (dualObj M) := by
  have hM : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  have : Subsingleton (Module.Dual R M) :=
    ⟨fun f g => LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr this

/-- The dual of a finite free module object is finite free. -/
theorem IsFiniteFree.dual {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    IsFiniteFree (dualObj M) := by
  have := hM.free
  have := hM.finite
  exact ⟨inferInstanceAs (Module.Free R (Module.Dual R M)),
    inferInstanceAs (Module.Finite R (Module.Dual R M))⟩

/-- A finite free module object and its dual have the same rank. -/
theorem rankOf_dual {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    rankOf (dualObj M) = rankOf M := by
  classical
  have := hM.free
  have := hM.finite
  exact ((Module.Free.chooseBasis R M).toDualEquiv.finrank_eq).symm

/-- The evaluation morphism from a module object into its double dual. -/
noncomputable def evalHom (M : ModuleCat.{u} R) : M ⟶ dualObj (dualObj M) :=
  ModuleCat.ofHom (Module.Dual.eval R M)

@[simp]
theorem evalHom_apply (M : ModuleCat.{u} R) (x : M) (φ : dualObj M) :
    (evalHom M).hom x φ = φ x :=
  rfl

/-- Evaluation is natural: `ev ≫ g^∨∨ = g ≫ ev`. -/
theorem evalHom_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    evalHom M ≫ dualHom (dualHom g) = g ≫ evalHom N := by
  ext x φ
  rfl

/-- For a finite free module object, evaluation into the double dual is an isomorphism. -/
noncomputable def evalIso {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    M ≅ dualObj (dualObj M) := by
  have := hM.free
  have := hM.finite
  exact (Module.evalEquiv R M).toModuleIso

@[simp]
theorem evalIso_hom {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    (evalIso hM).hom = evalHom M :=
  rfl

/-- The evaluation morphism of a finite free module object is an isomorphism. -/
theorem isIso_evalHom {M : ModuleCat.{u} R} (hM : IsFiniteFree M) : IsIso (evalHom M) :=
  ⟨(evalIso hM).inv, (evalIso hM).hom_inv_id, (evalIso hM).inv_hom_id⟩

/-! ## Scaling an isomorphism by a sign -/

/-- Rescaling an isomorphism of module objects by a unit of `ℤ`.  Signs are units, so this is
again an isomorphism; it is what turns the sign convention of the dual complex into an honest
comparison isomorphism. -/
def unitsZSMulIso {M N : ModuleCat.{u} R} (c : ℤˣ) (e : M ≅ N) : M ≅ N where
  hom := (c : ℤ) • e.hom
  inv := (c : ℤ) • e.inv
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul, e.hom_inv_id]
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul, e.inv_hom_id]

@[simp]
theorem unitsZSMulIso_hom {M N : ModuleCat.{u} R} (c : ℤˣ) (e : M ≅ N) :
    (unitsZSMulIso c e).hom = (c : ℤ) • e.hom :=
  rfl

/-! ## The dual of a bounded complex -/

/-- The termwise dual `K^∨` of a cochain complex of `R`-modules: the term in degree `i` is the
dual of the term of `K` in degree `-i`, and the differential is the transposed differential of
`K` with the usual sign `(-1)^{i+1}`.  The composite of two consecutive differentials vanishes
because dualising reverses composition. -/
noncomputable def dualComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X i := dualObj (K.X (-i))
  d i j := if h : i + 1 = j then (j.negOnePow : ℤ) • dualHom (K.d (-j) (-i)) else 0
  shape i j hij := dif_neg hij
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    rw [dif_pos hij', dif_pos hjk', Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      ← dualHom_comp, K.d_comp_d, dualHom_zero, smul_zero, smul_zero]

@[simp]
theorem dualComplex_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (dualComplex K).X i = dualObj (K.X (-i)) :=
  rfl

/-- The differential of the dual complex is the signed transpose of the differential of `K`. -/
theorem dualComplex_d (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) (h : i + 1 = j) :
    (dualComplex K).d i j = (j.negOnePow : ℤ) • dualHom (K.d (-j) (-i)) :=
  dif_pos h

/-- Dualising reflects the interval of support. -/
theorem IsSupportedIn.dual {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : IsSupportedIn K a b) : IsSupportedIn (dualComplex K) (-b) (-a) := by
  intro i hi
  rw [dualComplex_X]
  exact isZero_dualObj (h (-i) (by omega))

/-- **The dual of a strictly perfect complex is strictly perfect.** -/
theorem IsStrictlyPerfect.dual {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) : IsStrictlyPerfect (dualComplex K) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    exact ⟨-b, -a, hab.dual⟩
  finiteFree i := (hK.finiteFree (-i)).dual

/-- **The rank of the dual.**  With the cohomological indexing `(K^∨)^i = (K^{-i})^∨` the
alternating sum of ranks is unchanged: reindexing by `i ↦ -i` multiplies both the sign and the
degree by `-1`. -/
theorem rank_dual [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ∀ i : ℤ, IsFiniteFree (K.X i)) : rank (dualComplex K) = rank K := by
  rw [rank, rank, ← finsum_comp_equiv (Equiv.neg ℤ)
    (f := fun j : ℤ => (j.negOnePow : ℤ) * (rankOf (K.X j) : ℤ))]
  refine finsum_congr fun i => ?_
  have hr : rankOf ((dualComplex K).X i) = rankOf (K.X (-i)) := rankOf_dual (hK (-i))
  rw [hr]
  simp only [Equiv.neg_apply, Int.negOnePow_neg]

/-- The rank of the dual of a strictly perfect complex. -/
theorem IsStrictlyPerfect.rank_dual [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) : rank (dualComplex K) = rank K :=
  _root_.GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectComplex.rank_dual hK.finiteFree

/-! ## Functoriality of the dual -/

set_option backward.isDefEq.respectTransparency false in
/-- The dual of a morphism of cochain complexes.  The sign of the differential is the same on
both sides, so the commutation squares are exactly the transposed commutation squares of the
given morphism. -/
noncomputable def dualComplexMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) :
    dualComplex L ⟶ dualComplex K where
  f i := dualHom (φ.f (-i))
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    rw [dualComplex_d _ i j hij', dualComplex_d _ i j hij', Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, ← dualHom_comp, ← dualHom_comp, φ.comm (-j) (-i)]

@[simp]
theorem dualComplexMap_f {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (i : ℤ) :
    (dualComplexMap φ).f i = dualHom (φ.f (-i)) :=
  rfl

/-- Dualising a morphism of complexes preserves identities. -/
@[simp]
theorem dualComplexMap_id (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    dualComplexMap (𝟙 K) = 𝟙 (dualComplex K) :=
  HomologicalComplex.hom_ext _ _ fun i => dualHom_id (K.X (-i))

/-- Dualising a morphism of complexes reverses composition. -/
theorem dualComplexMap_comp {K L M : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)
    (ψ : L ⟶ M) : dualComplexMap (φ ≫ ψ) = dualComplexMap ψ ≫ dualComplexMap φ :=
  HomologicalComplex.hom_ext _ _ fun i => dualHom_comp (φ.f (-i)) (ψ.f (-i))

/-- An isomorphism of complexes dualises to an isomorphism. -/
noncomputable def dualComplexMapIso {K L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) :
    dualComplex L ≅ dualComplex K where
  hom := dualComplexMap e.hom
  inv := dualComplexMap e.inv
  hom_inv_id := by rw [← dualComplexMap_comp, e.inv_hom_id, dualComplexMap_id]
  inv_hom_id := by rw [← dualComplexMap_comp, e.hom_inv_id, dualComplexMap_id]

/-! ## Biduality -/

/-- The degreewise comparison of a complex of finite free modules with its double dual. -/
noncomputable def bidualityXIso {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ∀ i : ℤ, IsFiniteFree (K.X i)) (i : ℤ) :
    K.X i ≅ (dualComplex (dualComplex K)).X i :=
  K.XIsoOfEq (neg_neg i).symm ≪≫ evalIso (hK (- -i))

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the double dual, computed as the double transpose with the product of
the two signs. -/
theorem dualComplex_dualComplex_d (K : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ)
    (h : i + 1 = j) :
    (dualComplex (dualComplex K)).d i j =
      ((j.negOnePow : ℤ) * ((-i).negOnePow : ℤ)) • dualHom (dualHom (K.d (- -i) (- -j))) := by
  have hd : (dualComplex K).d (-j) (-i) = ((-i).negOnePow : ℤ) • dualHom (K.d (- -i) (- -j)) :=
    dualComplex_d K (-j) (-i) (by omega)
  rw [dualComplex_d _ i j h, hd, dualHom_zsmul, smul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- **Biduality.**  A complex of finite free modules is isomorphic to its double dual, by the
evaluation map twisted by the sign `(-1)^i`; the twist is exactly what compensates the sign
convention of `dualComplex`, so the result is a morphism of cochain complexes. -/
noncomputable def bidualityIso {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ∀ i : ℤ, IsFiniteFree (K.X i)) : K ≅ dualComplex (dualComplex K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => unitsZSMulIso i.negOnePow (bidualityXIso hK i)) (by
      intro i j hij
      have hij' : i + 1 = j := hij
      rw [dualComplex_dualComplex_d K i j hij']
      simp only [unitsZSMulIso_hom, bidualityXIso, Iso.trans_hom, evalIso_hom,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, Category.assoc]
      rw [evalHom_naturality, HomologicalComplex.XIsoOfEq_hom_comp_d_assoc,
        ← HomologicalComplex.d_comp_XIsoOfEq_hom K (neg_neg j).symm i, Category.assoc]
      congr 1
      rw [Int.negOnePow_neg, mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        mul_one])


/-! ## Tensor product with a finite free module -/

/-- The underlying module of a monoidal tensor product in `ModuleCat R` is the tensor product
of the underlying modules. -/
noncomputable def tensorRightLinearEquiv (M N : ModuleCat.{u} R) :
    (((MonoidalCategory.tensorRight N).obj M : ModuleCat.{u} R) : Type u) ≃ₗ[R] (M ⊗[R] N) :=
  LinearEquiv.refl R _

/-- The tensor product of two finite free module objects is finite free. -/
theorem IsFiniteFree.tensorRight {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) : IsFiniteFree ((MonoidalCategory.tensorRight N).obj M) := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  have e := tensorRightLinearEquiv M N
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

/-- The rank of a tensor product of finite free module objects is the product of the ranks. -/
theorem rankOf_tensorRight [Nontrivial R] {M N : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hN : IsFiniteFree N) :
    rankOf ((MonoidalCategory.tensorRight N).obj M) = rankOf M * rankOf N := by
  have := hM.free
  have := hM.finite
  have := hN.free
  have := hN.finite
  rw [rankOf, (tensorRightLinearEquiv M N).finrank_eq, Module.finrank_tensorProduct]

/-- Tensoring a complex supported in `[a, b]` with a module gives a complex supported in
`[a, b]`. -/
theorem IsSupportedIn.tensorRight {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : IsSupportedIn K a b) (M : ModuleCat.{u} R) :
    IsSupportedIn (PerfectComplex.tensorRight K M) a b := fun i hi =>
  (MonoidalCategory.tensorRight M).map_isZero (h i hi)

/-- **The termwise tensor product of a strictly perfect complex with a finite free module is
strictly perfect.** -/
theorem IsStrictlyPerfect.tensorRight {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    IsStrictlyPerfect (PerfectComplex.tensorRight K M) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    exact ⟨a, b, hab.tensorRight M⟩
  finiteFree i := (hK.finiteFree i).tensorRight hM

/-- **The rank of a tensor product**: `rank (K ⊗ M) = rank K * rank M`. -/
theorem rank_tensorRight [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    rank (PerfectComplex.tensorRight K M) = rank K * (rankOf M : ℤ) := by
  rw [rank, rank, finsum_mul]
  refine finsum_congr fun i => ?_
  have hr : rankOf ((PerfectComplex.tensorRight K M).X i) = rankOf (K.X i) * rankOf M :=
    rankOf_tensorRight (hK.finiteFree i) hM
  rw [hr]
  push_cast
  ring

/-- The tensor product of a complex with a finite free module placed in cohomological degree
`n`.  Since the second factor is concentrated in a single degree there is no total complex to
form: it is the termwise tensor product, shifted so that degree `p` of `K` contributes in
degree `p + n`. -/
noncomputable def tensorSingle (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (n : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-n)).obj
    (PerfectComplex.tensorRight K M)

@[simp]
theorem tensorSingle_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (n i : ℤ) :
    (tensorSingle K M n).X i = (MonoidalCategory.tensorRight M).obj (K.X (i + -n)) :=
  rfl

/-- Tensoring a strictly perfect complex with a finite free module placed in a single degree is
strictly perfect. -/
theorem isStrictlyPerfect_tensorSingle {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) (n : ℤ) :
    IsStrictlyPerfect (tensorSingle K M n) :=
  (hK.tensorRight hM).shift (-n)

/-- The rank of the tensor product with a finite free module in degree `n`. -/
theorem rank_tensorSingle [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) (n : ℤ) :
    rank (tensorSingle K M n) = (n.negOnePow : ℤ) * (rank K * (rankOf M : ℤ)) := by
  rw [tensorSingle, rank_shift, rank_tensorRight hK hM, Int.negOnePow_neg]


/-! ## Two-out-of-three for perfectness in a distinguished triangle -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Realisation of a derived morphism by a chain map.**  A strictly perfect complex is a
bounded above complex of projective modules, hence K-projective, so every morphism out of it in
the derived category is the image of an actual morphism of cochain complexes. -/
theorem exists_chainMap_of_derivedMap {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K)
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : K ⟶ L, DerivedCategory.Q.map φ = u := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  have _ : K.IsKProjective := Modules.Derived.isKProjective_of_isStrictlyPerfect hK hab
  obtain ⟨γ, hγ⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫ u ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L)
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective γ
  refine ⟨φ, ?_⟩
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
  rw [Functor.comp_map, hγ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).mp hnat).symm

/-- **The third vertex of a distinguished triangle with two strictly perfect vertices is a
mapping cone.**  Given strictly perfect representatives of the first two vertices, the derived
morphism between them is realised by a chain map whose mapping cone represents the third
vertex. -/
theorem exists_mappingCone_iso_of_distTriang
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (e : DerivedCategory.Q.obj K ≅ T.obj₁) (e' : DerivedCategory.Q.obj L ≅ T.obj₂) :
    ∃ φ : K ⟶ L,
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone φ) ≅ T.obj₃) := by
  obtain ⟨φ, hφ⟩ := exists_chainMap_of_derivedMap hK (e.hom ≫ T.mor₁ ≫ e'.inv)
  refine ⟨φ, ?_⟩
  have hT₁ : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ∈
      distTriang (DerivedCategory (ModuleCat.{u} R)) :=
    DerivedCategory.mappingCone_triangle_distinguished φ
  have hcomm : DerivedCategory.Q.map φ ≫ e'.hom = e.hom ≫ T.mor₁ := by
    rw [hφ, Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id]
  obtain ⟨c, hc₂, hc₃⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism _ _ hT₁ hT e.hom e'.hom hcomm
  refine ⟨?_⟩
  have hiso : IsIso c := by
    refine Pretriangulated.isIso₃_of_isIso₁₂
      (Triangle.homMk _ _ e.hom e'.hom c hcomm hc₂ hc₃) hT₁ hT ?_ ?_
    · exact e.isIso_hom
    · exact e'.isIso_hom
  exact @asIso _ _ _ _ c hiso

/-- **Two out of three, third vertex.**  If the first two vertices of a distinguished triangle
are perfect, so is the third. -/
theorem IsPerfect.of_distTriang₃ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsPerfect T.obj₁) (h₂ : IsPerfect T.obj₂) :
    IsPerfect T.obj₃ := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h₁
  obtain ⟨L, hL, ⟨e'⟩⟩ := h₂
  obtain ⟨φ, ⟨f⟩⟩ := exists_mappingCone_iso_of_distTriang T hT hK e e'
  exact ⟨CochainComplex.mappingCone φ, isStrictlyPerfect_mappingCone φ hK hL, ⟨f⟩⟩

/-- **Two out of three, second vertex.**  If the first and third vertices of a distinguished
triangle are perfect, so is the second. -/
theorem IsPerfect.of_distTriang₂ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsPerfect T.obj₁) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₂ :=
  IsPerfect.of_distTriang₃ T.invRotate (Pretriangulated.inv_rot_of_distTriang _ hT)
    (h₃.shift (-1)) h₁

/-- **Two out of three, first vertex.**  If the second and third vertices of a distinguished
triangle are perfect, so is the first. -/
theorem IsPerfect.of_distTriang₁ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₂ : IsPerfect T.obj₂) (h₃ : IsPerfect T.obj₃) :
    IsPerfect T.obj₁ := by
  have h := IsPerfect.of_distTriang₃ T.rotate (Pretriangulated.rot_of_distTriang _ hT) h₂ h₃
  exact (h.shift (-1)).of_iso
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) 1 (-1) (by omega)).app T.obj₁)

/-- **Additivity of the rank in a distinguished triangle.**  Given strictly perfect
representatives of the first two vertices, the third vertex has a strictly perfect
representative whose rank is the difference of the two ranks. -/
theorem exists_isStrictlyPerfect_rank_of_distTriang [Nontrivial R]
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (hL : IsStrictlyPerfect L)
    (e : DerivedCategory.Q.obj K ≅ T.obj₁) (e' : DerivedCategory.Q.obj L ≅ T.obj₂) :
    ∃ M : CochainComplex (ModuleCat.{u} R) ℤ, IsStrictlyPerfect M ∧
      Nonempty (DerivedCategory.Q.obj M ≅ T.obj₃) ∧ rank L = rank K + rank M := by
  obtain ⟨φ, ⟨f⟩⟩ := exists_mappingCone_iso_of_distTriang T hT hK e e'
  refine ⟨CochainComplex.mappingCone φ, isStrictlyPerfect_mappingCone φ hK hL, ⟨f⟩, ?_⟩
  rw [rank_mappingCone φ hK hL]
  ring

end Derived


/-! ## Derived base change of ranks and of global two-term resolutions -/

section BaseChangeRank

open scoped ChangeOfRings

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Base change preserves the rank of a finite free module object. -/
theorem rankOf_extendScalars [Nontrivial R] [Nontrivial S] {M : ModuleCat.{u} R}
    (hM : IsFiniteFree M) : rankOf ((ModuleCat.extendScalars f).obj M) = rankOf M := by
  have := hM.free
  have := hM.finite
  let _ : Algebra R S := f.toAlgebra
  have e : (((ModuleCat.extendScalars f).obj M : ModuleCat.{u} S) : Type u) ≃ₗ[S] (S ⊗[R] M) :=
    LinearEquiv.refl S _
  rw [rankOf, e.finrank_eq, Module.finrank_baseChange]

/-- **Base change preserves the rank of a strictly perfect complex.** -/
theorem rank_baseChange [Nontrivial R] [Nontrivial S] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) : rank (baseChange f K) = rank K :=
  finsum_congr fun i => by
    rw [baseChange_X, rankOf_extendScalars f (hK.finiteFree i)]

end BaseChangeRank

section BaseChangeResolution

attribute [local instance] HasDerivedCategory.standard

variable {S : Type u} [CommRing S] (f : R →+* S)

namespace GlobalTwoTermResolution

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- **Derived base change of a global two-term resolution.**  The termwise extension of scalars
of the resolving complex is again an actual two-term complex of finite free `S`-modules, and it
resolves its own image in `DerivedCategory (ModuleCat S)`. -/
noncomputable def baseChange (F : GlobalTwoTermResolution E) (f : R →+* S) :
    GlobalTwoTermResolution
      (DerivedCategory.Q.obj (PerfectComplex.baseChange f F.complex)) where
  complex := PerfectComplex.baseChange f F.complex
  supported i hi := (ModuleCat.extendScalars f).map_isZero (F.supported i hi)
  finiteFree i := (F.finiteFree i).extendScalars f
  iso := Iso.refl _

@[simp]
theorem baseChange_complex (F : GlobalTwoTermResolution E) (f : R →+* S) :
    (F.baseChange f).complex = PerfectComplex.baseChange f F.complex :=
  rfl

/-- The base change of a global two-term resolution has the same virtual rank. -/
theorem baseChange_virtualRank [Nontrivial R] [Nontrivial S] (F : GlobalTwoTermResolution E)
    (f : R →+* S) : (F.baseChange f).virtualRank = F.virtualRank :=
  rank_baseChange f F.isStrictlyPerfect

/-- **Derived base change is independent of the chosen resolution.**  Any two global two-term
resolutions of the same derived object have canonically quasi-isomorphic base changes, so the
base-changed object of `DerivedCategory (ModuleCat S)` depends only on `E`.  The comparison is
produced by realising the derived comparison as a chain map and base changing it. -/
theorem nonempty_baseChange_iso (F F' : GlobalTwoTermResolution E) (f : R →+* S) :
    Nonempty (DerivedCategory.Q.obj (PerfectComplex.baseChange f F.complex) ≅
      DerivedCategory.Q.obj (PerfectComplex.baseChange f F'.complex)) := by
  obtain ⟨φ, hφ⟩ :=
    exists_chainMap_of_derivedMap F.isStrictlyPerfect (F.iso ≪≫ F'.iso.symm).hom
  let _ : QuasiIso φ := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hφ]
    infer_instance
  let _ : F.complex.IsStrictlyLE 0 := Modules.Derived.isStrictlyLE_of_isSupportedIn F.supported
  let _ : F'.complex.IsStrictlyLE 0 := Modules.Derived.isStrictlyLE_of_isSupportedIn F'.supported
  let _ : ∀ n, Projective (F.complex.X n) := fun n =>
    Modules.Derived.projective_of_isFiniteFree (F.finiteFree n)
  let _ : ∀ n, Projective (F'.complex.X n) := fun n =>
    Modules.Derived.projective_of_isFiniteFree (F'.finiteFree n)
  exact ⟨Modules.Derived.baseChangeDerivedIso f 0 φ⟩

/-- The base change of a global two-term resolution is perfect over `S`. -/
theorem isPerfect_baseChange (F : GlobalTwoTermResolution E) (f : R →+* S) :
    IsPerfect (DerivedCategory.Q.obj (PerfectComplex.baseChange f F.complex)) :=
  (F.baseChange f).isPerfect

end GlobalTwoTermResolution

end BaseChangeResolution


/-! ## Consequences in the derived category -/

section DerivedConsequences

attribute [local instance] HasDerivedCategory.standard

/-- The image of the dual of a strictly perfect complex is a perfect object. -/
theorem isPerfect_dual {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K) :
    IsPerfect (DerivedCategory.Q.obj (dualComplex K)) :=
  isPerfect_Q hK.dual

/-- The image of the termwise tensor product of a strictly perfect complex with a finite free
module is a perfect object. -/
theorem isPerfect_tensorRight {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    IsPerfect (DerivedCategory.Q.obj (PerfectComplex.tensorRight K M)) :=
  isPerfect_Q (hK.tensorRight hM)

/-- The image of the tensor product with a finite free module in a single degree is perfect. -/
theorem isPerfect_tensorSingle {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {M : ModuleCat.{u} R} (hM : IsFiniteFree M) (n : ℤ) :
    IsPerfect (DerivedCategory.Q.obj (tensorSingle K M n)) :=
  isPerfect_Q (isStrictlyPerfect_tensorSingle hK hM n)

/-- **Perfect objects are stable under cones.**  Every morphism of perfect objects sits in a
distinguished triangle whose third vertex is again perfect. -/
theorem exists_isPerfect_cone {E E' : DerivedCategory (ModuleCat.{u} R)} (u : E ⟶ E')
    (hE : IsPerfect E) (hE' : IsPerfect E') :
    ∃ (Z : DerivedCategory (ModuleCat.{u} R)) (g : E' ⟶ Z) (h : Z ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk u g h ∈ distTriang _ ∧ IsPerfect Z := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  exact ⟨Z, g, h, hT, IsPerfect.of_distTriang₃ _ hT hE hE'⟩

end DerivedConsequences

/-! ## The dual of a global two-term resolution -/

section DualResolution

attribute [local instance] HasDerivedCategory.standard

namespace GlobalTwoTermResolution

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- The shifted dual `K^∨[1]` of the resolving complex of a global two-term resolution.  It is
again concentrated in degrees `-1` and `0`, which is the shape in which obstruction theories
use the dual. -/
noncomputable def dualShiftComplex (F : GlobalTwoTermResolution E) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).obj
    (dualComplex F.complex)

/-- **The shifted dual of a global two-term resolution is a global two-term resolution** of its
own image in the derived category. -/
noncomputable def dual (F : GlobalTwoTermResolution E) :
    GlobalTwoTermResolution (DerivedCategory.Q.obj F.dualShiftComplex) where
  complex := F.dualShiftComplex
  supported := ((F.supported.dual).shift 1).mono (by omega) (by omega)
  finiteFree i := by
    rw [dualShiftComplex, CochainComplex.shiftFunctor_obj_X', dualComplex_X]
    exact (F.finiteFree (-(i + 1))).dual
  iso := Iso.refl _

@[simp]
theorem dual_complex (F : GlobalTwoTermResolution E) : F.dual.complex = F.dualShiftComplex :=
  rfl

/-- The shifted dual of a global two-term resolution has the opposite virtual rank. -/
theorem dual_virtualRank [Nontrivial R] (F : GlobalTwoTermResolution E) :
    F.dual.virtualRank = -F.virtualRank := by
  rw [virtualRank, dual_complex, dualShiftComplex, rank_shift,
    PerfectComplex.rank_dual F.finiteFree]
  simp only [Int.negOnePow_one, Units.val_neg, Units.val_one]
  rw [neg_one_mul]
  rfl

/-- **Tensoring a global two-term resolution with a finite free module** gives a global
two-term resolution of the termwise tensor product. -/
noncomputable def tensorRight (F : GlobalTwoTermResolution E) {M : ModuleCat.{u} R}
    (hM : IsFiniteFree M) :
    GlobalTwoTermResolution
      (DerivedCategory.Q.obj (PerfectComplex.tensorRight F.complex M)) where
  complex := PerfectComplex.tensorRight F.complex M
  supported := F.supported.tensorRight M
  finiteFree i := (F.finiteFree i).tensorRight hM
  iso := Iso.refl _

@[simp]
theorem tensorRight_complex (F : GlobalTwoTermResolution E) {M : ModuleCat.{u} R}
    (hM : IsFiniteFree M) :
    (F.tensorRight hM).complex = PerfectComplex.tensorRight F.complex M :=
  rfl

/-- The virtual rank of the tensor product with a finite free module. -/
theorem tensorRight_virtualRank [Nontrivial R] (F : GlobalTwoTermResolution E)
    {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    (F.tensorRight hM).virtualRank = F.virtualRank * (rankOf M : ℤ) :=
  rank_tensorRight F.isStrictlyPerfect hM

/-- The shifted dual of a global two-term resolution is perfect. -/
theorem isPerfect_dualShiftComplex (F : GlobalTwoTermResolution E) :
    IsPerfect (DerivedCategory.Q.obj F.dualShiftComplex) :=
  F.dual.isPerfect

end GlobalTwoTermResolution

end DualResolution


end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
