/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Construction

/-!
# Independence of the virtual class of the chosen global resolution

Behrend–Fantechi, Proposition 5.3, in the affine model of
`VirtualFundamentalClass/Construction.lean`.

Two obstruction theories `φ : E ⟶ L` and `φ' : E' ⟶ L` over the same conormal complex
`L = conormalComplex k R I` which are related by an isomorphism `ψ : E ≅ E'` of two-term
complexes with `φ' ∘ ψ = φ` produce the same resolved cone, the same resolved-cone class and the
same virtual class.

## Contents

* Transport along an isomorphism of schemes: `length_self_eq_of_ringEquiv`,
  `genericLength_eq_of_isIso`, `fundamentalCycle_base_of_isIso` and
  `map_fundamentalCycle_of_isIso` — the fundamental cycle of a locally Noetherian scheme is
  carried to the fundamental cycle by an isomorphism.
* The algebra of the comparison: `symAlgHom`, `symAlgEquiv`, `bundleEquiv`, `productEquiv`,
  `productEquiv_comp_productMap`, `ideal_map_bundleEquiv` (the isomorphism of bundles carries
  the ideal of `C(E)` onto the ideal of `C(E')`), `ringEquiv`, `bundleSpaceIso`,
  `coneSchemeIso` and `toBundle_comp_bundleSpaceIso_inv`.
* The degree-generic virtual class `virtualClassAt`, which records the trivialisation of `E₁`
  and the degree as explicit parameters.  It agrees with `VirtualClass.virtualClass` for the
  canonical trivialisation and degree (`virtualClassAt_trivialization`, by `rfl`).  This is
  needed because for two different complexes `E`, `E'` the degrees `virtualDimension φ` and
  `virtualDimension φ'` are only propositionally equal, and the two canonical trivialisation
  index types are different types.
* Isomorphism invariance: `flatPullbackOpen_resolvedConeCycleAt`,
  `chowEquivOfAlgEquiv_resolvedConeClassAt`, `chowPullbackBundle_eq_resolvedConeClassAt_iff`
  (a class on the base is a virtual class for `φ` if and only if it is one for `φ'`, with no
  injectivity hypothesis), `virtualClassQuotAt_congr` (the canonical classes in
  `A_i(X) ⧸ ker π^*` agree), `virtualClassAt_congr` and `virtualClass_eq_virtualClassAt`
  (the virtual classes themselves agree, under the injectivity hypothesis inherited from
  `Construction.lean`), and `virtualDimension_congr`.
* Acyclic summands: `acyclicComplex`, `sumAcyclic`, `isObstructionTheory_sumAcyclic`,
  `productInl_comp_productMap`, `mem_ideal_sumAcyclic_iff`, `comap_ideal_sumAcyclic` (`C(E)` is
  the scheme-theoretic image of `C(E ⊕ [F = F])` under the bundle projection),
  `map_ideal_le_ideal_sumAcyclic` and `virtualDimension_sumAcyclic`.

## What is not done here

For an acyclic summand the equality `C(E') = p⁻¹(C(E))` of *schemes* (as opposed to the two
inclusions proved here) needs the flatness of `Sym(E⁻¹ ⊕ F)` over `Sym(E⁻¹)`, that is the
isomorphism `Sym(M ⊕ F) ≅ Sym(M)[X_j]`, which Mathlib does not provide; consequently the
cycle-level and class-level comparison for an acyclic summand is not proved.  The invariance
under a general chain-homotopy equivalence (as opposed to an isomorphism) of obstruction
theories is likewise not proved.
-/

universe u

set_option maxSynthPendingDepth 5

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass

open IntersectionTheory hiding Scheme AlgebraicCycle
open NormalSheafPicard.AffineIntrinsicNormalSheaf

/-! ## Transporting the fundamental cycle along an isomorphism -/

/-- The length of a commutative ring as a module over itself is invariant under ring
isomorphism: the two ideal lattices are order-isomorphic. -/
theorem length_self_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso e.idealComapOrderIso).symm

/-- A morphism of schemes is monotone for the specialization order. -/
theorem le_base_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {a b : X} (h : a ≤ b) :
    f.base a ≤ f.base b :=
  h.map f.continuous

/-- The two-sided inverse of an isomorphism of schemes on points, in the direction needed
below. -/
theorem inv_base_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    (inv f).base (f.base x) = x := by
  change (f ≫ inv f).base x = x
  rw [IsIso.hom_inv_id]
  rfl

/-- The two-sided inverse of an isomorphism of schemes on points, in the other direction. -/
theorem base_inv_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (y : Y) :
    f.base ((inv f).base y) = y := by
  change (inv f ≫ f).base y = y
  rw [IsIso.inv_hom_id]
  rfl

/-- Maximality for the specialization order (being a generic point) is preserved by an
isomorphism of schemes. -/
theorem isMax_base_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {x : X} (hx : IsMax x) :
    IsMax (f.base x) := by
  intro y hy
  have h1 : x ≤ (inv f).base y := by
    have h := le_base_of_le (inv f) hy
    rwa [inv_base_base f x] at h
  have h2 := le_base_of_le f (hx h1)
  rwa [base_inv_base f y] at h2

/-- The generic multiplicity of a point is preserved by an isomorphism of schemes: the stalks
are isomorphic rings. -/
theorem genericLength_eq_of_isIso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsIso f] (x : X) :
    Y.genericLength (f.base x) = X.genericLength x := by
  have hbij : Function.Bijective (f.stalkMap x).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hlen := length_self_eq_of_ringEquiv (RingEquiv.ofBijective (f.stalkMap x).hom hbij)
  change (Module.length _ _).toNat = (Module.length _ _).toNat
  rw [hlen]

/-- **The fundamental cycle is transported by an isomorphism of schemes.** -/
theorem fundamentalCycle_base_of_isIso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsIso f] (x : X) :
    Y.fundamentalCycle (f.base x) = X.fundamentalCycle x := by
  by_cases hx : IsMax x
  · have hy : IsMax (f.base x) := isMax_base_of_isIso f hx
    rw [Y.fundamentalCycle_apply_of_isMax _ hy, X.fundamentalCycle_apply_of_isMax x hx,
      genericLength_eq_of_isIso f x]
  · have hy : ¬ IsMax (f.base x) := by
      intro hy
      refine hx ?_
      have hback := isMax_base_of_isIso (inv f) hy
      rwa [inv_base_base f x] at hback
    rw [Y.fundamentalCycle_apply_of_not_isMax _ hy, X.fundamentalCycle_apply_of_not_isMax x hx]

/-- **The fundamental cycle is transported by the residue-degree pushforward along an
isomorphism of schemes.** -/
theorem map_fundamentalCycle_of_isIso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (ε : X ≅ Y) (dimX : DimensionFunction X)
    (dimY : DimensionFunction Y) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom dimX dimY X.fundamentalCycle =
      Y.fundamentalCycle := by
  have hiso : IsIso ε.inv := ⟨ε.hom, ε.inv_hom_id, ε.hom_inv_id⟩
  have hpull : AlgebraicCycle.pullbackOpen ε.inv X.fundamentalCycle =
      _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom dimX dimY X.fundamentalCycle :=
    AlgebraicCycle.pullbackOpen_eq_map_of_isIso ε.symm dimY dimX X.fundamentalCycle
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  have hval : _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom dimX dimY
      X.fundamentalCycle y = X.fundamentalCycle (ε.inv.base y) := by
    rw [← hpull]
    exact AlgebraicCycle.pullbackOpen_apply ε.inv X.fundamentalCycle y
  change _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom dimX dimY
    X.fundamentalCycle y = Y.fundamentalCycle y
  rw [hval, fundamentalCycle_base_of_isIso ε.inv y]


/-! ## Symmetric algebras of isomorphic modules -/

/-- The algebra map of symmetric algebras induced by a linear map. -/
noncomputable def symAlgHom {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) :
    SymmetricAlgebra S M →ₐ[S] SymmetricAlgebra S N :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι S N).comp f)

@[simp]
theorem symAlgHom_ι {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (x : M) :
    symAlgHom f (SymmetricAlgebra.ι S M x) = SymmetricAlgebra.ι S N (f x) :=
  SymmetricAlgebra.lift_ι_apply _ x

/-- The isomorphism of symmetric algebras induced by an isomorphism of modules. -/
noncomputable def symAlgEquiv {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (ψ : M ≃ₗ[S] N) :
    SymmetricAlgebra S M ≃ₐ[S] SymmetricAlgebra S N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι S N).comp (ψ : M →ₗ[S] N)))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι S M).comp (ψ.symm : N →ₗ[S] M)))
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro y
      simp)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro x
      simp)

@[simp]
theorem symAlgEquiv_ι {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (ψ : M ≃ₗ[S] N) (x : M) :
    symAlgEquiv ψ (SymmetricAlgebra.ι S M x) = SymmetricAlgebra.ι S N (ψ x) := by
  change SymmetricAlgebra.lift ((SymmetricAlgebra.ι S N).comp (ψ : M →ₗ[S] N))
    (SymmetricAlgebra.ι S M x) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

/-! ## The comparison of two obstruction theories related by an isomorphism -/

section Comparison

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))
variable (ψ : LinearTwoTermComplex.Hom E E')

/-- The isomorphism of the degree `-1` terms given by a bijective chain map. -/
noncomputable def zeroEquiv (hψ0 : Function.Bijective ψ.degreeZero) :
    E.degreeZero ≃ₗ[R ⧸ I] E'.degreeZero :=
  LinearEquiv.ofBijective ψ.degreeZero hψ0

@[simp]
theorem zeroEquiv_apply (hψ0 : Function.Bijective ψ.degreeZero) (x : E.degreeZero) :
    zeroEquiv ψ hψ0 x = ψ.degreeZero x :=
  rfl

/-- The isomorphism of the degree `0` terms given by a bijective chain map. -/
noncomputable def oneEquiv (hψ1 : Function.Bijective ψ.degreeOne) :
    E.degreeOne ≃ₗ[R ⧸ I] E'.degreeOne :=
  LinearEquiv.ofBijective ψ.degreeOne hψ1

@[simp]
theorem oneEquiv_apply (hψ1 : Function.Bijective ψ.degreeOne) (y : E.degreeOne) :
    oneEquiv ψ hψ1 y = ψ.degreeOne y :=
  rfl

/-- **The induced isomorphism of the coordinate rings of the two bundles `E₁` and `E'₁`.** -/
noncomputable def bundleEquiv (hψ0 : Function.Bijective ψ.degreeZero) :
    ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] ResolvedCone.bundleRing φ' :=
  symAlgEquiv (zeroEquiv ψ hψ0)

@[simp]
theorem bundleEquiv_ι (hψ0 : Function.Bijective ψ.degreeZero) (x : E.degreeZero) :
    bundleEquiv φ φ' ψ hψ0 (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      SymmetricAlgebra.ι (R ⧸ I) E'.degreeZero (ψ.degreeZero x) :=
  symAlgEquiv_ι _ x

/-- **The induced isomorphism of the coordinate rings of `C ×_X E₀` and `C ×_X E'₀`.** -/
noncomputable def productEquiv (hψ1 : Function.Bijective ψ.degreeOne) :
    ResolvedCone.productRing φ ≃ₐ[R ⧸ I] ResolvedCone.productRing φ' :=
  Algebra.TensorProduct.congr AlgEquiv.refl (symAlgEquiv (oneEquiv ψ hψ1))

@[simp]
theorem productEquiv_tmul (hψ1 : Function.Bijective ψ.degreeOne)
    (c : AffineNormalCone.associatedGradedRing R I)
    (b : SymmetricAlgebra (R ⧸ I) E.degreeOne) :
    productEquiv φ φ' ψ hψ1 (c ⊗ₜ[R ⧸ I] b) = c ⊗ₜ[R ⧸ I] symAlgEquiv (oneEquiv ψ hψ1) b :=
  rfl

/-- **The two coordinate-ring maps of `C ×_X E₀ → E₁` agree under the induced isomorphisms.**
This is the ring-theoretic heart of the independence statement: only the compatibility of the
two obstruction theories in degree `-1` is used, the degree `0` compatibility being automatic
from the chain-map condition on `ψ`. -/
theorem productEquiv_comp_productMap (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    (productEquiv φ φ' ψ hψ1).toAlgHom.comp (ResolvedCone.productMap φ) =
      (ResolvedCone.productMap φ').comp (bundleEquiv φ φ' ψ hψ0).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  have hd : E'.differential (ψ.degreeZero x) = ψ.degreeOne (E.differential x) :=
    (ψ.comm x).symm
  have h0 : φ'.degreeZero (ψ.degreeZero x) = φ.degreeZero x :=
    congrArg (fun f : E.degreeZero →ₗ[R ⧸ I] (conormalComplex k R I).degreeZero => f x) hcomp
  change productEquiv φ φ' ψ hψ1 (ResolvedCone.productMap φ
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) =
    ResolvedCone.productMap φ' (bundleEquiv φ φ' ψ hψ0
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x))
  rw [ResolvedCone.productMap_ι, bundleEquiv_ι, ResolvedCone.productMap_ι, hd, h0, map_add,
    productEquiv_tmul, productEquiv_tmul, map_one, symAlgEquiv_ι, oneEquiv_apply]

/-- The coordinate-ring maps agree pointwise. -/
theorem productEquiv_productMap (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) (a : ResolvedCone.bundleRing φ) :
    productEquiv φ φ' ψ hψ1 (ResolvedCone.productMap φ a) =
      ResolvedCone.productMap φ' (bundleEquiv φ φ' ψ hψ0 a) :=
  congrArg (fun f : ResolvedCone.bundleRing φ →ₐ[R ⧸ I] ResolvedCone.productRing φ' => f a)
    (productEquiv_comp_productMap φ φ' ψ hψ0 hψ1 hcomp)

/-- **The isomorphism of bundles carries the ideal of the resolved cone to the ideal of the
resolved cone.** -/
theorem mem_ideal_iff_bundleEquiv (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) (a : ResolvedCone.bundleRing φ) :
    a ∈ ResolvedCone.ideal φ ↔ bundleEquiv φ φ' ψ hψ0 a ∈ ResolvedCone.ideal φ' := by
  rw [ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff,
    ← productEquiv_productMap φ φ' ψ hψ0 hψ1 hcomp]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (productEquiv φ φ' ψ hψ1).injective (by rw [h, map_zero])

/-- The ideal of the resolved cone of `φ` is the contraction of the ideal of the resolved cone
of `φ'`. -/
theorem comap_ideal_bundleEquiv (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    Ideal.comap (bundleEquiv φ φ' ψ hψ0).toRingHom (ResolvedCone.ideal φ') =
      ResolvedCone.ideal φ :=
  Ideal.ext fun a => (mem_ideal_iff_bundleEquiv φ φ' ψ hψ0 hψ1 hcomp a).symm

/-- **The ideal of the resolved cone of `φ'` is the image of the ideal of the resolved cone of
`φ`.** -/
theorem ideal_map_bundleEquiv (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    Ideal.map (bundleEquiv φ φ' ψ hψ0).toRingHom (ResolvedCone.ideal φ) =
      ResolvedCone.ideal φ' := by
  rw [← comap_ideal_bundleEquiv φ φ' ψ hψ0 hψ1 hcomp]
  exact Ideal.map_comap_of_surjective _ (bundleEquiv φ φ' ψ hψ0).surjective _

/-- **The induced isomorphism of the coordinate rings of the two resolved cones.** -/
noncomputable def ringEquiv (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    ResolvedCone.ring φ ≃ₐ[R ⧸ I] ResolvedCone.ring φ' :=
  Ideal.quotientEquivAlg (ResolvedCone.ideal φ) (ResolvedCone.ideal φ')
    (bundleEquiv φ φ' ψ hψ0) (ideal_map_bundleEquiv φ φ' ψ hψ0 hψ1 hcomp).symm

@[simp]
theorem ringEquiv_mk (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) (a : ResolvedCone.bundleRing φ) :
    ringEquiv φ φ' ψ hψ0 hψ1 hcomp (Ideal.Quotient.mk (ResolvedCone.ideal φ) a) =
      Ideal.Quotient.mk (ResolvedCone.ideal φ') (bundleEquiv φ φ' ψ hψ0 a) :=
  rfl


/-! ### The induced isomorphism of schemes -/

/-- **The isomorphism `E'₁ ≅ E₁` of the two bundles.** -/
noncomputable def bundleSpaceIso (hψ0 : Function.Bijective ψ.degreeZero) :
    ResolvedCone.bundleSpace φ' ≅ ResolvedCone.bundleSpace φ :=
  VectorBundle.specIsoOfAlgEquiv (bundleEquiv φ φ' ψ hψ0)

/-- **The isomorphism `C(E') ≅ C(E)` of the two resolved cones.** -/
noncomputable def coneSchemeIso (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    ResolvedCone.scheme φ' ≅ ResolvedCone.scheme φ :=
  VectorBundle.specIsoOfAlgEquiv (ringEquiv φ φ' ψ hψ0 hψ1 hcomp)

theorem ringEquiv_symm_mk (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) (b : ResolvedCone.bundleRing φ') :
    (ringEquiv φ φ' ψ hψ0 hψ1 hcomp).symm (Ideal.Quotient.mk (ResolvedCone.ideal φ') b) =
      Ideal.Quotient.mk (ResolvedCone.ideal φ) ((bundleEquiv φ φ' ψ hψ0).symm b) := by
  apply (ringEquiv φ φ' ψ hψ0 hψ1 hcomp).injective
  rw [AlgEquiv.apply_symm_apply, ringEquiv_mk, AlgEquiv.apply_symm_apply]

/-- **The isomorphism of resolved cones is compatible with the closed immersions into the two
bundles.** -/
theorem toBundle_comp_bundleSpaceIso_inv (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero) :
    ResolvedCone.toBundle φ ≫ (bundleSpaceIso φ φ' ψ hψ0).inv =
      (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).inv ≫ ResolvedCone.toBundle φ' := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

end Comparison

/-! ## Functoriality of the cycle pushforward for closed immersions -/

/-- The residue-degree pushforward depends only on the morphism, not on the proof that it is
quasi-compact; this lets one rewrite the morphism inside a pushforward. -/
theorem map_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [_root_.AlgebraicGeometry.QuasiCompact f] [_root_.AlgebraicGeometry.QuasiCompact g]
    (h : f = g) (wx : X → ℤ) (wy : Y → ℤ) (c : AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f wx wy c =
      _root_.AlgebraicGeometry.AlgebraicCycle.map g wx wy c := by
  subst h
  rfl

/-- Residue-degree pushforward of cycles is functorial along two closed immersions, stated with
certified dimension gradings (which are automatically compatible). -/
theorem map_comp_closedImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [_root_.AlgebraicGeometry.IsClosedImmersion f]
    [_root_.AlgebraicGeometry.IsClosedImmersion g]
    (dX : DimensionFunction X) (dY : DimensionFunction Y) (dZ : DimensionFunction Z)
    (c : AlgebraicCycle X ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (f ≫ g) dX dZ c =
      _root_.AlgebraicGeometry.AlgebraicCycle.map g dY dZ
        (_root_.AlgebraicGeometry.AlgebraicCycle.map f dX dY c) := by
  have hdx : (dX : X → ℤ) = fun x ↦ dY (f.base x) :=
    funext fun x => DimensionFunction.apply_eq_of_isClosedImmersion dX dY f x
  have hdy : (dY : Y → ℤ) = fun y ↦ dZ (g.base y) :=
    funext fun y => DimensionFunction.apply_eq_of_isClosedImmersion dY dZ g y
  rw [hdx, hdy]
  exact (AlgebraicCycle.map_comp_of_isClosedImmersion f g (fun y ↦ dZ (g.base y)) dZ c).symm



/-! ## The virtual class with the trivialisation and the degree as explicit parameters

`VirtualClass.virtualClass φ dimX dimE RX RE hhom hinj` is built from the canonical
trivialisation `trivialization φ` of `E₁` and lives in degree `virtualDimension φ`.  Comparing
the virtual classes of two obstruction theories requires the two degrees and the two
trivialisation index types to be *the same*, which for two different complexes `E`, `E'` is only
propositionally true.  The following degree-generic version takes both as parameters; it agrees
with `virtualClass` for the canonical choices (`virtualClassAt_trivialization`).
-/

section AtDegree

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The resolved-cone cycle of `φ`, placed in an arbitrary degree `d`.  For `d = coneDegree φ`
this is `resolvedConeCycle φ dimE`. -/
noncomputable def resolvedConeCycleAt (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (d : ℤ) : cyclesOfDimension (ResolvedCone.bundleSpace φ) dimE d :=
  cyclesOfDimension.project
    (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
      (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle)

@[simp]
theorem resolvedConeCycleAt_apply (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (d : ℤ) (u : ResolvedCone.bundleSpace φ) :
    (resolvedConeCycleAt φ dimE d : AlgebraicCycle (ResolvedCone.bundleSpace φ) ℚ) u =
      if dimE u = d then
        _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
          (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle u
      else 0 :=
  rfl

/-- In the degree `vd + a` the degree-generic resolved-cone cycle is the resolved-cone cycle of
`VirtualFundamentalClass/Construction.lean`. -/
theorem resolvedConeCycleAt_coneDegree
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) :
    resolvedConeCycleAt φ dimE (coneDegree φ) = resolvedConeCycle φ dimE :=
  rfl

variable {ι : Type u} [Finite ι]
variable (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ)) (i : ℤ)
variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE
  (i + (Nat.card ι : ℤ)))

omit [Finite ι] in
/-- The resolved-cone class in the degree `i + rk ι`. -/
noncomputable def resolvedConeClassAt : RE.ChowGroup :=
  RE.quotientMap (resolvedConeCycleAt φ dimE (i + (Nat.card ι : ℤ)))

/-- **The virtual class of `φ` computed in the trivialisation `e` and the degree `i`.** -/
noncomputable def virtualClassAt
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    RX.ChowGroup :=
  VectorBundle.zeroSectionGysin' e dimX dimE i RX RE hhom hinj
    (resolvedConeClassAt φ dimE i RE)

/-- **The defining property of the degree-generic virtual class.** -/
@[simp]
theorem chowPullbackBundle_virtualClassAt
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    VectorBundle.chowPullbackBundle e dimX dimE i RX RE
        (virtualClassAt φ e dimX dimE i RX RE hhom hinj) =
      resolvedConeClassAt φ dimE i RE :=
  VectorBundle.pullback_zeroSectionGysin' e dimX dimE i RX RE hhom hinj _

/-- **Existence of a virtual class in the degree-generic setting**, with no injectivity
hypothesis: the resolved-cone class is a flat pullback from the base. -/
theorem exists_virtualClassAt
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    ∃ α : RX.ChowGroup, VectorBundle.chowPullbackBundle e dimX dimE i RX RE α =
      resolvedConeClassAt φ dimE i RE :=
  VectorBundle.chowPullbackBundle_surjective' e dimX dimE i RX RE hhom _

/-- **The canonical virtual class** in the degree-generic setting, an element of
`A_i(X) ⧸ ker π^*`; no injectivity hypothesis is needed. -/
noncomputable def virtualClassQuotAt
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    RX.ChowGroup ⧸ LinearMap.ker (VectorBundle.chowPullbackBundle e dimX dimE i RX RE) :=
  (VectorBundle.chowQuotientEquiv' e dimX dimE i RX RE hhom).symm
    (resolvedConeClassAt φ dimE i RE)

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The isomorphism `A_i(X) ⧸ ker π^* ≃ A_{i+r}(E₁)` is induced by the flat pullback. -/
theorem chowQuotientEquiv_mk
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (α : RX.ChowGroup) :
    VectorBundle.chowQuotientEquiv' e dimX dimE i RX RE hhom (Submodule.Quotient.mk α) =
      VectorBundle.chowPullbackBundle e dimX dimE i RX RE α :=
  rfl

/-- The canonical virtual class is the class of any cycle class pulling back to the
resolved-cone class. -/
theorem virtualClassQuotAt_eq_mk
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (α : RX.ChowGroup)
    (hα : VectorBundle.chowPullbackBundle e dimX dimE i RX RE α =
      resolvedConeClassAt φ dimE i RE) :
    virtualClassQuotAt φ e dimX dimE i RX RE hhom = Submodule.Quotient.mk α := by
  apply (VectorBundle.chowQuotientEquiv' e dimX dimE i RX RE hhom).injective
  rw [chowQuotientEquiv_mk, hα]
  exact (VectorBundle.chowQuotientEquiv' e dimX dimE i RX RE hhom).apply_symm_apply _

/-- The degree-generic virtual class is characterised by its defining property. -/
theorem eq_virtualClassAt_of_pullback_eq
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE))
    (α : RX.ChowGroup)
    (hα : VectorBundle.chowPullbackBundle e dimX dimE i RX RE α =
      resolvedConeClassAt φ dimE i RE) :
    α = virtualClassAt φ e dimX dimE i RX RE hhom hinj :=
  hinj (by rw [hα, chowPullbackBundle_virtualClassAt])

end AtDegree

section CanonicalDegree

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
variable (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
  (virtualDimension φ))
variable (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))

/-- The degree-generic resolved-cone class in the canonical trivialisation and degree is the
resolved-cone class of `VirtualFundamentalClass/Construction.lean`. -/
theorem resolvedConeClassAt_trivialization :
    resolvedConeClassAt (ι := Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) φ dimE
        (virtualDimension φ) RE = resolvedConeClass φ dimE RE :=
  rfl

/-- **The degree-generic virtual class in the canonical trivialisation and degree is the virtual
class of `VirtualFundamentalClass/Construction.lean`.** -/
theorem virtualClassAt_trivialization
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClassAt φ (trivialization φ) dimX dimE (virtualDimension φ) RX RE hhom hinj =
      virtualClass φ dimX dimE RX RE hhom hinj :=
  rfl

end CanonicalDegree


/-! ## Independence of the virtual class of the global resolution -/

section Independence

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E E' : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (φ' : LinearTwoTermComplex.Hom E' (conormalComplex k R I))

/-- **The two resolved-cone cycles correspond under the isomorphism of bundles**, at the level of
the underlying algebraic cycles: the pushforward of the fundamental cycle of `C(E)` pulls back to
the pushforward of the fundamental cycle of `C(E')`. -/
theorem pullbackOpen_map_fundamentalCycle_toBundle (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) :
    AlgebraicCycle.pullbackOpen (bundleSpaceIso φ φ' ψ hψ0).hom
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
          (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ')
        (coneDimension φ' dimE') dimE' (ResolvedCone.scheme φ').fundamentalCycle := by
  have hb : IsIso (bundleSpaceIso φ φ' ψ hψ0).inv :=
    ⟨(bundleSpaceIso φ φ' ψ hψ0).hom, (bundleSpaceIso φ φ' ψ hψ0).inv_hom_id,
      (bundleSpaceIso φ φ' ψ hψ0).hom_inv_id⟩
  have hc : IsIso (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).inv :=
    ⟨(coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).hom, (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).inv_hom_id,
      (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).hom_inv_id⟩
  have h1 : AlgebraicCycle.pullbackOpen (bundleSpaceIso φ φ' ψ hψ0).hom
      (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
        (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (bundleSpaceIso φ φ' ψ hψ0).inv dimE dimE'
        (_root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
          (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle) :=
    AlgebraicCycle.pullbackOpen_eq_map_of_isIso (bundleSpaceIso φ φ' ψ hψ0) dimE' dimE _
  have h2 : _root_.AlgebraicGeometry.AlgebraicCycle.map
      (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).inv (coneDimension φ dimE) (coneDimension φ' dimE')
      (ResolvedCone.scheme φ).fundamentalCycle = (ResolvedCone.scheme φ').fundamentalCycle :=
    map_fundamentalCycle_of_isIso (coneSchemeIso φ φ' ψ hψ0 hψ1 hcomp).symm
      (coneDimension φ dimE) (coneDimension φ' dimE')
  have h3 := map_congr_hom (toBundle_comp_bundleSpaceIso_inv φ φ' ψ hψ0 hψ1 hcomp)
    (coneDimension φ dimE) dimE' (ResolvedCone.scheme φ).fundamentalCycle
  rw [h1, ← map_comp_closedImmersion, h3,
    map_comp_closedImmersion _ _ (coneDimension φ dimE) (coneDimension φ' dimE') dimE', h2]

/-- **The two resolved-cone cycles correspond under the isomorphism of bundles**, in every
degree. -/
theorem flatPullbackOpen_resolvedConeCycleAt (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (d : ℤ) :
    cyclesOfDimension.flatPullbackOpen (bundleSpaceIso φ φ' ψ hψ0).hom
        (VectorBundle.dimension_comap_algEquiv (bundleEquiv φ φ' ψ hψ0) dimE dimE')
        (resolvedConeCycleAt φ dimE d) = resolvedConeCycleAt φ' dimE' d := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext u
  have hval : _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ')
      (coneDimension φ' dimE') dimE' (ResolvedCone.scheme φ').fundamentalCycle u =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
        (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle
        ((bundleSpaceIso φ φ' ψ hψ0).hom.base u) := by
    rw [← pullbackOpen_map_fundamentalCycle_toBundle φ φ' ψ hψ0 hψ1 hcomp dimE dimE']
    exact AlgebraicCycle.pullbackOpen_apply _ _ u
  have hdim : dimE' u = dimE ((bundleSpaceIso φ φ' ψ hψ0).hom.base u) :=
    VectorBundle.dimension_comap_algEquiv (bundleEquiv φ φ' ψ hψ0) dimE dimE' u
  change (if dimE ((bundleSpaceIso φ φ' ψ hψ0).hom.base u) = d then
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ)
        (coneDimension φ dimE) dimE (ResolvedCone.scheme φ).fundamentalCycle
        ((bundleSpaceIso φ φ' ψ hψ0).hom.base u) else 0) =
    if dimE' u = d then
      _root_.AlgebraicGeometry.AlgebraicCycle.map (ResolvedCone.toBundle φ')
        (coneDimension φ' dimE') dimE' (ResolvedCone.scheme φ').fundamentalCycle u else 0
  rw [hdim, hval]

/-- **The two resolved-cone classes correspond under the induced isomorphism of Chow groups.** -/
theorem chowEquivOfAlgEquiv_resolvedConeClassAt {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ))) :
    VectorBundle.chowEquivOfAlgEquiv (bundleEquiv φ φ' ψ hψ0) RE RE'
        (resolvedConeClassAt φ dimE i RE) = resolvedConeClassAt φ' dimE' i RE' := by
  change RE'.quotientMap (cyclesOfDimension.flatPullbackOpen
    (bundleSpaceIso φ φ' ψ hψ0).hom
    (VectorBundle.dimension_comap_algEquiv (bundleEquiv φ φ' ψ hψ0) dimE dimE')
    (resolvedConeCycleAt φ dimE (i + (Nat.card ι : ℤ)))) = _
  rw [flatPullbackOpen_resolvedConeCycleAt φ φ' ψ hψ0 hψ1 hcomp]
  rfl

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
  [IsNoetherianRing R] in
/-- The trivialisation of `E'₁` transported from a trivialisation of `E₁`.  Using it keeps the
index type, and hence the degree shift, unchanged. -/
noncomputable def trivializationTransport {ι : Type u} (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I)) :
    ResolvedCone.bundleRing φ' ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I) :=
  (bundleEquiv φ φ' ψ hψ0).symm.trans e

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
  [IsNoetherianRing R] in
/-- **Homogeneity of principal divisors transports along the isomorphism of bundles.** -/
theorem principalDivisorsHomogeneous_transport (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero)
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ'))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ') dimE' :=
  VectorBundle.principalDivisorsHomogeneous_of_isIso (bundleSpaceIso φ φ' ψ hψ0) dimE' dimE hhom

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero] in
/-- The flat pullback along the second bundle is the flat pullback along the first followed by
the isomorphism of Chow groups. -/
theorem chowPullbackBundle_transport {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ))) (α : RX.ChowGroup) :
    VectorBundle.chowPullbackBundle (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE'
        α =
      VectorBundle.chowEquivOfAlgEquiv (bundleEquiv φ φ' ψ hψ0) RE RE'
        (VectorBundle.chowPullbackBundle e dimX dimE i RX RE α) :=
  (congrArg (fun f : RX.ChowGroup →ₗ[ℚ] RE'.ChowGroup => f α)
    (VectorBundle.chowEquivOfAlgEquiv_comp_chowPullbackBundle (bundleEquiv φ φ' ψ hψ0) e
      (trivializationTransport φ φ' ψ hψ0 e) dimX dimE dimE' i RX RE RE')).symm

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero] in
/-- **Injectivity of the flat pullback transports along the isomorphism of bundles.** -/
theorem injective_chowPullbackBundle_transport {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ)))
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    Function.Injective (VectorBundle.chowPullbackBundle
      (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE') := by
  intro a b hab
  rw [chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE',
    chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE'] at hab
  exact hinj ((VectorBundle.chowEquivOfAlgEquiv (bundleEquiv φ φ' ψ hψ0) RE RE').injective hab)

/-- **Behrend–Fantechi, Proposition 5.3 (isomorphism invariance).**  Two obstruction theories
`φ : E ⟶ L` and `φ' : E' ⟶ L` related by an isomorphism `ψ : E ⟶ E'` of two-term complexes with
`φ' ∘ ψ = φ` in degree `-1` have the same virtual fundamental class.

The trivialisation of `E'₁` is the one transported from the trivialisation `e` of `E₁`, so that
both classes live in the same Chow group `RX.ChowGroup`; the homogeneity and injectivity
hypotheses for `φ'` are the transports of those for `φ`
(`principalDivisorsHomogeneous_transport`, `injective_chowPullbackBundle_transport`). -/
theorem virtualClassAt_congr {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (VectorBundle.chowPullbackBundle e dimX dimE i RX RE)) :
    virtualClassAt φ e dimX dimE i RX RE hhom hinj =
      virtualClassAt φ' (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE'
        (principalDivisorsHomogeneous_transport φ φ' ψ hψ0 dimE dimE' hhom)
        (injective_chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE'
          hinj) := by
  apply eq_virtualClassAt_of_pullback_eq
  rw [chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE',
    chowPullbackBundle_virtualClassAt,
    chowEquivOfAlgEquiv_resolvedConeClassAt φ φ' ψ hψ0 hψ1 hcomp dimE dimE' i RE RE']


omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
  [IsNoetherianRing R] in
/-- The two bundles `E₁` and `E'₁` have the same rank. -/
theorem finrank_degreeZero_congr (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) :
    Module.finrank (R ⧸ I) E.degreeZero = Module.finrank (R ⧸ I) E'.degreeZero :=
  (zeroEquiv ψ hψ0).finrank_eq

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
  [IsNoetherianRing R] in
/-- The two complexes have the same rank in degree zero. -/
theorem finrank_degreeOne_congr (ψ : LinearTwoTermComplex.Hom E E')
    (hψ1 : Function.Bijective ψ.degreeOne) :
    Module.finrank (R ⧸ I) E.degreeOne = Module.finrank (R ⧸ I) E'.degreeOne :=
  (oneEquiv ψ hψ1).finrank_eq

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero]
  [IsNoetherianRing R] in
/-- **Isomorphic obstruction theories have the same virtual dimension.** -/
theorem virtualDimension_congr (ψ : LinearTwoTermComplex.Hom E E')
    (hψ0 : Function.Bijective ψ.degreeZero) (hψ1 : Function.Bijective ψ.degreeOne) :
    virtualDimension φ = virtualDimension φ' := by
  rw [virtualDimension, virtualDimension, finrank_degreeZero_congr ψ hψ0,
    finrank_degreeOne_congr ψ hψ1]

/-- **A class is a virtual class for `φ` if and only if it is one for `φ'`.**  This is the form
of Behrend–Fantechi, Proposition 5.3 which needs no injectivity hypothesis at all. -/
theorem chowPullbackBundle_eq_resolvedConeClassAt_iff {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ))) (α : RX.ChowGroup) :
    VectorBundle.chowPullbackBundle e dimX dimE i RX RE α = resolvedConeClassAt φ dimE i RE ↔
      VectorBundle.chowPullbackBundle (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE'
        α = resolvedConeClassAt φ' dimE' i RE' := by
  rw [chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE',
    ← chowEquivOfAlgEquiv_resolvedConeClassAt φ φ' ψ hψ0 hψ1 hcomp dimE dimE' i RE RE']
  exact ⟨fun h => by rw [h], fun h =>
    (VectorBundle.chowEquivOfAlgEquiv (bundleEquiv φ φ' ψ hψ0) RE RE').injective h⟩

omit [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  [Module.Free (R ⧸ I) E'.degreeZero] [Module.Finite (R ⧸ I) E'.degreeZero] in
/-- **The kernels of the two flat pullbacks coincide**, so the two canonical virtual classes
live in the same quotient. -/
theorem ker_chowPullbackBundle_transport {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ))) :
    LinearMap.ker (VectorBundle.chowPullbackBundle (trivializationTransport φ φ' ψ hψ0 e)
        dimX dimE' i RX RE') =
      LinearMap.ker (VectorBundle.chowPullbackBundle e dimX dimE i RX RE) := by
  apply Submodule.ext
  intro α
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE']
  exact ⟨fun h =>
      (VectorBundle.chowEquivOfAlgEquiv (bundleEquiv φ φ' ψ hψ0) RE RE').injective
        (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

/-- **The canonical virtual classes of two isomorphic obstruction theories agree**, under the
canonical identification of the two quotients given by `ker_chowPullbackBundle_transport`.  This
statement carries no injectivity hypothesis. -/
theorem virtualClassQuotAt_congr {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    Submodule.quotEquivOfEq _ _
        (ker_chowPullbackBundle_transport φ φ' ψ hψ0 e dimX dimE dimE' i RX RE RE')
        (virtualClassQuotAt φ' (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE'
          (principalDivisorsHomogeneous_transport φ φ' ψ hψ0 dimE dimE' hhom)) =
      virtualClassQuotAt φ e dimX dimE i RX RE hhom := by
  obtain ⟨α, hα⟩ := exists_virtualClassAt φ e dimX dimE i RX RE hhom
  rw [virtualClassQuotAt_eq_mk φ e dimX dimE i RX RE hhom α hα,
    virtualClassQuotAt_eq_mk φ' (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX RE' _ α
      ((chowPullbackBundle_eq_resolvedConeClassAt_iff φ φ' ψ hψ0 hψ1 hcomp e dimX dimE dimE' i
        RX RE RE' α).mp hα),
    Submodule.quotEquivOfEq_mk]


/-- **A common virtual class for two isomorphic obstruction theories**, with no injectivity
hypothesis: one and the same class on the base pulls back to the resolved-cone class of `φ` and
to the resolved-cone class of `φ'`. -/
theorem exists_virtualClassAt_congr {ι : Type u} [Finite ι]
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (e : ResolvedCone.bundleRing φ ≃ₐ[R ⧸ I] MvPolynomial ι (R ⧸ I))
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ')) (i : ℤ)
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX i)
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (i + (Nat.card ι : ℤ)))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (i + (Nat.card ι : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE) :
    ∃ α : RX.ChowGroup,
      VectorBundle.chowPullbackBundle e dimX dimE i RX RE α = resolvedConeClassAt φ dimE i RE ∧
        VectorBundle.chowPullbackBundle (trivializationTransport φ φ' ψ hψ0 e) dimX dimE' i RX
          RE' α = resolvedConeClassAt φ' dimE' i RE' := by
  obtain ⟨α, hα⟩ := exists_virtualClassAt φ e dimX dimE i RX RE hhom
  exact ⟨α, hα, (chowPullbackBundle_eq_resolvedConeClassAt_iff φ φ' ψ hψ0 hψ1 hcomp e dimX dimE
    dimE' i RX RE RE' α).mp hα⟩

/-- **Behrend–Fantechi, Proposition 5.3, for the virtual class of
`VirtualFundamentalClass/Construction.lean`.**  The virtual class built from the canonical
trivialisation of `E₁` equals the virtual class of the isomorphic obstruction theory `φ'`
computed in the transported trivialisation of `E'₁`. -/
theorem virtualClass_eq_virtualClassAt
    (ψ : LinearTwoTermComplex.Hom E E') (hψ0 : Function.Bijective ψ.degreeZero)
    (hψ1 : Function.Bijective ψ.degreeOne)
    (hcomp : φ'.degreeZero.comp ψ.degreeZero = φ.degreeZero)
    (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
    (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
    (dimE' : DimensionFunction (ResolvedCone.bundleSpace φ'))
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (virtualDimension φ))
    (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))
    (RE' : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ') dimE'
      (virtualDimension φ + (bundleRank φ : ℤ)))
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj =
      virtualClassAt φ' (trivializationTransport φ φ' ψ hψ0 (trivialization φ)) dimX dimE'
        (virtualDimension φ) RX RE'
        (principalDivisorsHomogeneous_transport φ φ' ψ hψ0 dimE dimE' hhom)
        (injective_chowPullbackBundle_transport φ φ' ψ hψ0 (trivialization φ) dimX dimE dimE'
          (virtualDimension φ) RX RE RE' hinj) := by
  rw [← virtualClassAt_trivialization φ dimX dimE RX RE hhom hinj]
  exact virtualClassAt_congr φ φ' ψ hψ0 hψ1 hcomp (trivialization φ) dimX dimE dimE'
    (virtualDimension φ) RX RE RE' hhom hinj

end Independence


/-! ## Acyclic summands

Adding an acyclic direct summand `[F --id--> F]` to a two-term complex `E` does not change the
obstruction theory in any essential way.  Below `E' = E ⊕ [F = F]` and `φ' = φ ⊕ 0`.
-/

section Acyclic

/-- The acyclic two-term complex `[F --id--> F]`. -/
abbrev acyclicComplex (S : Type u) [CommRing S] (F : Type u) [AddCommGroup F] [Module S F] :
    LinearTwoTermComplex S where
  degreeZero := F
  degreeOne := F
  differential := LinearMap.id

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))
variable (F : Type u) [AddCommGroup F] [Module (R ⧸ I) F]

/-- **Adding an acyclic summand to an obstruction theory**: the chain map
`E ⊕ [F = F] ⟶ L` which is `φ` on `E` and zero on the acyclic summand. -/
noncomputable def sumAcyclic :
    LinearTwoTermComplex.Hom (E.sum (acyclicComplex (R ⧸ I) F)) (conormalComplex k R I) where
  degreeZero := LinearMap.coprod φ.degreeZero 0
  degreeOne := LinearMap.coprod φ.degreeOne 0
  comm x := by
    change φ.degreeOne (E.differential x.1) + (0 : _) =
      (conormalComplex k R I).differential (φ.degreeZero x.1 + 0)
    rw [add_zero, add_zero, φ.comm x.1]

@[simp]
theorem sumAcyclic_degreeZero (x : E.degreeZero × F) :
    (sumAcyclic φ F).degreeZero x = φ.degreeZero x.1 := by
  change φ.degreeZero x.1 + (0 : _) = _
  rw [add_zero]

@[simp]
theorem sumAcyclic_degreeOne (y : E.degreeOne × F) :
    (sumAcyclic φ F).degreeOne y = φ.degreeOne y.1 := by
  change φ.degreeOne y.1 + (0 : _) = _
  rw [add_zero]

/-- **Adding an acyclic summand preserves obstruction theories.** -/
theorem isObstructionTheory_sumAcyclic
    (h : PicardCriteria.IsObstructionTheory φ) :
    PicardCriteria.IsObstructionTheory (sumAcyclic φ F) := by
  obtain ⟨hsurj, hexact⟩ := PicardCriteria.isObstructionTheory_iff_exact_cone φ |>.1 h
  refine PicardCriteria.isObstructionTheory_iff_exact_cone (sumAcyclic φ F) |>.2 ⟨?_, ?_⟩
  · intro b
    obtain ⟨⟨a, n⟩, hn⟩ := hsurj b
    exact ⟨(a, (n, 0)), by
      change (conormalComplex k R I).differential a + (sumAcyclic φ F).degreeOne (n, 0) = b
      rw [sumAcyclic_degreeOne]
      exact hn⟩
  · rintro ⟨a, n, f⟩
    have hb : PicardCriteria.coneBeta (sumAcyclic φ F) (a, (n, f)) =
        PicardCriteria.coneBeta φ (a, n) := by
      change (conormalComplex k R I).differential a + (sumAcyclic φ F).degreeOne (n, f) =
        (conormalComplex k R I).differential a + φ.degreeOne n
      rw [sumAcyclic_degreeOne]
    rw [hb]
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := (hexact (a, n)).1 hz
      refine ⟨(x, -f), ?_⟩
      have h1 : φ.degreeZero x = a := congrArg Prod.fst hx
      have h2 : -E.differential x = n := congrArg Prod.snd hx
      change ((sumAcyclic φ F).degreeZero (x, -f),
        -(E.sum (acyclicComplex (R ⧸ I) F)).differential (x, -f)) = (a, (n, f))
      rw [sumAcyclic_degreeZero, h1]
      change (a, (-E.differential x, - -f)) = (a, (n, f))
      rw [h2, neg_neg]
    · rintro ⟨⟨x, g⟩, hx⟩
      have h1 : PicardCriteria.coneAlpha φ x = (a, n) := by
        have ha : (sumAcyclic φ F).degreeZero (x, g) = a := congrArg Prod.fst hx
        have hn : -(E.sum (acyclicComplex (R ⧸ I) F)).differential (x, g) = (n, f) :=
          congrArg Prod.snd hx
        rw [sumAcyclic_degreeZero] at ha
        change (φ.degreeZero x, -E.differential x) = (a, n)
        rw [ha]
        exact congrArg (fun z => (a, z)) (congrArg Prod.fst hn)
      exact (hexact (a, n)).2 ⟨x, h1⟩

/-! ### The resolved cone of a complex with an acyclic summand -/

/-- The coordinate-ring map of the bundle projection `p : E'₁ = E₁ ×_X F^∨ ⟶ E₁`. -/
noncomputable def bundleInl :
    ResolvedCone.bundleRing φ →ₐ[R ⧸ I] ResolvedCone.bundleRing (sumAcyclic φ F) :=
  symAlgHom (LinearMap.inl (R ⧸ I) E.degreeZero F)

@[simp]
theorem bundleInl_ι (x : E.degreeZero) :
    bundleInl φ F (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x) =
      SymmetricAlgebra.ι (R ⧸ I) (E.degreeZero × F) (x, 0) :=
  symAlgHom_ι _ x

/-- The corresponding map of the coordinate rings of `C ×_X E₀`. -/
noncomputable def productInl :
    ResolvedCone.productRing φ →ₐ[R ⧸ I] ResolvedCone.productRing (sumAcyclic φ F) :=
  Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (AffineNormalCone.associatedGradedRing R I))
    (symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F))

/-- The retraction of `productInl` coming from the first projection. -/
noncomputable def productFst :
    ResolvedCone.productRing (sumAcyclic φ F) →ₐ[R ⧸ I] ResolvedCone.productRing φ :=
  Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (AffineNormalCone.associatedGradedRing R I))
    (symAlgHom (LinearMap.fst (R ⧸ I) E.degreeOne F))

theorem productFst_productInl (z : ResolvedCone.productRing φ) :
    productFst φ F (productInl φ F z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
      change (AlgHom.id (R ⧸ I) _ (AlgHom.id (R ⧸ I) _ c)) ⊗ₜ[R ⧸ I]
        (symAlgHom (LinearMap.fst (R ⧸ I) E.degreeOne F)
          (symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F) b)) = c ⊗ₜ[R ⧸ I] b
      have hb : symAlgHom (LinearMap.fst (R ⧸ I) E.degreeOne F)
          (symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F) b) = b := by
        have hcomp : (symAlgHom (LinearMap.fst (R ⧸ I) E.degreeOne F)).comp
            (symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F)) =
            AlgHom.id (R ⧸ I) (SymmetricAlgebra (R ⧸ I) E.degreeOne) := by
          apply SymmetricAlgebra.algHom_ext
          apply LinearMap.ext
          intro y
          change symAlgHom (LinearMap.fst (R ⧸ I) E.degreeOne F)
            (symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F)
              (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne y)) = _
          rw [symAlgHom_ι, symAlgHom_ι]
          rfl
        exact congrArg (fun g : SymmetricAlgebra (R ⧸ I) E.degreeOne →ₐ[R ⧸ I]
          SymmetricAlgebra (R ⧸ I) E.degreeOne => g b) hcomp
      rw [hb]
      rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The map of coordinate rings of `C ×_X E₀ ⟶ C ×_X E'₀` is injective. -/
theorem productInl_injective : Function.Injective (productInl φ F) :=
  Function.LeftInverse.injective (productFst_productInl φ F)

/-- **The coordinate-ring square of the bundle projection.** -/
theorem productInl_comp_productMap :
    (productInl φ F).comp (ResolvedCone.productMap φ) =
      (ResolvedCone.productMap (sumAcyclic φ F)).comp (bundleInl φ F) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change productInl φ F (ResolvedCone.productMap φ
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x)) =
    ResolvedCone.productMap (sumAcyclic φ F) (bundleInl φ F
      (SymmetricAlgebra.ι (R ⧸ I) E.degreeZero x))
  rw [ResolvedCone.productMap_ι, bundleInl_ι, ResolvedCone.productMap_ι, sumAcyclic_degreeZero,
    map_add]
  change AffineNormalCone.conormalToAssociatedGraded R I (φ.degreeZero x) ⊗ₜ[R ⧸ I]
      symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F) 1 +
      (1 : AffineNormalCone.associatedGradedRing R I) ⊗ₜ[R ⧸ I]
        symAlgHom (LinearMap.inl (R ⧸ I) E.degreeOne F)
          (SymmetricAlgebra.ι (R ⧸ I) E.degreeOne (E.differential x)) = _
  rw [map_one, symAlgHom_ι]
  rfl

/-- **A point of `E₁` lies in `C(E)` if and only if the corresponding point of `E'₁` lies in
`C(E')`**, at the level of the defining ideals. -/
theorem mem_ideal_sumAcyclic_iff (a : ResolvedCone.bundleRing φ) :
    a ∈ ResolvedCone.ideal φ ↔ bundleInl φ F a ∈ ResolvedCone.ideal (sumAcyclic φ F) := by
  have hsq : productInl φ F (ResolvedCone.productMap φ a) =
      ResolvedCone.productMap (sumAcyclic φ F) (bundleInl φ F a) :=
    congrArg
      (fun g : ResolvedCone.bundleRing φ →ₐ[R ⧸ I]
        ResolvedCone.productRing (sumAcyclic φ F) => g a)
      (productInl_comp_productMap φ F)
  rw [ResolvedCone.mem_ideal_iff, ResolvedCone.mem_ideal_iff]
  change ResolvedCone.productMap φ a = 0 ↔
    ResolvedCone.productMap (sumAcyclic φ F) (bundleInl φ F a) = 0
  rw [← hsq]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => productInl_injective φ F (by rw [h, map_zero])⟩

/-- **`C(E)` is the scheme-theoretic image of `C(E')` under the bundle projection
`p : E'₁ ⟶ E₁`**: the ideal of `C(E)` is the contraction of the ideal of `C(E')`. -/
theorem comap_ideal_sumAcyclic :
    Ideal.comap (bundleInl φ F).toRingHom (ResolvedCone.ideal (sumAcyclic φ F)) =
      ResolvedCone.ideal φ :=
  Ideal.ext fun a => (mem_ideal_sumAcyclic_iff φ F a).symm

/-- **`C(E') ⊆ p⁻¹(C(E))`**: the extension of the ideal of `C(E)` is contained in the ideal of
`C(E')`.  (The reverse inclusion, that is the equality `C(E') = p⁻¹(C(E))`, would need the
flatness of `Sym(E⁻¹ ⊕ F)` over `Sym(E⁻¹)`, which is not developed here.) -/
theorem map_ideal_le_ideal_sumAcyclic :
    Ideal.map (bundleInl φ F).toRingHom (ResolvedCone.ideal φ) ≤
      ResolvedCone.ideal (sumAcyclic φ F) := by
  rw [Ideal.map_le_iff_le_comap, comap_ideal_sumAcyclic]

/-- **Adding an acyclic summand does not change the virtual dimension.** -/
theorem virtualDimension_sumAcyclic [Nontrivial (R ⧸ I)]
    [Module.Free (R ⧸ I) F] [Module.Finite (R ⧸ I) F]
    [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
    [Module.Free (R ⧸ I) E.degreeOne] [Module.Finite (R ⧸ I) E.degreeOne] :
    virtualDimension (sumAcyclic φ F) = virtualDimension φ := by
  change ((Module.finrank (R ⧸ I) (E.degreeOne × F) : ℤ) -
    (Module.finrank (R ⧸ I) (E.degreeZero × F) : ℤ)) = _
  rw [Module.finrank_prod, Module.finrank_prod]
  push_cast
  ring

end Acyclic

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.VirtualClass
