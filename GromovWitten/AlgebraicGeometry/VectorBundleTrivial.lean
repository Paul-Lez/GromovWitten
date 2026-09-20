/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension

/-!
# The trivial vector bundle over a scheme, and globally trivialised bundles

This file constructs the *trivial* vector bundle `X × 𝔸^ι` over an arbitrary scheme `X`, in the
form of the datum `BundleData X ι` of `VectorBundleTotalSpace.lean`, and develops the objects
needed to run the round-15 affine injectivity argument for `π^*` globally: global
trivialisations of an abstract bundle, and the constant sections of the trivial bundle attached
to constants in a base field.

## Main declarations

* `trivialAlgebraData X ι` — the quasi-coherent algebra `U ↦ MvPolynomial ι Γ(X, U)` with the
  transition maps `MvPolynomial.map (res X h)`; the pushout condition is
  `MvPolynomial.algebraTensorAlgEquiv`;
* `trivialData X ι : BundleData X ι` — the trivial bundle, with charts indexed by *all* affine
  opens of `X` and the identity trivialisations; `trivialData_chartι` identifies its charts with
  the affine pieces of the relative `Spec`, and `trivialData_bundlePoint` computes the generic
  points of its fibres;
* `GlobalTrivialisation 𝓔` — a compatible family of trivialisations of `𝓔 : BundleData X ι` over
  *every* affine open; `GlobalTrivialisation.totalSpaceIso` is the induced isomorphism
  `𝓔.totalSpace ≅ (trivialData X ι).totalSpace` over `X`, which matches the generic fibre points
  (`GlobalTrivialisation.totalSpaceIso_bundlePoint`) and the flat pullbacks
  (`GlobalTrivialisation.pullbackOpen_totalSpaceIso_pullbackBundle`);
* `totalRationalRelations_map_pullbackOpenLinear` — the span of principal divisors transports
  along an isomorphism of schemes;
* `sectionHom f ι c`, `sectionMap f ι c` — the constant section of the trivial bundle attached to a
  family `c : ι → k` of constants of a base field `k`, for `f : X ⟶ Spec k`; it is a section of
  the projection (`sectionMap_proj`), a closed immersion, and over an affine chart it is the
  `Spec` of the evaluation map `MvPolynomial ι Γ(X, U) → Γ(X, U)` at the constants
  (`sectionMap_chart`);
* `renameHom`, `forget` — for `ι = Option ι'`, the morphism
  `X × 𝔸^{Option ι'} ⟶ X × 𝔸^{ι'}` forgetting the last coordinate, together with its chart
  description `forget_affineι` and the compatibility `forget_bundlePoint` of the generic fibre
  points.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace

open GlobalBlowup RelativeSpec IntersectionTheory

universe u

noncomputable section

/-! ### The trivial quasi-coherent algebra `U ↦ MvPolynomial ι Γ(X, U)` -/

section TrivialData

variable (X : Scheme.{u}) (ι : Type u)

/-- Extending the coefficients of a polynomial algebra is a base change: the square of ring maps
`A → MvPolynomial ι A`, `A → B`, `MvPolynomial ι A → MvPolynomial ι B`, `B → MvPolynomial ι B`
is a pushout. -/
theorem isPushout_mvPolynomialMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (MvPolynomial ι A))) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (MvPolynomial.map f))
      (CommRingCat.ofHom (algebraMap B (MvPolynomial ι B))) := by
  let _ := f.toAlgebra
  refine isPushout_of_algEquiv _ (MvPolynomial.algebraTensorAlgEquiv (σ := ι) A B) fun p ↦ ?_
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rfl

/-- Evaluation at the origin commutes with extension of the coefficients. -/
theorem aeval_zero_mvPolynomialMap {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : MvPolynomial ι A) :
    MvPolynomial.aeval (fun _ ↦ (0 : B)) (MvPolynomial.map f p) =
      f (MvPolynomial.aeval (fun _ ↦ (0 : A)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp
  | mul_X p n hp => simp

/-- The quasi-coherent algebra of functions on the trivial bundle `X × 𝔸^ι`: over an affine open
`U` it is the polynomial algebra `MvPolynomial ι Γ(X, U)`, and the transition maps are the
restriction maps applied to the coefficients. -/
def trivialAlgebraData : AlgebraData X where
  ring U := MvPolynomial ι Γ(X, U.1)
  map h := MvPolynomial.map (res X h)
  map_id U := by
    rw [res_refl]
    exact RingHom.ext MvPolynomial.map_id
  map_comp h₁ h₂ := by
    rw [res_comp X h₁ h₂]
    exact RingHom.ext fun p ↦ (MvPolynomial.map_map (σ := ι) (res X h₂) (res X h₁) p).symm
  isPushout h := isPushout_mvPolynomialMap ι (res X h)

@[simp]
theorem trivialAlgebraData_ring (U : X.affineOpens) :
    (trivialAlgebraData X ι).ring U = MvPolynomial ι Γ(X, U.1) := rfl

@[simp]
theorem trivialAlgebraData_map {U V : X.affineOpens} (h : U ≤ V)
    (p : MvPolynomial ι Γ(X, V.1)) :
    (trivialAlgebraData X ι).map h p = MvPolynomial.map (res X h) p := rfl

/-- The augmentation of the trivial bundle: evaluation at the origin. -/
def trivialAug : RelativeSpec.Hom X (structureData X) (trivialAlgebraData X ι) where
  app U := MvPolynomial.aeval fun _ ↦ (0 : Γ(X, U.1))
  naturality h := RingHom.ext fun p ↦ aeval_zero_mvPolynomialMap ι (res X h) p

@[simp]
theorem trivialAug_app (U : X.affineOpens) (p : MvPolynomial ι Γ(X, U.1)) :
    (trivialAug X ι).app U p = MvPolynomial.aeval (fun _ ↦ (0 : Γ(X, U.1))) p := rfl

/-- **The trivial vector bundle `X × 𝔸^ι`** over an arbitrary scheme `X`: the relative `Spec` of
the polynomial algebra `U ↦ MvPolynomial ι Γ(X, U)`, trivialised by the identity over every
affine open of `X`.  It is an `abbrev` so that its chart index type `X.affineOpens` is
transparent to the elaborator. -/
abbrev trivialData : BundleData X ι where
  algebra := trivialAlgebraData X ι
  augmentation := trivialAug X ι
  J := X.affineOpens
  chart := id
  iSup_chart := iSup_affineOpens_eq_top X
  triv _ := AlgEquiv.refl
  augmentation_triv _ _ := rfl

@[simp]
theorem trivialData_chart (U : X.affineOpens) : (trivialData X ι).chart U = U := rfl

@[simp]
theorem trivialData_algebra : (trivialData X ι).algebra = trivialAlgebraData X ι := rfl

/-- The trivialising charts of the trivial bundle are exactly the affine pieces of its relative
`Spec`: the trivialisations are the identity. -/
theorem trivialData_chartι (U : X.affineOpens) :
    (trivialData X ι).chartι U = affineι X (trivialAlgebraData X ι) U := by
  have h : CommRingCat.ofHom
      ((AlgEquiv.refl : MvPolynomial ι Γ(X, U.1) ≃ₐ[Γ(X, U.1)] _)).toRingHom =
      𝟙 (CommRingCat.of (MvPolynomial ι Γ(X, U.1))) := rfl
  change ((trivialData X ι).chartIso U).inv ≫ affineι X (trivialAlgebraData X ι) U = _
  rw [BundleData.chartIso_inv]
  change Spec.map (CommRingCat.ofHom
    ((AlgEquiv.refl : MvPolynomial ι Γ(X, U.1) ≃ₐ[Γ(X, U.1)] _)).toRingHom) ≫ _ = _
  rw [h, Spec.map_id]
  exact Category.id_comp _

/-- The generic point of the fibre of the trivial bundle over a point of an affine open, computed
in the corresponding chart. -/
theorem trivialData_bundlePoint (U : X.affineOpens) (x : U.1.toScheme) :
    BundlePullbackGlobal.bundlePoint (trivialData X ι) (U.1.ι.base x) =
      (affineι X (trivialAlgebraData X ι) U).base
        (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, U.1)))
          ((isAffineOpen X U).isoSpec.hom.base x)) :=
  (BundlePullbackGlobal.bundlePoint_chart (trivialData X ι) U x).trans (congrArg
    (fun f : Spec (CommRingCat.of (MvPolynomial ι Γ(X, U.1))) ⟶ (trivialData X ι).totalSpace ↦
      f.base (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, U.1)))
        ((isAffineOpen X U).isoSpec.hom.base x)))
    (trivialData_chartι X ι U))

end TrivialData

/-! ### Generic points of the fibres of an arbitrary bundle -/

section BundlePoint

variable {X : Scheme.{u}} {ι : Type u}

/-- The generic point of the fibre over `x` specialises to every point of the total space lying
over `x`. -/
theorem bundlePoint_specializes (𝓑 : BundleData X ι) (x : X) (q : 𝓑.totalSpace)
    (hq : 𝓑.proj.base q = x) : BundlePullbackGlobal.bundlePoint 𝓑 x ⤳ q := by
  have hx : x ∈ (𝓑.chart (BundlePullbackGlobal.chartIndex 𝓑 x)).1 :=
    BundlePullbackGlobal.mem_chart_chartIndex 𝓑 x
  have hmem : 𝓑.proj.base q ∈ (𝓑.chart (BundlePullbackGlobal.chartIndex 𝓑 x)).1 := by
    rw [hq]; exact hx
  refine (BundlePullbackGlobal.chartBundlePoint_specializes_iff 𝓑
    (BundlePullbackGlobal.chartIndex 𝓑 x) ⟨x, hx⟩ q hmem).mpr ?_
  rw [hq]
  exact specializes_rfl

/-- Two bundles over the same base with an isomorphism of total spaces over `X` have matching
generic fibre points: both are the unique maximal point of the fibre. -/
theorem bundlePoint_map_of_isIso {𝓑 𝓒 : BundleData X ι} (φ : 𝓑.totalSpace ≅ 𝓒.totalSpace)
    (hφ : φ.hom ≫ 𝓒.proj = 𝓑.proj) (x : X) :
    φ.hom.base (BundlePullbackGlobal.bundlePoint 𝓑 x) =
      BundlePullbackGlobal.bundlePoint 𝓒 x := by
  have hφ' : φ.inv ≫ 𝓑.proj = 𝓒.proj := by
    rw [← hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hproj : ∀ q : 𝓑.totalSpace, 𝓒.proj.base (φ.hom.base q) = 𝓑.proj.base q := fun q ↦
    congrArg (fun g : 𝓑.totalSpace ⟶ X ↦ g.base q) hφ
  have hproj' : ∀ q : 𝓒.totalSpace, 𝓑.proj.base (φ.inv.base q) = 𝓒.proj.base q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ X ↦ g.base q) hφ'
  have hinv : ∀ q : 𝓒.totalSpace, φ.hom.base (φ.inv.base q) = q := fun q ↦
    congrArg (fun g : 𝓒.totalSpace ⟶ 𝓒.totalSpace ↦ g.base q) φ.inv_hom_id
  have h₁ : φ.hom.base (BundlePullbackGlobal.bundlePoint 𝓑 x) ⤳
      BundlePullbackGlobal.bundlePoint 𝓒 x := by
    have hspec : BundlePullbackGlobal.bundlePoint 𝓑 x ⤳
        φ.inv.base (BundlePullbackGlobal.bundlePoint 𝓒 x) :=
      bundlePoint_specializes 𝓑 x _ (by
        rw [hproj', BundlePullbackGlobal.proj_bundlePoint])
    have := hspec.map φ.hom.continuous
    rwa [hinv] at this
  have h₂ : BundlePullbackGlobal.bundlePoint 𝓒 x ⤳
      φ.hom.base (BundlePullbackGlobal.bundlePoint 𝓑 x) :=
    bundlePoint_specializes 𝓒 x _ (by
      rw [hproj, BundlePullbackGlobal.proj_bundlePoint])
  exact (h₁.antisymm h₂).eq

end BundlePoint

/-! ### Globally trivialised bundles -/

section GlobalTrivialisation

variable {X : Scheme.{u}} {ι : Type u}

/-- A **global trivialisation** of a bundle `𝓔 : BundleData X ι`: a trivialisation of its algebra
of functions over *every* affine open of `X`, compatible with the transition maps.  Such a datum
exhibits the total space of `𝓔` as the trivial bundle `X × 𝔸^ι`. -/
structure GlobalTrivialisation (𝓔 : BundleData X ι) where
  /-- The trivialisation over an affine open. -/
  e : ∀ U : X.affineOpens, 𝓔.algebra.ring U ≃ₐ[Γ(X, U.1)] MvPolynomial ι Γ(X, U.1)
  /-- The trivialisations are compatible with the transition maps. -/
  e_map : ∀ {U V : X.affineOpens} (h : U ≤ V) (a : 𝓔.algebra.ring V),
    e U (𝓔.algebra.map h a) = MvPolynomial.map (res X h) (e V a)

namespace GlobalTrivialisation

/-- The identity global trivialisation of the trivial bundle. -/
def trivial (X : Scheme.{u}) (ι : Type u) : GlobalTrivialisation (trivialData X ι) where
  e _ := AlgEquiv.refl
  e_map _ _ := rfl

variable {𝓔 : BundleData X ι} (t : GlobalTrivialisation 𝓔)

/-- The morphism of quasi-coherent algebras attached to a global trivialisation. -/
def toHom : RelativeSpec.Hom X (trivialAlgebraData X ι) 𝓔.algebra where
  app U := (t.e U).toAlgHom
  naturality h := RingHom.ext fun a ↦ t.e_map h a

instance isIso_toHom_map : IsIso t.toHom.map :=
  RelativeSpec.Hom.isIso_map _ fun U ↦ (t.e U).bijective

/-- **A globally trivialised bundle is the trivial bundle**: the isomorphism of total spaces
induced by a global trivialisation. -/
def totalSpaceIso : 𝓔.totalSpace ≅ (trivialData X ι).totalSpace := (asIso t.toHom.map).symm

theorem totalSpaceIso_inv : t.totalSpaceIso.inv = t.toHom.map := rfl

/-- The trivialisation isomorphism lies over `X`. -/
theorem totalSpaceIso_hom_proj : t.totalSpaceIso.hom ≫ (trivialData X ι).proj = 𝓔.proj := by
  have hmap : t.toHom.map ≫ 𝓔.proj = (trivialData X ι).proj :=
    RelativeSpec.Hom.map_toBase t.toHom
  have hi : t.totalSpaceIso.hom ≫ t.toHom.map = 𝟙 _ := (asIso t.toHom.map).inv_hom_id
  rw [← hmap, ← Category.assoc, hi, Category.id_comp]

/-- The trivialisation isomorphism matches the generic points of the fibres. -/
theorem totalSpaceIso_bundlePoint (x : X) :
    t.totalSpaceIso.hom.base (BundlePullbackGlobal.bundlePoint 𝓔 x) =
      BundlePullbackGlobal.bundlePoint (trivialData X ι) x :=
  bundlePoint_map_of_isIso t.totalSpaceIso t.totalSpaceIso_hom_proj x

theorem injective_totalSpaceIso_hom_base :
    Function.Injective t.totalSpaceIso.hom.base :=
  Function.LeftInverse.injective (g := t.totalSpaceIso.inv.base) fun q ↦
    congrArg (fun g : 𝓔.totalSpace ⟶ 𝓔.totalSpace ↦ g.base q) t.totalSpaceIso.hom_inv_id

/-- The trivialisation isomorphism matches the flat pullbacks of cycles. -/
theorem pullbackOpen_totalSpaceIso_pullbackBundle (w : IntersectionTheory.AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen t.totalSpaceIso.hom
        (BundlePullbackGlobal.pullbackBundle (trivialData X ι) w) =
      BundlePullbackGlobal.pullbackBundle 𝓔 w := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext q
  change BundlePullbackGlobal.pullbackBundle (trivialData X ι) w
    (t.totalSpaceIso.hom.base q) = BundlePullbackGlobal.pullbackBundle 𝓔 w q
  by_cases h : q ∈ Set.range (BundlePullbackGlobal.bundlePoint 𝓔)
  · obtain ⟨y, rfl⟩ := h
    rw [totalSpaceIso_bundlePoint, BundlePullbackGlobal.pullbackBundle_apply_bundlePoint,
      BundlePullbackGlobal.pullbackBundle_apply_bundlePoint]
  · have hne : t.totalSpaceIso.hom.base q ∉
        Set.range (BundlePullbackGlobal.bundlePoint (trivialData X ι)) := by
      rintro ⟨y, hy⟩
      exact h ⟨y, t.injective_totalSpaceIso_hom_base
        (by rw [totalSpaceIso_bundlePoint, hy])⟩
    rw [BundlePullbackGlobal.pullbackBundle_eq_zero_of_notMem _ _ hne,
      BundlePullbackGlobal.pullbackBundle_eq_zero_of_notMem _ _ h]

end GlobalTrivialisation

end GlobalTrivialisation

/-! ### Principal divisors along an isomorphism of schemes -/

section Relations

variable {A B : Scheme.{u}} (ε : A ≅ B) (dimA : DimensionFunction A) (dimB : DimensionFunction B)

/-- Along an isomorphism of schemes, residue-degree pushforward is the pullback of cycles along
the inverse. -/
theorem mapLinear_eq_pullbackOpenLinear_of_isIso :
    AlgebraicCycle.mapLinear ε.hom dimA dimB = AlgebraicCycle.pullbackOpenLinear ε.inv := by
  have hw : (dimA : A → ℤ) = fun a ↦ (dimB : B → ℤ) (ε.hom.base a) :=
    funext fun a ↦ DimensionFunction.apply_eq_of_isClosedImmersion dimA dimB ε.hom a
  refine LinearMap.ext fun z ↦ Function.locallyFinsuppWithin.coe_injective (funext fun y ↦ ?_)
  have hy : ε.hom.base (ε.inv.base y) = y :=
    congrArg (fun g : B ⟶ B ↦ g.base y) ε.inv_hom_id
  have key := AlgebraicCycle.map_closedImmersion_apply_image ε.hom (dimB : B → ℤ) z
    (ε.inv.base y)
  rw [hy] at key
  change _root_.AlgebraicGeometry.AlgebraicCycle.map ε.hom dimA dimB z y = z (ε.inv.base y)
  rw [hw]
  exact key

/-- Pulling a cycle back along an isomorphism and then along its inverse is the identity. -/
theorem pullbackOpen_hom_inv (z : IntersectionTheory.AlgebraicCycle A ℚ) :
    AlgebraicCycle.pullbackOpen ε.hom (AlgebraicCycle.pullbackOpen ε.inv z) = z := by
  refine Function.locallyFinsuppWithin.coe_injective (funext fun a ↦ ?_)
  have h : ε.inv.base (ε.hom.base a) = a := congrArg (fun g : A ⟶ A ↦ g.base a) ε.hom_inv_id
  change z (ε.inv.base (ε.hom.base a)) = z a
  rw [h]

/-- **The span of principal divisors is invariant under isomorphism.** -/
theorem totalRationalRelations_map_pullbackOpenLinear :
    Submodule.map (AlgebraicCycle.pullbackOpenLinear ε.hom)
        (totalRationalRelations B dimB) = totalRationalRelations A dimA := by
  have hle : ∀ {A' B' : Scheme.{u}} (ε' : A' ≅ B') (dimA' : DimensionFunction A')
      (dimB' : DimensionFunction B'),
      Submodule.map (AlgebraicCycle.pullbackOpenLinear ε'.inv)
        (totalRationalRelations A' dimA') ≤ totalRationalRelations B' dimB' := by
    intro A' B' ε' dimA' dimB'
    rw [← mapLinear_eq_pullbackOpenLinear_of_isIso ε' dimA' dimB']
    exact totalRationalRelations_map_closedImmersion ε'.hom dimA' dimB'
  refine le_antisymm (hle ε.symm dimB dimA) fun z hz ↦ ?_
  exact ⟨AlgebraicCycle.pullbackOpen ε.inv z, hle ε dimA dimB ⟨z, hz, rfl⟩,
    pullbackOpen_hom_inv ε z⟩

end Relations

namespace GlobalTrivialisation

variable {X : Scheme.{u}} {ι : Type u} {𝓔 : BundleData X ι} (t : GlobalTrivialisation 𝓔)

/-- The span of principal divisors of the total space is the span of principal divisors of the
trivial bundle, transported along the trivialisation. -/
theorem totalRationalRelations_totalSpaceIso
    (dimE : DimensionFunction 𝓔.totalSpace)
    (dimT : DimensionFunction (trivialData X ι).totalSpace) :
    Submodule.map (AlgebraicCycle.pullbackOpenLinear t.totalSpaceIso.hom)
        (totalRationalRelations (trivialData X ι).totalSpace dimT) =
      totalRationalRelations 𝓔.totalSpace dimE :=
  totalRationalRelations_map_pullbackOpenLinear t.totalSpaceIso dimE dimT

end GlobalTrivialisation

/-! ### Constant sections of the trivial bundle -/

section ConstantSection

open IntersectionTheory.FiniteTypeDimension

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (ι : Type u)
  (c : ι → k)

/-- Evaluation at a family of elements commutes with extension of the coefficients. -/
theorem aeval_mvPolynomialMap {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) (v : ι → A)
    (p : MvPolynomial ι A) :
    MvPolynomial.aeval (fun i ↦ g (v i)) (MvPolynomial.map g p) =
      g (MvPolynomial.aeval v p) := by
  have key : ((MvPolynomial.aeval (fun i ↦ g (v i)) : MvPolynomial ι B →ₐ[B] B).toRingHom.comp
        (MvPolynomial.map g)) =
      g.comp (MvPolynomial.aeval v : MvPolynomial ι A →ₐ[A] A).toRingHom :=
    MvPolynomial.ringHom_ext (fun a ↦ by simp) (fun i ↦ by simp)
  exact congrArg (fun φ : MvPolynomial ι A →+* B ↦ φ p) key

/-- The constants coming from the base field are compatible with the restriction maps of `X`. -/
theorem res_structureMap {U V : X.affineOpens} (h : U ≤ V) (a : k) :
    res X h (structureMap f V.1 a) = structureMap f U.1 a := by
  have key : f.appLE ⊤ V.1 (show V.1 ≤ f ⁻¹ᵁ ⊤ by simp) ≫
      X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op =
      f.appLE ⊤ U.1 (show U.1 ≤ f ⁻¹ᵁ ⊤ by simp) := Scheme.Hom.appLE_map f _ _
  have key2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        f.appLE ⊤ V.1 (show V.1 ≤ f ⁻¹ᵁ ⊤ by simp)) ≫
      X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        f.appLE ⊤ U.1 (show U.1 ≤ f ⁻¹ᵁ ⊤ by simp) := by
    rw [Category.assoc, key]
  exact congrArg (fun φ : CommRingCat.of k ⟶ Γ(X, U.1) ↦ φ.hom a) key2

/-- The morphism of quasi-coherent algebras given by evaluation of the coordinates at the
constants `c : ι → k` of the base field. -/
def sectionHom : RelativeSpec.Hom X (structureData X) (trivialAlgebraData X ι) where
  app U := MvPolynomial.aeval fun i ↦ structureMap f U.1 (c i)
  naturality {U V} h := RingHom.ext fun p ↦ by
    have hv : (fun i ↦ structureMap f U.1 (c i)) =
        fun i ↦ res X h (structureMap f V.1 (c i)) :=
      funext fun i ↦ (res_structureMap f h (c i)).symm
    change MvPolynomial.aeval (fun i ↦ structureMap f U.1 (c i))
        (MvPolynomial.map (res X h) p) =
      res X h (MvPolynomial.aeval (fun i ↦ structureMap f V.1 (c i)) p)
    rw [hv]
    exact aeval_mvPolynomialMap ι (res X h) (fun i ↦ structureMap f V.1 (c i)) p

@[simp]
theorem sectionHom_app (U : X.affineOpens) (p : MvPolynomial ι Γ(X, U.1)) :
    (sectionHom f ι c).app U p =
      MvPolynomial.aeval (fun i ↦ structureMap f U.1 (c i)) p := rfl

/-- **The constant section `σ_c : X → X × 𝔸^ι`** of the trivial bundle attached to a family
`c : ι → k` of constants of the base field. -/
def sectionMap : X ⟶ (trivialData X ι).totalSpace := (baseIso X).inv ≫ (sectionHom f ι c).map

/-- A constant section is a section of the projection. -/
theorem sectionMap_proj : sectionMap f ι c ≫ (trivialData X ι).proj = 𝟙 X := by
  rw [sectionMap, BundleData.proj, Category.assoc, RelativeSpec.Hom.map_toBase]
  exact (baseIso X).inv_hom_id

/-- The components of a constant section are surjective: they are retractions of the structure
maps of the trivial algebra. -/
theorem surjective_sectionHom_app (U : X.affineOpens) :
    Function.Surjective ((sectionHom f ι c).app U) := fun a ↦
  ⟨algebraMap Γ(X, U.1) (MvPolynomial ι Γ(X, U.1)) a, ((sectionHom f ι c).app U).commutes a⟩

instance isClosedImmersion_sectionMap : IsClosedImmersion (sectionMap f ι c) := by
  have h : IsClosedImmersion (sectionHom f ι c).map :=
    RelativeSpec.Hom.map_isClosedImmersion _ (surjective_sectionHom_app f ι c)
  change IsClosedImmersion ((baseIso X).inv ≫ (sectionHom f ι c).map)
  infer_instance

/- As in `VectorBundleTotalSpace.lean`, the index type of Mathlib's directed affine cover is
definitionally but not reducibly the type of affine opens, so the unifier is told not to respect
transparency in this proof. -/
set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `U`, the constant section is the spectrum of the evaluation map
`MvPolynomial ι Γ(X, U) → Γ(X, U)` at the constants. -/
theorem sectionMap_chart (U : X.affineOpens) :
    (isAffineOpen X U).isoSpec.inv ≫ U.1.ι ≫ sectionMap f ι c =
      Spec.map (CommRingCat.ofHom
          (MvPolynomial.aeval (R := Γ(X, U.1)) fun i ↦ structureMap f U.1 (c i)).toRingHom) ≫
        affineι X (trivialAlgebraData X ι) U := by
  have h₁ : (isAffineOpen X U).isoSpec.inv ≫ U.1.ι ≫ (baseIso X).inv =
      affineι X (structureData X) U := by
    rw [← Category.assoc, ← affineι_structureData_baseIso X U, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  calc (isAffineOpen X U).isoSpec.inv ≫ U.1.ι ≫ sectionMap f ι c
      = ((isAffineOpen X U).isoSpec.inv ≫ U.1.ι ≫ (baseIso X).inv) ≫ (sectionHom f ι c).map := by
        rw [sectionMap]; simp only [Category.assoc]
    _ = affineι X (structureData X) U ≫ (sectionHom f ι c).map := by rw [h₁]
    _ = _ := (sectionHom f ι c).affineι_map U

end ConstantSection

/-! ### Forgetting a coordinate -/

section Rename

/-- Contracting an extended ideal of a polynomial algebra along an injective renaming of the
variables gives back the extended ideal: both consist of the polynomials all of whose
coefficients lie in the ideal. -/
theorem comap_rename_map_C {A : Type u} [CommRing A] {σ τ : Type u} (g : σ → τ)
    (hg : Function.Injective g) (I : Ideal A) :
    Ideal.comap (MvPolynomial.rename (R := A) g : MvPolynomial σ A →ₐ[A] _).toRingHom
        (Ideal.map (MvPolynomial.C : A →+* MvPolynomial τ A) I) =
      Ideal.map (MvPolynomial.C : A →+* MvPolynomial σ A) I := by
  ext p
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h d
    have hd := h (Finsupp.mapDomain g d)
    rwa [show ((MvPolynomial.rename (R := A) g : MvPolynomial σ A →ₐ[A] _).toRingHom p) =
      MvPolynomial.rename g p from rfl, MvPolynomial.coeff_rename_mapDomain g hg p d] at hd
  · intro h m
    change (MvPolynomial.rename g p).coeff m ∈ I
    by_cases hm : ∃ d : σ →₀ ℕ, Finsupp.mapDomain g d = m
    · obtain ⟨d, rfl⟩ := hm
      rw [MvPolynomial.coeff_rename_mapDomain g hg p d]
      exact h d
    · rw [MvPolynomial.coeff_rename_eq_zero g p m fun u hu ↦ absurd ⟨u, hu⟩ hm]
      exact I.zero_mem

/-- An injective renaming of the variables carries the generic point of the fibre of the affine
space `𝔸^τ_A` to the generic point of the fibre of `𝔸^σ_A`. -/
theorem comap_rename_bundlePoint {A : Type u} [CommRing A] {σ τ : Type u} (g : σ → τ)
    (hg : Function.Injective g) (q : ↥(Spec (CommRingCat.of A))) :
    (Spec.map (CommRingCat.ofHom
          (MvPolynomial.rename (R := A) g : MvPolynomial σ A →ₐ[A] _).toRingHom)).base
        (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial τ A)) q) =
      VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial σ A)) q := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (MvPolynomial.rename (R := A) g : MvPolynomial σ A →ₐ[A] _).toRingHom
      (Ideal.map (algebraMap A (MvPolynomial τ A)) q.asIdeal) =
    Ideal.map (algebraMap A (MvPolynomial σ A)) q.asIdeal
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]
  exact comap_rename_map_C g hg q.asIdeal

variable (X : Scheme.{u}) (ι' : Type u)

/-- The morphism of quasi-coherent algebras adjoining one further coordinate. -/
def renameHom :
    RelativeSpec.Hom X (trivialAlgebraData X (Option ι')) (trivialAlgebraData X ι') where
  app _ := MvPolynomial.rename some
  naturality h := RingHom.ext fun p ↦ (MvPolynomial.map_rename (res X h) some p).symm

@[simp]
theorem renameHom_app (U : X.affineOpens) (p : MvPolynomial ι' Γ(X, U.1)) :
    (renameHom X ι').app U p = MvPolynomial.rename some p := rfl

/-- **Forgetting the last coordinate** `X × 𝔸^{Option ι'} ⟶ X × 𝔸^{ι'}`. -/
def forget : (trivialData X (Option ι')).totalSpace ⟶ (trivialData X ι').totalSpace :=
  (renameHom X ι').map

/-- Forgetting a coordinate is a morphism over `X`. -/
theorem forget_proj :
    forget X ι' ≫ (trivialData X ι').proj = (trivialData X (Option ι')).proj :=
  RelativeSpec.Hom.map_toBase (renameHom X ι')

/- As in `RelativeSpec.lean`, the locality instance for `IsAffineHom` is only found with the
transparency restriction of Mathlib's directed affine cover switched off. -/
set_option backward.isDefEq.respectTransparency false in
instance isAffineHom_forget : IsAffineHom (forget X ι') :=
  RelativeSpec.Hom.property_map_of_forall (renameHom X ι') @IsAffineHom fun _ ↦
    isAffineHom_of_isAffine _

/-- Over an affine chart, forgetting a coordinate is the spectrum of `MvPolynomial.rename some`. -/
theorem forget_affineι (U : X.affineOpens) :
    affineι X (trivialAlgebraData X (Option ι')) U ≫ forget X ι' =
      Spec.map (CommRingCat.ofHom
          (MvPolynomial.rename (R := Γ(X, U.1)) (some : ι' → Option ι') :
            MvPolynomial ι' Γ(X, U.1) →ₐ[Γ(X, U.1)] _).toRingHom) ≫
        affineι X (trivialAlgebraData X ι') U :=
  RelativeSpec.Hom.affineι_map (renameHom X ι') U

/-- Forgetting the last coordinate matches the generic points of the fibres over a chart. -/
theorem forget_bundlePoint_chart (U : X.affineOpens) (y : U.1.toScheme) :
    (forget X ι').base
        (BundlePullbackGlobal.bundlePoint (trivialData X (Option ι')) (U.1.ι.base y)) =
      BundlePullbackGlobal.bundlePoint (trivialData X ι') (U.1.ι.base y) := by
  rw [trivialData_bundlePoint, trivialData_bundlePoint]
  have hcomp : (forget X ι').base
      ((affineι X (trivialAlgebraData X (Option ι')) U).base
        (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial (Option ι') Γ(X, U.1)))
          ((isAffineOpen X U).isoSpec.hom.base y))) =
      (affineι X (trivialAlgebraData X (Option ι')) U ≫ forget X ι').base
        (VectorBundle.bundlePoint (AlgEquiv.refl (A₁ := MvPolynomial (Option ι') Γ(X, U.1)))
          ((isAffineOpen X U).isoSpec.hom.base y)) := rfl
  rw [hcomp, forget_affineι]
  exact congrArg (affineι X (trivialAlgebraData X ι') U).base
    (comap_rename_bundlePoint (some : ι' → Option ι') (Option.some_injective ι') _)

/-- **Forgetting the last coordinate matches the generic points of the fibres**: this is the
statement needed to run the induction on the rank one variable at a time. -/
theorem forget_bundlePoint (x : X) :
    (forget X ι').base (BundlePullbackGlobal.bundlePoint (trivialData X (Option ι')) x) =
      BundlePullbackGlobal.bundlePoint (trivialData X ι') x := by
  obtain ⟨U, hU⟩ := CycleGluing.exists_mem_of_iSup_eq_top (iSup_affineOpens_eq_top X) x
  exact forget_bundlePoint_chart X ι' U ⟨x, hU⟩

end Rename

end

end GromovWitten.AlgebraicGeometry.VectorBundleTotalSpace
