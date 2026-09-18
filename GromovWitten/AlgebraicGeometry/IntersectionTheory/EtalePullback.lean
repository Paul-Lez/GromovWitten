/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.StackChowVistoli
import GromovWitten.AlgebraicGeometry.Curves.RelativeDimension

/-!
# Flat pullback of cycles along etale morphisms and Vistoli cycles of etale groupoids

An etale morphism `f : R ⟶ U` of schemes is flat and unramified, so every point of `R` is a
generic point of its fibre and the length of the local ring of the fibre at it is one.  The flat
pullback of an algebraic cycle along `f` is therefore literally the restriction of the coefficient
function, exactly as for an open immersion, and the only thing to prove is that the restricted
coefficient function still has locally finite support.  That is proved here from local
quasi-finiteness of an etale morphism.

## Main definitions and results

* `AlgebraicCycle.pullbackEtale f c`, the flat pullback of a rational cycle along an etale
  morphism, with `pullbackEtale_add`, `pullbackEtale_smul`, `pullbackEtale_id`,
  `pullbackEtale_comp`, `pullbackEtale_eq_pullbackOpen` and `pullbackEtale_injective`.
* `cyclesOfDimension.flatPullbackEtale`, the dimension-graded version, under the explicit
  relative-dimension-zero hypothesis `∀ r, dimensionR r = dimensionU (f.base r)`.
* `height_le_height_base_of_etale` and `DimensionFunction.apply_le_of_etale`: the certified
  closure dimension never *decreases* along an etale morphism.  The reverse inequality is proved
  under the hypothesis that the etale morphism is specializing (`SpecializingMap`), which holds
  for instance for a morphism with closed underlying map; this gives
  `DimensionFunction.apply_eq_of_etale_of_specializingMap`.
* `EtalePresentationGroupoid`, a scheme-level presentation groupoid `R ⇉ U` whose two legs are
  etale, its Vistoli cycles `cycles` with `mem_cycles_iff`, and its Vistoli Chow group `chow`.
* `OpenPresentationGroupoid.toEtale`, the comparison with the open-immersion groupoids of
  `StackChowVistoli.lean`: the two Vistoli cycle groups are *equal* and the two Chow groups are
  canonically isomorphic.
* `DeligneMumfordStack.etalePresentation` and `DeligneMumfordStack.vistoliChow`, the presentation
  groupoid of the represented self-overlap of a chosen etale surjective atlas of a
  Deligne--Mumford stack and its Vistoli rational Chow group.

## What is conditional

The dimension compatibility of the two legs of a presentation groupoid (`src_dim` and `tgt_dim`)
is *data* of `EtalePresentationGroupoid`, exactly as in the open-immersion case.  It cannot be
proved for an arbitrary etale morphism: an open immersion is etale, and the closure dimension of a
point of an open subscheme is in general strictly smaller than the closure dimension of its image
(the generic point of `Spec` of a discrete valuation ring has closure dimension one, but zero on
the punctured spectrum).  `DimensionFunction.apply_eq_of_etale_of_specializingMap` supplies the
hypothesis whenever the legs are specializing, which is the case for a finite etale groupoid.

Pullback of *rational equivalence* along an etale morphism is not constructed: it needs a
comparison of orders of vanishing on a possibly non-integral etale cover, which is the same
missing Mathlib input recorded in `ChowGroupLocalization.lean`.  Consequently there is no
functoriality of the Vistoli groups for etale refinements here; the Vistoli Chow group is still
defined, as in the open case, as the quotient of the descent cycles by the rational equivalences
of the atlas.
-/

open CategoryTheory TopologicalSpace Topology Order

open scoped AlgebraicGeometry

attribute [local instance] specializationOrder

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Local finiteness of the pullback of a locally finite support -/

namespace AlgebraicCycle

variable {X Y : Scheme.{u}}

/-- **Preimages of finite sets are finite near every point of an etale morphism.**  Every point of
the source has an affine open neighbourhood which the morphism maps into an affine open of the
target; on it the morphism is quasi-finite and quasi-compact, so preimages of finite sets are
finite. -/
theorem exists_isOpen_finite_inter_preimage_of_etale (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.Etale f] (x : X) {A : Set Y} (hA : A.Finite) :
    ∃ V : X.Opens, x ∈ V ∧ ((V : Set X) ∩ f.base ⁻¹' A).Finite := by
  have hlqf : _root_.AlgebraicGeometry.LocallyQuasiFinite f :=
    Curves.locallyQuasiFinite_of_etale f
  obtain ⟨W, hW, hxW, -⟩ :=
    _root_.AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := Y) (x := f.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVsub⟩ :=
    _root_.AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := f ⁻¹ᵁ W) hxW
  have he : V ≤ f ⁻¹ᵁ W := hVsub
  have hVaff : _root_.AlgebraicGeometry.IsAffine V.toScheme := hV
  have hWaff : _root_.AlgebraicGeometry.IsAffine W.toScheme := hW
  have hAW : (Subtype.val ⁻¹' A : Set W.toScheme).Finite :=
    hA.preimage Subtype.val_injective.injOn
  have hfin : ((f.resLE W V he).base ⁻¹' (Subtype.val ⁻¹' A : Set W.toScheme)).Finite :=
    (f.resLE W V he).finite_preimage hAW
  refine ⟨V, hxV, (hfin.image Subtype.val).subset ?_⟩
  rintro r ⟨hrV, hrA⟩
  refine ⟨⟨r, hrV⟩, ?_, rfl⟩
  have hcoe : ((f.resLE W V he).base ⟨r, hrV⟩).1 = f.base r :=
    _root_.AlgebraicGeometry.Scheme.Hom.coe_resLE_apply f he ⟨r, hrV⟩
  change ((f.resLE W V he).base ⟨r, hrV⟩).1 ∈ A
  rw [hcoe]
  exact hrA

/-! ## Flat pullback of cycles along an etale morphism -/

/-- **Flat pullback of a rational algebraic cycle along an etale morphism.**  All multiplicities
are one: an etale morphism is flat and unramified, so the scheme-theoretic fibre over a point is
a disjoint union of spectra of finite separable field extensions and each of its points is a
reduced generic point of that fibre. -/
noncomputable def pullbackEtale (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (c : AlgebraicCycle Y ℚ) : AlgebraicCycle X ℚ where
  toFun x := c (f.base x)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨t, ht, hfinite⟩ := c.supportLocallyFiniteWithinDomain (f.base x) (by trivial)
    obtain ⟨V, hxV, hVfin⟩ := exists_isOpen_finite_inter_preimage_of_etale f x hfinite
    refine ⟨(V : Set X) ∩ f.base ⁻¹' t, Filter.inter_mem (V.isOpen.mem_nhds hxV)
      (f.continuous.continuousAt.preimage_mem_nhds ht), hVfin.subset ?_⟩
    rintro z ⟨⟨hzV, hzt⟩, hzs⟩
    exact ⟨hzV, ⟨hzt, hzs⟩⟩

@[simp]
lemma pullbackEtale_apply (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (c : AlgebraicCycle Y ℚ) (x : X) : pullbackEtale f c x = c (f.base x) :=
  rfl

/-- Flat pullback along an etale morphism is additive. -/
lemma pullbackEtale_add (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (c d : AlgebraicCycle Y ℚ) :
    pullbackEtale f (c + d) = pullbackEtale f c + pullbackEtale f d := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp

/-- Flat pullback along an etale morphism commutes with rational scalars. -/
lemma pullbackEtale_smul (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (q : ℚ) (c : AlgebraicCycle Y ℚ) :
    pullbackEtale f (q • c) = q • pullbackEtale f c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp

/-- Flat pullback along an etale morphism, bundled with its proved rational linearity. -/
noncomputable def pullbackEtaleLinear (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f] :
    AlgebraicCycle Y ℚ →ₗ[ℚ] AlgebraicCycle X ℚ where
  toFun := pullbackEtale f
  map_add' := pullbackEtale_add f
  map_smul' := pullbackEtale_smul f

@[simp]
lemma pullbackEtaleLinear_apply (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (c : AlgebraicCycle Y ℚ) : pullbackEtaleLinear f c = pullbackEtale f c :=
  rfl

/-- Flat pullback along the identity is the identity. -/
@[simp]
lemma pullbackEtale_id (c : AlgebraicCycle X ℚ) : pullbackEtale (𝟙 X) c = c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  rfl

/-- Flat pullback along etale morphisms is contravariantly functorial. -/
@[simp]
lemma pullbackEtale_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [_root_.AlgebraicGeometry.Etale f] [_root_.AlgebraicGeometry.Etale g]
    (c : AlgebraicCycle Z ℚ) :
    pullbackEtale f (pullbackEtale g c) = pullbackEtale (f ≫ g) c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  rfl

/-- **The etale pullback extends the open-immersion pullback.**  An open immersion is etale and
the two constructions are the same restriction of coefficient functions. -/
@[simp]
lemma pullbackEtale_eq_pullbackOpen (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] (c : AlgebraicCycle Y ℚ) :
    pullbackEtale f c = pullbackOpen f c := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  rfl

/-- **Flat pullback along a surjective etale morphism is injective on cycles.** -/
lemma pullbackEtale_injective (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    [_root_.AlgebraicGeometry.Surjective f] :
    Function.Injective (pullbackEtale f) := by
  intro c d h
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  obtain ⟨x, rfl⟩ := f.surjective y
  exact congrFun (congrArg (fun z : AlgebraicCycle X ℚ ↦ (z : X → ℚ)) h) x

end AlgebraicCycle

/-! ## Closure dimension along an etale morphism -/

variable {X Y : Scheme.{u}}

/-- **An etale morphism is strictly monotone for the specialization order.**  It is continuous,
hence monotone, and two comparable points of one fibre coincide because the fibres of an etale
morphism are discrete. -/
theorem strictMono_base_of_etale (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f] :
    StrictMono f.base := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · change f.base b ⤳ f.base a
    exact f.base.hom.map_specializes (show b ⤳ a from hab.le)
  · intro h
    exact hab.ne' (Curves.eq_of_specializes_of_etale f (show b ⤳ a from hab.le) h.symm)

/-- **The closure dimension of a point does not decrease along an etale morphism.**  Every strict
specialization chain ending at a point maps to a strict chain ending at its image. -/
theorem height_le_height_base_of_etale (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f] (x : X) :
    Order.height x ≤ Order.height (f.base x) :=
  Order.height_le_height_apply_of_strictMono _ (strictMono_base_of_etale f) x

/-- **A specializing etale morphism preserves the closure dimension of every point.**  The
inequality above is complemented by lifting every specialization chain below the image point. -/
theorem height_eq_of_etale_of_specializingMap (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (hf : SpecializingMap f.base) (x : X) :
    Order.height x = Order.height (f.base x) := by
  refine Order.height_eq_of_strictMono f.base (strictMono_base_of_etale f) ?_ x
  intro a b hba
  obtain ⟨a', ha', hfa'⟩ := hf (show f.base a ⤳ b from hba.le)
  refine ⟨a', lt_of_le_of_ne (show a ⤳ a' from ha') ?_, hfa'⟩
  rintro rfl
  exact hba.ne hfa'.symm

/-- **The certified closure dimension does not decrease along an etale morphism.**  This is the
integer form of `height_le_height_base_of_etale`; it is not a compatibility hypothesis. -/
theorem DimensionFunction.apply_le_of_etale (dimensionX : DimensionFunction X)
    (dimensionY : DimensionFunction Y) (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f] (x : X) :
    dimensionX x ≤ dimensionY (f.base x) := by
  have h : Order.height x ≤ Order.height (f.base x) := height_le_height_base_of_etale f x
  rw [dimensionX.height_eq, dimensionY.height_eq] at h
  have hnat : Int.toNat (dimensionX x) ≤ Int.toNat (dimensionY (f.base x)) := by
    exact_mod_cast h
  rw [← Int.toNat_of_nonneg (dimensionX.nonnegative x),
    ← Int.toNat_of_nonneg (dimensionY.nonnegative (f.base x))]
  exact_mod_cast hnat

/-- **A specializing etale morphism has relative dimension zero for the certified gradings.**
This is the hypothesis `hdim` required by the graded flat pullback below, proved rather than
assumed whenever the morphism lifts specializations; a morphism with closed underlying map, for
example a finite etale morphism, is such. -/
theorem DimensionFunction.apply_eq_of_etale_of_specializingMap (dimensionX : DimensionFunction X)
    (dimensionY : DimensionFunction Y) (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (hf : SpecializingMap f.base) (x : X) :
    dimensionX x = dimensionY (f.base x) := by
  have hcast : (Int.toNat (dimensionX x) : ℕ∞) =
      (Int.toNat (dimensionY (f.base x)) : ℕ∞) := by
    rw [← dimensionX.height_eq, ← dimensionY.height_eq]
    exact height_eq_of_etale_of_specializingMap f hf x
  have hnat : Int.toNat (dimensionX x) = Int.toNat (dimensionY (f.base x)) :=
    ENat.natCast_inj.mp hcast
  rw [← Int.toNat_of_nonneg (dimensionX.nonnegative x),
    ← Int.toNat_of_nonneg (dimensionY.nonnegative (f.base x))]
  exact congrArg Int.ofNat hnat

/-- An etale morphism with closed underlying map preserves the certified closure dimension. -/
theorem DimensionFunction.apply_eq_of_etale_of_isClosedMap (dimensionX : DimensionFunction X)
    (dimensionY : DimensionFunction Y) (f : X ⟶ Y) [_root_.AlgebraicGeometry.Etale f]
    (hf : IsClosedMap f.base) (x : X) :
    dimensionX x = dimensionY (f.base x) :=
  DimensionFunction.apply_eq_of_etale_of_specializingMap dimensionX dimensionY f
    hf.specializingMap x

/-! ## Dimension-graded flat pullback along an etale morphism -/

namespace cyclesOfDimension

variable {U R : Scheme.{u}} {dimensionU : DimensionFunction U}
  {dimensionR : DimensionFunction R} {i : ℤ}

/-- **Flat pullback of dimension-graded rational cycles along an etale morphism.**  The geometric
hypothesis is that the morphism has relative dimension zero for the two certified gradings; all
multiplicities are one. -/
noncomputable def flatPullbackEtale (f : R ⟶ U) [_root_.AlgebraicGeometry.Etale f]
    (hdim : ∀ r, dimensionR r = dimensionU (f.base r)) :
    cyclesOfDimension U dimensionU i →ₗ[ℚ] cyclesOfDimension R dimensionR i where
  toFun c := ⟨AlgebraicCycle.pullbackEtale f c.1, by
    intro r hr
    refine c.2 (f.base r) ?_
    rw [← hdim r]
    exact hr⟩
  map_add' c d := Subtype.ext (AlgebraicCycle.pullbackEtale_add f c.1 d.1)
  map_smul' q c := Subtype.ext (AlgebraicCycle.pullbackEtale_smul f q c.1)

@[simp]
theorem flatPullbackEtale_apply (f : R ⟶ U) [_root_.AlgebraicGeometry.Etale f]
    (hdim : ∀ r, dimensionR r = dimensionU (f.base r))
    (c : cyclesOfDimension U dimensionU i) (r : R) :
    ((flatPullbackEtale (i := i) f hdim c : cyclesOfDimension R dimensionR i) :
        AlgebraicCycle R ℚ) r = (c : AlgebraicCycle U ℚ) (f.base r) :=
  rfl

/-- Dimension-graded flat pullback along the identity is the identity. -/
@[simp]
theorem flatPullbackEtale_id
    (hdim : ∀ u, dimensionU u = dimensionU ((𝟙 U : U ⟶ U).base u)) :
    flatPullbackEtale (dimensionR := dimensionU) (i := i) (𝟙 U) hdim = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact AlgebraicCycle.pullbackEtale_id c.1

/-- Dimension-graded flat pullback along etale morphisms is contravariantly functorial. -/
@[simp]
theorem flatPullbackEtale_comp {V : Scheme.{u}} {dimensionV : DimensionFunction V}
    (f₁ : V ⟶ R) (f₂ : R ⟶ U)
    [_root_.AlgebraicGeometry.Etale f₁] [_root_.AlgebraicGeometry.Etale f₂]
    (h₁ : ∀ v, dimensionV v = dimensionR (f₁.base v))
    (h₂ : ∀ r, dimensionR r = dimensionU (f₂.base r))
    (h : ∀ v, dimensionV v = dimensionU ((f₁ ≫ f₂).base v)) :
    flatPullbackEtale (dimensionR := dimensionV) (i := i) (f₁ ≫ f₂) h =
      (flatPullbackEtale f₁ h₁).comp (flatPullbackEtale f₂ h₂) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact (AlgebraicCycle.pullbackEtale_comp f₁ f₂ c.1).symm

/-- **The graded etale pullback extends the graded open-immersion pullback.** -/
theorem flatPullbackEtale_eq_flatPullbackOpen (f : R ⟶ U)
    [_root_.AlgebraicGeometry.IsOpenImmersion f]
    (hdim : ∀ r, dimensionR r = dimensionU (f.base r)) :
    flatPullbackEtale (dimensionR := dimensionR) (i := i) f hdim =
      flatPullbackOpen (dimensionU := dimensionR) (i := i) f hdim := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact AlgebraicCycle.pullbackEtale_eq_pullbackOpen f c.1

end cyclesOfDimension

/-! ## Presentation groupoids with etale legs -/

/-- The scheme-level data of a presentation groupoid `R ⇉ U` of a stack by an atlas whose source
and target are *etale*.  This is the etale generalisation of `OpenPresentationGroupoid`: the two
legs are now only etale, which is what the presentation groupoid of a genuine etale atlas
supplies.  As in the open case the relative-dimension-zero statement for the two certified
gradings is data, because it genuinely fails for some etale morphisms (an open immersion is etale
and can drop the closure dimension of a point); `DimensionFunction.apply_eq_of_etale_of_isClosedMap`
proves it whenever the legs are closed, for example for a finite etale groupoid. -/
structure EtalePresentationGroupoid where
  /-- The atlas scheme `U`. -/
  base : Scheme.{u}
  /-- The arrow scheme `R = U ×_X U`. -/
  arrows : Scheme.{u}
  /-- The certified closure-dimension grading of the atlas. -/
  baseDim : DimensionFunction base
  /-- The certified closure-dimension grading of the arrow scheme. -/
  arrowsDim : DimensionFunction arrows
  /-- The source map `s : R ⟶ U` of the groupoid. -/
  src : arrows ⟶ base
  /-- The target map `t : R ⟶ U` of the groupoid. -/
  tgt : arrows ⟶ base
  /-- The source map is etale, so rational cycles pull back along it. -/
  src_etale : _root_.AlgebraicGeometry.Etale src
  /-- The target map is etale. -/
  tgt_etale : _root_.AlgebraicGeometry.Etale tgt
  /-- The source map has relative dimension zero for the two certified gradings. -/
  src_dim (r : arrows) : arrowsDim r = baseDim (src.base r)
  /-- The target map has relative dimension zero for the two certified gradings. -/
  tgt_dim (r : arrows) : arrowsDim r = baseDim (tgt.base r)

attribute [instance] EtalePresentationGroupoid.src_etale
attribute [instance] EtalePresentationGroupoid.tgt_etale

namespace EtalePresentationGroupoid

variable (G : EtalePresentationGroupoid.{u}) (i : ℤ)

/-- Flat pullback of dimension-graded rational cycles along the source map of the groupoid. -/
noncomputable def srcPullback :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ] cyclesOfDimension G.arrows G.arrowsDim i :=
  cyclesOfDimension.flatPullbackEtale G.src G.src_dim

/-- Flat pullback of dimension-graded rational cycles along the target map of the groupoid. -/
noncomputable def tgtPullback :
    cyclesOfDimension G.base G.baseDim i →ₗ[ℚ] cyclesOfDimension G.arrows G.arrowsDim i :=
  cyclesOfDimension.flatPullbackEtale G.tgt G.tgt_dim

/-- Coefficients of the source pullback of a cycle. -/
@[simp]
theorem srcPullback_apply (z : cyclesOfDimension G.base G.baseDim i) (r : G.arrows) :
    ((G.srcPullback i z : cyclesOfDimension G.arrows G.arrowsDim i) :
        AlgebraicCycle G.arrows ℚ) r =
      (z : AlgebraicCycle G.base ℚ) (G.src.base r) :=
  rfl

/-- Coefficients of the target pullback of a cycle. -/
@[simp]
theorem tgtPullback_apply (z : cyclesOfDimension G.base G.baseDim i) (r : G.arrows) :
    ((G.tgtPullback i z : cyclesOfDimension G.arrows G.arrowsDim i) :
        AlgebraicCycle G.arrows ℚ) r =
      (z : AlgebraicCycle G.base ℚ) (G.tgt.base r) :=
  rfl

/-- **Vistoli cycles of an etale presentation.**  The dimension-`i` rational cycles on the atlas
whose two flat pullbacks to the arrow scheme agree. -/
noncomputable def cycles : Submodule ℚ (cyclesOfDimension G.base G.baseDim i) :=
  invariantCycles (G.srcPullback i) (G.tgtPullback i)

/-- **Pointwise description of the Vistoli cycles of an etale presentation.**  A cycle descends
exactly when its coefficient function is constant along the point relation of the groupoid. -/
theorem mem_cycles_iff {z : cyclesOfDimension G.base G.baseDim i} :
    z ∈ G.cycles i ↔
      ∀ r : G.arrows,
        (z : AlgebraicCycle G.base ℚ) (G.src.base r) =
          (z : AlgebraicCycle G.base ℚ) (G.tgt.base r) := by
  rw [cycles, mem_invariantCycles_iff]
  constructor
  · intro h r
    have hr := congrArg
      (fun w : cyclesOfDimension G.arrows G.arrowsDim i ↦
        (w : AlgebraicCycle G.arrows ℚ) r) h
    simpa using hr
  · intro h
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext r
    exact h r

/-- Rational equivalence on the atlas, restricted to the Vistoli cycles. -/
noncomputable def relations : Submodule ℚ (G.cycles i) :=
  Submodule.comap (G.cycles i).subtype
    (RationalEquivalenceSystem.canonical
      (X := G.base) (dimension := G.baseDim) (i := i)).relations

/-- **The Vistoli rational Chow group of an etale presentation** in dimension `i`: descent cycles
on the atlas modulo rational equivalence on the atlas.  No descent of rational equivalence along
the two legs is used, exactly as in the open-immersion case. -/
noncomputable abbrev chow := G.cycles i ⧸ G.relations i

/-- The class of a Vistoli cycle in the Vistoli Chow group. -/
noncomputable abbrev quotientMap : G.cycles i →ₗ[ℚ] G.chow i :=
  (G.relations i).mkQ

/-- The Vistoli class of a cycle which is rationally equivalent to zero on the atlas
vanishes. -/
theorem quotientMap_eq_zero_of_mem_relations (z : G.cycles i)
    (hz : (z : cyclesOfDimension G.base G.baseDim i) ∈
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).relations) :
    G.quotientMap i z = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hz

/-- When the two legs of the presentation coincide every cycle on the atlas descends. -/
theorem cycles_eq_top_of_src_eq_tgt (h : G.src = G.tgt) : G.cycles i = ⊤ :=
  eq_top_iff.mpr fun z _ ↦ (G.mem_cycles_iff i).mpr fun r ↦ by rw [h]

/-- Every cycle on an atlas with a single point descends. -/
theorem cycles_eq_top_of_subsingleton [Subsingleton G.base] : G.cycles i = ⊤ :=
  eq_top_iff.mpr fun z _ ↦ (G.mem_cycles_iff i).mpr fun r ↦ by
    rw [Subsingleton.elim (G.src.base r) (G.tgt.base r)]

/-- The Vistoli cycles of an etale presentation with equal legs, identified with all cycles on
the atlas. -/
noncomputable def cyclesTopEquiv (h : G.src = G.tgt) :
    G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i :=
  (LinearEquiv.ofEq _ _ (G.cycles_eq_top_of_src_eq_tgt i h)).trans Submodule.topEquiv

/-- The identification of Vistoli cycles with all cycles is the inclusion. -/
@[simp]
theorem cyclesTopEquiv_apply (h : G.src = G.tgt) (z : G.cycles i) :
    G.cyclesTopEquiv i h z = (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

/-- Under the identification of Vistoli cycles with all cycles, the Vistoli relations become the
rational equivalence relations of the atlas. -/
theorem map_relations_cyclesTopEquiv (h : G.src = G.tgt) :
    Submodule.map
        ((G.cyclesTopEquiv i h : G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) :
          G.cycles i →ₗ[ℚ] cyclesOfDimension G.base G.baseDim i)
        (G.relations i) =
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).relations := by
  have hcoe :
      ((G.cyclesTopEquiv i h : G.cycles i ≃ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) :
          G.cycles i →ₗ[ℚ] cyclesOfDimension G.base G.baseDim i) =
        (G.cycles i).subtype :=
    LinearMap.ext fun _ ↦ rfl
  rw [hcoe, relations]
  refine Submodule.map_comap_eq_of_surjective ?_ _
  intro z
  refine ⟨⟨z, ?_⟩, rfl⟩
  rw [G.cycles_eq_top_of_src_eq_tgt i h]
  trivial

/-- **An etale presentation with equal legs computes the scheme Chow group of its atlas.** -/
noncomputable def chowEquivSchemeChow (h : G.src = G.tgt) :
    G.chow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).ChowGroup :=
  Submodule.Quotient.equiv _ _ (G.cyclesTopEquiv i h) (G.map_relations_cyclesTopEquiv i h)

/-- The comparison with the scheme Chow group sends the Vistoli class of a cycle to its ordinary
rational-equivalence class. -/
@[simp]
theorem chowEquivSchemeChow_quotientMap (h : G.src = G.tgt) (z : G.cycles i) :
    G.chowEquivSchemeChow i h (G.quotientMap i z) =
      (RationalEquivalenceSystem.canonical
        (X := G.base) (dimension := G.baseDim) (i := i)).quotientMap
        (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

end EtalePresentationGroupoid

/-! ## Comparison with the open-immersion presentation groupoids -/

/-- Every presentation groupoid with open-immersion legs is a presentation groupoid with etale
legs: an open immersion is etale. -/
def OpenPresentationGroupoid.toEtale (G : OpenPresentationGroupoid.{u}) :
    EtalePresentationGroupoid.{u} where
  base := G.base
  arrows := G.arrows
  baseDim := G.baseDim
  arrowsDim := G.arrowsDim
  src := G.src
  tgt := G.tgt
  src_etale := inferInstance
  tgt_etale := inferInstance
  src_dim := G.src_dim
  tgt_dim := G.tgt_dim

namespace OpenPresentationGroupoid

variable (G : OpenPresentationGroupoid.{u}) (i : ℤ)

/-- The two source pullbacks agree: the etale pullback of an open immersion is its open
pullback. -/
theorem toEtale_srcPullback : G.toEtale.srcPullback i = G.srcPullback i :=
  cyclesOfDimension.flatPullbackEtale_eq_flatPullbackOpen G.src G.src_dim

/-- The two target pullbacks agree. -/
theorem toEtale_tgtPullback : G.toEtale.tgtPullback i = G.tgtPullback i :=
  cyclesOfDimension.flatPullbackEtale_eq_flatPullbackOpen G.tgt G.tgt_dim

/-- **The etale and the open Vistoli cycle groups of an open presentation are the same
submodule.** -/
theorem toEtale_cycles : G.toEtale.cycles i = G.cycles i := by
  rw [EtalePresentationGroupoid.cycles, cycles, toEtale_srcPullback, toEtale_tgtPullback]
  exact rfl

/-- **The etale and the open Vistoli Chow groups of an open presentation agree.** -/
noncomputable def toEtaleChowEquiv : G.toEtale.chow i ≃ₗ[ℚ] G.chow i :=
  LinearEquiv.refl ℚ (G.chow i)

end OpenPresentationGroupoid

/-- **The Vistoli Chow group of a scheme with its identity etale atlas is its scheme Chow
group.** -/
noncomputable def identityEtalePresentationChowEquiv (X : Scheme.{u}) (dX : DimensionFunction X)
    (i : ℤ) :
    (identityPresentation X dX).toEtale.chow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := X) (dimension := dX) (i := i)).ChowGroup :=
  (identityPresentation X dX).toEtale.chowEquivSchemeChow i rfl

end GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## The Vistoli Chow group of a Deligne--Mumford stack -/

namespace GromovWitten.AlgebraicGeometry

namespace DeligneMumfordStack

variable (X : DeligneMumfordStack.{u})

/-- An etale surjective atlas of a Deligne--Mumford stack, chosen from its defining existence
statement.  The choice is internal: it cannot be replaced by a caller. -/
noncomputable def chosenEtaleAtlas : StackChart X.toStack :=
  Classical.choose X.etaleAtlas

/-- The chosen etale atlas is etale and surjective on every scheme base change. -/
theorem chosenEtaleAtlas_isEtaleSurjective : X.chosenEtaleAtlas.IsEtaleSurjective :=
  Classical.choose_spec X.etaleAtlas

/-- The represented self-overlap `U ×_X U` of the chosen etale atlas, retained together with the
etale-surjective property of its first projection. -/
private noncomputable def chosenEtaleAtlasSelfOverlapWithProperty :
    {p : X.chosenEtaleAtlas.PullbackPresentation X.chosenEtaleAtlas.scheme
        (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme)) //
      ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
        MorphismProperty _root_.AlgebraicGeometry.Scheme.{u}) p.fst} :=
  let h := X.chosenEtaleAtlas_isEtaleSurjective
  let p := Classical.choice <| h.1 X.chosenEtaleAtlas.scheme
    (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme))
  ⟨p, h.2 X.chosenEtaleAtlas.scheme
    (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme)) p⟩

/-- **The arrow scheme `R = U ×_X U` of the chosen etale atlas of a Deligne--Mumford stack.**
This is an actual scheme, supplied by the representability clause of the etale atlas. -/
noncomputable def chosenEtaleAtlasSelfOverlap :
    X.chosenEtaleAtlas.PullbackPresentation X.chosenEtaleAtlas.scheme
      (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme)) :=
  X.chosenEtaleAtlasSelfOverlapWithProperty.1

/-- The first projection of the self-overlap is etale, being a base change of the etale atlas. -/
theorem chosenEtaleAtlasSelfOverlap_fst_etale :
    _root_.AlgebraicGeometry.Etale X.chosenEtaleAtlasSelfOverlap.fst :=
  X.chosenEtaleAtlasSelfOverlapWithProperty.2.1

/-- The first projection of the self-overlap is surjective. -/
theorem chosenEtaleAtlasSelfOverlap_fst_surjective :
    _root_.AlgebraicGeometry.Surjective X.chosenEtaleAtlasSelfOverlap.fst :=
  X.chosenEtaleAtlasSelfOverlapWithProperty.2.2

/-- The second projection of the self-overlap is etale: the swapped presentation is another
pullback presentation, to which representable etaleness applies. -/
theorem chosenEtaleAtlasSelfOverlap_snd_etale :
    _root_.AlgebraicGeometry.Etale X.chosenEtaleAtlasSelfOverlap.snd :=
  (X.chosenEtaleAtlas_isEtaleSurjective.2 X.chosenEtaleAtlas.scheme
    (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme))
    X.chosenEtaleAtlasSelfOverlap.selfSwap).1

/-- The second projection of the self-overlap is surjective, by the same swapped-presentation
argument. -/
theorem chosenEtaleAtlasSelfOverlap_snd_surjective :
    _root_.AlgebraicGeometry.Surjective X.chosenEtaleAtlasSelfOverlap.snd :=
  (X.chosenEtaleAtlas_isEtaleSurjective.2 X.chosenEtaleAtlas.scheme
    (X.chosenEtaleAtlas.obj X.chosenEtaleAtlas.scheme (𝟙 X.chosenEtaleAtlas.scheme))
    X.chosenEtaleAtlasSelfOverlap.selfSwap).2

/-- **The etale presentation groupoid `R ⇉ U` of a Deligne--Mumford stack.**  The atlas is the
chosen etale surjective atlas, the arrow scheme is its represented self-overlap and the two legs
are the two projections, which are etale because they are base changes of the atlas.  The
certified dimension gradings and the relative-dimension-zero statements for the two legs are
supplied by the caller: they are not provable for an arbitrary etale morphism, see
`DimensionFunction.apply_eq_of_etale_of_specializingMap`. -/
noncomputable def etalePresentation
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r)) :
    IntersectionTheory.EtalePresentationGroupoid.{u} where
  base := X.chosenEtaleAtlas.scheme
  arrows := X.chosenEtaleAtlasSelfOverlap.space
  baseDim := baseDim
  arrowsDim := arrowsDim
  src := X.chosenEtaleAtlasSelfOverlap.fst
  tgt := X.chosenEtaleAtlasSelfOverlap.snd
  src_etale := X.chosenEtaleAtlasSelfOverlap_fst_etale
  tgt_etale := X.chosenEtaleAtlasSelfOverlap_snd_etale
  src_dim := hsrc
  tgt_dim := htgt

/-- **The Vistoli rational Chow group of a Deligne--Mumford stack** in dimension `i`: the
dimension-`i` rational cycles on the chosen etale atlas whose two pullbacks to the self-overlap
agree, modulo rational equivalence on the atlas. -/
noncomputable abbrev vistoliChow
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r))
    (i : ℤ) :=
  (X.etalePresentation baseDim arrowsDim hsrc htgt).chow i

/-- The Vistoli class of a descent cycle on the chosen etale atlas of a Deligne--Mumford
stack. -/
noncomputable abbrev vistoliQuotientMap
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.fst.base r))
    (htgt : ∀ r, arrowsDim r = baseDim (X.chosenEtaleAtlasSelfOverlap.snd.base r))
    (i : ℤ) :
    (X.etalePresentation baseDim arrowsDim hsrc htgt).cycles i →ₗ[ℚ]
      X.vistoliChow baseDim arrowsDim hsrc htgt i :=
  (X.etalePresentation baseDim arrowsDim hsrc htgt).quotientMap i

/-- **The etale presentation groupoid of a Deligne--Mumford stack whose two overlap projections
are specializing.**  The relative-dimension-zero statements are then theorems, not hypotheses:
a specializing etale morphism preserves the certified closure dimension.  A finite etale
groupoid, that is a separated Deligne--Mumford stack with finite stabilizers, is of this kind. -/
noncomputable def etalePresentationOfSpecializing
    (baseDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlas.scheme)
    (arrowsDim : IntersectionTheory.DimensionFunction X.chosenEtaleAtlasSelfOverlap.space)
    (hsrc : SpecializingMap X.chosenEtaleAtlasSelfOverlap.fst.base)
    (htgt : SpecializingMap X.chosenEtaleAtlasSelfOverlap.snd.base) :
    IntersectionTheory.EtalePresentationGroupoid.{u} :=
  let _ := X.chosenEtaleAtlasSelfOverlap_fst_etale
  let _ := X.chosenEtaleAtlasSelfOverlap_snd_etale
  X.etalePresentation baseDim arrowsDim
    (fun r ↦ IntersectionTheory.DimensionFunction.apply_eq_of_etale_of_specializingMap
      arrowsDim baseDim X.chosenEtaleAtlasSelfOverlap.fst hsrc r)
    (fun r ↦ IntersectionTheory.DimensionFunction.apply_eq_of_etale_of_specializingMap
      arrowsDim baseDim X.chosenEtaleAtlasSelfOverlap.snd htgt r)

end DeligneMumfordStack

end GromovWitten.AlgebraicGeometry
