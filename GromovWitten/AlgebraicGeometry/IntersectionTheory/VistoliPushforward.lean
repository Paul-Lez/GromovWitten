/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtaleBaseChange
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardCurve

/-!
# Proper pushforward and étale pullback on Vistoli Chow groups

A *cartesian morphism* `Φ : H → G` of étale presentation groupoids consists of maps of atlases
and of arrow schemes such that the arrow scheme of `H` is the base change of the arrow scheme
of `G` along the map of atlases, both via the source and via the target maps.  When the map of
atlases `f` is proper, proper pushforward of cycles on the atlases descends to the Vistoli Chow
groups: invariant cycles go to invariant cycles by étale base change of proper pushforward, and
the divisor of an invariant system `F` goes to the divisor of its *norm pushforward* `N F`,
`(N F) v = ∏_{w ∈ supp F, f w = v} N_{κ(w)/κ(v)} (F w)`, which is again invariant by étale base
change of residue norms.  When the map of atlases is étale, étale pullback descends as well.

For the induced maps on Vistoli Chow groups, the atlas of `G` is locally of finite type over a
field `k` (the atlas of `H` then is too, through the map of atlases), and both groupoids satisfy
the standing hypotheses `EtalePresentationGroupoid.Good`; the cycle-level statements
(`pushCycles`, `properPushforward_mem_cycles`, the base change lemmas) need neither.

The étale-pullback half (`pullCycles`, `InvariantSystem.etalePull`, `vistoliPullback`) mirrors
the `MoritaMap` API of `VistoliRelations.lean`; the two should later be unified through a common
parent structure of groupoid maps.

## Main definitions

* `residueUnitNorm f x : κ(x)ˣ →* κ(f x)ˣ`: the norm along the residue field map (`1` when the
  residue extension is not finite).
* `normPushFamily f S a`: the norm pushforward of a family of residue units supported on `S`.
* `CartesianGroupoidMap H G`: cartesian morphisms of étale presentation groupoids.
* `InvariantSystem.normPush`, `InvariantSystem.etalePull`: norm pushforward, resp. étale
  pullback, of invariant systems.
* `CartesianGroupoidMap.vistoliPushforward`, `CartesianGroupoidMap.vistoliPullback`: the induced
  maps of Vistoli Chow groups; `CartesianGroupoidMap.chowPushforward` on the groups `chow`.

## Main results

* `map_pointDivisor`: for `f` proper between schemes locally of finite type over a field, the
  pushforward of the divisor of the point generator `(w, φ)` is the divisor of the point
  generator `(f w, N φ)`.
* `unitPull_normPushFamily_of_isPullback`: étale base change of the norm pushforward, for an
  arbitrary cartesian square (from `norm_residueFieldMap_eq_prod`, `EtaleBaseChange.lean`).
* `pullbackEtale_map_of_isPullback`: étale base change of proper pushforward of cycles for an
  arbitrary cartesian square (from `pullbackEtale_map`, `EtaleBaseChange.lean`).
* `InvariantSystem.map_divisorCycle_normPush` (Theorem E3): `f_* div F = div (N F)`.
* `CartesianGroupoidMap.properPushforward_mem_cycles`: proper pushforward preserves Vistoli
  cycles.
* `InvariantSystem.flatPullbackEtale_divisor_etalePull`: étale pullback of the divisor of an
  invariant system.
* `CartesianGroupoidMap.vistoliChow_toChow_vistoliPushforward`: compatibility of the Vistoli
  pushforward with the comparison maps to `chow`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

/-! ## Norms along residue field maps -/

section ResidueNorm

variable {X Y : Scheme.{u}}

/-- The norm `κ(x)ˣ → κ(f x)ˣ` along the residue field map of `f : X ⟶ Y` at `x`, for the
algebra structure given by `f.residueFieldMap x`.  It is `1` when `κ(x) / κ(f x)` is not finite
(Mathlib's convention for `Algebra.norm`). -/
noncomputable def residueUnitNorm (f : X ⟶ Y) (x : X) :
    (X.residueField x)ˣ →* (Y.residueField (f.base x))ˣ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Units.map (Algebra.norm (Y.residueField (f.base x)) : X.residueField x →* _)

/-- The value of `residueUnitNorm`. -/
theorem coe_residueUnitNorm (f : X ⟶ Y) (x : X) (a : (X.residueField x)ˣ) :
    ((residueUnitNorm f x a : (Y.residueField (f.base x))ˣ) : Y.residueField (f.base x)) =
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.norm (Y.residueField (f.base x)) (a : X.residueField x) :=
  rfl

/-- The residue norm is trivial along a residue field extension which is not finite. -/
theorem residueUnitNorm_eq_one_of_not_finite (f : X ⟶ Y) (x : X)
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      ¬ Module.Finite (Y.residueField (f.base x)) (X.residueField x))
    (a : (X.residueField x)ˣ) : residueUnitNorm f x a = 1 := by
  let _ := (f.residueFieldMap x).hom.toAlgebra
  exact Units.ext (Algebra.norm_eq_one_of_not_module_finite h _)

/-- The residue norm at `x`, transported to a point `y` equal to `f x`. -/
noncomputable def residueUnitNormTo (f : X ⟶ Y) {x : X} {y : Y} (h : f.base x = y) :
    (X.residueField x)ˣ →* (Y.residueField y)ˣ :=
  (Units.map (Y.residueFieldCongr h).hom.hom.toMonoidHom).comp (residueUnitNorm f x)

/-- `residueUnitNormTo` along the trivial equality is `residueUnitNorm`. -/
@[simp]
theorem residueUnitNormTo_rfl (f : X ⟶ Y) (x : X) (a : (X.residueField x)ˣ) :
    residueUnitNormTo f (rfl : f.base x = f.base x) a = residueUnitNorm f x a := by
  apply Units.ext
  simp [residueUnitNormTo]

/-- The residue norm commutes with transport along an equality of source points. -/
theorem residueUnitNorm_residueFieldCongr (f : X ⟶ Y) {x x' : X} (h : x = x')
    (a : (X.residueField x)ˣ) :
    residueUnitNorm f x' (Units.map (X.residueFieldCongr h).hom.hom.toMonoidHom a) =
      Units.map (Y.residueFieldCongr (congrArg f.base h)).hom.hom.toMonoidHom
        (residueUnitNorm f x a) := by
  subst h
  apply Units.ext
  simp

end ResidueNorm

/-! ## Dimension bookkeeping for finite residue extensions -/

section Dimension

variable {X Y : Scheme.{u}} {k : Type u} [Field k]

open FiniteTypeDimension in
/-- A morphism with finite residue field extension at `x` preserves the residue transcendence
degree over `k` at `x`. -/
theorem resTrdeg_comp_of_finite (sY : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X)
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f.base x)) (X.residueField x)) :
    resTrdeg (f ≫ sY) x = resTrdeg sY (f.base x) := by
  let K := Y.residueField (f.base x)
  let L := X.residueField x
  let _ : Algebra k K := (residueMap sY (f.base x)).toAlgebra
  let _ : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra k L := (residueMap (f ≫ sY) x).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun c ↦
    (residueFieldMap_residueMap sY f x c).symm
  have : Module.Finite K L := h
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have h' := trdeg_add_eq k K (A := L)
  rw [trdeg_eq_zero (R := K) (A := L), add_zero] at h'
  change Cardinal.toENat (Algebra.trdeg k L) = Cardinal.toENat (Algebra.trdeg k K)
  rw [h']

/-- For schemes locally of finite type over a field, a morphism with finite residue field
extension at `x` preserves the (certified) dimension at `x`. -/
theorem dim_eq_of_residue_finite (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (dimX : DimensionFunction X)
    (dimY : DimensionFunction Y) (x : X)
    (h : letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (f.base x)) (X.residueField x)) :
    dimX x = dimY (f.base x) := by
  rw [ProperPushforwardDivisor.dimensionFunction_eq dimX
      (FiniteTypeDimension.dimensionFunction (f ≫ sY)),
    ProperPushforwardDivisor.dimensionFunction_eq dimY
      (FiniteTypeDimension.dimensionFunction sY),
    FiniteTypeDimension.dimensionFunction_apply, FiniteTypeDimension.dimensionFunction_apply,
    resTrdeg_comp_of_finite sY f x h]

/-- For schemes locally of finite type over a field, the residue norm along a morphism vanishes
(is `1`) at every point where the morphism drops the dimension. -/
theorem residueUnitNorm_eq_one_of_dim_ne (sY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (dimX : DimensionFunction X)
    (dimY : DimensionFunction Y) (x : X) (hx : dimX x ≠ dimY (f.base x))
    (a : (X.residueField x)ˣ) : residueUnitNorm f x a = 1 :=
  residueUnitNorm_eq_one_of_not_finite f x
    (fun h ↦ hx (dim_eq_of_residue_finite sY f dimX dimY x h)) a

end Dimension

/-! ## The norm generator of a generator, in point form -/

section NormImage

variable {X Y : Scheme.{u}}

/-- The residue function of the norm generator `(f(W), N φ)` is the residue norm of the residue
function of `(W, φ)`, after identifying the generic point of `f(W)` with `f w`. -/
theorem residueFunction_normImage (g : RationalFunctionGenerator X) (f : X ⟶ Y) [QuasiCompact f]
    [IsLocallyNoetherian Y] :
    Units.map (Y.residueFieldCongr
        (g.subspace.genericPointImage_properImage f)).hom.hom.toMonoidHom
      (g.normImage f).residueFunction =
      residueUnitNorm f g.subspace.genericPointImage g.residueFunction := by
  set W := g.subspace
  set W' := W.properImage f
  have h := W.genericPointImage_properImage f
  let _ := (f.residueFieldMap W.genericPointImage).hom.toAlgebra
  let e₁ : W'.scheme.functionField ≃+* Y.residueField (f.base W.genericPointImage) :=
    W'.functionFieldEquivResidueField.trans (Y.residueFieldCongr h).commRingCatIsoToRingEquiv
  let e₂ : W.scheme.functionField ≃+* X.residueField W.genericPointImage :=
    W.functionFieldEquivResidueField
  have he : (algebraMap (Y.residueField (f.base W.genericPointImage))
        (X.residueField W.genericPointImage)).comp (e₁ : _ →+* _) =
      (e₂ : _ →+* _).comp (algebraMap W'.scheme.functionField W.scheme.functionField) := by
    ext x
    have hc := IntegralClosedSubscheme.functionFieldIso_comm f W W' (W.toProperImage f)
      (W.toProperImage_inclusion f) x
    exact hc.symm
  have hn := Algebra.norm_eq_of_equiv_equiv e₁ e₂ he (g.function : W.scheme.functionField)
  apply Units.ext
  rw [coe_residueUnitNorm]
  change e₁ (Algebra.norm W'.scheme.functionField (g.function : W.scheme.functionField)) = _
  rw [hn, RingEquiv.apply_symm_apply]
  rfl

variable [IsLocallyNoetherian Y] [NoetherianSpace Y]

/-- The divisor of the norm generator of a generator `(W, φ)` is the divisor of the point
generator at `f w` of the residue norm of the residue function of `(W, φ)`. -/
theorem divisor_normImage_eq_pointGenerator (dimY : DimensionFunction Y)
    (g : RationalFunctionGenerator X) (f : X ⟶ Y) [QuasiCompact f] :
    (g.normImage f).divisor dimY =
      (pointGenerator (f.base g.subspace.genericPointImage)
        (residueUnitNorm f g.subspace.genericPointImage g.residueFunction)).divisor dimY := by
  calc (g.normImage f).divisor dimY
      = (pointGenerator _ (g.normImage f).residueFunction).divisor dimY :=
        (divisor_pointGenerator dimY _).symm
    _ = (pointGenerator (f.base g.subspace.genericPointImage)
          (Units.map (Y.residueFieldCongr
            (g.subspace.genericPointImage_properImage f)).hom.hom.toMonoidHom
            (g.normImage f).residueFunction)).divisor dimY :=
        (divisor_pointGenerator_congr dimY _ _).symm
    _ = _ := by rw [residueFunction_normImage]

/-- The divisor of the norm generator of a point generator. -/
theorem divisor_normImage_pointGenerator [IsLocallyNoetherian X] [NoetherianSpace X]
    (dimY : DimensionFunction Y)
    (f : X ⟶ Y) [QuasiCompact f] (w : X) (φ : (X.residueField w)ˣ) :
    ((pointGenerator w φ).normImage f).divisor dimY =
      (pointGenerator (f.base w) (residueUnitNorm f w φ)).divisor dimY := by
  rw [divisor_normImage_eq_pointGenerator]
  have hw := genericPointImage_pointGenerator w φ
  have hres := residueFunction_pointGenerator w φ
  conv_rhs => rw [← hres, residueUnitNorm_residueFieldCongr f hw]
  rw [divisor_pointGenerator_congr]

end NormImage

/-! ## Proper pushforward of the divisor of a point generator -/

section PointDivisor

variable {X Y : Scheme.{u}}

/-- `pointDivisor` of the trivial unit vanishes. -/
theorem pointDivisor_one_eq_zero [IsLocallyNoetherian X] [NoetherianSpace X]
    (dim : DimensionFunction X) (w : X) : pointDivisor dim w 1 = 0 := by
  rw [pointDivisor_eq, divisor_pointGenerator_one]

/-- `pointDivisor` is additive in the unit. -/
theorem pointDivisor_mul [IsLocallyNoetherian X] [NoetherianSpace X]
    (dim : DimensionFunction X) (w : X) (a b : (X.residueField w)ˣ) :
    pointDivisor dim w (a * b) = pointDivisor dim w a + pointDivisor dim w b := by
  have h := divisor_pointGenerator_sub dim w (a * b) b
  rw [mul_div_cancel_right] at h
  rw [pointDivisor_eq, pointDivisor_eq, pointDivisor_eq, ← h, sub_add_cancel]

/-- `pointDivisor` sends finite products of units to sums. -/
theorem pointDivisor_prod [IsLocallyNoetherian X] [NoetherianSpace X]
    (dim : DimensionFunction X) (w : X) {ι : Type*} (s : Finset ι)
    (t : ι → (X.residueField w)ˣ) :
    pointDivisor dim w (∏ j ∈ s, t j) = ∑ j ∈ s, pointDivisor dim w (t j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pointDivisor_one_eq_zero]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, pointDivisor_mul, ih]

/-- `pointDivisor` is invariant under transport along an equality of points. -/
theorem pointDivisor_residueFieldCongr (dim : DimensionFunction X) {x x' : X} (h : x = x')
    (a : (X.residueField x)ˣ) :
    pointDivisor dim x' (Units.map (X.residueFieldCongr h).hom.hom.toMonoidHom a) =
      pointDivisor dim x a := by
  subst h
  rfl

variable {k : Type u} [Field k]

/-- **Proper pushforward of the divisor of a point generator** (Fulton, Prop. 1.4 (b), in point
form).  Let `f : X ⟶ Y` be proper, `Y` locally of finite type over a field `k` (so `X` is too,
through `f`), and the underlying space of `Y` Noetherian (then so is that of `X`).  For every
point `w` of `X` and unit `φ ∈ κ(w)ˣ`, the residue-degree pushforward of `div(φ)` on `closure {w}`
is `div(N φ)` on `closure {f w}`, where `N : κ(w)ˣ → κ(f w)ˣ` is the residue norm (`1` when
`κ(w)/κ(f w)` is not finite, in particular whenever `f` drops the dimension at `w`). -/
theorem map_pointDivisor (f : X ⟶ Y) [IsProper f] (sY : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sY] [NoetherianSpace Y]
    (dimX : DimensionFunction X) (dimY : DimensionFunction Y) (w : X)
    (φ : (X.residueField w)ˣ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map f dimX dimY (pointDivisor dimX w φ) =
      pointDivisor dimY (f.base w) (residueUnitNorm f w φ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  rw [pointDivisor_eq, pointDivisor_eq]
  have hgen := genericPointImage_pointGenerator w φ
  rcases eq_or_lt_of_le (dimX.apply_le_of_isProper dimY f w) with heq | hlt
  · rw [ProperPushforwardDivisor.map_divisor_of_dim_eq f dimX dimY (f ≫ sY) sY _
      (by rw [hgen]; exact heq), divisor_normImage_pointGenerator]
  · rw [residueUnitNorm_eq_one_of_dim_ne sY f dimX dimY w hlt.ne' φ,
      divisor_pointGenerator_one]
    rcases eq_or_lt_of_le (Int.le_sub_one_of_lt hlt) with heq1 | hlt2
    · exact ProperPushforwardCurve.map_divisor_eq_zero_of_dim_eq_sub_one f dimX dimY (f ≫ sY)
        sY _ (by rw [hgen]; exact heq1)
    · exact properPushforward_divisor_eq_zero_of_dim_le f (f ≫ sY) _ (by rw [hgen]; omega)

end PointDivisor

/-! ## Norm pushforward of a finitely supported family of residue units -/

section NormPushFamily

variable {X Y : Scheme.{u}}

open scoped Classical in
/-- **The norm pushforward of a family of residue units** supported on a finite set `S`: at
`y`, the product over the points `x ∈ S` with `f x = y` of the residue norms of `a x`. -/
noncomputable def normPushFamily (f : X ⟶ Y) (S : Finset X)
    (a : ∀ x : X, (X.residueField x)ˣ) (y : Y) : (Y.residueField y)ˣ :=
  ∏ x ∈ S, if h : f.base x = y then residueUnitNormTo f h (a x) else 1

open scoped Classical in
/-- The norm pushforward is trivial away from the image of the index set. -/
theorem normPushFamily_eq_one_of_not_mem (f : X ⟶ Y) (S : Finset X)
    (a : ∀ x : X, (X.residueField x)ˣ) {y : Y} (hy : y ∉ S.image f.base) :
    normPushFamily f S a y = 1 := by
  refine Finset.prod_eq_one fun x hx ↦ ?_
  rw [dif_neg]
  exact fun h ↦ hy (Finset.mem_image.2 ⟨x, hx, h⟩)

/-- If the norm pushforward is nontrivial at `y`, some `x ∈ S` over `y` has a nontrivial residue
norm. -/
theorem exists_of_normPushFamily_ne_one (f : X ⟶ Y) (S : Finset X)
    (a : ∀ x : X, (X.residueField x)ˣ) {y : Y} (hy : normPushFamily f S a y ≠ 1) :
    ∃ x ∈ S, f.base x = y ∧ residueUnitNorm f x (a x) ≠ 1 := by
  classical
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_one_of_prod_ne_one hy
  by_cases h : f.base x = y
  · refine ⟨x, hx, h, fun h1 ↦ hne ?_⟩
    rw [dif_pos h, residueUnitNormTo, MonoidHom.comp_apply, h1, map_one]
  · exact absurd (dif_neg h) hne

variable [IsLocallyNoetherian Y] [NoetherianSpace Y]

/-- The divisor of the point generator of a norm pushforward, summed over a finite set
containing the image of the index set, is the sum of the divisors of the residue norms. -/
theorem sum_pointDivisor_normPushFamily (dimY : DimensionFunction Y) (f : X ⟶ Y) (S : Finset X)
    (a : ∀ x : X, (X.residueField x)ˣ) (T : Finset Y) (hT : ∀ x ∈ S, f.base x ∈ T) :
    ∑ y ∈ T, pointDivisor dimY y (normPushFamily f S a y) =
      ∑ x ∈ S, pointDivisor dimY (f.base x) (residueUnitNorm f x (a x)) := by
  classical
  have hterm : ∀ y : Y, ∀ x : X,
      pointDivisor dimY y (if h : f.base x = y then residueUnitNormTo f h (a x) else 1) =
        if f.base x = y then pointDivisor dimY (f.base x) (residueUnitNorm f x (a x)) else 0 := by
    intro y x
    split_ifs with h
    · exact pointDivisor_residueFieldCongr dimY h _
    · exact pointDivisor_one_eq_zero dimY y
  simp only [normPushFamily, pointDivisor_prod, hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (hT x hx)]

end NormPushFamily

/-! ## Cartesian morphisms of étale presentation groupoids -/

/-- **A cartesian morphism of étale presentation groupoids** `H → G`: maps of atlases and of
arrow schemes commuting with the source and target maps, such that both squares
`H.arrows → G.arrows` over `H.base → G.base` (via the sources, resp. the targets) are cartesian:
the arrow scheme of `H` is the base change of the arrow scheme of `G` along the map of atlases,
in both ways.  No condition on the map of atlases is imposed; properness, resp. étaleness, of
`onBase` is assumed separately where needed. -/
structure CartesianGroupoidMap (H G : EtalePresentationGroupoid.{u}) where
  /-- The map of atlases. -/
  onBase : H.base ⟶ G.base
  /-- The map of arrow schemes. -/
  onArrows : H.arrows ⟶ G.arrows
  /-- Compatibility with the source maps. -/
  src_comm : onArrows ≫ G.src = H.src ≫ onBase
  /-- Compatibility with the target maps. -/
  tgt_comm : onArrows ≫ G.tgt = H.tgt ≫ onBase
  /-- The source square is cartesian. -/
  isPullback_src : IsPullback onArrows H.src G.src onBase
  /-- The target square is cartesian. -/
  isPullback_tgt : IsPullback onArrows H.tgt G.tgt onBase

namespace CartesianGroupoidMap

variable {H G : EtalePresentationGroupoid.{u}} (Φ : CartesianGroupoidMap H G)

/-- The map of atlases intertwines the source maps on points. -/
theorem onBase_src_apply (r' : H.arrows) :
    Φ.onBase.base (H.src.base r') = G.src.base (Φ.onArrows.base r') := by
  have h := congrArg (fun f : H.arrows ⟶ G.base ↦ f.base r') Φ.src_comm
  simpa using h.symm

/-- The map of atlases intertwines the target maps on points. -/
theorem onBase_tgt_apply (r' : H.arrows) :
    Φ.onBase.base (H.tgt.base r') = G.tgt.base (Φ.onArrows.base r') := by
  have h := congrArg (fun f : H.arrows ⟶ G.base ↦ f.base r') Φ.tgt_comm
  simpa using h.symm

/-- The map of arrow schemes is proper when the map of atlases is (base change). -/
theorem isProper_onArrows [IsProper Φ.onBase] : IsProper Φ.onArrows :=
  MorphismProperty.of_isPullback (P := @IsProper) Φ.isPullback_src.flip ‹_›

/-- The map of arrow schemes is étale when the map of atlases is (base change). -/
theorem etale_onArrows [Etale Φ.onBase] : Etale Φ.onArrows :=
  MorphismProperty.of_isPullback (P := @Etale) Φ.isPullback_src.flip ‹_›

end CartesianGroupoidMap

/-! ## Étale base change of norms and of proper pushforward -/

section BaseChange

/-! ### Transport along isomorphisms -/

section Iso

variable {W P Z : Scheme.{u}}

/-- The residue norm along `e ≫ φ` for an isomorphism `e`, at `w`, of the image of a unit of
`κ(e w)`, is the residue norm along `φ` at `e w`. -/
theorem residueUnitNorm_iso_comp (e : W ≅ P) (φ : P ⟶ Z) (w : W)
    (c : (P.residueField (e.hom.base w))ˣ) :
    residueUnitNorm (e.hom ≫ φ) w (Units.map (e.hom.residueFieldMap w).hom.toMonoidHom c) =
      residueUnitNorm φ (e.hom.base w) c := by
  apply Units.ext
  rw [coe_residueUnitNorm, coe_residueUnitNorm]
  let _ : Algebra (Z.residueField (φ.base (e.hom.base w))) (W.residueField w) :=
    ((e.hom ≫ φ).residueFieldMap w).hom.toAlgebra
  let _ : Algebra (Z.residueField (φ.base (e.hom.base w))) (P.residueField (e.hom.base w)) :=
    (φ.residueFieldMap (e.hom.base w)).hom.toAlgebra
  let e₂ : P.residueField (e.hom.base w) ≃+* W.residueField w :=
    (asIso (e.hom.residueFieldMap w)).commRingCatIsoToRingEquiv
  have he : (algebraMap (Z.residueField (φ.base (e.hom.base w))) (W.residueField w)).comp
        ((RingEquiv.refl _ : Z.residueField (φ.base (e.hom.base w)) ≃+* _) : _ →+* _) =
      (e₂ : _ →+* _).comp (algebraMap (Z.residueField (φ.base (e.hom.base w)))
        (P.residueField (e.hom.base w))) := by
    ext x
    change ((e.hom ≫ φ).residueFieldMap w).hom x =
      (e.hom.residueFieldMap w).hom ((φ.residueFieldMap (e.hom.base w)).hom x)
    rw [Scheme.residueFieldMap_comp]
    rfl
  have h := Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl _) e₂ he (c : P.residueField _)
  exact h.symm

open scoped Classical in
/-- The norm pushforward along `e ≫ φ`, for an isomorphism `e`, of the pullback along `e` of a
family is the norm pushforward along `φ` of the family, over the image index set. -/
theorem normPushFamily_iso_comp (e : W ≅ P) (φ : P ⟶ Z) (T : Finset W)
    (b : ∀ p : P, (P.residueField p)ˣ) (z : Z) :
    normPushFamily (e.hom ≫ φ) T (unitPull e.hom b) z =
      normPushFamily φ (T.image e.hom.base) b z := by
  unfold normPushFamily
  rw [Finset.prod_image fun x _ y _ hxy ↦ e.hom.isOpenEmbedding.injective hxy]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  by_cases hw : φ.base (e.hom.base w) = z
  · rw [dif_pos hw, dif_pos (show (e.hom ≫ φ).base w = z from hw)]
    apply Units.ext
    simp only [residueUnitNormTo, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map]
    congr 2
    exact residueUnitNorm_iso_comp e φ w (b (e.hom.base w))
  · rw [dif_neg hw, dif_neg (show ¬ (e.hom ≫ φ).base w = z from hw)]

/-- Residue-degree pushforward along an isomorphism undoes étale pullback along it. -/
theorem map_pullbackEtale_iso (e : W ≅ P) (dimW : DimensionFunction W)
    (dimP : DimensionFunction P) (c : AlgebraicCycle P ℚ) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map e.hom dimW dimP
      (AlgebraicCycle.pullbackEtale e.hom c) = c := by
  have hdim : (dimW : W → ℤ) = fun w ↦ (dimP : P → ℤ) (e.hom.base w) := by
    funext w
    exact DimensionFunction.apply_eq_of_isClosedImmersion dimW dimP e.hom w
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  have hp : e.hom.base (e.inv.base p) = p := Scheme.inv_hom_apply e p
  have hval := AlgebraicCycle.map_closedImmersion_apply_image e.hom (dimP : P → ℤ)
    (AlgebraicCycle.pullbackEtale e.hom c) (e.inv.base p)
  rw [hp, AlgebraicCycle.pullbackEtale_apply, hp] at hval
  rw [hdim]
  exact hval

end Iso

variable {U V U' V' : Scheme.{u}} {g' : U' ⟶ U} {f' : U' ⟶ V'} {f : U ⟶ V} {g : V' ⟶ V}

open scoped Classical in
/-- **Étale base change of the norm pushforward, from its pointwise form.**  For a commutative
square `g' ≫ f = f' ≫ g` whose fibres over pairs `(u, v')` are finite and which satisfies the
pointwise base change formula for residue norms, pulling back the norm pushforward of a finitely
supported family `a` along `g` gives, at `v'`, the norm pushforward along `f'` of the pullback of
`a` along `g'`, over any finite index set `T` containing the points over `S` and `v'`. -/
theorem unitPull_normPushFamily_of_pointwise (hw : g' ≫ f = f' ≫ g)
    (hfin : ∀ (u : U) (v' : V'), {u' : U' | g'.base u' = u ∧ f'.base u' = v'}.Finite)
    (hpw : ∀ (a : ∀ x : U, (U.residueField x)ˣ) (u : U) (v' : V') (hv : f.base u = g.base v'),
      Units.map (g.residueFieldMap v').hom.toMonoidHom (residueUnitNormTo f hv (a u)) =
        ∏ u' ∈ (hfin u v').toFinset,
          if h' : f'.base u' = v' then residueUnitNormTo f' h' (unitPull g' a u') else 1)
    (S : Finset U) (a : ∀ x : U, (U.residueField x)ˣ) (ha : ∀ x ∉ S, a x = 1) (v' : V')
    (T : Finset U') (hT : ∀ u', g'.base u' ∈ S → f'.base u' = v' → u' ∈ T) :
    unitPull g (normPushFamily f S a) v' = normPushFamily f' T (unitPull g' a) v' := by
  have hpt : ∀ u', f.base (g'.base u') = g.base (f'.base u') := fun u' ↦ by
    have := congrArg (fun φ : U' ⟶ V ↦ φ.base u') hw
    simpa using this
  set t : U' → (V'.residueField v')ˣ := fun u' ↦
    if h' : f'.base u' = v' then residueUnitNormTo f' h' (unitPull g' a u') else 1 with ht_def
  have ht1 : ∀ u', t u' ≠ 1 → g'.base u' ∈ S ∧ f'.base u' = v' := by
    intro u' hu'
    by_contra hP
    refine hu' ?_
    simp only [ht_def]
    split_ifs with h'
    · have hS : g'.base u' ∉ S := fun hs ↦ hP ⟨hs, h'⟩
      rw [show unitPull g' a u' = 1 from (unitPull_eq_one_iff g' a u').2 (ha _ hS), map_one]
    · rfl
  have hR : normPushFamily f' T (unitPull g' a) v' =
      ∏ u ∈ S.filter (fun u ↦ f.base u = g.base v'),
        ∏ u' ∈ (T.filter fun u' ↦ g'.base u' ∈ S ∧ f'.base u' = v').filter
          (fun u' ↦ g'.base u' = u), t u' := by
    have hmaps : ∀ u' ∈ T.filter (fun u' ↦ g'.base u' ∈ S ∧ f'.base u' = v'),
        g'.base u' ∈ S.filter (fun u ↦ f.base u = g.base v') := by
      intro u' hu'
      rw [Finset.mem_filter] at hu' ⊢
      exact ⟨hu'.2.1, by rw [← hu'.2.2, hpt]⟩
    calc normPushFamily f' T (unitPull g' a) v' = ∏ u' ∈ T, t u' := rfl
      _ = ∏ u' ∈ T.filter (fun u' ↦ g'.base u' ∈ S ∧ f'.base u' = v'), t u' :=
        (Finset.prod_filter_of_ne fun u' _ hu' ↦ ht1 u' hu').symm
      _ = _ := (Finset.prod_fiberwise_of_maps_to hmaps t).symm
  have hfib : ∀ u ∈ S.filter (fun u ↦ f.base u = g.base v'),
      (T.filter fun u' ↦ g'.base u' ∈ S ∧ f'.base u' = v').filter (fun u' ↦ g'.base u' = u) =
        (hfin u v').toFinset := by
    intro u hu
    rw [Finset.mem_filter] at hu
    ext u'
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨-, -, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩
      exact ⟨⟨hT u' (h3 ▸ hu.1) h2, h3 ▸ hu.1, h2⟩, h3⟩
  rw [hR, Finset.prod_congr rfl fun u hu ↦ by rw [hfib u hu], Finset.prod_filter]
  change Units.map (g.residueFieldMap v').hom.toMonoidHom (normPushFamily f S a (g.base v')) = _
  rw [normPushFamily, map_prod]
  refine Finset.prod_congr rfl fun u _ ↦ ?_
  split_ifs with hv
  · exact hpw a u v' hv
  · exact map_one _

section PullbackForms

open Limits

variable (f g)

/-- Transport of a family of residue units along an equality of points, inverse form. -/
theorem residueFieldCongr_inv_apply_family {X : Scheme.{u}} {x y : X} (h : x = y)
    (a : ∀ x : X, (X.residueField x)ˣ) :
    (X.residueFieldCongr h).inv.hom (a y : X.residueField y) = a x := by
  subst h
  rfl

open scoped Classical in
/-- **Étale base change of residue norms, units form** (from E-geo's
`norm_residueFieldMap_eq_prod`). -/
theorem units_map_residueUnitNormTo_pullback [FormallyUnramified g] [LocallyOfFiniteType g]
    (a : ∀ x : U, (U.residueField x)ˣ) (u : U) (v' : V') (hv : f.base u = g.base v') :
    Units.map (g.residueFieldMap v').hom.toMonoidHom (residueUnitNormTo f hv (a u)) =
      ∏ p ∈ (finite_fibre_pair f g u v').toFinset,
        if h' : (pullback.snd f g).base p = v' then
          residueUnitNormTo (pullback.snd f g) h' (unitPull (pullback.fst f g) a p)
        else 1 := by
  apply Units.ext
  rw [Units.coe_map, Units.coe_prod]
  change (g.residueFieldMap v').hom ((V.residueFieldCongr hv).hom.hom
      (residueUnitNorm f u (a u) : V.residueField (f.base u))) = _
  rw [coe_residueUnitNorm]
  refine (norm_residueFieldMap_eq_prod f g hv (a u : U.residueField u)).trans ?_
  change _ = ∏ p ∈ fibrePair f g u v', _
  rw [← Finset.prod_attach (fibrePair f g u v')]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  have hp := (mem_fibrePair f g).1 p.2
  rw [dif_pos hp.2]
  change _ = (V'.residueFieldCongr hp.2).hom.hom
      (residueUnitNorm (pullback.snd f g) p.1 (unitPull (pullback.fst f g) a p.1) :
        V'.residueField ((pullback.snd f g).base p.1))
  rw [coe_residueUnitNorm]
  have hx : (pullback.fst f g).residueFieldMap p.1
      ((U.residueFieldCongr hp.1).inv (a u : U.residueField u)) =
        (unitPull (pullback.fst f g) a p.1 : (pullback f g).residueField p.1) := by
    change _ = ((pullback.fst f g).residueFieldMap p.1).hom
      (a ((pullback.fst f g).base p.1) : U.residueField ((pullback.fst f g).base p.1))
    rw [← residueFieldCongr_inv_apply_family hp.1 a]
  simp only [hx]

end PullbackForms


/-! ### Arbitrary cartesian squares -/

/-- Étale base change of the norm pushforward for Mathlib's fibre product. -/
theorem unitPull_normPushFamily_pullback [Etale g] (S : Finset U)
    (a : ∀ x : U, (U.residueField x)ˣ) (ha : ∀ x ∉ S, a x = 1) (v' : V')
    (T : Finset ↑(Limits.pullback f g))
    (hT : ∀ p, (Limits.pullback.fst f g).base p ∈ S → (Limits.pullback.snd f g).base p = v' →
      p ∈ T) :
    unitPull g (normPushFamily f S a) v' =
      normPushFamily (Limits.pullback.snd f g) T (unitPull (Limits.pullback.fst f g) a) v' :=
  unitPull_normPushFamily_of_pointwise Limits.pullback.condition (finite_fibre_pair f g)
    (units_map_residueUnitNormTo_pullback f g) S a ha v' T hT

open scoped Classical in
/-- Étale base change of the norm pushforward, for a fibre product presented by an isomorphism
with Mathlib's fibre product. -/
theorem unitPull_normPushFamily_of_iso [Etale g]
    (e : U' ≅ Limits.pullback f g) (hfst : e.hom ≫ Limits.pullback.fst f g = g')
    (hsnd : e.hom ≫ Limits.pullback.snd f g = f') (S : Finset U)
    (a : ∀ x : U, (U.residueField x)ˣ) (ha : ∀ x ∉ S, a x = 1) (v' : V')
    (T : Finset U') (hT : ∀ u', g'.base u' ∈ S → f'.base u' = v' → u' ∈ T) :
    unitPull g (normPushFamily f S a) v' = normPushFamily f' T (unitPull g' a) v' := by
  subst hfst hsnd
  rw [show unitPull (e.hom ≫ Limits.pullback.fst f g) a =
      unitPull e.hom (unitPull (Limits.pullback.fst f g) a) from
        funext (unitPull_comp _ _ a),
    normPushFamily_iso_comp]
  refine unitPull_normPushFamily_pullback (f := f) (g := g) S a ha v' _ fun p hp1 hp2 ↦ ?_
  have hp : e.hom.base (e.inv.base p) = p := Scheme.inv_hom_apply e p
  refine Finset.mem_image.2 ⟨e.inv.base p, hT _ ?_ ?_, hp⟩
  · change (Limits.pullback.fst f g).base (e.hom.base (e.inv.base p)) ∈ S
    rwa [hp]
  · change (Limits.pullback.snd f g).base (e.hom.base (e.inv.base p)) = v'
    rwa [hp]

/-- **Étale base change of the norm pushforward** (blueprint E2, the computation behind
Theorem E2).  For a cartesian square `g' ≫ f = f' ≫ g` with `g` étale, and a
family `a` of residue units supported in a finite set `S`, pulling back the norm pushforward of
`a` along `g` gives, at `v'`, the norm pushforward along `f'` of the pullback of `a` along `g'`,
computed with any finite index set `T` containing the points over `S` and `v'`. -/
theorem unitPull_normPushFamily_of_isPullback (h : IsPullback g' f' f g) [Etale g]
    (S : Finset U) (a : ∀ x : U, (U.residueField x)ˣ) (ha : ∀ x ∉ S, a x = 1) (v' : V')
    (T : Finset U') (hT : ∀ u', g'.base u' ∈ S → f'.base u' = v' → u' ∈ T) :
    unitPull g (normPushFamily f S a) v' = normPushFamily f' T (unitPull g' a) v' :=
  unitPull_normPushFamily_of_iso h.isoPullback h.isoPullback_hom_fst h.isoPullback_hom_snd S a
    ha v' T hT

/-- Étale base change of proper pushforward, for a fibre product presented by an isomorphism
with Mathlib's fibre product. -/
theorem pullbackEtale_map_of_iso [QuasiCompact f] [QuasiCompact f'] [Etale g] [Etale g']
    (e : U' ≅ Limits.pullback f g) (hfst : e.hom ≫ Limits.pullback.fst f g = g')
    (hsnd : e.hom ≫ Limits.pullback.snd f g = f') (dimU : DimensionFunction U)
    (dimV : DimensionFunction V) (dimU' : DimensionFunction U') (dimV' : DimensionFunction V')
    (hU' : ∀ u', dimU' u' = dimU (g'.base u')) (hV' : ∀ v', dimV' v' = dimV (g.base v'))
    (z : AlgebraicCycle U ℚ) :
    AlgebraicCycle.pullbackEtale g (_root_.AlgebraicGeometry.AlgebraicCycle.map f dimU dimV z) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map f' dimU' dimV'
        (AlgebraicCycle.pullbackEtale g' z) := by
  subst hfst hsnd
  let dimP := DimensionFunction.comapClosedImmersion e.inv dimU'
  have hP : ∀ p, dimP p = dimU ((Limits.pullback.fst f g).base p) := by
    intro p
    have hp : e.hom.base (e.inv.base p) = p := Scheme.inv_hom_apply e p
    change dimU' (e.inv.base p) = _
    rw [hU']
    change dimU ((Limits.pullback.fst f g).base (e.hom.base (e.inv.base p))) = _
    rw [hp]
  rw [pullbackEtale_map f g dimU dimV dimP dimV' hP hV' z,
    ← AlgebraicCycle.map_comp_of_between e.hom (Limits.pullback.snd f g) dimU' dimP dimV'
      (fun w _ ↦ DimensionFunction.apply_eq_of_isClosedImmersion dimU' dimP e.hom w)]
  congr 1
  rw [← map_pullbackEtale_iso e dimU' dimP
    (AlgebraicCycle.pullbackEtale (Limits.pullback.fst f g) z)]
  rfl

/-- **Étale base change of proper pushforward** (blueprint E1, for an arbitrary cartesian
square): `g^* f_* z = f'_* g'^* z` for `f` quasi-compact (e.g. proper), `g` étale and dimension
functions compatible with the étale maps. -/
theorem pullbackEtale_map_of_isPullback (h : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiCompact f'] [Etale g] [Etale g'] (dimU : DimensionFunction U) (dimV : DimensionFunction V)
    (dimU' : DimensionFunction U') (dimV' : DimensionFunction V')
    (hU' : ∀ u', dimU' u' = dimU (g'.base u')) (hV' : ∀ v', dimV' v' = dimV (g.base v'))
    (z : AlgebraicCycle U ℚ) :
    AlgebraicCycle.pullbackEtale g (_root_.AlgebraicGeometry.AlgebraicCycle.map f dimU dimV z) =
      _root_.AlgebraicGeometry.AlgebraicCycle.map f' dimU' dimV'
        (AlgebraicCycle.pullbackEtale g' z) :=
  pullbackEtale_map_of_iso h.isoPullback h.isoPullback_hom_fst h.isoPullback_hom_snd dimU dimV
    dimU' dimV' hU' hV' z

end BaseChange

/-! ## Norm pushforward of invariant systems -/

namespace InvariantSystem

variable {H G : EtalePresentationGroupoid.{u}} {i : ℤ} {k : Type u} [Field k]

open scoped Classical in
/-- **The norm pushforward of an invariant system along a cartesian morphism whose map of atlases
is locally of finite type** (e.g. proper; blueprint E2).  At a point `v` of the atlas of `G` its
value is the product, over the points `w` of the support of `F` lying over `v`, of the residue
norms `N_{κ(w)/κ(v)} (F w)` (trivial when `κ(w)/κ(v)` is not finite).  The dimension of the
support uses that the atlas of `G` is locally of finite type over a field `k`; the invariance
(Theorem E2) uses that the arrow scheme of `H` is quasi-compact and the étale base change of
residue norms. -/
noncomputable def normPush (F : InvariantSystem H i) (Φ : CartesianGroupoidMap H G)
    [LocallyOfFiniteType Φ.onBase] (sG : G.base ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sG] (hH : H.Good) : InvariantSystem G i where
  support := (F.support.image Φ.onBase.base).filter
    fun v ↦ normPushFamily Φ.onBase F.support F.value v ≠ 1
  value := normPushFamily Φ.onBase F.support F.value
  mem_support_iff v := by
    rw [Finset.mem_filter]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    by_contra hv
    exact h (normPushFamily_eq_one_of_not_mem _ _ _ hv)
  dim_support v hv := by
    obtain ⟨w, hw, hwv, hne⟩ :=
      exists_of_normPushFamily_ne_one _ _ _ (Finset.mem_filter.1 hv).2
    have hdim : H.baseDim w = G.baseDim (Φ.onBase.base w) := by
      by_contra hd
      exact hne (residueUnitNorm_eq_one_of_dim_ne sG Φ.onBase H.baseDim G.baseDim w hd _)
    rw [← hwv, ← hdim]
    exact F.dim_support w hw
  invariant r := by
    change unitPull G.src (normPushFamily Φ.onBase F.support F.value) r =
      unitPull G.tgt (normPushFamily Φ.onBase F.support F.value) r
    have := hH.compactSpace_arrows
    have ha : ∀ x ∉ F.support, F.value x = 1 := fun x hx ↦ by
      by_contra h
      exact hx ((F.mem_support_iff x).2 h)
    let T : Finset H.arrows :=
      (finite_preimage_of_etale_of_compactSpace H.src F.support.finite_toSet).toFinset ∪
        (finite_preimage_of_etale_of_compactSpace H.tgt F.support.finite_toSet).toFinset
    rw [unitPull_normPushFamily_of_isPullback Φ.isPullback_src.flip F.support F.value ha r T
        (fun r' h _ ↦ Finset.mem_union_left _ (by simpa using h)),
      unitPull_normPushFamily_of_isPullback Φ.isPullback_tgt.flip F.support F.value ha r T
        (fun r' h _ ↦ Finset.mem_union_right _ (by simpa using h)),
      show unitPull H.src F.value = unitPull H.tgt F.value from funext F.unitPull_src_eq]

variable (F : InvariantSystem H i) (Φ : CartesianGroupoidMap H G)
  (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG] (hH : H.Good)

variable [LocallyOfFiniteType Φ.onBase] in
/-- The values of the norm pushforward of an invariant system. -/
@[simp]
theorem normPush_value : (F.normPush Φ sG hH).value = normPushFamily Φ.onBase F.support F.value :=
  rfl

variable [LocallyOfFiniteType Φ.onBase] in
open scoped Classical in
/-- The support of the norm pushforward of an invariant system. -/
theorem normPush_support : (F.normPush Φ sG hH).support =
    (F.support.image Φ.onBase.base).filter
      fun v ↦ normPushFamily Φ.onBase F.support F.value v ≠ 1 :=
  rfl

/-- **Theorem E3: proper pushforward of the divisor of an invariant system.**  For a cartesian
morphism `Φ : H → G` with proper map of atlases, `H` and `G` satisfying the standing hypotheses
and the atlas of `G` locally of finite type over a field, the residue-degree pushforward of
`∑_w div (F w)` is `∑_v div ((N F) v)` for the norm pushforward `N F`. -/
theorem map_divisorCycle_normPush [IsProper Φ.onBase] (hG : G.Good) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim F.divisorCycle =
      (F.normPush Φ sG hH).divisorCycle := by
  classical
  have := hH.isNoetherian_base
  have := hG.isNoetherian_base
  have hmap : ∀ s : Finset H.base,
      _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim
          (∑ w ∈ s, pointDivisor H.baseDim w (F.value w)) =
        ∑ w ∈ s, _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim
          (pointDivisor H.baseDim w (F.value w)) := fun s ↦
    map_sum (AlgebraicCycle.mapLinear Φ.onBase H.baseDim G.baseDim) _ s
  rw [divisorCycle, divisorCycle, hmap,
    Finset.sum_congr rfl fun w _ ↦ map_pointDivisor Φ.onBase sG H.baseDim G.baseDim w (F.value w),
    normPush_support, normPush_value, Finset.sum_filter_of_ne, sum_pointDivisor_normPushFamily]
  · exact fun x hx ↦ Finset.mem_image_of_mem _ hx
  · intro v _ hv h1
    rw [h1, pointDivisor_one_eq_zero] at hv
    exact hv rfl

/-- **Theorem E3, graded form**: the proper pushforward of the divisor of an invariant system is
the divisor of its norm pushforward. -/
theorem properPushforward_divisor_normPush [IsProper Φ.onBase] (hG : G.Good) :
    cyclesOfDimension.properPushforward (dimension := H.baseDim) (dimensionY := G.baseDim)
        (i := i) Φ.onBase F.divisor = (F.normPush Φ sG hH).divisor := by
  apply Subtype.ext
  change _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim
      (F.divisor : AlgebraicCycle H.base ℚ) =
    ((F.normPush Φ sG hH).divisor : AlgebraicCycle G.base ℚ)
  rw [coe_divisor _ hH, coe_divisor _ hG, map_divisorCycle_normPush F Φ sG hH hG]

end InvariantSystem

/-! ## The Vistoli pushforward -/

namespace CartesianGroupoidMap

variable {H G : EtalePresentationGroupoid.{u}} (Φ : CartesianGroupoidMap H G) [IsProper Φ.onBase]
  (i : ℤ)

/-- **Proper pushforward along the map of atlases preserves Vistoli cycles** (blueprint E3.b.1,
from the étale base change of proper pushforward applied to both cartesian squares). -/
theorem properPushforward_mem_cycles {z : cyclesOfDimension H.base H.baseDim i}
    (hz : z ∈ H.cycles i) :
    cyclesOfDimension.properPushforward (dimension := H.baseDim) (dimensionY := G.baseDim)
      Φ.onBase z ∈ G.cycles i := by
  have := Φ.isProper_onArrows
  rw [EtalePresentationGroupoid.mem_cycles_iff] at hz ⊢
  intro r
  have hsrc := pullbackEtale_map_of_isPullback Φ.isPullback_src.flip H.baseDim G.baseDim
    H.arrowsDim G.arrowsDim H.src_dim G.src_dim (z : AlgebraicCycle H.base ℚ)
  have htgt := pullbackEtale_map_of_isPullback Φ.isPullback_tgt.flip H.baseDim G.baseDim
    H.arrowsDim G.arrowsDim H.tgt_dim G.tgt_dim (z : AlgebraicCycle H.base ℚ)
  have heq : AlgebraicCycle.pullbackEtale H.src (z : AlgebraicCycle H.base ℚ) =
      AlgebraicCycle.pullbackEtale H.tgt (z : AlgebraicCycle H.base ℚ) :=
    Function.locallyFinsuppWithin.ext fun r' ↦ hz r'
  have h1 := congrArg (fun c : AlgebraicCycle G.arrows ℚ ↦ c r) hsrc
  have h2 := congrArg (fun c : AlgebraicCycle G.arrows ℚ ↦ c r) htgt
  simp only [AlgebraicCycle.pullbackEtale_apply] at h1 h2
  change _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim
      (z : AlgebraicCycle H.base ℚ) (G.src.base r) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map Φ.onBase H.baseDim G.baseDim
      (z : AlgebraicCycle H.base ℚ) (G.tgt.base r)
  rw [h1, h2, heq]

/-- **Proper pushforward of Vistoli cycles** along a cartesian morphism with proper map of
atlases. -/
noncomputable def pushCycles : H.cycles i →ₗ[ℚ] G.cycles i :=
  (cyclesOfDimension.properPushforward (dimension := H.baseDim) (dimensionY := G.baseDim)
    (i := i) Φ.onBase).restrict fun _ hz ↦ Φ.properPushforward_mem_cycles i hz

/-- The proper pushforward of a Vistoli cycle is its proper pushforward on the atlas. -/
theorem coe_pushCycles (z : H.cycles i) :
    ((Φ.pushCycles i z : G.cycles i) : cyclesOfDimension G.base G.baseDim i) =
      cyclesOfDimension.properPushforward (dimension := H.baseDim) (dimensionY := G.baseDim)
        Φ.onBase (z : cyclesOfDimension H.base H.baseDim i) :=
  rfl

variable {k : Type u} [Field k]

/-- **Proper pushforward preserves the Vistoli relations** (blueprint E3.b.2): the pushforward
of the divisor of an invariant system is the divisor of its norm pushforward. -/
theorem vistoliRelations_le_comap_pushCycles (sG : G.base ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sG] (hH : H.Good) (hG : G.Good) :
    H.vistoliRelations i ≤ (G.vistoliRelations i).comap (Φ.pushCycles i) := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨F, hF⟩
  refine EtalePresentationGroupoid.mem_vistoliRelations_of_divisor _ (F.normPush Φ sG hH) ?_
  rw [coe_pushCycles, hF, F.properPushforward_divisor_normPush Φ sG hH hG]

/-- **The Vistoli pushforward** `A_i(H) → A_i(G)` along a cartesian morphism of étale
presentation groupoids with proper map of atlases, both groupoids satisfying the standing
hypotheses and the atlas of `G` locally of finite type over a field (blueprint E3.b.3). -/
noncomputable def vistoliPushforward (sG : G.base ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sG] (hH : H.Good) (hG : G.Good) :
    H.vistoliChow i →ₗ[ℚ] G.vistoliChow i :=
  (H.vistoliRelations i).mapQ (G.vistoliRelations i) (Φ.pushCycles i)
    (Φ.vistoliRelations_le_comap_pushCycles i sG hH hG)

/-- The Vistoli pushforward sends the class of a Vistoli cycle to the class of its proper
pushforward. -/
@[simp]
theorem vistoliPushforward_mk (sG : G.base ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sG] (hH : H.Good) (hG : G.Good) (z : H.cycles i) :
    Φ.vistoliPushforward i sG hH hG (H.vistoliQuotientMap i z) =
      G.vistoliQuotientMap i (Φ.pushCycles i z) :=
  rfl

end CartesianGroupoidMap

/-! ## Étale pullback on the Vistoli groups -/

namespace CartesianGroupoidMap

variable {H G : EtalePresentationGroupoid.{u}} (Φ : CartesianGroupoidMap H G) [Etale Φ.onBase]
  {k : Type u} [Field k]

/-- An étale map of atlases preserves the certified dimensions when the atlas of `G` is locally
of finite type over a field. -/
theorem baseDim_eq_of_etale (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG]
    (u : H.base) : H.baseDim u = G.baseDim (Φ.onBase.base u) :=
  dimensionFunction_apply_eq_of_etale sG Φ.onBase H.baseDim G.baseDim u

/-- Preimages of finite sets under an étale map of atlases with quasi-compact source are
finite. -/
theorem finite_preimage_of_etale (hH : H.Good) {A : Set G.base} (hA : A.Finite) :
    (Φ.onBase.base ⁻¹' A).Finite := by
  have := hH.compactSpace_base
  exact finite_preimage_of_etale_of_compactSpace Φ.onBase hA

variable (i : ℤ) (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG]

/-- Étale pullback along the map of atlases preserves Vistoli cycles (only the commutation of
the map of atlases with the source and target maps is used). -/
theorem flatPullbackEtale_mem_cycles {z : cyclesOfDimension G.base G.baseDim i}
    (hz : z ∈ G.cycles i) :
    cyclesOfDimension.flatPullbackEtale Φ.onBase (Φ.baseDim_eq_of_etale sG) z ∈ H.cycles i := by
  rw [EtalePresentationGroupoid.mem_cycles_iff] at hz ⊢
  intro r'
  simp only [cyclesOfDimension.flatPullbackEtale_apply]
  rw [Φ.onBase_src_apply, Φ.onBase_tgt_apply]
  exact hz _

/-- **Étale pullback of Vistoli cycles** along a cartesian morphism with étale map of
atlases. -/
noncomputable def pullCycles : G.cycles i →ₗ[ℚ] H.cycles i :=
  (cyclesOfDimension.flatPullbackEtale Φ.onBase (Φ.baseDim_eq_of_etale sG)).restrict
    fun _ hz ↦ Φ.flatPullbackEtale_mem_cycles i sG hz

/-- The étale pullback of a Vistoli cycle is its étale pullback on the atlas. -/
theorem coe_pullCycles (z : G.cycles i) :
    ((Φ.pullCycles i sG z : H.cycles i) : cyclesOfDimension H.base H.baseDim i) =
      cyclesOfDimension.flatPullbackEtale Φ.onBase (Φ.baseDim_eq_of_etale sG)
        (z : cyclesOfDimension G.base G.baseDim i) :=
  rfl

end CartesianGroupoidMap

namespace InvariantSystem

variable {H G : EtalePresentationGroupoid.{u}} {i : ℤ} {k : Type u} [Field k]

/-- **The étale pullback of an invariant system** along a cartesian morphism with étale map of
atlases (blueprint E4.2): the value at `u` is the image of the value at `onBase u` in `κ(u)`, and
the support is the (finite) preimage of the support. -/
noncomputable def etalePull (F : InvariantSystem G i) (Φ : CartesianGroupoidMap H G)
    [Etale Φ.onBase] (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG]
    (hH : H.Good) : InvariantSystem H i where
  support := (Φ.finite_preimage_of_etale hH F.support.finite_toSet).toFinset
  value := unitPull Φ.onBase F.value
  mem_support_iff u' := by
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe, F.mem_support_iff, ne_eq,
      ne_eq, unitPull_eq_one_iff]
  dim_support u' hu := by
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] at hu
    rw [Φ.baseDim_eq_of_etale sG]
    exact F.dim_support _ hu
  invariant r' := by
    change unitPull H.src (unitPull Φ.onBase F.value) r' =
      unitPull H.tgt (unitPull Φ.onBase F.value) r'
    rw [← unitPull_comp, ← unitPull_comp, ← unitPull_congr Φ.src_comm,
      ← unitPull_congr Φ.tgt_comm, unitPull_comp, unitPull_comp,
      show unitPull G.src F.value = unitPull G.tgt F.value from funext F.unitPull_src_eq]

variable (F : InvariantSystem G i) (Φ : CartesianGroupoidMap H G) [Etale Φ.onBase]
  (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG] (hH : H.Good)

/-- The values of the étale pullback of an invariant system. -/
@[simp]
theorem etalePull_value : (F.etalePull Φ sG hH).value = unitPull Φ.onBase F.value :=
  rfl

/-- The support of the étale pullback of an invariant system is the preimage of its support. -/
theorem mem_etalePull_support (u' : H.base) :
    u' ∈ (F.etalePull Φ sG hH).support ↔ Φ.onBase.base u' ∈ F.support :=
  Set.Finite.mem_toFinset _

/-- **The divisor of the étale pullback of an invariant system is the étale pullback of its
divisor** (blueprint E4.3), under the standing hypotheses on both groupoids. -/
theorem flatPullbackEtale_divisor_etalePull (hG : G.Good) :
    cyclesOfDimension.flatPullbackEtale Φ.onBase (Φ.baseDim_eq_of_etale sG) F.divisor =
      (F.etalePull Φ sG hH).divisor := by
  have := hG.isNoetherian_base
  have := hH.isNoetherian_base
  apply Subtype.ext
  change AlgebraicCycle.pullbackEtale Φ.onBase (F.divisor : AlgebraicCycle G.base ℚ) =
    ((F.etalePull Φ sG hH).divisor : AlgebraicCycle H.base ℚ)
  rw [coe_divisor _ hH, coe_divisor _ hG, divisorCycle, divisorCycle,
    Finset.sum_congr rfl fun w _ ↦ pointDivisor_eq G.baseDim w (F.value w),
    Finset.sum_congr rfl fun w' _ ↦ pointDivisor_eq H.baseDim w' _]
  exact pullbackEtale_sum_divisor_pointGenerator Φ.onBase G.baseDim H.baseDim
    (Φ.baseDim_eq_of_etale sG) hG.covByDimension_base hH.covByDimension_base F.support F.value

end InvariantSystem

namespace CartesianGroupoidMap

variable {H G : EtalePresentationGroupoid.{u}} (Φ : CartesianGroupoidMap H G) [Etale Φ.onBase]
  {k : Type u} [Field k] (i : ℤ) (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG]

/-- **Étale pullback preserves the Vistoli relations**: the pullback of the divisor of an
invariant system is the divisor of its étale pullback. -/
theorem vistoliRelations_le_comap_pullCycles (hH : H.Good) (hG : G.Good) :
    G.vistoliRelations i ≤ (H.vistoliRelations i).comap (Φ.pullCycles i sG) := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨F, hF⟩
  refine EtalePresentationGroupoid.mem_vistoliRelations_of_divisor _ (F.etalePull Φ sG hH) ?_
  rw [coe_pullCycles, hF, F.flatPullbackEtale_divisor_etalePull Φ sG hH hG]

/-- **The Vistoli étale pullback** `A_i(G) → A_i(H)` along a cartesian morphism of étale
presentation groupoids with étale map of atlases, both groupoids satisfying the standing
hypotheses and the atlas of `G` locally of finite type over a field (blueprint E4.4). -/
noncomputable def vistoliPullback (hH : H.Good) (hG : G.Good) :
    G.vistoliChow i →ₗ[ℚ] H.vistoliChow i :=
  (G.vistoliRelations i).mapQ (H.vistoliRelations i) (Φ.pullCycles i sG)
    (Φ.vistoliRelations_le_comap_pullCycles i sG hH hG)

/-- The Vistoli pullback sends the class of a Vistoli cycle to the class of its étale
pullback. -/
@[simp]
theorem vistoliPullback_mk (hH : H.Good) (hG : G.Good) (z : G.cycles i) :
    Φ.vistoliPullback i sG hH hG (G.vistoliQuotientMap i z) =
      H.vistoliQuotientMap i (Φ.pullCycles i sG z) :=
  rfl

end CartesianGroupoidMap

/-! ## Compatibility with the pushforward on the atlas -/

namespace CartesianGroupoidMap

variable {H G : EtalePresentationGroupoid.{u}} (Φ : CartesianGroupoidMap H G) [IsProper Φ.onBase]
  (i : ℤ) {k : Type u} [Field k] (sG : G.base ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sG]

include sG in
/-- Proper pushforward of Vistoli cycles preserves rational equivalence on the atlases (the atlas
of `G` being locally of finite type over a field). -/
theorem relations_le_comap_pushCycles :
    H.relations i ≤ (G.relations i).comap (Φ.pushCycles i) := fun _ hz ↦
  (properPushforwardDescending Φ.onBase i (Φ.onBase ≫ sG)
    (properPushforwardHRel_of_isProper Φ.onBase (Φ.onBase ≫ sG) sG H.baseDim G.baseDim
      i)).maps_relations hz

/-- **Proper pushforward on the groups `EtalePresentationGroupoid.chow`** (Vistoli cycles modulo
all rational equivalences of the atlas) along a cartesian morphism with proper map of atlases,
the atlas of `G` being locally of finite type over a field. -/
noncomputable def chowPushforward : H.chow i →ₗ[ℚ] G.chow i :=
  (H.relations i).mapQ (G.relations i) (Φ.pushCycles i) (Φ.relations_le_comap_pushCycles i sG)

/-- The pushforward on `chow` sends the class of a Vistoli cycle to the class of its proper
pushforward. -/
@[simp]
theorem chowPushforward_mk (z : H.cycles i) :
    Φ.chowPushforward i sG (H.quotientMap i z) = G.quotientMap i (Φ.pushCycles i z) :=
  rfl

/-- **The Vistoli pushforward is compatible with the comparison maps to `chow`.** -/
theorem vistoliChow_toChow_vistoliPushforward (hH : H.Good) (hG : G.Good)
    (c : H.vistoliChow i) :
    EtalePresentationGroupoid.vistoliChow_toChow hG (Φ.vistoliPushforward i sG hH hG c) =
      Φ.chowPushforward i sG (EtalePresentationGroupoid.vistoliChow_toChow hH c) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ c
  rfl

/-- On the underlying cycles of the atlases, the pushforward of Vistoli cycles is the cycle-level
map inducing `properPushforwardChowOfProper`. -/
theorem properPushforwardChowOfProper_quotientMap_pushCycles (z : H.cycles i) :
    properPushforwardChowOfProper Φ.onBase (Φ.onBase ≫ sG) sG H.baseDim G.baseDim i
        ((RationalEquivalenceSystem.canonical (X := H.base) (dimension := H.baseDim)
          (i := i)).quotientMap (z : cyclesOfDimension H.base H.baseDim i)) =
      (RationalEquivalenceSystem.canonical (X := G.base) (dimension := G.baseDim)
          (i := i)).quotientMap ((Φ.pushCycles i z : G.cycles i) :
            cyclesOfDimension G.base G.baseDim i) :=
  rfl

end CartesianGroupoidMap

end GromovWitten.AlgebraicGeometry.IntersectionTheory
