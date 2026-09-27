/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointStalk
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClass
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry

/-!
# Orders of vanishing on point closures

For a specialisation `w ⤳ v` in a scheme `X`, `pointStalk h` (`PointStalk.lean`) is the local
ring `O_{X,v} / p_w` of the reduced closure of `w` at `v`; its fraction field is `κ(w)`.  This
file defines the order function `pointOrd h : κ(w)ˣ → ℤ` (the integer-valued `Ring.ordFrac` of
`pointStalk h` when that ring has Krull dimension one, and `0` otherwise) and computes with it
the coefficients of the divisors used in the construction of the first Chern class.

The bridge is `IntegralClosedSubscheme.pointStalkEquivStalk`: for an integral closed subscheme
`V` with generic point `ξ` and a point `q` of `V`, the stalk of `V` at `q` is the point stalk of
`ξ ⤳ ι q`, compatibly with `K(V) ≅ κ(ξ)`.  Hence `Scheme.ord` on `V` at `q` is `pointOrd`
(`IntegralClosedSubscheme.ord_eq_pointOrd`); no affine chart is involved.

## Main results

* `ordFrac_ringEquiv`: `Ring.ordFrac` is invariant under ring isomorphisms compatible with the
  fraction fields.
* `pointOrd`, `pointOrd_mul`, `pointOrd_one`, `pointOrd_inv`, `pointOrdHom`: the order function
  and the fact that it is a group homomorphism.
* `IntegralClosedSubscheme.pointStalkEquivStalk`, `IntegralClosedSubscheme.ord_eq_pointOrd`,
  `IntegralClosedSubscheme.ringKrullDim_pointStalk_eq_coheight`.
* `RationalFunctionGenerator.divisor_apply_eq_pointOrd` and `divisor_pointGenerator_apply`: for
  `x ⤳ Q`, the coefficient at `Q` of `(pointGenerator x u).divisor dim` is `pointOrd hxQ u`
  (no dimension hypothesis needed); `divisor_pointGenerator_apply_eq_ordFrac` is the
  `Ring.ordFrac` form when `dim x = dim Q + 1`, and
  `divisor_pointGenerator_apply_eq_zero_of_dim_ne` gives vanishing when `dim x ≠ dim Q + 1`
  (under `CovByDimension`).
* `ringKrullDim_pointStalk_eq_one_iff_covBy`, `covBy_of_dim_eq_add_one`: `pointStalk (w ⤳ v)` has
  Krull dimension one iff `v ⋖ w`, which holds when `dim w = dim v + 1`.
* `LineBundleData.divisor_frame_apply`: the coefficient at `Q` of the divisor of the rational
  section with coordinate `1` in a chart `j`, along `pointSubscheme x`, is
  `pointOrd hxQ` of the image in `κ(x)` of the transition unit `L.g j' j` (`Q ∈ U j'`).
* `finite_setOf_not_pointStalk_unit`: for `f : κ(w)ˣ`, only finitely many `v` with `w ⤳ v` and
  `dim w = dim v + 1` have `f` outside the image of the units of `pointStalk (w ⤳ v)`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing Order

open scoped WithZero

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Invariance of `Ring.ordFrac` under isomorphisms -/

section OrdFracInvariance

variable {R S K L : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]

omit [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsNoetherianRing S] [Ring.KrullDimLE 1 S] in
/-- `Ring.ordMonoidWithZeroHom` is invariant under a ring isomorphism. -/
theorem ordMonoidWithZeroHom_ringEquiv (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst ha
    simp
  have ha' : e a ≠ 0 := (map_ne_zero_iff e e.injective).2 ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha'),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha),
    LocalOrdSymmetry.ord_ringEquiv]

/-- **`Ring.ordFrac` is invariant under ring isomorphisms compatible with the fraction
fields.**  If `e : R ≃+* S` and `F : K ≃+* L` satisfy `F ∘ algebraMap R K = algebraMap S L ∘ e`,
then `ordFrac S (F k) = ordFrac R k` for every `k : K`. -/
theorem ordFrac_ringEquiv (e : R ≃+* S) (F : K ≃+* L)
    (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (e r)) (k : K) :
    Ring.ordFrac S (F k) = Ring.ordFrac R k := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective R k
  have key : ∀ c : R, Ring.ordFrac S (algebraMap S L (e c)) =
      Ring.ordFrac R (algebraMap R K c) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp
    rw [Ring.ordFrac_eq_ord S ((map_ne_zero_iff e e.injective).2 hc), Ring.ordFrac_eq_ord R hc,
      ordMonoidWithZeroHom_ringEquiv]
  rw [map_div₀, hF, hF, map_div₀, map_div₀, key, key]

end OrdFracInvariance

/-! ## The order function of a point stalk -/

section PointOrd

variable {X : Scheme.{u}} {w v : X}

/-- A point stalk of Krull dimension one has Krull dimension at most one. -/
theorem krullDimLE_one_pointStalk_of_eq_one {h : w ⤳ v} (hd : ringKrullDim (pointStalk h) = 1) :
    Ring.KrullDimLE 1 (pointStalk h) := by
  rw [Ring.krullDimLE_iff, hd]
  rfl

variable [IsLocallyNoetherian X]

/-- **The order of a unit of `κ(w)` along the point stalk `pointStalk h`**, for `h : w ⤳ v`.
When `pointStalk h` (the local ring of the closure of `w` at `v`) has Krull dimension one, this
is `Ring.ordFrac (pointStalk h)` of the unit, converted to an integer; otherwise it is the junk
value `0` (matching the convention of `Scheme.ord` at points of coheight different from one). -/
noncomputable def pointOrd (h : w ⤳ v) (u : (X.residueField w)ˣ) : ℤ :=
  if hd : ringKrullDim (pointStalk h) = 1 then
    haveI := krullDimLE_one_pointStalk_of_eq_one hd
    Multiplicative.toAdd (WithZero.unzero
      ((map_ne_zero (Ring.ordFrac (pointStalk h) : X.residueField w →*₀ ℤᵐ⁰)).2 u.ne_zero))
  else 0

/-- In Krull dimension one, `pointOrd` is `Ring.ordFrac` of the point stalk. -/
theorem pointOrd_of_eq_one {h : w ⤳ v} (hd : ringKrullDim (pointStalk h) = 1)
    [Ring.KrullDimLE 1 (pointStalk h)] (u : (X.residueField w)ˣ) :
    ((Multiplicative.ofAdd (pointOrd h u) : Multiplicative ℤ) : ℤᵐ⁰) =
      Ring.ordFrac (pointStalk h) (u : X.residueField w) := by
  rw [pointOrd, dif_pos hd, ofAdd_toAdd, WithZero.coe_unzero]

/-- Outside Krull dimension one, `pointOrd` is `0`. -/
theorem pointOrd_of_ne_one {h : w ⤳ v} (hd : ringKrullDim (pointStalk h) ≠ 1)
    (u : (X.residueField w)ˣ) : pointOrd h u = 0 := by
  rw [pointOrd, dif_neg hd]

/-- `pointOrd` is multiplicative. -/
theorem pointOrd_mul (h : w ⤳ v) (u u' : (X.residueField w)ˣ) :
    pointOrd h (u * u') = pointOrd h u + pointOrd h u' := by
  by_cases hd : ringKrullDim (pointStalk h) = 1
  · have := krullDimLE_one_pointStalk_of_eq_one hd
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective (α := Multiplicative ℤ)
    rw [ofAdd_add, WithZero.coe_mul, pointOrd_of_eq_one hd, pointOrd_of_eq_one hd,
      pointOrd_of_eq_one hd, Units.val_mul, map_mul]
  · simp [pointOrd_of_ne_one hd]

/-- `pointOrd` sends `1` to `0`. -/
theorem pointOrd_one (h : w ⤳ v) : pointOrd h (1 : (X.residueField w)ˣ) = 0 := by
  have := pointOrd_mul h 1 1
  rw [mul_one] at this
  omega

/-- `pointOrd` sends inverses to negatives. -/
theorem pointOrd_inv (h : w ⤳ v) (u : (X.residueField w)ˣ) :
    pointOrd h u⁻¹ = - pointOrd h u := by
  have := pointOrd_mul h u⁻¹ u
  rw [inv_mul_cancel, pointOrd_one] at this
  omega

/-- `pointOrd h` bundled as a group homomorphism `κ(w)ˣ →* Multiplicative ℤ`. -/
noncomputable def pointOrdHom (h : w ⤳ v) : (X.residueField w)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (pointOrd h u)
  map_one' := by rw [pointOrd_one]; rfl
  map_mul' u u' := by rw [pointOrd_mul, ofAdd_add]

/-- The value of `pointOrdHom`. -/
@[simp]
theorem pointOrdHom_apply (h : w ⤳ v) (u : (X.residueField w)ˣ) :
    pointOrdHom h u = Multiplicative.ofAdd (pointOrd h u) := rfl

end PointOrd

/-! ## Point stalks as stalks of integral closed subschemes -/

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-- Every point of an integral closed subscheme is, in `X`, a specialisation of the image of
its generic point. -/
theorem genericPointImage_specializes (q : V.scheme) :
    V.genericPointImage ⤳ V.inclusion.base q :=
  ((genericPoint_spec V.scheme).specializes (Set.mem_univ q)).map V.inclusion.continuous

/-- The composite `O_{X, ι q} → O_{V, q} → K(V) ≅ κ(ξ_V)` is `pointStalkMap`. -/
theorem functionFieldIso_algebraMap_stalkMap (q : V.scheme)
    (t : X.presheaf.stalk (V.inclusion.base q)) :
    V.functionFieldIso.hom (algebraMap (V.scheme.presheaf.stalk q) V.scheme.functionField
      (V.inclusion.stalkMap q t)) = pointStalkMap (V.genericPointImage_specializes q) t := by
  rw [pointStalkMap_apply, ← V.stalkMap_functionFieldIso]
  congr 1
  change V.scheme.presheaf.stalkSpecializes _ (V.inclusion.stalkMap q t) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- The kernel of the stalk map of the inclusion of `V` at `q` is the kernel of
`pointStalkMap`. -/
theorem ker_stalkMap_inclusion (q : V.scheme) :
    RingHom.ker (V.inclusion.stalkMap q).hom =
      RingHom.ker (pointStalkMap (V.genericPointImage_specializes q)) := by
  ext t
  rw [RingHom.mem_ker, RingHom.mem_ker, ← functionFieldIso_algebraMap_stalkMap,
    map_eq_zero_iff (ConcreteCategory.hom V.functionFieldIso.hom) (RingHom.injective _),
    map_eq_zero_iff (algebraMap _ _) (IsFractionRing.injective _ _)]

/-- **The stalk of an integral closed subscheme is a point stalk**: for `q` a point of `V`, the
point stalk of `ξ_V ⤳ ι q` is isomorphic to the stalk of `V` at `q` (through the surjective
stalk map of the closed immersion). -/
noncomputable def pointStalkEquivStalk (q : V.scheme) :
    pointStalk (V.genericPointImage_specializes q) ≃+* V.scheme.presheaf.stalk q :=
  (Ideal.quotEquivOfEq (V.ker_stalkMap_inclusion q).symm).trans
    (RingHom.quotientKerEquivOfSurjective (V.inclusion.stalkMap_surjective q))

/-- `pointStalkEquivStalk` on classes. -/
theorem pointStalkEquivStalk_mk (q : V.scheme) (t : X.presheaf.stalk (V.inclusion.base q)) :
    V.pointStalkEquivStalk q (Ideal.Quotient.mk _ t) = V.inclusion.stalkMap q t := rfl

/-- `pointStalkEquivStalk` is compatible with the fraction fields `κ(ξ_V)` and `K(V)`, identified
by `functionFieldIso`. -/
theorem functionFieldIso_algebraMap_pointStalkEquivStalk (q : V.scheme)
    (a : pointStalk (V.genericPointImage_specializes q)) :
    V.functionFieldIso.hom (algebraMap (V.scheme.presheaf.stalk q) V.scheme.functionField
      (V.pointStalkEquivStalk q a)) = algebraMap _ (X.residueField V.genericPointImage) a := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [pointStalkEquivStalk_mk, functionFieldIso_algebraMap_stalkMap]
  rfl

/-- The Krull dimension of the point stalk of `ξ_V ⤳ ι q` is the coheight of `q` in `V`. -/
theorem ringKrullDim_pointStalk_eq_coheight (q : V.scheme) :
    ringKrullDim (pointStalk (V.genericPointImage_specializes q)) = coheight q := by
  rw [ringKrullDim_eq_of_ringEquiv (V.pointStalkEquivStalk q), ringKrullDim_stalk_eq_coheight]

/-- **`Scheme.ord` on an integral closed subscheme is `pointOrd`.**  For a rational function
`f` on `V` and a point `q` of `V`, the order of `f` at `q` is the `pointOrd` along
`ξ_V ⤳ ι q` of the image of `f` in `κ(ξ_V)`.  (Both sides are the junk value `0` when `q` does
not have coheight one.) -/
theorem ord_eq_pointOrd [IsLocallyNoetherian X] (q : V.scheme)
    (f : V.scheme.functionFieldˣ) :
    V.scheme.ord (f : V.scheme.functionField) q =
      pointOrd (V.genericPointImage_specializes q)
        (Units.map V.functionFieldEquivResidueField.toMonoidHom f) := by
  have hdim := V.ringKrullDim_pointStalk_eq_coheight q
  by_cases hq : coheight q = 1
  · have hd : ringKrullDim (pointStalk (V.genericPointImage_specializes q)) = 1 := by
      rw [hdim, hq]
      rfl
    have := krullDimLE_one_pointStalk_of_eq_one hd
    have := krullDimLE_of_coheight_le (X := V.scheme) hq.le
    rw [Scheme.ord_eq_iff hq f.ne_zero, pointOrd_of_eq_one hd]
    change Ring.ordFrac (V.scheme.presheaf.stalk q) (f : V.scheme.functionField) = _
    have hF : ∀ r : pointStalk (V.genericPointImage_specializes q),
        V.functionFieldEquivResidueField.symm (algebraMap _ _ r) =
          algebraMap (V.scheme.presheaf.stalk q) V.scheme.functionField
            (V.pointStalkEquivStalk q r) := by
      intro r
      rw [RingEquiv.symm_apply_eq, functionFieldEquivResidueField_apply,
        functionFieldIso_algebraMap_pointStalkEquivStalk]
    have := ordFrac_ringEquiv (V.pointStalkEquivStalk q) V.functionFieldEquivResidueField.symm
      hF (V.functionFieldEquivResidueField (f : V.scheme.functionField))
    rw [RingEquiv.symm_apply_apply] at this
    rw [this]
    rfl
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq, pointOrd_of_ne_one]
    rw [hdim]
    exact_mod_cast hq

end IntegralClosedSubscheme

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (V : IntegralClosedSubscheme X)

/-- Every specialisation in `X` of the image of the generic point of `V` lies in `V`. -/
theorem mem_range_of_specializes {y : X} (h : V.genericPointImage ⤳ y) :
    y ∈ Set.range V.inclusion.base :=
  h.mem_closed V.inclusion.isClosedEmbedding.isClosed_range ⟨_, rfl⟩

/-- For a specialisation `y` of `w = ξ_V`, the point stalk of `w ⤳ y` has Krull dimension one
exactly when `y` is covered by `w` in the specialisation order. -/
theorem ringKrullDim_pointStalk_eq_one_iff_covBy {w : X} (e : V.genericPointImage = w) {y : X}
    (h : w ⤳ y) : ringKrullDim (pointStalk h) = 1 ↔ y ⋖ w := by
  subst e
  obtain ⟨q, rfl⟩ := V.mem_range_of_specializes h
  rw [V.ringKrullDim_pointStalk_eq_coheight q, WithBot.coe_eq_one,
    HomogeneityLocal.coheight_eq_one_iff_covBy (HomogeneityLocal.isTop_genericPoint _)]
  exact ⟨HomogeneityLocal.covBy_map_of_isClosedImmersion V.inclusion,
    HomogeneityLocal.covBy_of_covBy_map V.inclusion V.inclusion.isClosedEmbedding.isInducing⟩

end IntegralClosedSubscheme

namespace RationalFunctionGenerator

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The coefficient of a principal divisor at a point is a `pointOrd`.**  For a generator `g`
whose subspace has generic point `w` (up to the equality `e`) and a specialisation `y` of `w`,
the coefficient of `g.divisor dim` at `y` is the `pointOrd` along `w ⤳ y` of the residue class of
the rational function of `g`. -/
theorem divisor_apply_eq_pointOrd (dim : DimensionFunction X) (g : RationalFunctionGenerator X)
    {w : X} (e : g.subspace.genericPointImage = w) {y : X} (h : w ⤳ y) :
    (g.divisor dim : X → ℚ) y =
      pointOrd h (Units.map (X.residueFieldCongr e).hom.hom.toMonoidHom g.residueFunction) := by
  subst e
  obtain ⟨q, rfl⟩ := g.subspace.mem_range_of_specializes h
  unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward
  rw [AlgebraicCycle.map_closedImmersion_apply_image g.subspace.inclusion (dim : X → ℤ),
    Scheme.principalCycle_apply, g.subspace.ord_eq_pointOrd q g.function]
  congr 2

end RationalFunctionGenerator

section PointGenerator

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

open LineBundleInjective

/-- **Coefficients of point-generator divisors.**  For `x ⤳ Q`, the coefficient at `Q` of the
divisor of the canonical generator `pointGenerator x u` is `pointOrd hxQ u`. -/
theorem divisor_pointGenerator_apply (dim : DimensionFunction X) (x : X)
    (u : (X.residueField x)ˣ) {Q : X} (hxQ : x ⤳ Q) :
    ((pointGenerator x u).divisor dim : X → ℚ) Q = pointOrd hxQ u := by
  rw [RationalFunctionGenerator.divisor_apply_eq_pointOrd dim _
    (genericPointImage_pointGenerator x u) hxQ, residueFunction_pointGenerator]

/-- The point stalk of `w ⤳ v` has Krull dimension one exactly when `v` is covered by `w` in the
specialisation order. -/
theorem ringKrullDim_pointStalk_eq_one_iff_covBy {w v : X} (h : w ⤳ v) :
    ringKrullDim (pointStalk h) = 1 ↔ v ⋖ w :=
  (pointSubscheme w).ringKrullDim_pointStalk_eq_one_iff_covBy (genericPointImage_pointSubscheme w) h

omit [IsLocallyNoetherian X] [NoetherianSpace X] in
/-- If `w ⤳ v` and `dim w = dim v + 1`, then `v` is covered by `w`: heights are finite, so no
point lies strictly between them. -/
theorem covBy_of_dim_eq_add_one (dim : DimensionFunction X) {w v : X} (h : w ⤳ v)
    (hd : dim w = dim v + 1) : v ⋖ w := by
  have hw := dim.height_eq w
  have hv := dim.height_eq v
  have hv0 := dim.nonnegative v
  have hwv : height w = height v + 1 := by
    rw [hw, hv, hd]
    norm_cast
    omega
  have hvfin : height v < ⊤ := by rw [hv]; exact ENat.natCast_lt_top _
  have hwfin : height w < ⊤ := by rw [hw]; exact ENat.natCast_lt_top _
  have hlt : v < w := by
    refine lt_of_le_not_ge (HomogeneityLocal.le_iff_specializes.2 h) fun hwv' ↦ ?_
    have hvw : v = w :=
      (Specializes.antisymm (HomogeneityLocal.le_iff_specializes.1 hwv') h).eq
    rw [hvw] at hd
    omega
  refine ⟨hlt, fun z hvz hzw ↦ ?_⟩
  have h1 := height_strictMono hvz hvfin
  have h2 := height_strictMono hzw (lt_of_le_of_lt (height_mono hzw.le) hwfin)
  rw [hwv] at h2
  exact absurd (Order.add_one_le_of_lt h1) (not_le.2 h2)

/-- If `w ⤳ v` and `dim w = dim v + 1`, the point stalk of `w ⤳ v` has Krull dimension one. -/
theorem ringKrullDim_pointStalk_eq_one_of_dim_eq (dim : DimensionFunction X) {w v : X} (h : w ⤳ v)
    (hd : dim w = dim v + 1) : ringKrullDim (pointStalk h) = 1 :=
  (ringKrullDim_pointStalk_eq_one_iff_covBy h).2 (covBy_of_dim_eq_add_one dim h hd)

/-- If `w ⤳ v` and `dim w = dim v + 1`, the point stalk of `w ⤳ v` has Krull dimension at most
one (the instance needed by `Ring.ordFrac`). -/
theorem krullDimLE_one_pointStalk_of_dim_eq (dim : DimensionFunction X) {w v : X} (h : w ⤳ v)
    (hd : dim w = dim v + 1) : Ring.KrullDimLE 1 (pointStalk h) :=
  krullDimLE_one_pointStalk_of_eq_one (ringKrullDim_pointStalk_eq_one_of_dim_eq dim h hd)

/-- Under `CovByDimension`, a point stalk of Krull dimension one comes from a pair of points
whose dimensions differ by one. -/
theorem dim_eq_add_one_of_ringKrullDim_pointStalk_eq_one (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {w v : X} (h : w ⤳ v)
    (hd : ringKrullDim (pointStalk h) = 1) : dim w = dim v + 1 :=
  (hcov v w ((ringKrullDim_pointStalk_eq_one_iff_covBy h).1 hd)).symm

/-- Under `CovByDimension`, `pointOrd h` vanishes when the dimensions of the two points do not
differ by one. -/
theorem pointOrd_eq_zero_of_dim_ne (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {w v : X} (h : w ⤳ v)
    (hd : dim w ≠ dim v + 1) (u : (X.residueField w)ˣ) : pointOrd h u = 0 :=
  pointOrd_of_ne_one
    (fun h1 ↦ hd (dim_eq_add_one_of_ringKrullDim_pointStalk_eq_one dim hcov h h1)) u

/-- Under `CovByDimension`, the coefficient at `Q` of the divisor of `pointGenerator x u`
vanishes when `dim x ≠ dim Q + 1`. -/
theorem divisor_pointGenerator_apply_eq_zero_of_dim_ne (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (x : X) (u : (X.residueField x)ˣ) (Q : X)
    (hd : dim x ≠ dim Q + 1) : ((pointGenerator x u).divisor dim : X → ℚ) Q = 0 := by
  by_cases hxQ : x ⤳ Q
  · rw [divisor_pointGenerator_apply dim x u hxQ, pointOrd_eq_zero_of_dim_ne dim hcov hxQ hd]
    simp
  · exact divisor_pointGenerator_apply_eq_zero dim x u Q hxQ

/-- **Coefficients of point-generator divisors, `Ring.ordFrac` form.**  If `x ⤳ Q` and
`dim x = dim Q + 1` (so that `pointStalk hxQ` has Krull dimension one, see
`krullDimLE_one_pointStalk_of_dim_eq`), the coefficient at `Q` of the divisor of
`pointGenerator x u` is `Ring.ordFrac (pointStalk hxQ) u`, converted to an integer. -/
theorem divisor_pointGenerator_apply_eq_ordFrac (dim : DimensionFunction X) (x : X)
    (u : (X.residueField x)ˣ) {Q : X} (hxQ : x ⤳ Q) (hd : dim x = dim Q + 1)
    [Ring.KrullDimLE 1 (pointStalk hxQ)] :
    ((pointGenerator x u).divisor dim : X → ℚ) Q =
      ((Multiplicative.toAdd (WithZero.unzero ((map_ne_zero
        (Ring.ordFrac (pointStalk hxQ) : X.residueField x →*₀ ℤᵐ⁰)).2 u.ne_zero)) : ℤ) : ℚ) := by
  rw [divisor_pointGenerator_apply dim x u hxQ]
  congr 1
  apply Multiplicative.ofAdd.injective
  apply WithZero.coe_injective
  rw [pointOrd_of_eq_one (ringKrullDim_pointStalk_eq_one_of_dim_eq dim hxQ hd), ofAdd_toAdd,
    WithZero.coe_unzero]

end PointGenerator

/-! ## Rational sections given by a chart frame -/

section Frame

variable {X : Scheme.{u}}

/-- The image in `κ(x)` of a unit of `Γ(X, U)`, for `x ∈ U`: germ at `x`, then residue. -/
noncomputable def sectionResidueUnit {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)ˣ) :
    (X.residueField x)ˣ :=
  Units.map ((X.residue x).hom.comp (X.presheaf.germ U x hx).hom).toMonoidHom a

/-- The value of `sectionResidueUnit`. -/
theorem sectionResidueUnit_val {U : X.Opens} {x : X} (hx : x ∈ U) (a : Γ(X, U)ˣ) :
    (sectionResidueUnit hx a : X.residueField x) =
      X.residue x (X.presheaf.germ U x hx (a : Γ(X, U))) := rfl

variable [IsLocallyNoetherian X]

/-- `pointOrd` of `sectionResidueUnit` only depends on the points, not on how they are
presented. -/
theorem pointOrd_sectionResidueUnit_congr {w w' v : X} (e : w = w') (h : w ⤳ v) (h' : w' ⤳ v)
    {U : X.Opens} (hw : w ∈ U) (hw' : w' ∈ U) (a : Γ(X, U)ˣ) :
    pointOrd h (sectionResidueUnit hw a) = pointOrd h' (sectionResidueUnit hw' a) := by
  subst e
  rfl

/-- **Orders of a frame section on an integral closed subscheme.**  For the rational section of
`L` along `V` with coordinate `1` in a chart `j`, and a point `q` of `V` whose image lies in the
chart `j'`, the coefficient of its divisor at the image of `q` is the `pointOrd` along
`ξ_V ⤳ ι q` of the image in `κ(ξ_V)` of the transition unit `L.g j' j`. -/
theorem LineBundleData.divisor_frame_apply_image (L : LineBundleData X)
    (V : IntegralClosedSubscheme X) (dim : DimensionFunction X) (j j' : L.J)
    (hj : V.eta ∈ (L.U j : X.Opens)) (q : V.scheme)
    (hq : V.inclusion.base q ∈ (L.U j' : X.Opens)) :
    ((⟨j, hj, 1⟩ : L.RationalSection V).divisor dim : X → ℚ) (V.inclusion.base q) =
      pointOrd (V.genericPointImage_specializes q)
        (sectionResidueUnit (memInf (V.eta_mem_of_mem_preimage hq) hj)
          (L.g j' j)) := by
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  rw [AlgebraicCycle.map_closedImmersion_apply_image V.inclusion (dim : X → ℤ),
    LineBundleData.RationalSection.divisorCycle_apply,
    LineBundleData.RationalSection.ord_well_defined _ j' q hq, V.ord_eq_pointOrd q]
  congr 2
  refine Units.ext ?_
  change V.functionFieldIso.hom ((L.unitAt V j' j _ * 1 : V.scheme.functionFieldˣ) :
    V.scheme.functionField) = _
  rw [mul_one]
  exact V.stalkMap_functionFieldIso _

variable [NoetherianSpace X]

open LineBundleInjective

/-- **Orders of the frame section of a chart.**  Let `L` be a line bundle, `x : X`, `j` a chart
containing (the generic point of `pointSubscheme x`, i.e.) `x`, and consider the rational
section `⟨j, hj, 1⟩` of `L` along `pointSubscheme x` with coordinate `1` in the chart `j`.  For
`x ⤳ Q` with `Q` in a chart `j'`, the coefficient at `Q` of its divisor is the `pointOrd` along
`x ⤳ Q` of the image in `κ(x)` of the transition unit `L.g j' j`. -/
theorem LineBundleData.divisor_frame_apply (L : LineBundleData X) (dim : DimensionFunction X)
    (x : X) (j j' : L.J) (hj : (pointSubscheme x).eta ∈ (L.U j : X.Opens)) {Q : X}
    (hxQ : x ⤳ Q) (hQ : Q ∈ (L.U j' : X.Opens))
    (hx : x ∈ (L.U j' : X.Opens) ⊓ (L.U j : X.Opens)) :
    ((⟨j, hj, 1⟩ : L.RationalSection (pointSubscheme x)).divisor dim : X → ℚ) Q =
      pointOrd hxQ (sectionResidueUnit hx (L.g j' j)) := by
  have h' : (pointSubscheme x).genericPointImage ⤳ Q := by
    rw [genericPointImage_pointSubscheme]
    exact hxQ
  obtain ⟨q, rfl⟩ := (pointSubscheme x).mem_range_of_specializes h'
  rw [LineBundleData.divisor_frame_apply_image L _ dim j j' hj q hQ]
  exact congrArg _
    (pointOrd_sectionResidueUnit_congr (genericPointImage_pointSubscheme x) _ _ _ _ _)

end Frame

/-! ## Local finiteness of the non-unit locus -/

section Finiteness

attribute [local instance] specializationOrder in
/-- A maximal point for the specialisation order is a generic point of an irreducible component
(a copy of the private lemma of `ChowGroup.lean`). -/
private lemma isMax_mem_genericPoints'
    {T : Type*} [TopologicalSpace T] [T0Space T] [QuasiSober T]
    {x : T} (hx : IsMax x) : x ∈ genericPoints T := by
  rw [genericPoints, irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro s hs hxs
  let y : T := hs.2.genericPoint
  have hy : IsGenericPoint y s := hs.2.isGenericPoint_genericPoint_closure.trans
    hs.1.closure_eq
  have hxy : x ≤ y := by
    change y ⤳ x
    rw [specializes_iff_closure_subset, hy.def]
    exact hxs
  have hyx : y ≤ x := hx hxy
  have heq : x = y := le_antisymm hxy hyx
  simpa only [heq] using hy.def.symm.le

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

omit [IsLocallyNoetherian X] in
/-- **Local finiteness, subscheme form.**  Let `V` be an integral closed subscheme with generic
point `w` and `f` a unit of `κ(w)`.  Only finitely many points `v` covered by `w` have the
property that `f` is not the image of a unit of `pointStalk (w ⤳ v)`. -/
theorem IntegralClosedSubscheme.finite_setOf_not_pointStalk_unit
    (V : IntegralClosedSubscheme X) {w : X} (e : V.genericPointImage = w)
    (f : (X.residueField w)ˣ) :
    {v : X | ∃ h : w ⤳ v, v ⋖ w ∧
      ¬ ∃ a : (pointStalk h)ˣ, algebraMap (pointStalk h) (X.residueField w) a = f}.Finite := by
  subst e
  have hf0 : V.functionFieldEquivResidueField.symm (f : X.residueField V.genericPointImage) ≠ 0 :=
    by simp
  obtain ⟨U, -, g, hne, hg, hunit⟩ := exists_isUnit_germ_eq (X := V.scheme) _ hf0
  let C : Set V.scheme := (U : Set V.scheme)ᶜ
  have hC : IsClosed C := U.isOpen.isClosed_compl
  have : NoetherianSpace V.scheme := V.inclusion.isClosedEmbedding.isInducing.noetherianSpace
  have : QuasiSober C := hC.isClosedEmbedding_subtypeVal.quasiSober
  have hgen : (genericPoints C).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  refine ((hgen.image fun c : C ↦ c.1).image V.inclusion.base).subset ?_
  rintro y ⟨h, hcovy, hnot⟩
  obtain ⟨q, rfl⟩ := V.mem_range_of_specializes h
  have hqη : q ⋖ genericPoint V.scheme :=
    HomogeneityLocal.covBy_of_covBy_map V.inclusion V.inclusion.isClosedEmbedding.isInducing hcovy
  have hηU : genericPoint V.scheme ∈ U :=
    ((genericPoint_spec V.scheme).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hqU : q ∉ U := by
    intro hqU
    apply hnot
    refine ⟨Units.map (V.pointStalkEquivStalk q).symm.toMonoidHom
      (hunit.map (V.scheme.presheaf.germ U q hqU).hom).unit, ?_⟩
    rw [Units.coe_map, ← V.functionFieldIso_algebraMap_pointStalkEquivStalk]
    change V.functionFieldIso.hom (algebraMap _ _ (V.pointStalkEquivStalk q
      ((V.pointStalkEquivStalk q).symm (V.scheme.presheaf.germ U q hqU g)))) = _
    rw [RingEquiv.apply_symm_apply, Scheme.algebraMap_germ_eq_germToFunctionField, hg]
    exact V.functionFieldEquivResidueField.apply_symm_apply _
  refine ⟨q, ⟨⟨q, hqU⟩, isMax_mem_genericPoints' fun c hc ↦ ?_, rfl⟩, rfl⟩
  have hcq : c.1 ⤳ q := by
    change c ⤳ ⟨q, hqU⟩ at hc
    simpa only [subtype_specializes_iff] using hc
  have hcη : c.1 < genericPoint V.scheme := by
    refine lt_of_le_not_ge (HomogeneityLocal.isTop_genericPoint _ _) fun hle ↦ c.2 ?_
    have : c.1 = genericPoint V.scheme :=
      (Specializes.antisymm (HomogeneityLocal.le_iff_specializes.1 hle)
        (HomogeneityLocal.le_iff_specializes.1 (HomogeneityLocal.isTop_genericPoint _ _))).eq
    rw [this]
    exact hηU
  have hle : c.1 ≤ q := by
    by_contra hcon
    exact hqη.2 (lt_of_le_not_ge (HomogeneityLocal.le_iff_specializes.2 hcq) hcon) hcη
  change (⟨q, hqU⟩ : C) ⤳ c
  simpa only [subtype_specializes_iff] using HomogeneityLocal.le_iff_specializes.1 hle

/-- **Local finiteness of the non-unit locus.**  For `w : X` and a unit `f` of `κ(w)`, only
finitely many specialisations `v` of `w` with `dim w = dim v + 1` have the property that `f` is
not the image of a unit of `pointStalk (w ⤳ v)`. -/
theorem finite_setOf_not_pointStalk_unit (dim : DimensionFunction X) (w : X)
    (f : (X.residueField w)ˣ) :
    {v : X | ∃ h : w ⤳ v, dim w = dim v + 1 ∧
      ¬ ∃ a : (pointStalk h)ˣ, algebraMap (pointStalk h) (X.residueField w) a = f}.Finite :=
  ((LineBundleInjective.pointSubscheme w).finite_setOf_not_pointStalk_unit
    (LineBundleInjective.genericPointImage_pointSubscheme w) f).subset
    fun _ ⟨h, hd, hn⟩ ↦ ⟨h, covBy_of_dim_eq_add_one dim h hd, hn⟩

end Finiteness

end GromovWitten.AlgebraicGeometry.IntersectionTheory
