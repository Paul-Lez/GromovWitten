/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral

/-!
# Restriction of Čech line bundles along closed immersions

For a closed immersion `i : Z ⟶ X` and a Čech line bundle `L : LineBundleData X`, we define the
restriction `L.restrict i : LineBundleData Z` (same index type, charts `i ⁻¹ᵁ U j`, transition
units pulled back along `i`), identify point stalks and `pointOrd` along `i`, and prove the
projection formula `i_* (c₁(L|_Z) ∩ α) = c₁(L) ∩ i_* α`.

## Main results

* `LineBundleData.restrict`: the restriction of `L` along a closed immersion, with
  `restrict_g` (transition units are pullbacks) and `restrict_trivial_g` (the restriction of the
  trivial bundle has trivial transition units).
* `closedResidueFieldEquiv i z : κ(i z) ≃+* κ(z)` and
  `pointStalkClosedEquiv i h : pointStalk (i z₁ ⤳ i z₂) ≃+* pointStalk (z₁ ⤳ z₂)`, compatible
  with the residue-field isomorphisms (`closedResidueFieldEquiv_algebraMap_pointStalk`).
* `pointOrd_closedResidueFieldEquiv`: `pointOrd` is preserved by closed immersions.
* `map_divisor_restrict_pointFrame`: the pushforward of the frame divisor of `L.restrict i` at
  `z` is the frame divisor of `L` at `i z`.
* `closedImmersionPushforward_c1Cycle_restrict`: the projection formula at cycle level, for
  `c1Cycle`, under `CovByDimension` on `X`.
* `closedImmersionPushforward_c1_restrict`: the projection formula on Chow groups for `c1`,
  given `KillsRelations` witnesses for `L` and `L.restrict i`.
* `closedImmersionPushforward_firstChernClass_restrict`: the projection formula on Chow groups
  for `firstChernClass`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

open scoped WithZero

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

/-! ## Pulling units back along a morphism -/

section PullUnit

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- The pullback of a unit `a` of `Γ(X, V)` along `i : Z ⟶ X` to a unit of `Γ(Z, U)`, for an
open `U ≤ i ⁻¹ᵁ V`, through `Scheme.Hom.appLE`. -/
noncomputable def pullUnit {U : Z.Opens} {V : X.Opens} (h : U ≤ i ⁻¹ᵁ V) (a : Γ(X, V)ˣ) :
    Γ(Z, U)ˣ :=
  Units.map (i.appLE V U h).hom.toMonoidHom a

/-- The value of `pullUnit`. -/
theorem pullUnit_val {U : Z.Opens} {V : X.Opens} (h : U ≤ i ⁻¹ᵁ V) (a : Γ(X, V)ˣ) :
    (pullUnit i h a : Γ(Z, U)) = i.appLE V U h a :=
  rfl

/-- `pullUnit` is multiplicative. -/
theorem pullUnit_mul {U : Z.Opens} {V : X.Opens} (h : U ≤ i ⁻¹ᵁ V) (a b : Γ(X, V)ˣ) :
    pullUnit i h (a * b) = pullUnit i h a * pullUnit i h b :=
  map_mul _ a b

/-- `pullUnit` sends `1` to `1`. -/
@[simp]
theorem pullUnit_one {U : Z.Opens} {V : X.Opens} (h : U ≤ i ⁻¹ᵁ V) :
    pullUnit i h (1 : Γ(X, V)ˣ) = 1 :=
  map_one _

/-- Restricting a pulled-back unit is pulling back to the smaller open. -/
theorem resUnit_pullUnit {U U' : Z.Opens} {V : X.Opens} (h : U ≤ i ⁻¹ᵁ V) (h' : U' ≤ U)
    (a : Γ(X, V)ˣ) : resUnit h' (pullUnit i h a) = pullUnit i (h'.trans h) a := by
  apply Units.ext
  change (Z.presheaf.map (homOfLE h').op).hom (i.appLE V U h a) = i.appLE V U' _ a
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- Pulling back a restricted unit is pulling back the unit itself. -/
theorem pullUnit_resUnit {U : Z.Opens} {V V' : X.Opens} (h : U ≤ i ⁻¹ᵁ V) (h' : V ≤ V')
    (a : Γ(X, V')ˣ) :
    pullUnit i h (resUnit h' a) = pullUnit i (h.trans (i.preimage_mono h')) a := by
  apply Units.ext
  change i.appLE V U h ((X.presheaf.map (homOfLE h').op).hom a) = i.appLE V' U _ a
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end PullUnit

/-! ## Restriction of line bundle data -/

namespace LineBundleData

variable {X Z : Scheme.{u}}

/-- The preimage of an affine open along a closed immersion is an affine open. -/
theorem preimage_mem_affineOpens (i : Z ⟶ X) [IsClosedImmersion i] (U : X.affineOpens) :
    i ⁻¹ᵁ (U : X.Opens) ∈ Z.affineOpens :=
  IsAffineOpen.preimage (X := Z) (Y := X) (U := (U : X.Opens)) U.2 i

/-- The intersection of two preimages lies in the preimage of the intersection. -/
theorem inf_preimage_le_preimage_inf (i : Z ⟶ X) (U V : X.Opens) :
    i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ V ≤ i ⁻¹ᵁ (U ⊓ V) :=
  fun _ h => h

/-- **Restriction of a Čech line bundle along a closed immersion.**  Same index type, charts the
preimages `i ⁻¹ᵁ U j` (affine because closed immersions are affine morphisms), transition units
the pullbacks of `L.g j j'`. -/
noncomputable def restrict (L : LineBundleData X) (i : Z ⟶ X) [IsClosedImmersion i] :
    LineBundleData Z where
  J := L.J
  U j := ⟨i ⁻¹ᵁ (L.U j : X.Opens), preimage_mem_affineOpens i (L.U j)⟩
  covers z := L.covers (i.base z)
  g j j' := pullUnit i (Scheme.Hom.preimage_inf i).ge (L.g j j')
  g_self j := by
    rw [L.g_self, pullUnit_one]
  g_cocycle j j' j'' := by
    rw [resUnit_pullUnit, resUnit_pullUnit, resUnit_pullUnit]
    have h := congrArg (pullUnit i (U := ((i ⁻¹ᵁ (L.U j : X.Opens)) ⊓
      (i ⁻¹ᵁ (L.U j' : X.Opens))) ⊓ (i ⁻¹ᵁ (L.U j'' : X.Opens)))
      (V := ((L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) ⊓ (L.U j'' : X.Opens))
      ((inf_le_inf_right _ (Scheme.Hom.preimage_inf i).ge).trans
        (Scheme.Hom.preimage_inf i).ge))
      (L.g_cocycle j j' j'')
    rw [pullUnit_mul] at h
    rw [pullUnit_resUnit, pullUnit_resUnit, pullUnit_resUnit] at h
    exact h

variable (L : LineBundleData X) (i : Z ⟶ X) [IsClosedImmersion i]

/-- The index type of the restriction. -/
@[simp]
theorem restrict_J : (L.restrict i).J = L.J := rfl

/-- The charts of the restriction are the preimages of the charts. -/
theorem restrict_U (j : L.J) : ((L.restrict i).U j : Z.Opens) = i ⁻¹ᵁ (L.U j : X.Opens) := rfl

/-- The transition units of the restriction are the pullbacks of the transition units. -/
theorem restrict_g (j j' : L.J) :
    (L.restrict i).g j j' =
      pullUnit i (inf_preimage_le_preimage_inf i _ _) (L.g j j') := rfl

/-- The canonical chart of the restriction at `z` is the canonical chart of `L` at `i z`. -/
theorem keyChart_restrict (z : Z) : (L.restrict i).keyChart z = L.keyChart (i.base z) := rfl

/-- The restriction of the trivial line bundle has trivial transition units. -/
theorem restrict_trivial_g (j j' : ((trivial X).restrict i).J) :
    ((trivial X).restrict i).g j j' = 1 :=
  pullUnit_one _ _

end LineBundleData

/-! ## Residue fields and point stalks along closed immersions -/

section ClosedImmersionStalk

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The residue-field map of `i` at `z` on residue classes. -/
theorem residueFieldMap_residue_apply (z : Z) (t : X.presheaf.stalk (i.base z)) :
    (i.residueFieldMap z).hom (X.residue (i.base z) t) = Z.residue z (i.stalkMap z t) := by
  have := congrArg (fun f => f.hom t) (Scheme.residue_residueFieldMap i z)
  simpa using this

/-- The residue-field map of a closed immersion is bijective. -/
theorem residueFieldMap_bijective_of_isClosedImmersion (z : Z) :
    Function.Bijective (i.residueFieldMap z).hom := by
  refine ⟨(i.residueFieldMap z).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue (i.base z) c, residueFieldMap_residue_apply i z c⟩

/-- **The residue fields `κ(i z) ≅ κ(z)`** of a closed immersion, given by the residue-field map
of `i`. -/
noncomputable def closedResidueFieldEquiv (z : Z) :
    X.residueField (i.base z) ≃+* Z.residueField z :=
  RingEquiv.ofBijective (i.residueFieldMap z).hom
    (residueFieldMap_bijective_of_isClosedImmersion i z)

/-- `closedResidueFieldEquiv` is the residue-field map. -/
theorem closedResidueFieldEquiv_apply (z : Z) (a : X.residueField (i.base z)) :
    closedResidueFieldEquiv i z a = (i.residueFieldMap z).hom a := rfl

/-- `closedResidueFieldEquiv` on residue classes. -/
theorem closedResidueFieldEquiv_residue (z : Z) (t : X.presheaf.stalk (i.base z)) :
    closedResidueFieldEquiv i z (X.residue (i.base z) t) = Z.residue z (i.stalkMap z t) :=
  residueFieldMap_residue_apply i z t

variable {i}

omit [IsClosedImmersion i] in
/-- The image under a closed immersion of a specialisation. -/
theorem specializes_hom_base {z₁ z₂ : Z} (h : z₁ ⤳ z₂) : i.base z₁ ⤳ i.base z₂ :=
  i.base.hom.map_specializes h

variable (i)

omit [IsClosedImmersion i] in
/-- `pointStalkMap` commutes with the stalk and residue-field maps of `i`. -/
theorem residueFieldMap_pointStalkMap {z₁ z₂ : Z} (h : z₁ ⤳ z₂)
    (t : X.presheaf.stalk (i.base z₂)) :
    (i.residueFieldMap z₁).hom (pointStalkMap (specializes_hom_base (i := i) h) t) =
      pointStalkMap h (i.stalkMap z₂ t) := by
  rw [pointStalkMap_apply, pointStalkMap_apply, residueFieldMap_residue_apply,
    Scheme.Hom.stalkSpecializes_stalkMap_apply]

omit [IsClosedImmersion i] in
/-- The kernel of `pointStalkMap` of the image specialisation is the kernel of the stalk map of
`i` followed by the quotient map onto `pointStalk h`. -/
theorem ker_pointStalkMap_specializes_base {z₁ z₂ : Z} (h : z₁ ⤳ z₂) :
    RingHom.ker (pointStalkMap (specializes_hom_base (i := i) h)) =
      RingHom.ker ((Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))).comp
        (i.stalkMap z₂).hom) := by
  ext t
  rw [RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    RingHom.mem_ker, ← residueFieldMap_pointStalkMap,
    map_eq_zero_iff _ (i.residueFieldMap z₁).hom.injective]

/-- **Point stalks along a closed immersion.**  For `z₁ ⤳ z₂` in `Z`, the point stalk of
`i z₁ ⤳ i z₂` in `X` is isomorphic to the point stalk of `z₁ ⤳ z₂` in `Z`, through the
(surjective) stalk map of `i`. -/
noncomputable def pointStalkClosedEquiv {z₁ z₂ : Z} (h : z₁ ⤳ z₂) :
    pointStalk (specializes_hom_base (i := i) h) ≃+* pointStalk h :=
  (Ideal.quotEquivOfEq (ker_pointStalkMap_specializes_base i h)).trans
    (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp (i.stalkMap_surjective z₂)))

/-- `pointStalkClosedEquiv` on classes. -/
theorem pointStalkClosedEquiv_mk {z₁ z₂ : Z} (h : z₁ ⤳ z₂) (t : X.presheaf.stalk (i.base z₂)) :
    pointStalkClosedEquiv i h (Ideal.Quotient.mk _ t) =
      Ideal.Quotient.mk _ (i.stalkMap z₂ t) := rfl

/-- `pointStalkClosedEquiv` is compatible with the residue-field isomorphism
`closedResidueFieldEquiv i z₁ : κ(i z₁) ≃ κ(z₁)` of the fraction fields. -/
theorem closedResidueFieldEquiv_algebraMap_pointStalk {z₁ z₂ : Z} (h : z₁ ⤳ z₂)
    (a : pointStalk (specializes_hom_base (i := i) h)) :
    closedResidueFieldEquiv i z₁ (algebraMap _ (X.residueField (i.base z₁)) a) =
      algebraMap (pointStalk h) (Z.residueField z₁) (pointStalkClosedEquiv i h a) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [pointStalkClosedEquiv_mk, pointStalk_algebraMap_mk, pointStalk_algebraMap_mk]
  exact residueFieldMap_pointStalkMap i h t

/-- The Krull dimensions of the two point stalks agree. -/
theorem ringKrullDim_pointStalk_specializes_base {z₁ z₂ : Z} (h : z₁ ⤳ z₂) :
    ringKrullDim (pointStalk (specializes_hom_base (i := i) h)) = ringKrullDim (pointStalk h) :=
  ringKrullDim_eq_of_ringEquiv (pointStalkClosedEquiv i h)

/-- **`pointOrd` is preserved by closed immersions.**  For `z₁ ⤳ z₂` in `Z` and a unit `u` of
`κ(i z₁)`, the order of `u` along `i z₁ ⤳ i z₂` is the order of its image in `κ(z₁)` along
`z₁ ⤳ z₂`. -/
theorem pointOrd_closedResidueFieldEquiv [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    {z₁ z₂ : Z} (h : z₁ ⤳ z₂) (u : (X.residueField (i.base z₁))ˣ) :
    pointOrd h (Units.map (closedResidueFieldEquiv i z₁).toMonoidHom u) =
      pointOrd (specializes_hom_base (i := i) h) u := by
  have hdim := ringKrullDim_pointStalk_specializes_base i h
  by_cases hd : ringKrullDim (pointStalk h) = 1
  · have hd' := hdim.trans hd
    have := krullDimLE_one_pointStalk_of_eq_one hd
    have := krullDimLE_one_pointStalk_of_eq_one hd'
    have key := ordFrac_ringEquiv (pointStalkClosedEquiv i h) (closedResidueFieldEquiv i z₁)
      (closedResidueFieldEquiv_algebraMap_pointStalk i h) (u : X.residueField (i.base z₁))
    have e1 := pointOrd_of_eq_one hd (Units.map (closedResidueFieldEquiv i z₁).toMonoidHom u)
    have e2 := pointOrd_of_eq_one hd' u
    rw [Units.coe_map] at e1
    have e3 : ((Multiplicative.ofAdd (pointOrd h
        (Units.map (closedResidueFieldEquiv i z₁).toMonoidHom u)) : Multiplicative ℤ) : ℤᵐ⁰) =
        ((Multiplicative.ofAdd (pointOrd (specializes_hom_base (i := i) h) u) :
          Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [e1, e2]
      exact key
    exact Multiplicative.ofAdd.injective (WithZero.coe_injective e3)
  · rw [pointOrd_of_ne_one hd, pointOrd_of_ne_one (hdim ▸ hd)]

/-- `closedResidueFieldEquiv` sends the residue class of a section unit to the residue class of
its pullback. -/
theorem closedResidueFieldEquiv_sectionResidueUnit {U : Z.Opens} {V : X.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) {z : Z} (hz : z ∈ U) (a : Γ(X, V)ˣ) :
    Units.map (closedResidueFieldEquiv i z).toMonoidHom
        (sectionResidueUnit (show i.base z ∈ V from hUV hz) a) =
      sectionResidueUnit hz (pullUnit i hUV a) := by
  apply Units.ext
  rw [Units.coe_map, sectionResidueUnit_val, sectionResidueUnit_val, pullUnit_val]
  change closedResidueFieldEquiv i z (X.residue _ (X.presheaf.germ V _ _ (a : Γ(X, V)))) = _
  rw [closedResidueFieldEquiv_residue, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
    CommRingCat.comp_apply, Z.presheaf.germ_res_apply]

end ClosedImmersionStalk

/-! ## The projection formula for `c₁` at cycle level -/

section Projection

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

include i in
/-- `CovByDimension` passes to a closed subscheme, for any dimension function on it. -/
theorem covByDimension_of_isClosedImmersion {dimX : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dimX) (dimZ : DimensionFunction Z) :
    HomogeneityLocal.CovByDimension dimZ := by
  intro x η hxη
  rw [DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i x,
    DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i η]
  exact hcov _ _ (HomogeneityLocal.covBy_map_of_isClosedImmersion i hxη)

/-- The weights of the cycle pushforward along a closed immersion: any dimension function on `Z`
is the pullback of any dimension function on `X`. -/
theorem dimensionFunction_eq_comp_closedImmersion (dimX : DimensionFunction X)
    (dimZ : DimensionFunction Z) :
    (dimZ : Z → ℤ) = fun z => dimX (i.base z) :=
  funext fun z => DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z

/-- The cycle pushforward along a closed immersion, at a point of the image. -/
theorem closedImmersion_map_apply_base (dimX : DimensionFunction X) (dimZ : DimensionFunction Z)
    (c : AlgebraicCycle Z ℚ) (q : Z) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map i dimZ dimX c (i.base q) = c q := by
  rw [dimensionFunction_eq_comp_closedImmersion i dimX dimZ]
  exact AlgebraicCycle.map_closedImmersion_apply_image i (dimX : X → ℤ) c q

/-- The cycle pushforward along a closed immersion vanishes off the image. -/
theorem closedImmersion_map_apply_of_not_mem_range (dimX : DimensionFunction X)
    (dimZ : DimensionFunction Z)
    (c : AlgebraicCycle Z ℚ) {y : X} (hy : y ∉ Set.range i.base) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map i dimZ dimX c y = 0 := by
  rw [dimensionFunction_eq_comp_closedImmersion i dimX dimZ]
  exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range i (dimX : X → ℤ) c y hy

/-- The pushforward of the class of a point along a closed immersion is the class of its image. -/
theorem properPushforward_point_of_isClosedImmersion {dimX : DimensionFunction X}
    {dimZ : DimensionFunction Z}
    {k : ℤ} (z : Z) (hz : dimZ z = k) :
    cyclesOfDimension.properPushforward (dimensionY := dimX) i (cyclesOfDimension.point z hz) =
      cyclesOfDimension.point (i.base z)
        ((DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).symm.trans hz) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  change _root_.AlgebraicGeometry.AlgebraicCycle.map i dimZ dimX
    (cyclesOfDimension.point z hz : AlgebraicCycle Z ℚ) y = _
  by_cases hy : y ∈ Set.range i.base
  · obtain ⟨q, rfl⟩ := hy
    rw [closedImmersion_map_apply_base]
    by_cases hq : q = z
    · subst hq
      rw [cyclesOfDimension.point_apply_self, cyclesOfDimension.point_apply_self]
    · rw [cyclesOfDimension.point_apply_of_ne _ _ _ hq,
        cyclesOfDimension.point_apply_of_ne _ _ _ (fun e => hq (i.isClosedEmbedding.injective e))]
  · rw [closedImmersion_map_apply_of_not_mem_range i dimX dimZ _ hy,
      cyclesOfDimension.point_apply_of_ne _ _ _ (fun e => hy ⟨z, e.symm⟩)]

variable [IsLocallyNoetherian X] [NoetherianSpace X] [IsLocallyNoetherian Z] [NoetherianSpace Z]
  (L : LineBundleData X)

/-- **Frame divisors along a closed immersion.**  For `z ⤳ q` in `Z`, the coefficient at `q` of
the divisor of the frame of `L.restrict i` at `z` is the coefficient at `i q` of the divisor of
the frame of `L` at `i z`. -/
theorem divisor_restrict_pointFrame_apply_of_specializes (dimX : DimensionFunction X)
    (dimZ : DimensionFunction Z) {z q : Z} (h : z ⤳ q) :
    (((L.restrict i).pointFrame z).divisor dimZ : Z → ℚ) q =
      ((L.pointFrame (i.base z)).divisor dimX : X → ℚ) (i.base q) := by
  have hv : z ∈ i ⁻¹ᵁ (L.U (L.keyChart (i.base z)) : X.Opens) ⊓
      i ⁻¹ᵁ (L.U (L.keyChart (i.base q)) : X.Opens) :=
    memInf (L.mem_keyChart (i.base z))
      ((specializes_hom_base (i := i) h).mem_open (L.U (L.keyChart (i.base q))).1.2
        (L.mem_keyChart (i.base q)))
  have hv' : i.base z ∈ (L.U (L.keyChart (i.base z)) : X.Opens) ⊓
      (L.U (L.keyChart (i.base q)) : X.Opens) := hv
  have hZ := (L.restrict i).divisor_pointFrame_apply dimZ h hv
  have hX := L.divisor_pointFrame_apply dimX (specializes_hom_base (i := i) h) hv'
  have hs := closedResidueFieldEquiv_sectionResidueUnit i
    (Scheme.Hom.preimage_inf i).ge hv
    (L.g (L.keyChart (i.base z)) (L.keyChart (i.base q)))
  have ho := pointOrd_closedResidueFieldEquiv i h
    (sectionResidueUnit hv' (L.g (L.keyChart (i.base z)) (L.keyChart (i.base q))))
  rw [hZ, hX, ← ho, hs]
  rfl

/-- **Pushforward of frame divisors.**  The cycle pushforward along `i` of the divisor of the
frame of `L.restrict i` at `z` is the divisor of the frame of `L` at `i z`. -/
theorem map_divisor_restrict_pointFrame (dimX : DimensionFunction X)
    (dimZ : DimensionFunction Z) (z : Z) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map i dimZ dimX
        (((L.restrict i).pointFrame z).divisor dimZ) =
      (L.pointFrame (i.base z)).divisor dimX := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y ∈ Set.range i.base
  · obtain ⟨q, rfl⟩ := hy
    rw [closedImmersion_map_apply_base]
    by_cases h : z ⤳ q
    · exact divisor_restrict_pointFrame_apply_of_specializes i L dimX dimZ h
    · rw [LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ h,
        LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _
          (fun h' => h ((i.isClosedEmbedding.isInducing.specializes_iff).1 h'))]
  · rw [closedImmersion_map_apply_of_not_mem_range i dimX dimZ _ hy,
      LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _
        (fun h' => hy (h'.mem_closed i.isClosedEmbedding.isClosed_range ⟨z, rfl⟩))]

open RationalEquivalenceSystem.DescendingMap in
/-- **The projection formula for `c₁` at cycle level** (Fulton, Prop. 2.5(c), for a closed
immersion):
for a closed immersion `i : Z ⟶ X`, any dimension function `dimZ` on `Z` and a `(k+1)`-cycle `α`
on `Z`, `i_* (c₁(L|_Z) ∩ α) = c₁(L) ∩ i_* α`.  Here `c₁` is the cycle-level `c1Cycle` (valued in
the Chow group), `i_*` on the left is the Chow-group pushforward and on the right the cycle
pushforward.  The only hypothesis is `CovByDimension` for `dimX`. -/
theorem closedImmersionPushforward_c1Cycle_restrict {dimX : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dimX) (dimZ : DimensionFunction Z) (k : ℤ)
    (α : cyclesOfDimension Z dimZ (k + 1)) :
    closedImmersionPushforward (chowSystem dimZ k) i
        (chowSystem dimX k) (c1Cycle (L.restrict i) dimZ k α) =
      c1Cycle L dimX k (cyclesOfDimension.properPushforward i α) := by
  have hcovZ := covByDimension_of_isClosedImmersion i hcov dimZ
  refine LinearMap.congr_fun (c1Cycle_ext
    (f := (closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)).comp
      (c1Cycle (L.restrict i) dimZ k))
    (g := (c1Cycle L dimX k).comp (cyclesOfDimension.properPushforward i)) fun z => ?_) α
  by_cases hz : dimZ z = k + 1
  · have hz' : dimX (i.base z) = k + 1 :=
      (DimensionFunction.apply_eq_of_isClosedImmersion dimZ dimX i z).symm.trans hz
    rw [LinearMap.comp_apply, LinearMap.comp_apply, cyclesOfDimension.pointProj_eq_point hz,
      properPushforward_point_of_isClosedImmersion,
      c1Cycle_single hcovZ hz ((L.restrict i).pointFrame z),
      c1Cycle_single hcov hz' (L.pointFrame (i.base z)),
      closedImmersionPushforward_quotientMap]
    congr 1
    apply Subtype.ext
    exact map_divisor_restrict_pointFrame i L dimX dimZ z
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hz, map_zero, map_zero]

open RationalEquivalenceSystem.DescendingMap in
/-- **The projection formula for `c₁` on Chow groups**, for the descended first Chern classes
`c1` of `L` and of `L.restrict i`, given their `KillsRelations` witnesses:
`i_* (c₁(L|_Z) ∩ α) = c₁(L) ∩ i_* α` for `α ∈ A_{k+1}(Z)`. -/
theorem closedImmersionPushforward_c1_restrict {dimX : DimensionFunction X}
    {hcov : HomogeneityLocal.CovByDimension dimX} {dimZ : DimensionFunction Z}
    {hcovZ : HomogeneityLocal.CovByDimension dimZ} {k : ℤ}
    (hLZ : KillsRelations (L.restrict i) dimZ hcovZ k) (hL : KillsRelations L dimX hcov k)
    (α : (chowSystem dimZ (k + 1)).ChowGroup) :
    closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k) (c1 hLZ α) =
      c1 hL (closedImmersionPushforward (chowSystem dimZ (k + 1)) i (chowSystem dimX (k + 1))
        α) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
      (c1 hLZ ((chowSystem dimZ (k + 1)).quotientMap a)) =
    c1 hL (closedImmersionPushforward (chowSystem dimZ (k + 1)) i (chowSystem dimX (k + 1))
      ((chowSystem dimZ (k + 1)).quotientMap a))
  rw [c1_quotientMap_single, closedImmersionPushforward_quotientMap, c1_quotientMap_single,
    closedImmersionPushforward_c1Cycle_restrict i L hcov dimZ k a]

omit [IsLocallyNoetherian X] [NoetherianSpace X] [IsLocallyNoetherian Z] [NoetherianSpace Z] in
/-- The unit-differences hypothesis on the local rings of `X` passes to the local rings of `Z`
along the stalk maps of any morphism `Z ⟶ X` (in particular of a closed immersion). -/
theorem unitDifferences_stalk_of_hom (i : Z ⟶ X)
    (hU : ∀ x : X, VectorBundle.UnitDifferences (X.presheaf.stalk x)) (z : Z) :
    VectorBundle.UnitDifferences (Z.presheaf.stalk z) :=
  unitDifferences_of_ringHom (i.stalkMap z).hom (hU (i.base z))

open RationalEquivalenceSystem.DescendingMap in
/-- **The projection formula for `firstChernClass`**: for a closed immersion `i : Z ⟶ X` and
`α ∈ A_{k+1}(Z)`, `i_* (c₁(L|_Z) ∩ α) = c₁(L) ∩ i_* α`, where `c₁` is `firstChernClass`
(on `Z` for any of its admissible hypotheses `hUZ`, `hcovZ`; see
`unitDifferences_stalk_of_hom` and `covByDimension_of_isClosedImmersion`). -/
theorem closedImmersionPushforward_firstChernClass_restrict
    (hU : ∀ x : X, VectorBundle.UnitDifferences (X.presheaf.stalk x))
    (hUZ : ∀ z : Z, VectorBundle.UnitDifferences (Z.presheaf.stalk z))
    {dimX : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dimX)
    {dimZ : DimensionFunction Z} (hcovZ : HomogeneityLocal.CovByDimension dimZ) (k : ℤ)
    (α : (chowSystem dimZ (k + 1)).ChowGroup) :
    closedImmersionPushforward (chowSystem dimZ k) i (chowSystem dimX k)
        (firstChernClass hUZ hcovZ (L.restrict i) k α) =
      firstChernClass hU hcov L k
        (closedImmersionPushforward (chowSystem dimZ (k + 1)) i (chowSystem dimX (k + 1)) α) :=
  closedImmersionPushforward_c1_restrict i L _ _ α

end Projection

end GromovWitten.AlgebraicGeometry.IntersectionTheory
