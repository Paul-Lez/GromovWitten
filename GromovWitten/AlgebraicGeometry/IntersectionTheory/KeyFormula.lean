/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassDescent
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyInjective

/-!
# The key formula, and `c₁` on Chow groups

This file proves the key formula of Stacks, Lemma 42.27.1 (`lemma-key-formula`), and its two
consequences, Stacks, Lemmas 42.28.2 and 42.28.3: the first Chern class `c₁(L)` factors through
rational equivalence, and first Chern classes commute on Chow groups.

The tame symbol is not used.  Everything is proved for an arbitrary *symbol family*
`symb : PointSymbolFamily X`, i.e. a map `κ(w)ˣ × κ(w)ˣ → κ(v)ˣ` for every specialisation
`w ⤳ v`, under three explicit hypotheses:
* `hmul : symb.IsBimultiplicative`: multiplicativity in each argument;
* `hnorm : symb.IsNormalized`: `symb h u g = ū ^ ord_h(g)` and `symb h g u = ū ^ (-ord_h(g))`
  for a unit `u` of the point stalk `pointStalk h`;
* `hkey : symb.SatisfiesKeyLemma dim`: the conclusion of the key lemma (Stacks 42.6.3) at every
  pair `w ⤳ Q` with `dim w = dim Q + 2`.

The first two are only required at specialisations `h` with `ringKrullDim (pointStalk h) = 1`.

The setting is a scheme `X` with `[IsLocallyNoetherian X] [NoetherianSpace X]`, a dimension
function `dim` and `hcov : HomogeneityLocal.CovByDimension dim`.  For a rational section `s` of a
line bundle `L` along `pointSubscheme w` and a specialisation `v` of `w`, `s.pointCoordAt h` is
the coordinate of `s` in `κ(w)ˣ` in the canonical chart `L.keyChart v` at `v`, and
`L.pointFrame v` is the rational section along `pointSubscheme v` with coordinate `1` in that
chart.

## Main results

* `unitDifferences_pointStalk`: point stalks inherit `UnitDifferences` from the stalks of `X`
  (not used below; recorded for the instantiation of `symb` by the tame symbol).
* `LineBundleData.RationalSection.divisor_apply_eq_pointOrd`: the coefficient at `Q` of the
  divisor of a rational section along `pointSubscheme w` is a `pointOrd` along `w ⤳ Q`.
* `LineBundleData.divisor_pointFrame_apply`: coefficients of frame divisors.
* `LineBundleData.RationalSection.finite_setOf_not_isPointStalkUnit`: local finiteness of the
  locus where a coordinate is not a point-stalk unit.
* `keyFormula`: the key formula, an equality of cycles
  `∑ᵥ (ord_v(f_v) • div(frame_N v) - ord_v(g_v) • div(frame_L v)) = ∑ᵥ div(symb(f_v, g_v))`.
* `c1Cycle_divisor_pointSubscheme`: `c₁(N)` of the divisor of a rational section.
* `killsRelations_of_symbol`: `KillsRelations L dim hcov i` for every `L` and `i`.
* `c1Chow`: the resulting `c₁(L) : A_{i+1} →ₗ[ℚ] A_i` for every `L`.
* `c1_comm_of_symbol`, `c1Chow_comm_of_symbol`: `c₁(L) ∘ c₁(N) = c₁(N) ∘ c₁(L)` on `A_{i+2}`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

/-! ## Canonical charts, point coordinates and frames -/

section Charts

variable {X : Scheme.{u}}

/-- The canonical chart of a line bundle at a point `x`: the chart chosen by `L.covers x`. -/
noncomputable def LineBundleData.keyChart (L : LineBundleData X) (x : X) : L.J :=
  (L.covers x).choose

/-- A point lies in its canonical chart. -/
theorem LineBundleData.mem_keyChart (L : LineBundleData X) (x : X) :
    x ∈ (L.U (L.keyChart x) : X.Opens) :=
  (L.covers x).choose_spec

variable [IsLocallyNoetherian X] [NoetherianSpace X]

/-- If `w ⤳ v` and `v` lies in an open `U`, then the generic point of `pointSubscheme w` lies in
`U`. -/
theorem eta_pointSubscheme_mem {w v : X} (h : w ⤳ v) {U : X.Opens} (hv : v ∈ U) :
    (pointSubscheme w).eta ∈ U := by
  change (pointSubscheme w).genericPointImage ∈ U
  rw [genericPointImage_pointSubscheme]
  exact h.mem_open U.isOpen hv

omit [IsLocallyNoetherian X] [NoetherianSpace X] in
private theorem residueFieldCongr_toFunctionField (V : IntegralClosedSubscheme X) {w : X}
    (e : V.genericPointImage = w) {U : X.Opens} (hU : V.eta ∈ U) (hw : w ∈ U) (a : Γ(X, U)) :
    (X.residueFieldCongr e).hom (V.functionFieldIso.hom (V.toFunctionField U hU a)) =
      X.residue w (X.presheaf.germ U w hw a) := by
  subst e
  rw [Scheme.residueFieldCongr_refl]
  change V.functionFieldIso.hom (V.inclusion.stalkMap _ (X.presheaf.germ U V.eta hU a)) = _
  rw [V.stalkMap_functionFieldIso]

/-- `pointFieldEquiv w` sends the image of a section in the function field of `pointSubscheme w`
to its residue class at `w`. -/
theorem pointFieldEquiv_toFunctionField {w : X} {U : X.Opens} (hU : (pointSubscheme w).eta ∈ U)
    (hw : w ∈ U) (a : Γ(X, U)) :
    pointFieldEquiv w ((pointSubscheme w).toFunctionField U hU a) =
      X.residue w (X.presheaf.germ U w hw a) :=
  residueFieldCongr_toFunctionField _ (genericPointImage_pointSubscheme w) hU hw a

/-- The transition units of a line bundle along `pointSubscheme w`, read in `κ(w)`. -/
theorem LineBundleData.pointFieldEquiv_unitAt (L : LineBundleData X) {w : X} (j k : L.J)
    (h : (pointSubscheme w).eta ∈ (L.U j : X.Opens) ⊓ (L.U k : X.Opens))
    (hw : w ∈ (L.U j : X.Opens) ⊓ (L.U k : X.Opens)) :
    Units.map (pointFieldEquiv w).toMonoidHom (L.unitAt (pointSubscheme w) j k h) =
      sectionResidueUnit hw (L.g j k) :=
  Units.ext (pointFieldEquiv_toFunctionField h hw _)

namespace LineBundleData.RationalSection

variable {L : LineBundleData X} {w : X}

/-- The coordinate in `κ(w)` of a rational section of `L` along `pointSubscheme w`, in a chart
`j` containing `w`. -/
noncomputable def pointCoord (s : L.RationalSection (pointSubscheme w)) (j : L.J)
    (hj : (pointSubscheme w).eta ∈ (L.U j : X.Opens)) : (X.residueField w)ˣ :=
  Units.map (pointFieldEquiv w).toMonoidHom (s.coord j hj)

/-- Change of chart for `pointCoord`. -/
theorem pointCoord_eq_mul (s : L.RationalSection (pointSubscheme w)) (j k : L.J)
    (hj : (pointSubscheme w).eta ∈ (L.U j : X.Opens))
    (hk : (pointSubscheme w).eta ∈ (L.U k : X.Opens))
    (hw : w ∈ (L.U j : X.Opens) ⊓ (L.U k : X.Opens)) :
    s.pointCoord j hj = sectionResidueUnit hw (L.g j k) * s.pointCoord k hk := by
  rw [pointCoord, s.coord_eq_unitAt_mul_coord j k hj hk, map_mul,
    L.pointFieldEquiv_unitAt j k _ hw]
  rfl

/-- The coordinate in `κ(w)` of a rational section of `L` along `pointSubscheme w`, in the
canonical chart `L.keyChart v` of a specialisation `v` of `w`. -/
noncomputable def pointCoordAt (s : L.RationalSection (pointSubscheme w)) {v : X}
    (h : w ⤳ v) : (X.residueField w)ˣ :=
  s.pointCoord (L.keyChart v) (eta_pointSubscheme_mem h (L.mem_keyChart v))

end LineBundleData.RationalSection

/-- The frame of `L` at `v`: the rational section of `L` along `pointSubscheme v` with
coordinate `1` in the canonical chart `L.keyChart v`. -/
noncomputable def LineBundleData.pointFrame (L : LineBundleData X) (v : X) :
    L.RationalSection (pointSubscheme v) :=
  ⟨L.keyChart v, eta_pointSubscheme_mem (specializes_refl v) (L.mem_keyChart v), 1⟩

end Charts

/-! ## Units of point stalks coming from sections -/

section StalkUnits

variable {X : Scheme.{u}} {w v : X}

/-- The inclusion of the units of `pointStalk h` into `κ(w)ˣ`. -/
noncomputable def pointStalkUnitIncl (h : w ⤳ v) : (pointStalk h)ˣ →* (X.residueField w)ˣ :=
  Units.map (algebraMap (pointStalk h) (X.residueField w)).toMonoidHom

/-- The residue map from the units of `pointStalk h` to `κ(v)ˣ`. -/
noncomputable def pointStalkResidueUnit (h : w ⤳ v) : (pointStalk h)ˣ →* (X.residueField v)ˣ :=
  Units.map ((pointStalkResidueEquiv h).toRingHom.comp (residue (pointStalk h))).toMonoidHom

/-- The unit of `pointStalk h` given by a unit of the sections over an open containing `v`. -/
noncomputable def pointStalkSectionUnit (h : w ⤳ v) {U : X.Opens} (hv : v ∈ U) (a : Γ(X, U)ˣ) :
    (pointStalk h)ˣ :=
  Units.map ((Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))).comp
    (X.presheaf.germ U v hv).hom).toMonoidHom a

/-- The image in `κ(w)` of `pointStalkSectionUnit` is the residue class of the section at `w`. -/
theorem pointStalkUnitIncl_sectionUnit (h : w ⤳ v) {U : X.Opens} (hv : v ∈ U) (hw : w ∈ U)
    (a : Γ(X, U)ˣ) :
    pointStalkUnitIncl h (pointStalkSectionUnit h hv a) = sectionResidueUnit hw a := by
  refine Units.ext ?_
  change pointStalkMap h (X.presheaf.germ U v hv a) = X.residue w (X.presheaf.germ U w hw a)
  rw [pointStalkMap_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The residue in `κ(v)` of `pointStalkSectionUnit` is the residue class of the section at
`v`. -/
theorem pointStalkResidueUnit_sectionUnit (h : w ⤳ v) {U : X.Opens} (hv : v ∈ U)
    (a : Γ(X, U)ˣ) :
    pointStalkResidueUnit h (pointStalkSectionUnit h hv a) = sectionResidueUnit hv a :=
  Units.ext (pointStalkResidueEquiv_residue_mk h _)

variable [IsLocallyNoetherian X]

/-- `pointOrd` vanishes on units of the point stalk. -/
theorem pointOrd_pointStalkUnitIncl (h : w ⤳ v) (u : (pointStalk h)ˣ) :
    pointOrd h (pointStalkUnitIncl h u) = 0 := by
  by_cases hd : ringKrullDim (pointStalk h) = 1
  · have := krullDimLE_one_pointStalk_of_eq_one hd
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective (α := Multiplicative ℤ)
    rw [pointOrd_of_eq_one hd]
    change Ring.ordFrac (pointStalk h)
      (algebraMap (pointStalk h) (X.residueField w) (u : pointStalk h)) = _
    rw [Ring.ordFrac_of_isUnit u.isUnit]
    rfl
  · exact pointOrd_of_ne_one hd _

/-- `pointOrd` of an integer power. -/
theorem pointOrd_zpow (h : w ⤳ v) (u : (X.residueField w)ˣ) (n : ℤ) :
    pointOrd h (u ^ n) = n * pointOrd h u := by
  have := map_zpow (pointOrdHom h) u n
  rw [pointOrdHom_apply, pointOrdHom_apply] at this
  have := congrArg Multiplicative.toAdd this
  rw [toAdd_ofAdd, toAdd_zpow, toAdd_ofAdd] at this
  rw [this, smul_eq_mul]

end StalkUnits

/-! ## Coefficients of divisors of rational sections along `pointSubscheme w` -/

section Coefficients

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

private theorem divisor_apply_eq_pointOrd_aux {L : LineBundleData X}
    {V : IntegralClosedSubscheme X} (s : L.RationalSection V) (dim : DimensionFunction X) {w Q : X}
    (e : V.genericPointImage = w) (h : w ⤳ Q) (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens))
    (hQ : Q ∈ (L.U j : X.Opens)) :
    (s.divisor dim : X → ℚ) Q = pointOrd h (Units.map
      ((X.residueFieldCongr e).hom.hom.toMonoidHom.comp
        V.functionFieldEquivResidueField.toMonoidHom) (s.coord j hj)) := by
  subst e
  obtain ⟨q, rfl⟩ := V.mem_range_of_specializes h
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  rw [AlgebraicCycle.map_closedImmersion_apply_image V.inclusion (dim : X → ℤ),
    LineBundleData.RationalSection.divisorCycle_apply,
    LineBundleData.RationalSection.ord_well_defined _ j q hQ, V.ord_eq_pointOrd q]
  congr 2

omit [IsLocallyNoetherian X] in
private theorem divisor_apply_eq_zero_aux {L : LineBundleData X}
    {V : IntegralClosedSubscheme X} (s : L.RationalSection V) (dim : DimensionFunction X) {w Q : X}
    (e : V.genericPointImage = w) (h : ¬ w ⤳ Q) : (s.divisor dim : X → ℚ) Q = 0 := by
  subst e
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  by_cases hmem : Q ∈ Set.range V.inclusion.base
  · obtain ⟨q, rfl⟩ := hmem
    exact absurd (V.genericPointImage_specializes q) h
  · exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range V.inclusion
      (dim : X → ℤ) _ Q hmem

variable [NoetherianSpace X]

/-- **Coefficients of the divisor of a rational section along `pointSubscheme w`.**  For
`w ⤳ Q` and a chart `j` containing `Q`, the coefficient at `Q` of the divisor of `s` is the
`pointOrd` along `w ⤳ Q` of the coordinate of `s` in the chart `j`. -/
theorem LineBundleData.RationalSection.divisor_apply_eq_pointOrd {L : LineBundleData X} {w : X}
    (s : L.RationalSection (pointSubscheme w)) (dim : DimensionFunction X) {Q : X} (h : w ⤳ Q)
    (j : L.J) (hj : (pointSubscheme w).eta ∈ (L.U j : X.Opens)) (hQ : Q ∈ (L.U j : X.Opens)) :
    (s.divisor dim : X → ℚ) Q = pointOrd h (s.pointCoord j hj) :=
  divisor_apply_eq_pointOrd_aux s dim (genericPointImage_pointSubscheme w) h j hj hQ

/-- The coefficient at `Q` of the divisor of a rational section along `pointSubscheme w`
vanishes unless `w ⤳ Q`. -/
theorem LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes
    {L : LineBundleData X} {w : X} (s : L.RationalSection (pointSubscheme w))
    (dim : DimensionFunction X) {Q : X} (h : ¬ w ⤳ Q) : (s.divisor dim : X → ℚ) Q = 0 :=
  divisor_apply_eq_zero_aux s dim (genericPointImage_pointSubscheme w) h

/-- The coordinate of the frame `L.pointFrame v` in its own chart is `1`. -/
theorem LineBundleData.pointCoord_pointFrame (L : LineBundleData X) (v : X)
    (hj : (pointSubscheme v).eta ∈ (L.U (L.keyChart v) : X.Opens)) :
    (L.pointFrame v).pointCoord (L.keyChart v) hj = 1 := by
  change Units.map _ ((L.pointFrame v).coord (L.pointFrame v).j₀ (L.pointFrame v).hj₀) = 1
  rw [LineBundleData.RationalSection.coord_j₀]
  exact map_one _

/-- **Coefficients of frame divisors.**  For `v ⤳ Q`, the coefficient at `Q` of the divisor of
the frame `L.pointFrame v` is minus the `pointOrd` along `v ⤳ Q` of the residue class at `v` of
the transition unit from the canonical chart at `v` to the canonical chart at `Q`. -/
theorem LineBundleData.divisor_pointFrame_apply (L : LineBundleData X) (dim : DimensionFunction X)
    {v Q : X} (h : v ⤳ Q)
    (hv : v ∈ (L.U (L.keyChart v) : X.Opens) ⊓ (L.U (L.keyChart Q) : X.Opens)) :
    ((L.pointFrame v).divisor dim : X → ℚ) Q =
      - pointOrd h (sectionResidueUnit hv (L.g (L.keyChart v) (L.keyChart Q))) := by
  have hQ := eta_pointSubscheme_mem h (L.mem_keyChart Q)
  have hv' := eta_pointSubscheme_mem (specializes_refl v) (L.mem_keyChart v)
  rw [(L.pointFrame v).divisor_apply_eq_pointOrd dim h _ hQ (L.mem_keyChart Q)]
  have hc := (L.pointFrame v).pointCoord_eq_mul _ _ hv' hQ hv
  rw [L.pointCoord_pointFrame v hv'] at hc
  rw [eq_inv_of_mul_eq_one_right hc.symm, pointOrd_inv]
  push_cast
  rfl

end Coefficients

/-! ## Unit differences pass to point stalks -/

section UnitDifferences

/-- `UnitDifferences` passes along any ring hom to a nontrivial ring: the image of the infinite
set stays infinite, because the images of two distinct elements differ by a unit, hence are
distinct. -/
theorem unitDifferences_of_ringHom {R S : Type u} [CommRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (h : VectorBundle.UnitDifferences R) : VectorBundle.UnitDifferences S := by
  obtain ⟨Λ, hinf, hunit⟩ := h
  have hinj : Set.InjOn f Λ := by
    intro x hx y hy hxy
    by_contra hne
    have hu := (hunit x hx y hy hne).map f
    rw [map_sub, hxy, sub_self] at hu
    exact not_isUnit_zero hu
  refine ⟨f '' Λ, hinf.image hinj, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  have hxy : x ≠ y := fun hcon ↦ hne (by rw [hcon])
  rw [← map_sub]
  exact (hunit x hx y hy hxy).map f

/-- Every point stalk `pointStalk (w ⤳ v)` inherits `UnitDifferences` from the stalk
`𝒪_{X,v}`. -/
theorem unitDifferences_pointStalk {X : Scheme.{u}} {w v : X} (h : w ⤳ v)
    (hU : VectorBundle.UnitDifferences (X.presheaf.stalk v)) :
    VectorBundle.UnitDifferences (pointStalk h) :=
  unitDifferences_of_ringHom (Ideal.Quotient.mk _) hU

end UnitDifferences

/-! ## Units of point stalks and local finiteness -/

section Finiteness

variable {X : Scheme.{u}}

/-- `f ∈ κ(w)ˣ` is the image of a unit of the point stalk `pointStalk h`. -/
def IsPointStalkUnit {w v : X} (h : w ⤳ v) (f : (X.residueField w)ˣ) : Prop :=
  ∃ a : (pointStalk h)ˣ, pointStalkUnitIncl h a = f

/-- Point-stalk units are closed under multiplication. -/
theorem IsPointStalkUnit.mul {w v : X} {h : w ⤳ v} {f g : (X.residueField w)ˣ}
    (hf : IsPointStalkUnit h f) (hg : IsPointStalkUnit h g) : IsPointStalkUnit h (f * g) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨a * b, map_mul _ a b⟩

variable [IsLocallyNoetherian X]

/-- `pointOrd` vanishes on point-stalk units. -/
theorem IsPointStalkUnit.pointOrd_eq_zero {w v : X} {h : w ⤳ v} {f : (X.residueField w)ˣ}
    (hf : IsPointStalkUnit h f) : pointOrd h f = 0 := by
  obtain ⟨a, rfl⟩ := hf
  exact pointOrd_pointStalkUnitIncl h a

variable [NoetherianSpace X]

/-- **Local finiteness for coordinates of rational sections.**  Only finitely many
specialisations `v` of `w` with `dim w = dim v + 1` have the property that the coordinate of `s`
in the canonical chart at `v` is not a point-stalk unit at `v`. -/
theorem LineBundleData.RationalSection.finite_setOf_not_isPointStalkUnit
    (dim : DimensionFunction X) {L : LineBundleData X} {w : X}
    (s : L.RationalSection (pointSubscheme w)) :
    {v : X | ∃ h : w ⤳ v, dim w = dim v + 1 ∧ ¬ IsPointStalkUnit h (s.pointCoordAt h)}.Finite := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun j : L.J ↦ ((L.U j : X.Opens) : Set X)) (fun j ↦ (L.U j : X.Opens).isOpen)
    (fun x _ ↦ Set.mem_iUnion.2 (L.covers x))
  let T : L.J → Set X := fun k ↦
    if hk : w ∈ (L.U k : X.Opens) then
      {v : X | ∃ h : w ⤳ v, dim w = dim v + 1 ∧
        ¬ ∃ a : (pointStalk h)ˣ, algebraMap (pointStalk h) (X.residueField w) a =
          s.pointCoord k (eta_pointSubscheme_mem (specializes_refl w) hk)}
    else ∅
  have hT : ∀ k, (T k).Finite := by
    intro k
    by_cases hk : w ∈ (L.U k : X.Opens)
    · simp only [T, dif_pos hk]
      exact finite_setOf_not_pointStalk_unit dim w _
    · simp only [T, dif_neg hk]
      exact Set.finite_empty
  refine (t.finite_toSet.biUnion fun k _ ↦ hT k).subset ?_
  rintro v ⟨h, hd, hnot⟩
  obtain ⟨k, hkt, hvk⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
  have hwk : w ∈ (L.U k : X.Opens) := h.mem_open (L.U k : X.Opens).isOpen hvk
  refine Set.mem_iUnion₂.2 ⟨k, hkt, ?_⟩
  simp only [T, dif_pos hwk]
  refine ⟨h, hd, fun ⟨a, ha⟩ ↦ hnot ?_⟩
  have hv : v ∈ (L.U (L.keyChart v) : X.Opens) ⊓ (L.U k : X.Opens) :=
    memInf (L.mem_keyChart v) hvk
  have hw : w ∈ (L.U (L.keyChart v) : X.Opens) ⊓ (L.U k : X.Opens) :=
    memInf (h.mem_open (L.U (L.keyChart v) : X.Opens).isOpen (L.mem_keyChart v)) hwk
  refine ⟨pointStalkSectionUnit h hv (L.g (L.keyChart v) k) * a, ?_⟩
  rw [LineBundleData.RationalSection.pointCoordAt, s.pointCoord_eq_mul _ k _
    (eta_pointSubscheme_mem (specializes_refl w) hwk) hw, map_mul,
    pointStalkUnitIncl_sectionUnit h hv hw]
  congr 1
  exact Units.ext ha

end Finiteness

/-! ## Symbol families -/

section Symbols

variable (X : Scheme.{u})

/-- A **symbol family** on `X`: for every specialisation `w ⤳ v`, a map
`κ(w)ˣ × κ(w)ˣ → κ(v)ˣ`.  (The intended example is the tame symbol of the one-dimensional local
domain `pointStalk h`; no property is built in, see `IsBimultiplicative`, `IsNormalized` and
`SatisfiesKeyLemma`.) -/
abbrev PointSymbolFamily : Type u :=
  ∀ {w v : X}, w ⤳ v → (X.residueField w)ˣ → (X.residueField w)ˣ → (X.residueField v)ˣ

variable {X}

namespace PointSymbolFamily

/-- The symbol at every specialisation `h` with `pointStalk h` of Krull dimension one is
multiplicative in each argument separately. -/
def IsBimultiplicative (symb : PointSymbolFamily X) : Prop :=
  ∀ {w v : X} (h : w ⤳ v), ringKrullDim (pointStalk h) = 1 →
    (∀ f f' g : (X.residueField w)ˣ, symb h (f * f') g = symb h f g * symb h f' g) ∧
    (∀ f g g' : (X.residueField w)ˣ, symb h f (g * g') = symb h f g * symb h f g')

/-- The normalisation of the tame symbol on units: at every specialisation `h` with `pointStalk h`
of Krull dimension one, for a unit `u` of `pointStalk h` and any `g`,
`symb h u g = ū ^ ord_h(g)` and `symb h g u = ū ^ (-ord_h(g))`, where `ū` is the residue class of
`u` in `κ(v)`. -/
def IsNormalized [IsLocallyNoetherian X] (symb : PointSymbolFamily X) : Prop :=
  ∀ {w v : X} (h : w ⤳ v), ringKrullDim (pointStalk h) = 1 →
    ∀ (u : (pointStalk h)ˣ) (g : (X.residueField w)ˣ),
      symb h (pointStalkUnitIncl h u) g = pointStalkResidueUnit h u ^ pointOrd h g ∧
      symb h g (pointStalkUnitIncl h u) = pointStalkResidueUnit h u ^ (-pointOrd h g)

/-- The conclusion of the key lemma (Stacks 42.6.3) for the symbol family: for `w ⤳ Q` with
`dim w = dim Q + 2` and all `f g ∈ κ(w)ˣ`, the orders along `v ⤳ Q` of the symbols
`symb (w ⤳ v) f g`, over the points `v` between `w` and `Q` with `dim w = dim v + 1`, sum to
zero. -/
def SatisfiesKeyLemma [IsLocallyNoetherian X] (dim : DimensionFunction X)
    (symb : PointSymbolFamily X) : Prop :=
  ∀ {w Q : X}, w ⤳ Q → dim w = dim Q + 2 → ∀ f g : (X.residueField w)ˣ,
    ∑ᶠ v : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1}, pointOrd v.2.2.1 (symb v.2.1 f g) = 0

end PointSymbolFamily

end Symbols

/-! ## The key formula -/

section KeyFormula

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

omit [IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The coefficient of a finite sum of cycles is the sum of the coefficients. -/
private theorem finsum_cycle_apply' {ι : Type*} (F : ι → AlgebraicCycle X ℚ)
    (hF : (Function.support F).Finite) (x : X) :
    ((∑ᶠ i, F i : AlgebraicCycle X ℚ) : X → ℚ) x = ∑ᶠ i, ((F i : X → ℚ) x) := by
  let e : AlgebraicCycle X ℚ →+ ℚ :=
    { toFun := fun z ↦ (z : X → ℚ) x
      map_zero' := rfl
      map_add' := fun z z' ↦ by rw [Function.locallyFinsuppWithin.coe_add]; rfl }
  exact e.map_finsum hF

omit [IsLocallyNoetherian X] [NoetherianSpace X] in
private theorem finite_support_apply {ι : Type*} {F : ι → AlgebraicCycle X ℚ}
    (hF : (Function.support F).Finite) (x : X) :
    (Function.support fun i ↦ (F i : X → ℚ) x).Finite :=
  hF.subset fun i hi h0 ↦ hi (by change (F i : X → ℚ) x = 0; rw [h0]; rfl)

omit [NoetherianSpace X] in
/-- A symbol of two point-stalk units is trivial. -/
theorem PointSymbolFamily.eq_one_of_isPointStalkUnit {symb : PointSymbolFamily X}
    (hnorm : symb.IsNormalized) {w v : X} (h : w ⤳ v) (hd : ringKrullDim (pointStalk h) = 1)
    {f g : (X.residueField w)ˣ} (hf : IsPointStalkUnit h f) (hg : IsPointStalkUnit h g) :
    symb h f g = 1 := by
  obtain ⟨a, rfl⟩ := hf
  rw [(hnorm h hd a g).1, hg.pointOrd_eq_zero, zpow_zero]

/-- Under `CovByDimension`, the coefficient at `Q` of the divisor of a rational section along
`pointSubscheme v` vanishes unless `v ⤳ Q` and `dim v = dim Q + 1`. -/
theorem LineBundleData.RationalSection.divisor_apply_eq_zero_of_not {L : LineBundleData X}
    (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim) {v : X}
    (s : L.RationalSection (pointSubscheme v)) {Q : X} (h : ¬ (v ⤳ Q ∧ dim v = dim Q + 1)) :
    (s.divisor dim : X → ℚ) Q = 0 := by
  by_cases hvQ : v ⤳ Q
  · rw [s.divisor_apply_eq_pointOrd dim hvQ (L.keyChart Q)
      (eta_pointSubscheme_mem hvQ (L.mem_keyChart Q)) (L.mem_keyChart Q),
      pointOrd_eq_zero_of_dim_ne dim hcov hvQ (fun hd ↦ h ⟨hvQ, hd⟩)]
    rfl
  · exact s.divisor_apply_eq_zero_of_not_specializes dim hvQ

/-- Under `CovByDimension`, the coefficient at `Q` of the divisor of `pointGenerator x u`
vanishes unless `x ⤳ Q` and `dim x = dim Q + 1`. -/
theorem divisor_pointGenerator_apply_eq_zero_of_not (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (x : X) (u : (X.residueField x)ˣ) {Q : X}
    (h : ¬ (x ⤳ Q ∧ dim x = dim Q + 1)) : ((pointGenerator x u).divisor dim : X → ℚ) Q = 0 := by
  by_cases hxQ : x ⤳ Q
  · exact divisor_pointGenerator_apply_eq_zero_of_dim_ne dim hcov x u Q (fun hd ↦ h ⟨hxQ, hd⟩)
  · exact divisor_pointGenerator_apply_eq_zero dim x u Q hxQ

variable {L N : LineBundleData X} {w : X}

/-- The codimension-one specialisations `v` of `w` at which the coordinates of `s` and `t` in
the canonical charts at `v` are not both point-stalk units form a finite set. -/
theorem LineBundleData.RationalSection.finite_setOf_not_isPointStalkUnit_and
    (dim : DimensionFunction X) (s : L.RationalSection (pointSubscheme w))
    (t : N.RationalSection (pointSubscheme w)) :
    {v : {v : X // w ⤳ v ∧ dim w = dim v + 1} | ¬ (IsPointStalkUnit v.2.1 (s.pointCoordAt v.2.1) ∧
      IsPointStalkUnit v.2.1 (t.pointCoordAt v.2.1))}.Finite := by
  refine (((s.finite_setOf_not_isPointStalkUnit dim).union
    (t.finite_setOf_not_isPointStalkUnit dim)).preimage Subtype.val_injective.injOn).subset ?_
  intro v hv
  by_cases hs : IsPointStalkUnit v.2.1 (s.pointCoordAt v.2.1)
  · exact Or.inr ⟨v.2.1, v.2.2, fun ht ↦ hv ⟨hs, ht⟩⟩
  · exact Or.inl ⟨v.2.1, v.2.2, hs⟩

/-- Finiteness of the support of `v ↦ ord_v(s) • D v` over the codimension-one specialisations
`v` of `w`, where `ord_v(s)` is the order of the coordinate of `s` in the canonical chart at
`v`. -/
theorem LineBundleData.RationalSection.finite_support_pointOrd_smul {M : Type*}
    [AddCommGroup M] [Module ℚ M] (dim : DimensionFunction X)
    (s : L.RationalSection (pointSubscheme w)) (D : {v : X // w ⤳ v ∧ dim w = dim v + 1} → M) :
    (Function.support fun v : {v : X // w ⤳ v ∧ dim w = dim v + 1} ↦
      (pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • D v).Finite := by
  refine ((s.finite_setOf_not_isPointStalkUnit dim).preimage
    Subtype.val_injective.injOn).subset ?_
  intro v hv
  refine ⟨v.2.1, v.2.2, fun hu ↦ hv ?_⟩
  change (pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • D v = 0
  rw [hu.pointOrd_eq_zero, Int.cast_zero, zero_smul]

/-- Finiteness of the support of the left-hand side of the key formula. -/
theorem finite_support_keyFormula_lhs (dim : DimensionFunction X)
    (s : L.RationalSection (pointSubscheme w)) (t : N.RationalSection (pointSubscheme w)) :
    (Function.support fun v : {v : X // w ⤳ v ∧ dim w = dim v + 1} ↦
      ((pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • (N.pointFrame v.1).divisor dim -
        (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) • (L.pointFrame v.1).divisor dim)).Finite :=
  ((s.finite_support_pointOrd_smul dim _).union (t.finite_support_pointOrd_smul dim _)).subset
    (Function.support_sub _ _)

/-- Finiteness of the support of the right-hand side of the key formula. -/
theorem finite_support_keyFormula_rhs (dim : DimensionFunction X) {symb : PointSymbolFamily X}
    (hnorm : symb.IsNormalized) (s : L.RationalSection (pointSubscheme w))
    (t : N.RationalSection (pointSubscheme w)) :
    (Function.support fun v : {v : X // w ⤳ v ∧ dim w = dim v + 1} ↦
      (pointGenerator v.1 (symb v.2.1 (s.pointCoordAt v.2.1) (t.pointCoordAt v.2.1))).divisor
        dim).Finite := by
  refine (s.finite_setOf_not_isPointStalkUnit_and dim t).subset ?_
  intro v hv hu
  apply hv
  change (pointGenerator v.1 _).divisor dim = 0
  rw [PointSymbolFamily.eq_one_of_isPointStalkUnit hnorm v.2.1
    (ringKrullDim_pointStalk_eq_one_of_dim_eq dim v.2.1 v.2.2) hu.1 hu.2,
    LineBundleInjective.divisor_pointGenerator_one dim]

/-- **The key formula** (Stacks, Lemma 42.27.1, `lemma-key-formula`), for an arbitrary symbol
family `symb` that is bimultiplicative (`hmul`), normalised on units (`hnorm`) and satisfies the
conclusion of the key lemma (`hkey`).  Let `s`, `t` be rational sections of the line bundles
`L`, `N` along `pointSubscheme w`.  For a codimension-one specialisation `v` of `w`, write
`f_v`, `g_v ∈ κ(w)ˣ` for the coordinates of `s`, `t` in the canonical charts at `v`.  Then, as
cycles on `X`, with (finite) sums over the `v` with `w ⤳ v` and `dim w = dim v + 1`,
`∑ (ord_v(f_v) • div(frame_N v) - ord_v(g_v) • div(frame_L v)) = ∑ div(symb(f_v, g_v))`,
where `frame_L v = L.pointFrame v` is the section along `pointSubscheme v` with coordinate `1` in
the canonical chart of `L` at `v`, and `div(symb(f_v, g_v))` is the divisor of the point
generator of `symb (w ⤳ v) f_v g_v ∈ κ(v)ˣ`.  Both families have finite support
(`finite_support_keyFormula_lhs`, `finite_support_keyFormula_rhs`). -/
theorem keyFormula {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L N : LineBundleData X) {w : X}
    (s : L.RationalSection (pointSubscheme w)) (t : N.RationalSection (pointSubscheme w)) :
    ∑ᶠ v : {v : X // w ⤳ v ∧ dim w = dim v + 1},
        ((pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • (N.pointFrame v.1).divisor dim -
          (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) • (L.pointFrame v.1).divisor dim) =
      ∑ᶠ v : {v : X // w ⤳ v ∧ dim w = dim v + 1},
        (pointGenerator v.1 (symb v.2.1 (s.pointCoordAt v.2.1) (t.pointCoordAt v.2.1))).divisor
          dim := by
  classical
  ext Q
  have hLfin := finite_support_keyFormula_lhs dim s t
  have hRfin := finite_support_keyFormula_rhs dim hnorm s t
  rw [finsum_cycle_apply' _ hLfin Q, finsum_cycle_apply' _ hRfin Q]
  have hLfin' := finite_support_apply hLfin Q
  have hRfin' := finite_support_apply hRfin Q
  simp only [Function.locallyFinsuppWithin.coe_sub, Function.locallyFinsuppWithin.coe_rational_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hLfin' ⊢
  by_cases hQ : w ⤳ Q ∧ dim w = dim Q + 2
  swap
  · have hv : ∀ v : {v : X // w ⤳ v ∧ dim w = dim v + 1}, ¬ (v.1 ⤳ Q ∧ dim v.1 = dim Q + 1) :=
      fun v hv ↦ hQ ⟨v.2.1.trans hv.1, by have := v.2.2; omega⟩
    rw [finsum_eq_zero_of_forall_eq_zero, finsum_eq_zero_of_forall_eq_zero]
    · intro v
      exact divisor_pointGenerator_apply_eq_zero_of_not dim hcov _ _ (hv v)
    · intro v
      rw [(N.pointFrame v.1).divisor_apply_eq_zero_of_not dim hcov (hv v),
        (L.pointFrame v.1).divisor_apply_eq_zero_of_not dim hcov (hv v)]
      ring
  obtain ⟨hwQ, hdQ⟩ := hQ
  have hFQ := eta_pointSubscheme_mem hwQ (L.mem_keyChart Q)
  have hGQ := eta_pointSubscheme_mem hwQ (N.mem_keyChart Q)
  set F := s.pointCoord (L.keyChart Q) hFQ
  set G := t.pointCoord (N.keyChart Q) hGQ
  let K : {v : X // w ⤳ v ∧ dim w = dim v + 1} → ℚ := fun v ↦
    if hvQ : v.1 ⤳ Q then (pointOrd hvQ (symb v.2.1 F G) : ℚ) else 0
  have hpt : ∀ v : {v : X // w ⤳ v ∧ dim w = dim v + 1},
      ((pointGenerator v.1 (symb v.2.1 (s.pointCoordAt v.2.1) (t.pointCoordAt v.2.1))).divisor
          dim : X → ℚ) Q =
        ((pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) * ((N.pointFrame v.1).divisor dim : X → ℚ) Q -
          (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) *
            ((L.pointFrame v.1).divisor dim : X → ℚ) Q) + K v := by
    rintro ⟨x, hwx, hdx⟩
    by_cases hxQ : x ⤳ Q
    swap
    · have hn : ¬ (x ⤳ Q ∧ dim x = dim Q + 1) := fun h ↦ hxQ h.1
      simp only [K, dif_neg hxQ]
      rw [divisor_pointGenerator_apply_eq_zero_of_not dim hcov _ _ hn,
        (N.pointFrame x).divisor_apply_eq_zero_of_not dim hcov hn,
        (L.pointFrame x).divisor_apply_eq_zero_of_not dim hcov hn]
      ring
    simp only [K, dif_pos hxQ]
    have hd1 := ringKrullDim_pointStalk_eq_one_of_dim_eq dim hwx hdx
    have hxL : x ∈ (L.U (L.keyChart x) : X.Opens) ⊓ (L.U (L.keyChart Q) : X.Opens) :=
      memInf (L.mem_keyChart x) (hxQ.mem_open (L.U _ : X.Opens).isOpen (L.mem_keyChart Q))
    have hxN : x ∈ (N.U (N.keyChart x) : X.Opens) ⊓ (N.U (N.keyChart Q) : X.Opens) :=
      memInf (N.mem_keyChart x) (hxQ.mem_open (N.U _ : X.Opens).isOpen (N.mem_keyChart Q))
    have hwL : w ∈ (L.U (L.keyChart x) : X.Opens) ⊓ (L.U (L.keyChart Q) : X.Opens) :=
      memInf (hwx.mem_open (L.U _ : X.Opens).isOpen (L.mem_keyChart x))
        (hwQ.mem_open (L.U _ : X.Opens).isOpen (L.mem_keyChart Q))
    have hwN : w ∈ (N.U (N.keyChart x) : X.Opens) ⊓ (N.U (N.keyChart Q) : X.Opens) :=
      memInf (hwx.mem_open (N.U _ : X.Opens).isOpen (N.mem_keyChart x))
        (hwQ.mem_open (N.U _ : X.Opens).isOpen (N.mem_keyChart Q))
    set a := pointStalkSectionUnit hwx hxL (L.g (L.keyChart x) (L.keyChart Q))
    set b := pointStalkSectionUnit hwx hxN (N.g (N.keyChart x) (N.keyChart Q))
    have hf : s.pointCoordAt hwx = pointStalkUnitIncl hwx a * F := by
      rw [LineBundleData.RationalSection.pointCoordAt, s.pointCoord_eq_mul _ _ _ hFQ hwL,
        pointStalkUnitIncl_sectionUnit hwx hxL hwL]
    have hg : t.pointCoordAt hwx = pointStalkUnitIncl hwx b * G := by
      rw [LineBundleData.RationalSection.pointCoordAt, t.pointCoord_eq_mul _ _ _ hGQ hwN,
        pointStalkUnitIncl_sectionUnit hwx hxN hwN]
    have hfrL : ((L.pointFrame x).divisor dim : X → ℚ) Q =
        - pointOrd hxQ (pointStalkResidueUnit hwx a) := by
      rw [L.divisor_pointFrame_apply dim hxQ hxL, pointStalkResidueUnit_sectionUnit]
    have hfrN : ((N.pointFrame x).divisor dim : X → ℚ) Q =
        - pointOrd hxQ (pointStalkResidueUnit hwx b) := by
      rw [N.divisor_pointFrame_apply dim hxQ hxN, pointStalkResidueUnit_sectionUnit]
    have hsymb : symb hwx (pointStalkUnitIncl hwx a * F) (pointStalkUnitIncl hwx b * G) =
        pointStalkResidueUnit hwx a ^ pointOrd hwx (pointStalkUnitIncl hwx b * G) *
          (pointStalkResidueUnit hwx b ^ (-pointOrd hwx F) * symb hwx F G) := by
      rw [(hmul hwx hd1).1, (hnorm hwx hd1 a _).1, (hmul hwx hd1).2, (hnorm hwx hd1 b F).2]
    rw [divisor_pointGenerator_apply dim x _ hxQ, hf, hg, hsymb, hfrL, hfrN]
    simp only [pointOrd_mul, pointOrd_zpow, pointOrd_pointStalkUnitIncl]
    push_cast
    ring
  have hKfin : (Function.support K).Finite := by
    have hK : K = fun v ↦ ((pointGenerator v.1 (symb v.2.1 (s.pointCoordAt v.2.1)
        (t.pointCoordAt v.2.1))).divisor dim : X → ℚ) Q -
        ((pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) * ((N.pointFrame v.1).divisor dim : X → ℚ) Q -
          (pointOrd v.2.1 (t.pointCoordAt v.2.1) : ℚ) *
            ((L.pointFrame v.1).divisor dim : X → ℚ) Q) := by
      funext v
      rw [hpt v]
      ring
    rw [hK]
    exact (hRfin'.union hLfin').subset (Function.support_sub _ _)
  have hK0 : ∑ᶠ v, K v = 0 := by
    let ι : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1} →
        {v : X // w ⤳ v ∧ dim w = dim v + 1} := fun u ↦ ⟨u.1, u.2.1, u.2.2.2⟩
    have hι : Function.Injective ι := fun a b hab ↦ Subtype.ext (congrArg Subtype.val hab :)
    have hsupp : Function.support K ⊆ Set.range ι := by
      intro v hv
      by_cases hvQ : v.1 ⤳ Q
      · exact ⟨⟨v.1, v.2.1, hvQ, v.2.2⟩, rfl⟩
      · exact absurd (dif_neg hvQ) hv
    rw [finsum_comp_of_injective_of_support_subset_range hι K hsupp]
    have hval : ∀ u : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1},
        K (ι u) = ((pointOrd u.2.2.1 (symb u.2.1 F G) : ℤ) : ℚ) := fun u ↦ dif_pos u.2.2.1
    rw [finsum_congr hval]
    have hfin : (Function.support fun u : {v : X // w ⤳ v ∧ v ⤳ Q ∧ dim w = dim v + 1} ↦
        pointOrd u.2.2.1 (symb u.2.1 F G)).Finite := by
      refine (hKfin.preimage hι.injOn).subset ?_
      intro u hu
      change K (ι u) ≠ 0
      rw [hval u]
      exact_mod_cast hu
    have h2 := (Int.castAddHom ℚ).map_finsum hfin
    rw [hkey hwQ hdQ F G, map_zero] at h2
    exact h2.symm
  rw [finsum_congr hpt, finsum_add_distrib hLfin' hKfin, hK0, add_zero]

end KeyFormula

/-! ## The first Chern class on Chow groups -/

section FirstChernClass

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]

/-- **`c₁` of the divisor of a rational section along `pointSubscheme w`.**  If
`dim w = i + 1 + 1` and `s` is a rational section of `L` along `pointSubscheme w`, then
`c₁(N)` of the divisor of `s` is the class of `∑ ord_v(s) • div(frame_N v)`, the sum running over
the codimension-one specialisations `v` of `w`, where `ord_v(s)` is the order of the coordinate
of `s` in the canonical chart of `L` at `v` (Stacks, discussion before Lemma 42.27.1). -/
theorem c1Cycle_divisor_pointSubscheme (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} {L N : LineBundleData X} {w : X}
    (hw : dim w = i + 1 + 1) (s : L.RationalSection (pointSubscheme w))
    (hmem : s.divisor dim ∈ cyclesOfDimension X dim (i + 1)) :
    c1Cycle N dim i ⟨s.divisor dim, hmem⟩ =
      qProj dim i (∑ᶠ v : {v : X // w ⤳ v ∧ dim w = dim v + 1},
        (pointOrd v.2.1 (s.pointCoordAt v.2.1) : ℚ) • (N.pointFrame v.1).divisor dim) := by
  have hsupp : Function.support (fun x : X ↦ (s.divisor dim : X → ℚ) x • chernSummand N dim i x)
      ⊆ Set.range (Subtype.val : {v : X // w ⤳ v ∧ dim w = dim v + 1} → X) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx0 : (s.divisor dim : X → ℚ) x ≠ 0 := fun h0 ↦ hx (by rw [h0, zero_smul])
    by_cases hwx : w ⤳ x
    · by_cases hd : dim x = i + 1
      · exact ⟨⟨x, hwx, by omega⟩, rfl⟩
      · exact absurd (hmem x hd) hx0
    · exact absurd (s.divisor_apply_eq_zero_of_not_specializes dim hwx) hx0
  change (∑ᶠ x : X, (s.divisor dim : X → ℚ) x • chernSummand N dim i x) = _
  rw [finsum_comp_of_injective_of_support_subset_range Subtype.val_injective _ hsupp,
    map_finsum (qProj dim i)
      (s.finite_support_pointOrd_smul dim fun v ↦ (N.pointFrame v.1).divisor dim)]
  refine finsum_congr fun v ↦ ?_
  have hv : dim v.1 = i + 1 := by have := v.2.2; omega
  rw [map_smul, qProj_eq_quotientMap _ ((N.pointFrame v.1).divisor_mem_cyclesOfDimension dim hcov
      (by rw [genericPointImage_pointSubscheme]; exact hv)), ← chernSummand_eq hcov hv,
    s.divisor_apply_eq_pointOrd dim v.2.1 (L.keyChart v.1) _ (L.mem_keyChart v.1)]
  rfl

/-- The divisor of the point generator of `r ∈ κ(w)ˣ` is the divisor of the rational section of
the trivial line bundle along `pointSubscheme w` with coordinate `r`. -/
theorem divisor_pointGenerator_eq_trivial (dim : DimensionFunction X) (w : X)
    (r : (X.residueField w)ˣ) (j : (LineBundleData.trivial X).J)
    (hj : (pointSubscheme w).eta ∈ ((LineBundleData.trivial X).U j : X.Opens)) :
    (pointGenerator w r).divisor dim =
      (⟨j, hj, Units.map (pointFieldEquiv w).symm.toMonoidHom r⟩ :
        (LineBundleData.trivial X).RationalSection (pointSubscheme w)).divisor dim := by
  change (pointSubscheme w).pushforward dim ((pointSubscheme w).scheme.principalCycle _) =
    (pointSubscheme w).pushforward dim (LineBundleData.RationalSection.divisorCycle _)
  rw [LineBundleData.RationalSection.divisorCycle_trivial]
  rfl

/-- The image in `A_i` of a finite sum of point-generator divisors along the codimension-one
specialisations of a point `w` of dimension `i + 1 + 1` vanishes. -/
theorem qProj_finsum_pointGenerator_divisor (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} {w : X} (hw : dim w = i + 1 + 1)
    (u : (v : {v : X // w ⤳ v ∧ dim w = dim v + 1}) → (X.residueField v.1)ˣ) :
    qProj dim i (∑ᶠ v : {v : X // w ⤳ v ∧ dim w = dim v + 1},
      (pointGenerator v.1 (u v)).divisor dim) = 0 := by
  by_cases hfin : (Function.support fun v : {v : X // w ⤳ v ∧ dim w = dim v + 1} ↦
      (pointGenerator v.1 (u v)).divisor dim).Finite
  · rw [map_finsum (qProj dim i) hfin]
    refine finsum_eq_zero_of_forall_eq_zero fun v ↦ qProj_divisor _
      (RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov _ ?_)
    rw [genericPointImage_pointGenerator]
    have := v.2.2
    omega
  · rw [finsum_of_infinite_support hfin, map_zero]

/-- **`c₁` factors through rational equivalence** (Stacks, Lemma 42.28.2, `lemma-factors`), for
every line bundle `L` and every `i`, given a symbol family satisfying `hmul`, `hnorm` and
`hkey`: `c₁(L)` kills the divisor of every rational-function generator of dimension `i + 2`. -/
theorem killsRelations_of_symbol {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) : KillsRelations L dim hcov i := by
  intro g hg
  set w := g.subspace.genericPointImage
  have hw : dim w = i + 1 + 1 := by rw [hg]; ring
  set T := LineBundleData.trivial X
  let t : T.RationalSection (pointSubscheme w) :=
    ⟨T.keyChart w, eta_pointSubscheme_mem (specializes_refl w) (T.mem_keyChart w),
      Units.map (pointFieldEquiv w).symm.toMonoidHom g.residueFunction⟩
  have hdiv : g.divisor dim = t.divisor dim :=
    (divisor_pointGenerator dim g).symm.trans (divisor_pointGenerator_eq_trivial dim w _ _ _)
  have hmem : t.divisor dim ∈ cyclesOfDimension X dim (i + 1) :=
    t.divisor_mem_cyclesOfDimension dim hcov (by rw [genericPointImage_pointSubscheme]; exact hw)
  have heq : (⟨g.divisor dim, RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov g
      (show dim g.subspace.genericPointImage = (i + 1) + 1 by omega)⟩ :
        cyclesOfDimension X dim (i + 1)) = ⟨t.divisor dim, hmem⟩ := Subtype.ext hdiv
  rw [heq, c1Cycle_divisor_pointSubscheme dim hcov hw t hmem]
  have hK := keyFormula symb hmul hnorm hkey hcov L T (L.pointFrame w) t
  have h0 : ∀ v : X, (T.pointFrame v).divisor dim = 0 := fun v ↦ trivial_divisor_eq_zero dim _ _
  simp only [h0, smul_zero, zero_sub] at hK
  rw [finsum_neg_distrib] at hK
  have hq := congrArg (qProj dim i) hK
  rw [map_neg, qProj_finsum_pointGenerator_divisor dim hcov hw] at hq
  exact neg_eq_zero.mp hq

/-- **Commutativity of first Chern classes** (Stacks, Lemma 42.28.3, `lemma-cap-commutative`),
given a symbol family satisfying `hmul`, `hnorm` and `hkey`: for line bundles `L`, `N` and any
witnesses that `c₁(L)` and `c₁(N)` factor through rational equivalence in the relevant degrees,
`c₁(L) (c₁(N) α) = c₁(N) (c₁(L) α)` for every `α ∈ A_{i+2}`. -/
theorem c1_comm_of_symbol {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L N : LineBundleData X) {i : ℤ} (hL₀ : KillsRelations L dim hcov i)
    (hL₁ : KillsRelations L dim hcov (i + 1)) (hN₀ : KillsRelations N dim hcov i)
    (hN₁ : KillsRelations N dim hcov (i + 1)) (α : (chowSystem dim (i + 1 + 1)).ChowGroup) :
    c1 hL₀ (c1 hN₁ α) = c1 hN₀ (c1 hL₁ α) := by
  refine Submodule.Quotient.induction_on _ α (fun β ↦ ?_)
  change c1 hL₀ (c1 hN₁ ((chowSystem dim (i + 1 + 1)).quotientMap β)) =
    c1 hN₀ (c1 hL₁ ((chowSystem dim (i + 1 + 1)).quotientMap β))
  rw [c1_quotientMap_single, c1_quotientMap_single]
  have hext : (c1 hL₀).comp (c1Cycle N dim (i + 1)) = (c1 hN₀).comp (c1Cycle L dim (i + 1)) := by
    apply c1Cycle_ext
    intro x
    by_cases hx : dim x = i + 1 + 1
    · rw [cyclesOfDimension.pointProj_eq_point hx, LinearMap.comp_apply, LinearMap.comp_apply,
        c1Cycle_single hcov hx (N.pointFrame x), c1Cycle_single hcov hx (L.pointFrame x),
        c1_quotientMap_single, c1_quotientMap_single,
        c1Cycle_divisor_pointSubscheme dim hcov hx, c1Cycle_divisor_pointSubscheme dim hcov hx]
      have hq := congrArg (qProj dim i)
        (keyFormula symb hmul hnorm hkey hcov L N (L.pointFrame x) (N.pointFrame x))
      rw [finsum_sub_distrib ((L.pointFrame x).finite_support_pointOrd_smul dim
          fun v ↦ (N.pointFrame v.1).divisor dim)
          ((N.pointFrame x).finite_support_pointOrd_smul dim
            fun v ↦ (L.pointFrame v.1).divisor dim), map_sub,
        qProj_finsum_pointGenerator_divisor dim hcov hx] at hq
      exact (sub_eq_zero.mp hq).symm
    · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero]
  exact LinearMap.congr_fun hext β

/-- **The first Chern class on Chow groups**, `c₁(L) : A_{i+1} → A_i`, for every line bundle `L`,
defined from a symbol family satisfying `hmul`, `hnorm` and `hkey` (which provide
`killsRelations_of_symbol`).  It is `c1` of FirstChernClass.lean, so its value does not depend
on the symbol family. -/
noncomputable def c1Chow {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) :
    (chowSystem dim (i + 1)).ChowGroup →ₗ[ℚ] (chowSystem dim i).ChowGroup :=
  c1 (killsRelations_of_symbol symb hmul hnorm hkey hcov L i)

/-- `c1Chow` on the class of a cycle is `c1Cycle`. -/
theorem c1Chow_quotientMap {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L : LineBundleData X) (i : ℤ) (α : cyclesOfDimension X dim (i + 1)) :
    c1Chow symb hmul hnorm hkey hcov L i ((chowSystem dim (i + 1)).quotientMap α) =
      c1Cycle L dim i α :=
  c1_quotientMap_single _ α

/-- **Commutativity of `c1Chow`** (Stacks, Lemma 42.28.3): for line bundles `L`, `N` and
`α ∈ A_{i+2}`, `c₁(L) (c₁(N) α) = c₁(N) (c₁(L) α)`. -/
theorem c1Chow_comm_of_symbol {dim : DimensionFunction X} (symb : PointSymbolFamily X)
    (hmul : symb.IsBimultiplicative) (hnorm : symb.IsNormalized)
    (hkey : symb.SatisfiesKeyLemma dim) (hcov : HomogeneityLocal.CovByDimension dim)
    (L N : LineBundleData X) (i : ℤ) (α : (chowSystem dim (i + 1 + 1)).ChowGroup) :
    c1Chow symb hmul hnorm hkey hcov L i (c1Chow symb hmul hnorm hkey hcov N (i + 1) α) =
      c1Chow symb hmul hnorm hkey hcov N i (c1Chow symb hmul hnorm hkey hcov L (i + 1) α) :=
  c1_comm_of_symbol symb hmul hnorm hkey hcov L N _ _ _ _ α

end FirstChernClass

end GromovWitten.AlgebraicGeometry.IntersectionTheory
