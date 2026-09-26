/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClass

/-!
# Toward the descent of `c₁` to Fulton's symmetric identity

Fulton's Intersection Theory Thm 2.4 proves the descent condition `KillsRelations` for `c₁(L)`
(Goal 3 of `FirstChernClass.lean`) from a *symmetric identity*: given a subvariety `W` of
dimension `i + 2`, a rational function `r` on `W` and a rational section `s` of `L` along `W`
with no common support components (in the sense that at every codimension-one point of `W` at
least one of `r`, `s` does not vanish/blow up there), the two ways of computing `c₁(L) ∩ [div r]`
agree:

`∑ᵥ ord_W(r, v) · [s restricted to v̄]  =  ∑ᵥ ord_W(s, v) · [pointGenerator (ι v) (residue of r)]`.

A first obstacle (isolated by agent C2, task C4's predecessor): on a *non-normal* scheme
"`s.ord v = 0`" does **not** make the coordinate of `s` a unit of the local ring at `v` (e.g.
`1 + t ∈ Frac k[[t², t³]]` has order `0` but is not in the subring `k[[t², t³]]`), so a residue
class cannot be extracted from `ord v = 0` alone.  Fulton avoids exactly this by restricting a
pseudo-divisor to a subvariety `V` only when `V ⊄ |D|`, i.e. when the local equation is a unit of
the local ring *at the generic point of `V`* — the hypothesis this file calls `IsUnitAt`.  This
is *stronger* than `ord = 0` (`ord_eq_zero_of_isUnitAt`) but not equivalent to it in general: the
converse needs the local ring to be a discrete valuation ring, which is a normality hypothesis not
available in this repository's ambient setting (see the "Not done" section of the report).

## Main declarations

* `AlgebraicGeometry.Scheme.IsUnitAt`, `residueUnitAt` — for a unit `f` of the function field of
  an integral locally Noetherian scheme `Y`: `f` is a unit *at* a point `v` when it is the image,
  under the canonical algebra map from the stalk at `v`, of a unit of that stalk; `residueUnitAt`
  is the residue class of that stalk unit.  `ord_eq_zero_of_isUnitAt` : `IsUnitAt` implies
  vanishing order zero (not conversely).
* `IntegralClosedSubscheme.toFunctionField_unit_isUnitAt` — a unit of sections of `X` pushed into
  the function field of a closed subscheme via `toFunctionField` is a unit at every point of the
  subscheme lying over its domain of definition.
* `LineBundleData.RationalSection.IsUnitAt`, `.residueUnit` — the section-level counterpart,
  independent of the chart used to compute it (`isUnitAt_iff_of_chart`).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral Y]

/-- A unit `f` of the function field of `Y` is a *unit at* a point `v` when it lies in the image,
under the canonical algebra map from the stalk at `v` into the function field, of a unit of that
stalk.  This is Fulton's condition "`v ∉ |div f|`" (the local equation is a unit at `v`), the
correct substitute on a possibly non-normal scheme for "the order of vanishing at `v` is zero"
(`ord_eq_zero_of_isUnitAt`; the converse needs the stalk at `v` to be a discrete valuation ring). -/
def IsUnitAt (f : Y.functionFieldˣ) (v : Y) : Prop :=
  ∃ u : (Y.presheaf.stalk v)ˣ,
    algebraMap (Y.presheaf.stalk v) Y.functionField (u : Y.presheaf.stalk v) =
      (f : Y.functionField)

/-- The distinguished stalk unit witnessing `IsUnitAt`.  Well defined regardless of which proof
of `IsUnitAt f v` is supplied (proof irrelevance), and in fact the *unique* such stalk unit since
`algebraMap (Y.presheaf.stalk v) Y.functionField` is injective (`IsFractionRing.injective`,
`Y.functionField` being the fraction field of every stalk of an integral scheme). -/
noncomputable def unitAt {f : Y.functionFieldˣ} {v : Y} (h : IsUnitAt f v) :
    (Y.presheaf.stalk v)ˣ :=
  h.choose

@[simp]
lemma algebraMap_unitAt {f : Y.functionFieldˣ} {v : Y} (h : IsUnitAt f v) :
    algebraMap (Y.presheaf.stalk v) Y.functionField (unitAt h : Y.presheaf.stalk v) =
      (f : Y.functionField) :=
  h.choose_spec

/-- `unitAt` is the *unique* stalk unit witnessing `IsUnitAt`, since the algebra map from the
stalk to the function field is injective. -/
lemma unitAt_unique {f : Y.functionFieldˣ} {v : Y} (h : IsUnitAt f v) (u : (Y.presheaf.stalk v)ˣ)
    (hu : algebraMap (Y.presheaf.stalk v) Y.functionField (u : Y.presheaf.stalk v) =
      (f : Y.functionField)) :
    unitAt h = u := by
  apply Units.ext
  exact IsFractionRing.injective (Y.presheaf.stalk v) Y.functionField
    (by rw [algebraMap_unitAt, hu])

/-- The residue class, in the residue field at `v`, of a unit of the function field which is a
unit at `v`. -/
noncomputable def residueUnitAt {f : Y.functionFieldˣ} {v : Y} (h : IsUnitAt f v) :
    (Y.residueField v)ˣ :=
  Units.map (Y.residue v).hom.toMonoidHom (unitAt h)

/-- `1` is a unit at every point. -/
lemma isUnitAt_one (v : Y) : IsUnitAt (1 : Y.functionFieldˣ) v :=
  ⟨1, by simp⟩

/-- The product of two units at `v` is a unit at `v`. -/
lemma isUnitAt_mul {f g : Y.functionFieldˣ} {v : Y} (hf : IsUnitAt f v) (hg : IsUnitAt g v) :
    IsUnitAt (f * g) v :=
  ⟨unitAt hf * unitAt hg, by
    rw [Units.val_mul, map_mul, algebraMap_unitAt, algebraMap_unitAt, ← Units.val_mul]⟩

/-- The witnessing unit is multiplicative. -/
lemma unitAt_mul {f g : Y.functionFieldˣ} {v : Y} (hf : IsUnitAt f v) (hg : IsUnitAt g v) :
    unitAt (isUnitAt_mul hf hg) = unitAt hf * unitAt hg :=
  unitAt_unique _ _ (by
    rw [Units.val_mul, map_mul, algebraMap_unitAt, algebraMap_unitAt, ← Units.val_mul])

/-- The residue unit is multiplicative. -/
lemma residueUnitAt_mul {f g : Y.functionFieldˣ} {v : Y} (hf : IsUnitAt f v) (hg : IsUnitAt g v) :
    residueUnitAt (isUnitAt_mul hf hg) = residueUnitAt hf * residueUnitAt hg := by
  change Units.map (Y.residue v).hom.toMonoidHom (unitAt (isUnitAt_mul hf hg)) =
    Units.map (Y.residue v).hom.toMonoidHom (unitAt hf) *
      Units.map (Y.residue v).hom.toMonoidHom (unitAt hg)
  rw [unitAt_mul, map_mul]

/-- The inverse of a unit at `v` is a unit at `v`. -/
lemma isUnitAt_inv {f : Y.functionFieldˣ} {v : Y} (hf : IsUnitAt f v) :
    IsUnitAt f⁻¹ v := by
  refine ⟨(unitAt hf)⁻¹, ?_⟩
  have hφ : Units.map (algebraMap (Y.presheaf.stalk v) Y.functionField).toMonoidHom (unitAt hf) =
      f := Units.ext (algebraMap_unitAt hf)
  have h2 : Units.map (algebraMap (Y.presheaf.stalk v) Y.functionField).toMonoidHom
      (unitAt hf)⁻¹ = f⁻¹ := by rw [map_inv, hφ]
  have h3 := congrArg Units.val h2
  rw [Units.coe_map] at h3
  exact h3

/-- Cancelling a known unit at `v` from a product. -/
lemma isUnitAt_mul_left_iff {f g : Y.functionFieldˣ} {v : Y} (hf : IsUnitAt f v) :
    IsUnitAt (f * g) v ↔ IsUnitAt g v := by
  refine ⟨fun hfg ↦ ?_, isUnitAt_mul hf⟩
  have h := isUnitAt_mul (isUnitAt_inv hf) hfg
  rwa [inv_mul_cancel_left] at h

/-- **`IsUnitAt` implies vanishing order zero.**  Not conversely on a non-normal scheme: see the
module docstring. -/
theorem ord_eq_zero_of_isUnitAt [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
    {f : Y.functionFieldˣ} {v : Y} (h : IsUnitAt f v) :
    Y.ord (f : Y.functionField) v = 0 := by
  by_cases hz : Order.coheight v = 1
  · rw [Scheme.ord_eq_iff hz (Units.ne_zero f)]
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk v) := krullDimLE_of_coheight_le hz.le
    have h1 : Y.ordHom v hz (f : Y.functionField) = 1 := by
      rw [← algebraMap_unitAt h]
      exact Ring.ordFrac_of_isUnit (unitAt h).isUnit
    rw [h1]
    simp
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _

/-- A point where a function has nonzero order of vanishing has coheight one (`ord` is `0` by
convention off the coheight-one locus). -/
theorem coheight_eq_one_of_ord_ne_zero [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
    {f : Y.functionField} {v : Y} (h : Y.ord f v ≠ 0) :
    Order.coheight v = 1 := by
  by_contra hc
  exact h (Scheme.ord_eq_zero_of_coheight_neq_one hc f)

/-- A point where a function has nonzero order of vanishing is not a unit there
(`ord_eq_zero_of_isUnitAt`, contrapositive). -/
theorem not_isUnitAt_of_ord_ne_zero [_root_.AlgebraicGeometry.IsLocallyNoetherian Y]
    {f : Y.functionFieldˣ} {v : Y} (h : Y.ord (f : Y.functionField) v ≠ 0) :
    ¬ IsUnitAt f v :=
  fun hu ↦ h (ord_eq_zero_of_isUnitAt hu)

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.IntersectionTheory
open LineBundleInjective

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (W : IntegralClosedSubscheme X)

/-- A unit of sections of `X` over an open `U` containing `η_W`, pushed into the function field
of `W` via `toFunctionField`, is a unit at every point of `W.scheme` whose image in `X` lies in
`U`.  The key geometric input: transition units of a line bundle are never an obstruction to
restricting a rational section, wherever they are defined. -/
theorem toFunctionField_unit_isUnitAt {U : X.Opens} (h : W.eta ∈ U) (a : Γ(X, U)ˣ) (v : W.scheme)
    (hxv : W.inclusion.base v ∈ U) :
    Scheme.IsUnitAt (Units.map (W.toFunctionField U h).toMonoidHom a) v := by
  have hxv' : v ∈ (W.inclusion ⁻¹ᵁ U : W.scheme.Opens) := hxv
  have : Nonempty (W.inclusion ⁻¹ᵁ U) := ⟨⟨v, hxv'⟩⟩
  refine ⟨Units.map (W.scheme.presheaf.germ (W.inclusion ⁻¹ᵁ U) v hxv').hom.toMonoidHom
      (Units.map (W.inclusion.app U).hom.toMonoidHom a), ?_⟩
  change algebraMap (W.scheme.presheaf.stalk v) W.scheme.functionField
      (W.scheme.presheaf.germ (W.inclusion ⁻¹ᵁ U) v hxv'
        ((W.inclusion.app U).hom (a : Γ(X, U)))) =
      W.toFunctionField U h (a : Γ(X, U))
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact (W.toFunctionField_eq_germToFunctionField_app U h a).symm

/-- The residue class, in the residue field of `X` at `ι v = W.inclusion.base v`, of a unit of
the function field of `W` which is a unit at `v`: `Scheme.residueUnitAt`, transported along the
residue-field isomorphism of the closed immersion `W.inclusion` at `v`. -/
noncomputable def residueUnitAtX {f : W.scheme.functionFieldˣ} {v : W.scheme}
    (h : Scheme.IsUnitAt f v) : (X.residueField (W.inclusion.base v))ˣ :=
  Units.map (CategoryTheory.inv (W.inclusion.residueFieldMap v)).hom.toMonoidHom
    (Scheme.residueUnitAt h)

end IntegralClosedSubscheme

namespace LineBundleData

namespace RationalSection

variable {X : Scheme.{u}} {L : LineBundleData X} {W : IntegralClosedSubscheme X}
  (s : L.RationalSection W)

/-- `s` is a *unit at* a point `v` of `W.scheme` when its coordinate, in the chart `L.covers`
chooses for the image of `v`, is `Scheme.IsUnitAt` there (independent of that choice,
`isUnitAt_iff_of_chart`).  Fulton's condition for restricting a pseudo-divisor to a subvariety
through `v`: `v ∉ |div s|`. -/
noncomputable def IsUnitAt (v : W.scheme) : Prop :=
  Scheme.IsUnitAt
    (s.coord (L.covers (W.inclusion.base v)).choose
      (W.eta_mem_of_mem_preimage (L.covers (W.inclusion.base v)).choose_spec)) v

/-- `IsUnitAt` does not depend on the chart used to compute it, as long as the chart's image in
`X` contains the image of `v` (mirrors `RationalSection.ord_well_defined`). -/
theorem isUnitAt_iff_of_chart (j : L.J) (v : W.scheme)
    (hxj : W.inclusion.base v ∈ (L.U j : X.Opens)) :
    s.IsUnitAt v ↔ Scheme.IsUnitAt (s.coord j (W.eta_mem_of_mem_preimage hxj)) v := by
  set j₁ := (L.covers (W.inclusion.base v)).choose
  set hxj₁ := (L.covers (W.inclusion.base v)).choose_spec
  change Scheme.IsUnitAt (s.coord j₁ (W.eta_mem_of_mem_preimage hxj₁)) v ↔ _
  rw [s.coord_eq_unitAt_mul_coord j₁ j (W.eta_mem_of_mem_preimage hxj₁)
    (W.eta_mem_of_mem_preimage hxj)]
  have hunit : Scheme.IsUnitAt
      (L.unitAt W j₁ j (memInf (W.eta_mem_of_mem_preimage hxj₁) (W.eta_mem_of_mem_preimage hxj)))
      v :=
    W.toFunctionField_unit_isUnitAt _ (L.g j₁ j) v (memInf hxj₁ hxj)
  exact Scheme.isUnitAt_mul_left_iff hunit

/-- `IsUnitAt` implies the order of the section vanishes there.  Not conversely on a non-normal
scheme (module docstring). -/
theorem ord_eq_zero_of_isUnitAt {v : W.scheme} (h : s.IsUnitAt v) : s.ord v = 0 := by
  obtain ⟨j, hxj⟩ := L.covers (W.inclusion.base v)
  rw [s.ord_well_defined j v hxj]
  exact Scheme.ord_eq_zero_of_isUnitAt ((s.isUnitAt_iff_of_chart j v hxj).mp h)

/-- The residue class, in the residue field of `v`, of a rational section which is a unit
there. -/
noncomputable def residueUnit (v : W.scheme) (h : s.IsUnitAt v) : (W.scheme.residueField v)ˣ :=
  Scheme.residueUnitAt h

/-- Scaling a section by a unit which is itself a unit at `v` preserves `IsUnitAt`. -/
theorem smul_isUnitAt {f : W.scheme.functionFieldˣ} {v : W.scheme} (hf : Scheme.IsUnitAt f v)
    (h : s.IsUnitAt v) : (s.smul f).IsUnitAt v := by
  unfold IsUnitAt
  rw [smul_coord]
  exact Scheme.isUnitAt_mul hf h

/-- The residue unit of a scaled section is the product of the residue units. -/
theorem smul_residueUnit {f : W.scheme.functionFieldˣ} {v : W.scheme} (hf : Scheme.IsUnitAt f v)
    (h : s.IsUnitAt v) :
    (s.smul f).residueUnit v (s.smul_isUnitAt hf h) =
      Scheme.residueUnitAt hf * s.residueUnit v h := by
  unfold residueUnit Scheme.residueUnitAt
  rw [← map_mul]
  congr 1
  apply Scheme.unitAt_unique
  unfold RationalSection.IsUnitAt at h
  rw [Units.val_mul, map_mul, Scheme.algebraMap_unitAt, Scheme.algebraMap_unitAt,
    ← Units.val_mul, ← s.smul_coord f _ _]

/-- **Goal 2.** The restriction of a rational section of `L` which is a unit at `v` to the
integral closed subscheme `pointSubscheme (ι v)` (the closure, in `X`, of the point `ι v = ι
v.inclusion.base v`), via the residue field of `v`.  Its coordinate is the residue unit of `s`
at `v`, transported into the function field of `pointSubscheme (ι v)` through the residue field
of `X` at `ι v` (using that the residue field map of the closed immersion `W.inclusion` at `v`
is an isomorphism). -/
noncomputable def restrict [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
    (v : W.scheme) (h : s.IsUnitAt v) :
    L.RationalSection (pointSubscheme (W.inclusion.base v)) where
  j₀ := (L.covers (W.inclusion.base v)).choose
  hj₀ := by
    rw [show (pointSubscheme (W.inclusion.base v)).eta =
        (pointSubscheme (W.inclusion.base v)).genericPointImage from rfl,
      genericPointImage_pointSubscheme]
    exact (L.covers (W.inclusion.base v)).choose_spec
  f := Units.map (pointFieldEquiv (W.inclusion.base v)).symm.toMonoidHom (W.residueUnitAtX h)

end RationalSection

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]
  (L : LineBundleData X)

/-- **Goal 3** (Fulton, *Intersection Theory* Thm 2.4, no-common-component case). For a
rational-function generator `g = (W, r)` (`W := g.subspace`, `r := g.function`) and a rational
section `s` of `L` along `W`, with the hypotheses `hrs`/`hsr` that at every codimension-one point
of `W` at least one of `r`, `s` is a unit there (no common support components with `div r`), the
divisor of `s` restricted along the points where `r` vanishes/blows up equals the divisor of the
point generators attached to the residues of `r` at the points where `s` vanishes/blows up.  This
is the identity behind Fulton's proof that `c₁(L)` kills principal-divisor relations
(`killsRelations_of_symmetricIdentity` below).  It is proved in the affine, single-chart model in
`IntersectionTheory/DivisorSymmetryAffine.lean` (agent C3, concurrent with this file — not
imported here); its general form additionally needs the *moving lemma* that a section `s` with no
common support components with `div r` exists at all (true e.g. when the finitely many generic
points of the codimension-one components of `div r` lie in a common affine open, by the Chinese
remainder theorem in the semilocal ring of that finite set of points).  Neither is established in
this file: this declaration only states the identity as a hypothesis for
`killsRelations_of_symmetricIdentity`. -/
def SymmetricIdentity (dim : DimensionFunction X) (g : RationalFunctionGenerator X)
    (s : L.RationalSection g.subspace)
    (hrs : ∀ v : g.subspace.scheme, Order.coheight v = 1 →
      ¬ Scheme.IsUnitAt g.function v → s.IsUnitAt v)
    (hsr : ∀ v : g.subspace.scheme, Order.coheight v = 1 →
      ¬ s.IsUnitAt v → Scheme.IsUnitAt g.function v) : Prop :=
  (∑ᶠ v : g.subspace.scheme,
      if h : g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v = 0 then
        (0 : AlgebraicCycle X ℚ)
      else
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
          (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
            (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor dim) =
  ∑ᶠ v : g.subspace.scheme,
      if h : s.ord v = 0 then
        (0 : AlgebraicCycle X ℚ)
      else
        (s.ord v : ℚ) •
          (pointGenerator (g.subspace.inclusion.base v)
            (g.subspace.residueUnitAtX (hsr v (Scheme.coheight_eq_one_of_ord_ne_zero h)
              (fun hu ↦ h (s.ord_eq_zero_of_isUnitAt hu))))).divisor dim

end LineBundleData

/-! ## Goal 4: `c₁(L)` kills relations, given the symmetric identity -/

/-- A finsum over `α` of a function vanishing off the range of an injective `g : α → β`
equals the finsum, over `β`, of its precomposition with `g`. -/
theorem finsum_comp_of_injective_of_support_subset_range {α β M : Type*} [AddCommMonoid M]
    {g : β → α} (hg : Function.Injective g) (f : α → M)
    (h : Function.support f ⊆ Set.range g) :
    ∑ᶠ x, f x = ∑ᶠ y, f (g y) := by
  rw [← finsum_mem_univ f, ← finsum_mem_inter_support f Set.univ, Set.univ_inter,
    ← Set.inter_eq_self_of_subset_right h, finsum_mem_inter_support, finsum_mem_range hg]

variable {X : Scheme.{u}}

/-- A point of coheight one of `W` has the dimension forced by `hcov`, one less than the
dimension of `W`'s own generic point.  Extracted from the common pattern in
`HomogeneityLocal.principalDivisorsHomogeneous_of_covByDimension` and
`RationalFunctionGenerator.divisor_mem_cyclesOfDimension` (FirstChernClass.lean). -/
theorem dim_eq_of_coheight_one {dim : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dim) {W : IntegralClosedSubscheme X} {k : ℤ}
    (hW : dim W.genericPointImage = k + 1) {v : W.scheme} (hv : Order.coheight v = 1) :
    dim (W.inclusion.base v) = k := by
  have hcovy : v ⋖ genericPoint W.scheme :=
    (HomogeneityLocal.coheight_eq_one_iff_covBy (HomogeneityLocal.isTop_genericPoint W.scheme)).1
      hv
  have hkey := hcov _ _ (HomogeneityLocal.covBy_map_of_isClosedImmersion W.inclusion hcovy)
  change dim (W.inclusion.base v) + 1 = dim W.genericPointImage at hkey
  omega

variable [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- The value of `c₁(L)` on the class of `g.divisor dim`, expanded as a finsum over the points of
`g.subspace.scheme`, reindexing `c1Cycle`'s own defining finsum (over `X`) along the closed
immersion `g.subspace.inclusion`: the pushed-forward principal cycle vanishes off the image, and
equals the order of `g.function` at the preimage point on the image. -/
theorem c1Cycle_divisor_eq_finsum {L : LineBundleData X} {dim : DimensionFunction X} (i : ℤ)
    (g : RationalFunctionGenerator X) (hmem : g.divisor dim ∈ cyclesOfDimension X dim (i + 1)) :
    c1Cycle L dim i ⟨g.divisor dim, hmem⟩ =
      ∑ᶠ v : g.subspace.scheme,
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
          chernSummand L dim i (g.subspace.inclusion.base v) := by
  have hval : ∀ v : g.subspace.scheme,
      (g.divisor dim : AlgebraicCycle X ℚ) (g.subspace.inclusion.base v) =
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) := by
    intro v
    unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward
    rw [AlgebraicCycle.map_closedImmersion_apply_image g.subspace.inclusion (dim : X → ℤ),
      _root_.AlgebraicGeometry.Scheme.principalCycle_apply]
  have hsupp : Function.support (fun x : X ↦ (g.divisor dim : AlgebraicCycle X ℚ) x •
      chernSummand L dim i x) ⊆ Set.range g.subspace.inclusion.base := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxr
    apply hx
    have hz : (g.divisor dim : AlgebraicCycle X ℚ) x = 0 := by
      unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward
      exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range g.subspace.inclusion
        (dim : X → ℤ) _ x hxr
    rw [hz, zero_smul]
  change (∑ᶠ x : X, (g.divisor dim : AlgebraicCycle X ℚ) x • chernSummand L dim i x) = _
  rw [finsum_comp_of_injective_of_support_subset_range
    g.subspace.inclusion.isClosedEmbedding.injective _ hsupp]
  simp_rw [hval]

/-- The composite `(chowSystem dim i).quotientMap ∘ cyclesOfDimension.projectLinear dim i`,
defined on *all* cycles (not just those already graded in dimension `i`): a genuine linear map,
so it commutes freely with finite sums, and it agrees with `quotientMap` on any cycle already
known to be graded (`qProj_eq_quotientMap`). -/
noncomputable def qProj (dim : DimensionFunction X) (i : ℤ) :
    AlgebraicCycle X ℚ →ₗ[ℚ] (chowSystem dim i).ChowGroup :=
  (chowSystem dim i).quotientMap.comp (cyclesOfDimension.projectLinear dim i)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
theorem qProj_eq_quotientMap {dim : DimensionFunction X} {i : ℤ} (c : AlgebraicCycle X ℚ)
    (hmem : c ∈ cyclesOfDimension X dim i) :
    qProj dim i c = (chowSystem dim i).quotientMap ⟨c, hmem⟩ := by
  change (chowSystem dim i).quotientMap (cyclesOfDimension.projectLinear dim i c) = _
  congr 1
  exact cyclesOfDimension.project_coe ⟨c, hmem⟩

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- `qProj` kills the divisor of *any* rational-function generator known to be graded in the
target dimension: this is Fulton's Prop. 2.5, `quotientMap_divisor` from `ChowGroup.lean`. -/
theorem qProj_divisor {dim : DimensionFunction X} {i : ℤ} (h : RationalFunctionGenerator X)
    (hmem : h.divisor dim ∈ cyclesOfDimension X dim i) : qProj dim i (h.divisor dim) = 0 := by
  rw [qProj_eq_quotientMap (h.divisor dim) hmem]
  exact (chowSystem dim i).quotientMap_divisor h hmem

/-- **Goal 4.** If every rational-function generator `g` with `dim g.subspace.genericPointImage =
i + 2` admits a rational section `s` of `L` along `g.subspace` and no-common-support hypotheses
`hrs`/`hsr` witnessing `SymmetricIdentity L dim g s hrs hsr`, then `c₁(L)` kills the relations in
grade `i` (`KillsRelations`, FirstChernClass.lean).  The divisor of `g` expands, via
`c1Cycle_divisor_eq_finsum`, as the finsum over `g.subspace.scheme` of `chernSummand`s weighted by
the order of `g.function`; wherever that order is nonzero the point has coheight one (hence, via
`hcov`, the dimension forced by `hg`) and `chernSummand_eq` identifies the summand with `qProj` of
`s`'s restricted divisor there — exactly the left side of the symmetric identity.  The identity
transports this to the right side, a finsum of point-generator divisors, each killed
unconditionally by `qProj_divisor`. -/
theorem killsRelations_of_symmetricIdentity {L : LineBundleData X}
    {dim : DimensionFunction X} (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ)
    (hex : ∀ g : RationalFunctionGenerator X, dim g.subspace.genericPointImage = i + 2 →
      ∃ (s : L.RationalSection g.subspace)
        (hrs : ∀ v : g.subspace.scheme, Order.coheight v = 1 →
          ¬ Scheme.IsUnitAt g.function v → s.IsUnitAt v)
        (hsr : ∀ v : g.subspace.scheme, Order.coheight v = 1 →
          ¬ s.IsUnitAt v → Scheme.IsUnitAt g.function v),
        L.SymmetricIdentity dim g s hrs hsr) :
    KillsRelations L dim hcov i := by
  intro g hg
  obtain ⟨s, hrs, hsr, hsym⟩ := hex g hg
  have hg' : dim g.subspace.genericPointImage = (i + 1) + 1 := by omega
  have hmem : g.divisor dim ∈ cyclesOfDimension X dim (i + 1) :=
    RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov g hg'
  rw [c1Cycle_divisor_eq_finsum i g hmem]
  have hNoethW : NoetherianSpace g.subspace.scheme :=
    g.subspace.inclusion.isClosedEmbedding.isInducing.noetherianSpace
  have hfW : (Function.support (fun v : g.subspace.scheme ↦
      (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ))).Finite := by
    have heq : (fun v : g.subspace.scheme ↦
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ)) =
        (g.subspace.scheme.principalCycle (g.function : g.subspace.scheme.functionField) :
          g.subspace.scheme → ℚ) := by
      funext v
      exact (_root_.AlgebraicGeometry.Scheme.principalCycle_apply _ v).symm
    rw [heq]
    exact finite_support_univ _
  have hfS : (Function.support (fun v : g.subspace.scheme ↦ (s.ord v : ℚ))).Finite := by
    have heq : (fun v : g.subspace.scheme ↦ (s.ord v : ℚ)) =
        (s.divisorCycle : g.subspace.scheme → ℚ) := by
      funext v
      exact (LineBundleData.RationalSection.divisorCycle_apply _ v).symm
    rw [heq]
    exact finite_support_univ _
  have hterm1 : ∀ v : g.subspace.scheme,
      (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
          chernSummand L dim i (g.subspace.inclusion.base v) =
        qProj dim i (if h : g.subspace.scheme.ord
            (g.function : g.subspace.scheme.functionField) v = 0 then
          (0 : AlgebraicCycle X ℚ)
        else
          (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
            (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
              (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor dim) := by
    intro v
    by_cases h : g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v = 0
    · have hz : (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) = 0 :=
        by exact_mod_cast h
      rw [dif_pos h, hz, zero_smul, map_zero]
    · rw [dif_neg h]
      have hdimv : dim (g.subspace.inclusion.base v) = i + 1 :=
        dim_eq_of_coheight_one hcov hg' (Scheme.coheight_eq_one_of_ord_ne_zero h)
      have hmemv : (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
          (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor dim ∈ cyclesOfDimension X dim i :=
        (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
          (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor_mem_cyclesOfDimension dim hcov
          (by rw [genericPointImage_pointSubscheme]; exact hdimv)
      rw [chernSummand_eq hcov hdimv
        (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
          (Scheme.not_isUnitAt_of_ord_ne_zero h))),
        qProj_eq_quotientMap _ (Submodule.smul_mem (cyclesOfDimension X dim i)
          (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) hmemv)]
      exact (map_smul (chowSystem dim i).quotientMap _ _).symm
  have hterm2 : ∀ v : g.subspace.scheme,
      qProj dim i (if h : s.ord v = 0 then
          (0 : AlgebraicCycle X ℚ)
        else
          (s.ord v : ℚ) •
            (pointGenerator (g.subspace.inclusion.base v)
              (g.subspace.residueUnitAtX (hsr v (Scheme.coheight_eq_one_of_ord_ne_zero h)
                (fun hu ↦ h (s.ord_eq_zero_of_isUnitAt hu))))).divisor dim) = 0 := by
    intro v
    by_cases h : s.ord v = 0
    · rw [dif_pos h, map_zero]
    · rw [dif_neg h, map_smul]
      have hdimv : dim (g.subspace.inclusion.base v) = i + 1 :=
        dim_eq_of_coheight_one hcov hg' (Scheme.coheight_eq_one_of_ord_ne_zero h)
      set gen := pointGenerator (g.subspace.inclusion.base v)
        (g.subspace.residueUnitAtX (hsr v (Scheme.coheight_eq_one_of_ord_ne_zero h)
          (fun hu ↦ h (s.ord_eq_zero_of_isUnitAt hu)))) with hgendef
      have hmemv : gen.divisor dim ∈ cyclesOfDimension X dim i :=
        RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov gen
          (by rw [hgendef, genericPointImage_pointGenerator]; exact hdimv)
      rw [qProj_divisor gen hmemv, smul_zero]
  have hf1 : Function.HasFiniteSupport (fun v : g.subspace.scheme ↦
      if h : g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v = 0 then
        (0 : AlgebraicCycle X ℚ)
      else
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
          (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
            (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor dim) := by
    apply hfW.subset
    intro v hv
    simp only [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [h0]
  rw [finsum_congr hterm1, ← map_finsum (qProj dim i) hf1]
  have hsym' : (∑ᶠ v : g.subspace.scheme,
      if h : g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v = 0 then
        (0 : AlgebraicCycle X ℚ)
      else
        (g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) v : ℚ) •
          (s.restrict v (hrs v (Scheme.coheight_eq_one_of_ord_ne_zero h)
            (Scheme.not_isUnitAt_of_ord_ne_zero h))).divisor dim) =
      ∑ᶠ v : g.subspace.scheme,
        if h : s.ord v = 0 then
          (0 : AlgebraicCycle X ℚ)
        else
          (s.ord v : ℚ) •
            (pointGenerator (g.subspace.inclusion.base v)
              (g.subspace.residueUnitAtX (hsr v (Scheme.coheight_eq_one_of_ord_ne_zero h)
                (fun hu ↦ h (s.ord_eq_zero_of_isUnitAt hu))))).divisor dim :=
    hsym
  rw [hsym', map_finsum (qProj dim i) (hfS.subset (by
    intro v hv
    simp only [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [h0]))]
  simp [hterm2]

end GromovWitten.AlgebraicGeometry.IntersectionTheory
