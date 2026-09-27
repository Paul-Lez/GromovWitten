/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import GromovWitten.AlgebraicGeometry.Curves.FibreDimension
import GromovWitten.AlgebraicGeometry.Curves.SmoothLocusDimension
import GromovWitten.AlgebraicGeometry.Stacks.OverlapSwap

/-!
# The dimension formula for a flat morphism over a locally Noetherian base

For a flat morphism `q : W ⟶ U` of locally Noetherian schemes, this file proves the dimension
formula of Stacks 00ON (Matsumura 13.B Th. 19(2), EGA IV 6.1.2) and its global consequences, all
in the *codimension* convention `Order.coheight`, which by `ringKrullDim_stalk_eq_coheight` is the
Krull dimension of the local ring at the point.

## Main results

* `coheight_eq_coheight_apply_add_fibreCodim`: the local formula.  At every `x : W`,
  `Order.coheight x = Order.coheight (q x) + fibreCodim q x`, where `fibreCodim q x` is the Krull
  dimension of the local ring `fibreStalk q x = O_{W, x} ⧸ 𝔪_{q x} · O_{W, x}` of the
  scheme-theoretic fibre of `q` through `x` (`fibreCodim_eq_ringKrullDim_fibreStalk`).
* `coheight_apply_le_coheight_of_flat`: codimension monotonicity,
  `Order.coheight (q x) ≤ Order.coheight x`.
* `topologicalKrullDim_eq_iSup_coheight`: for an arbitrary scheme, `dim X = ⨆ x, coheight x`.
* `topologicalKrullDim_le_add_of_fibreCodim_le`, `add_le_topologicalKrullDim_of_le_fibreCodim`,
  `topologicalKrullDim_eq_add_of_fibreCodim`: the global formula `dim W = dim U + r` for a flat `q`
  all of whose fibre local rings have Krull dimension `≤ r` and for which every point of `U` is
  the image of a point whose fibre local ring has Krull dimension `≥ r` (in particular `q` is
  surjective).  The variants `topologicalKrullDim_le_add_of_krullDimLE_fibreStalk` and
  `topologicalKrullDim_eq_add_of_ringKrullDim_fibreStalk` are phrased with `Ring.KrullDimLE` and
  `ringKrullDim` of the fibre local ring.  Dimensions take values in `WithBot ℕ∞`; the empty and
  the infinite-dimensional cases are covered.
* `topologicalKrullDim_eq_of_pure` and `topologicalKrullDim_eq_of_schemePureDimension`: a nonempty
  space of pure dimension `d` has total dimension `d`, so the formula can be fed with the
  repository's `SchemePureDimension` data for the base.
* `TotalDimensionFormulaAt`, `OverlapTotalDimensionFormula` and
  `stackDimensionIndependent_of_overlapTotalDimensionFormula`: atlas independence for the stack
  dimension needs only the *total* dimension formula for the two projections of an overlap, not the
  pure-dimension formula of `Stacks/OverlapSwap.lean`; and the pure form implies the total form
  (`overlapTotalDimensionFormula_of_overlapDimensionFormula`), so this is a strict weakening of the
  hypothesis of `stackDimensionIndependent_of_overlapDimensionFormula`.

## Why `Order.coheight`, and not the pure-dimension statements of the field case

Two things are *not* proved here, because both are false over a general locally Noetherian base;
this is the precise sense in which `Curves/SmoothPureDimension.lean` needs its base field.

First, the field case proves `height_apply_le_height : Order.height (q x) ≤ Order.height x`, where
`Order.height x` is the dimension of the *closure* of `x` (`topologicalKrullDim_closure_singleton`)
rather than the Krull dimension of `O_{X, x}`.  That inequality fails for a flat morphism of
locally Noetherian schemes: let `R` be a Noetherian local domain of dimension `2` (say `k[x, y]`
localised at the origin), `U := Spec R` with closed point `𝔪` and generic point `η`, and let
`q : W ⟶ U` be the open immersion of the punctured spectrum `W := U \ {𝔪}`.  Open immersions are
flat and `W` is locally Noetherian.  Every chain of primes realising `dim R = 2` ends at the unique
maximal ideal `𝔪`, so `Order.height (q η) = topologicalKrullDim U = 2`, while removing `𝔪` leaves
only chains of length `1`, so `Order.height η = topologicalKrullDim W = 1`.  Mathlib's
`AlgebraicGeometry.coheight_eq_of_isOpenImmersion` records the dual fact that `Order.coheight`,
unlike `Order.height`, *is* invariant under open immersions: going-down controls codimensions, not
dimensions of closures.

Second, and for the same reason, the *pure*-dimension form of the formula fails: there is no
statement `SmoothPureDimensionFormulaAt q` (`Stacks/OverlapSwap.lean`) for all `q` over a locally
Noetherian base.  With `R` and `U` as above, let `W := U ⊔ (U \ {𝔪})` and let `q : W ⟶ U` be the
identity on the first summand and the open immersion on the second.  Then `q` is étale (hence
smooth) and surjective, each fibre is a finite discrete set of points, so
`SchemeMorphismPureRelativeDimension q 0` holds, and `SchemePureDimension U 2` holds because `R` is
a `2`-dimensional domain.  But the irreducible components of `W` are `U`, of dimension `2`, and the
punctured spectrum, of dimension `1`, so `SchemePureDimension W (2 + 0)` is false.  Only the
*total* dimension formula survives in this generality, which is exactly what the results above
prove.  So an atlas-level statement `AtlasLocallyNoetherian` cannot be obtained from a general
scheme-level *pure*-dimension formula.  This is not fatal for atlas independence: by
`stackDimensionIndependent_of_overlapTotalDimensionFormula`, `StackDimensionIndependent X` already
follows from the total-dimension formula for the two overlap projections, and that is the form the
going-down results of this file produce.

## Remaining gap

Feeding `Curves.PureRelativeDimension r q` (a statement about the irreducible components of the
scheme-theoretic fibres `q.fiber u`) into the results above requires identifying `fibreStalk q x`
with the stalk of `q.fiber (q x)` at `x`, i.e. computing the stalk of a fibre product of schemes.
Mathlib currently has no lemma computing stalks of pullbacks, so that bridge is left open, and
with it both the derivation of the hypotheses of `topologicalKrullDim_eq_add_of_fibreCodim` from a
pure relative dimension and the proof of `OverlapTotalDimensionFormula` for stacks with locally
Noetherian atlases.
-/

open CategoryTheory Limits Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-- In a scheme, the height of the maximal ideal of the local ring at `x` is the coheight of the
point `x`: both compute the Krull dimension of the local ring `O_{X, x}`. -/
theorem height_maximalIdeal_stalk (X : Scheme.{u}) (x : X) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height = Order.coheight x := by
  have h : ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height : WithBot ℕ∞)
      = (Order.coheight x : WithBot ℕ∞) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact ringKrullDim_stalk_eq_coheight x
  exact_mod_cast h

/-- The local ring at `x` of the scheme-theoretic fibre of `q : W ⟶ U` through `x`, presented as
the quotient of the local ring `O_{W, x}` by the ideal generated by the image of the maximal
ideal of `O_{U, q x}`; this is `O_{W, x} ⊗_{O_{U, q x}} κ(q x)`. -/
abbrev fibreStalk {W U : Scheme.{u}} (q : W ⟶ U) (x : W) : Type u :=
  (W.presheaf.stalk x) ⧸
    ((IsLocalRing.maximalIdeal (U.presheaf.stalk (q x))).map (q.stalkMap x).hom)

/-- The codimension of `x` inside the scheme-theoretic fibre of `q` through `x`: the height of
the maximal ideal of the fibre local ring `fibreStalk q x`, i.e. the Krull dimension of the local
ring of the fibre `W_{q x}` at `x`. -/
def fibreCodim {W U : Scheme.{u}} (q : W ⟶ U) (x : W) : ℕ∞ :=
  ((IsLocalRing.maximalIdeal (W.presheaf.stalk x)).map
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (U.presheaf.stalk (q x))).map
      (q.stalkMap x).hom))).height

/-- **The local dimension formula for a flat morphism** (Stacks 00ON, EGA IV 6.1.2).  For a flat
morphism `q : W ⟶ U` of locally Noetherian schemes and `x : W`, the Krull dimension of `O_{W, x}`
is the Krull dimension of `O_{U, q x}` plus the Krull dimension of the local ring of the fibre
`W_{q x}` at `x`; in coheight form,
`Order.coheight x = Order.coheight (q x) + fibreCodim q x`. -/
theorem coheight_eq_coheight_apply_add_fibreCodim {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] (x : W) :
    Order.coheight x = Order.coheight (q x) + fibreCodim q x := by
  have hflat : (q.stalkMap x).hom.Flat := Flat.stalkMap q x
  algebraize [(q.stalkMap x).hom]
  let _ : IsLocalHom (algebraMap (U.presheaf.stalk (q x)) (W.presheaf.stalk x)) := by
    rw [(q.stalkMap x).hom.algebraMap_toAlgebra]
    infer_instance
  have hgd : Algebra.HasGoingDown (U.presheaf.stalk (q x)) (W.presheaf.stalk x) :=
    Algebra.HasGoingDown.of_flat
  have hkey := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (IsLocalRing.maximalIdeal (U.presheaf.stalk (q x)))
      (IsLocalRing.maximalIdeal (W.presheaf.stalk x))
  rw [(q.stalkMap x).hom.algebraMap_toAlgebra, height_maximalIdeal_stalk W x,
    height_maximalIdeal_stalk U (q x)] at hkey
  exact hkey
/-- **Codimension monotonicity under a flat morphism over a locally Noetherian base.**  For a
flat morphism `q : W ⟶ U` of locally Noetherian schemes, the Krull dimension of the local ring at
`x` is at least the Krull dimension of the local ring at the image point `q x`; equivalently,
`Order.coheight (q x) ≤ Order.coheight x`.  This is the codimension-monotonicity fact that
going-down for flat local homomorphisms controls; see the module docstring for why the analogous
statement for `Order.height` (the dimension of the closure of the point) is false here. -/
theorem coheight_apply_le_coheight_of_flat {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] (x : W) :
    Order.coheight (q x) ≤ Order.coheight x := by
  rw [coheight_eq_coheight_apply_add_fibreCodim q x]
  exact le_self_add

/-- For a scheme, the topological Krull dimension (the length of the longest chain of irreducible
closed subsets) is the order-theoretic Krull dimension of its space of points, ordered by
specialisation. -/
theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X := by
  have hiso : @Order.krullDim X (specializationOrder X).toPreorder = Order.krullDim X :=
    @Order.krullDim_eq_of_orderIso X X (specializationOrder X).toPreorder _
      { toEquiv := Equiv.refl X, map_rel_iff' := Iff.rfl }
  change Order.krullDim (TopologicalSpace.IrreducibleCloseds X) = _
  rw [← hiso]
  exact @Order.krullDim_eq_of_orderIso (TopologicalSpace.IrreducibleCloseds X) X _
    (specializationOrder X).toPreorder (irreducibleSetEquivPoints (α := X))

/-- The topological Krull dimension of a scheme is the supremum over its points of the Krull
dimensions of the local rings, i.e. of the coheights. -/
theorem topologicalKrullDim_eq_iSup_coheight (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, (Order.coheight x : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_coheight]

/-- **Upper bound in the dimension formula for a flat morphism.**  If `q : W ⟶ U` is a flat
morphism of locally Noetherian schemes all of whose fibre local rings have Krull dimension at
most `r`, then `dim W ≤ dim U + r`. -/
theorem topologicalKrullDim_le_add_of_fibreCodim_le {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] {r : ℕ} (h : ∀ x : W, fibreCodim q x ≤ r) :
    topologicalKrullDim W ≤ topologicalKrullDim U + r := by
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [topologicalKrullDim_eq_iSup_coheight W, iSup_of_empty]
    exact bot_le
  · have hU : Nonempty U := ⟨q hW.some⟩
    have key : (⨆ x : W, Order.coheight x) ≤ (⨆ u : U, Order.coheight u) + (r : ℕ∞) := by
      refine iSup_le fun x => ?_
      rw [coheight_eq_coheight_apply_add_fibreCodim q x]
      exact add_le_add (le_iSup (fun u : U => Order.coheight u) (q x)) (h x)
    rw [topologicalKrullDim_eq_krullDim, topologicalKrullDim_eq_krullDim,
      Order.krullDim_eq_iSup_coheight_of_nonempty (α := W),
      Order.krullDim_eq_iSup_coheight_of_nonempty (α := U)]
    exact_mod_cast key

/-- **Lower bound in the dimension formula for a flat morphism.**  If `q : W ⟶ U` is a flat
morphism of locally Noetherian schemes such that every point `u : U` is the image of a point of
`W` whose fibre local ring has Krull dimension at least `r` (in particular `q` is surjective),
then `dim U + r ≤ dim W`. -/
theorem add_le_topologicalKrullDim_of_le_fibreCodim {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] {r : ℕ}
    (h : ∀ u : U, ∃ x : W, q x = u ∧ (r : ℕ∞) ≤ fibreCodim q x) :
    topologicalKrullDim U + r ≤ topologicalKrullDim W := by
  rcases isEmpty_or_nonempty U with hU | hU
  · rw [topologicalKrullDim_eq_iSup_coheight U, iSup_of_empty, WithBot.bot_add]
    exact bot_le
  · obtain ⟨x0, -, -⟩ := h hU.some
    have hW : Nonempty W := ⟨x0⟩
    have key : (⨆ u : U, (Order.coheight u + (r : ℕ∞))) ≤ ⨆ x : W, Order.coheight x := by
      refine iSup_le fun u => ?_
      obtain ⟨x, hxu, hx⟩ := h u
      refine le_trans ?_ (le_iSup (fun y : W => Order.coheight y) x)
      rw [coheight_eq_coheight_apply_add_fibreCodim q x, hxu]
      exact add_le_add le_rfl hx
    have key2 : (⨆ u : U, Order.coheight u) + (r : ℕ∞) ≤ ⨆ x : W, Order.coheight x := by
      rw [ENat.iSup_add]
      exact key
    rw [topologicalKrullDim_eq_krullDim, topologicalKrullDim_eq_krullDim,
      Order.krullDim_eq_iSup_coheight_of_nonempty (α := W),
      Order.krullDim_eq_iSup_coheight_of_nonempty (α := U)]
    exact_mod_cast key2

/-- **The dimension formula for a flat morphism over a locally Noetherian base** (Stacks 02JU in
the form controlled by going-down).  If `q : W ⟶ U` is flat between locally Noetherian schemes,
every fibre local ring of `q` has Krull dimension at most `r`, and every point of `U` is the image
of a point whose fibre local ring has Krull dimension exactly `r`, then
`dim W = dim U + r`.  Both the empty and the infinite-dimensional cases are covered, the
dimensions being valued in `WithBot ℕ∞`. -/
theorem topologicalKrullDim_eq_add_of_fibreCodim {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] {r : ℕ} (hle : ∀ x : W, fibreCodim q x ≤ r)
    (hge : ∀ u : U, ∃ x : W, q x = u ∧ (r : ℕ∞) ≤ fibreCodim q x) :
    topologicalKrullDim W = topologicalKrullDim U + r :=
  le_antisymm (topologicalKrullDim_le_add_of_fibreCodim_le q hle)
    (add_le_topologicalKrullDim_of_le_fibreCodim q hge)
/-- The ideal cutting out the fibre local ring of `q` at `x` is proper: the stalk map is a local
homomorphism, so the image of the maximal ideal of `O_{U, q x}` lands inside the maximal ideal of
`O_{W, x}`. -/
theorem map_maximalIdeal_stalkMap_ne_top {W U : Scheme.{u}} (q : W ⟶ U) (x : W) :
    (IsLocalRing.maximalIdeal (U.presheaf.stalk (q x))).map (q.stalkMap x).hom ≠ ⊤ :=
  (IsLocalRing.map_maximalIdeal_lt_top (q.stalkMap x).hom).ne

/-- `fibreCodim q x` is the Krull dimension of the fibre local ring `fibreStalk q x`, i.e. of the
local ring of the scheme-theoretic fibre `W_{q x}` at `x`. -/
theorem fibreCodim_eq_ringKrullDim_fibreStalk {W U : Scheme.{u}} (q : W ⟶ U) (x : W) :
    (fibreCodim q x : WithBot ℕ∞) = ringKrullDim (fibreStalk q x) := by
  have hI := map_maximalIdeal_stalkMap_ne_top q x
  have hnt : Nontrivial (fibreStalk q x) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hloc : IsLocalRing (fibreStalk q x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal (W.presheaf.stalk x)).map
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (U.presheaf.stalk (q x))).map
        (q.stalkMap x).hom)) = IsLocalRing.maximalIdeal (fibreStalk q x) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hrw : fibreCodim q x = (IsLocalRing.maximalIdeal (fibreStalk q x)).height := by
    rw [← hmax]
    rfl
  rw [hrw, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]

/-- **Upper bound in the dimension formula, in terms of the fibre local rings.**  For `q : W ⟶ U`
flat between locally Noetherian schemes whose fibre local rings all have Krull dimension at most
`r`, one has `dim W ≤ dim U + r`. -/
theorem topologicalKrullDim_le_add_of_krullDimLE_fibreStalk {W U : Scheme.{u}} (q : W ⟶ U)
    [Flat q] [IsLocallyNoetherian W] [IsLocallyNoetherian U] {r : ℕ}
    (h : ∀ x : W, Ring.KrullDimLE r (fibreStalk q x)) :
    topologicalKrullDim W ≤ topologicalKrullDim U + r := by
  refine topologicalKrullDim_le_add_of_fibreCodim_le q fun x => ?_
  have h1 : ringKrullDim (fibreStalk q x) ≤ (r : WithBot ℕ∞) := Ring.krullDimLE_iff.mp (h x)
  rw [← fibreCodim_eq_ringKrullDim_fibreStalk] at h1
  exact_mod_cast h1

/-- **The dimension formula for a flat morphism, in terms of the fibre local rings.**  If
`q : W ⟶ U` is flat between locally Noetherian schemes, every fibre local ring of `q` has Krull
dimension at most `r`, and every point of `U` is the image of a point whose fibre local ring has
Krull dimension at least `r`, then `dim W = dim U + r`. -/
theorem topologicalKrullDim_eq_add_of_ringKrullDim_fibreStalk {W U : Scheme.{u}} (q : W ⟶ U)
    [Flat q] [IsLocallyNoetherian W] [IsLocallyNoetherian U] {r : ℕ}
    (hle : ∀ x : W, Ring.KrullDimLE r (fibreStalk q x))
    (hge : ∀ u : U, ∃ x : W, q x = u ∧ (r : WithBot ℕ∞) ≤ ringKrullDim (fibreStalk q x)) :
    topologicalKrullDim W = topologicalKrullDim U + r := by
  refine le_antisymm (topologicalKrullDim_le_add_of_krullDimLE_fibreStalk q hle)
    (add_le_topologicalKrullDim_of_le_fibreCodim q fun u => ?_)
  obtain ⟨x, hxu, hx⟩ := hge u
  refine ⟨x, hxu, ?_⟩
  rw [← fibreCodim_eq_ringKrullDim_fibreStalk] at hx
  exact_mod_cast hx
/-- A nonempty space all of whose irreducible components have topological Krull dimension `d` has
topological Krull dimension `d`.  Together with `topologicalKrullDim_le_of_pure` this converts the
repository's pure-dimension predicate into a statement about the total dimension. -/
theorem topologicalKrullDim_eq_of_pure {T : Type*} [TopologicalSpace T] (hne : Nonempty T) {d : ℕ}
    (h : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = d) :
    topologicalKrullDim T = d := by
  refine le_antisymm (topologicalKrullDim_le_of_pure h) ?_
  obtain ⟨z⟩ := hne
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({z} : Set T)) isIrreducible_singleton.closure
  rw [← h C hC]
  exact topologicalKrullDim_subspace_le T C

/-- **The dimension formula over a locally Noetherian base, with the base given in the
repository's pure-dimension terms.**  If `U` is nonempty and pure of dimension `a`, `q : W ⟶ U` is
flat between locally Noetherian schemes, every fibre local ring of `q` has Krull dimension at most
`r`, and every point of `U` is the image of a point whose fibre local ring has Krull dimension at
least `r`, then `dim W = a + r`.  The conclusion is about the *total* dimension of `W`: the
pure-dimension conclusion `SchemePureDimension W (a + r)` is false in this generality, see the
module docstring. -/
theorem topologicalKrullDim_eq_of_schemePureDimension {W U : Scheme.{u}} (q : W ⟶ U) [Flat q]
    [IsLocallyNoetherian W] [IsLocallyNoetherian U] {a r : ℕ} (hne : Nonempty U)
    (hU : SchemePureDimension U a) (hle : ∀ x : W, fibreCodim q x ≤ r)
    (hge : ∀ u : U, ∃ x : W, q x = u ∧ (r : ℕ∞) ≤ fibreCodim q x) :
    topologicalKrullDim W = ((a + r : ℕ) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_add_of_fibreCodim q hle hge, topologicalKrullDim_eq_of_pure hne hU]
  push_cast
  ring

/-- The *total*-dimension analogue of `SmoothPureDimensionFormulaAt`: a smooth surjection of pure
relative dimension `r` whose base is pure of dimension `a` has total dimension `a + r`.  This is
strictly weaker than `SmoothPureDimensionFormulaAt`, which asserts that *every* irreducible
component of the source has dimension `a + r`; unlike that statement, it is not refuted over a
locally Noetherian base by the counterexample of the module docstring. -/
def TotalDimensionFormulaAt {W U : Scheme.{u}} (q : W ⟶ U) : Prop :=
  ∀ r a : ℕ, _root_.AlgebraicGeometry.Smooth q → _root_.AlgebraicGeometry.Surjective q →
    SchemeMorphismPureRelativeDimension q r → SchemePureDimension U a →
      topologicalKrullDim W = ((a + r : ℕ) : WithBot ℕ∞)

/-- The pure-dimension formula implies its total-dimension weakening for a morphism with nonempty
source. -/
theorem totalDimensionFormulaAt_of_smoothPureDimensionFormulaAt {W U : Scheme.{u}} (q : W ⟶ U)
    (hne : Nonempty W) (h : SmoothPureDimensionFormulaAt q) : TotalDimensionFormulaAt q :=
  fun r a hsm hsurj hq hU => topologicalKrullDim_eq_of_pure hne (h r a hsm hsurj hq hU)

/-- The total-dimension formula for the two projections of the overlap of two atlas dimension
presentations; the total-dimension analogue of `OverlapDimensionFormula`. -/
def OverlapTotalDimensionFormula (X : AlgebraicStack.{u}) : Prop :=
  ∀ A B : StackDimensionPresentation X,
    TotalDimensionFormulaAt (A.overlap B).fst ∧ TotalDimensionFormulaAt (A.overlap B).snd

/-- **Atlas independence needs only the total-dimension formula.**  Computing the *total*
dimension of the overlap `U ×_X V` through each of its two smooth projections already gives
`dim U + r_V = dim V + r_U`, hence `dim U - r_U = dim V - r_V`: the pure-dimension conclusion of
`SmoothPureDimensionFormulaAt` is never needed, and neither is the nonemptiness hypothesis of
`stackDimensionIndependent_of_overlapDimensionFormula` (the total formula for the overlap already
forces its dimension to be a natural number, hence its space to be nonempty).  This is the form of
the dimension formula that the going-down results of this file produce over a locally Noetherian
base. -/
theorem stackDimensionIndependent_of_overlapTotalDimensionFormula {X : AlgebraicStack.{u}}
    (hF : OverlapTotalDimensionFormula X) : StackDimensionIndependent X := by
  intro A B
  have h1 : topologicalKrullDim (A.overlap B).space
      = ((A.atlasDimension + B.relativeDimension : ℕ) : WithBot ℕ∞) :=
    (hF A B).2 B.relativeDimension A.atlasDimension (A.overlap_snd_smooth B)
      (A.overlap_snd_surjective B) (A.overlap_snd_relativeDimension B) A.atlasPureDimension
  have h2 : topologicalKrullDim (A.overlap B).space
      = ((B.atlasDimension + A.relativeDimension : ℕ) : WithBot ℕ∞) :=
    (hF A B).1 A.relativeDimension B.atlasDimension (A.overlap_fst_smooth B)
      (A.overlap_fst_surjective B) (A.overlap_fst_relativeDimension B) B.atlasPureDimension
  have hkey : A.atlasDimension + B.relativeDimension
      = B.atlasDimension + A.relativeDimension := by
    have h := h1.symm.trans h2
    exact_mod_cast h
  simp only [StackDimensionPresentation.correctedDimension]
  omega
/-- The pure-dimension overlap formula implies its total-dimension weakening, so
`stackDimensionIndependent_of_overlapTotalDimensionFormula` subsumes
`stackDimensionIndependent_of_overlapDimensionFormula`. -/
theorem overlapTotalDimensionFormula_of_overlapDimensionFormula {X : AlgebraicStack.{u}}
    (hF : OverlapDimensionFormula X)
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme) :
    OverlapTotalDimensionFormula X := by
  intro A B
  obtain ⟨x⟩ := hne A
  obtain ⟨w, -⟩ := (A.overlap_snd_surjective B).surj x
  exact ⟨totalDimensionFormulaAt_of_smoothPureDimensionFormulaAt _ ⟨w⟩ (hF A B).1,
    totalDimensionFormulaAt_of_smoothPureDimensionFormulaAt _ ⟨w⟩ (hF A B).2⟩
end

end GromovWitten.AlgebraicGeometry.Curves
