/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.KeyFormula
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors

/-!
# The line bundle `O(D)` of an effective Cartier divisor as Čech data

For an effective Cartier divisor `D` on a scheme `X`, with chosen local equations
`r_x := D.localEquation x` on the affine opens `U_x := D.localEquationOpen x`, we build the
Čech presentation of the line bundle `O(D)` and its canonical rational section.

The local equations are non-zero-divisors on every open contained in `U_x` (affine or not), and
on every affine open of `U_x ⊓ U_y` both `r_x` and `r_y` generate the ideal of `D`; gluing over the
affine opens of the overlap gives a unique section `r_x / r_y` with `r_x = (r_x / r_y) * r_y`,
which is a unit with inverse `r_y / r_x`.

## Main results

* `Curves.EffectiveCartierDivisor.lineBundleData`: the `LineBundleData` of `O(D)`, with index
  type `X`, charts `U_x`, and transition units `g x y = r_x / r_y` (`lineBundleData_g_val`,
  `equationOn_eq_ratio_mul`).
* `Curves.EffectiveCartierDivisor.equationResidueUnit`: the residue class of `r_x` at a point
  `w ∈ U_x` outside the support of `D`, a unit of `κ(w)` (`isUnit_germ_localEquation`).
* `Curves.EffectiveCartierDivisor.exists_pointStalk_unit_equationResidueUnit`: for `w ⤳ v` with
  `v ∈ U_x` outside the support, the residue class of `r_x` in `κ(w)` comes from a unit of
  `pointStalk (w ⤳ v)` whose residue in `κ(v)` is the residue class of `r_x` at `v`.
* `Curves.EffectiveCartierDivisor.canonicalSection`: the canonical rational section of `O(D)`
  along an integral closed subscheme whose generic point is not in the support of `D`, with
  coordinate the image of `r_x` in every chart `x` (`coord_canonicalSection`).
* `Curves.EffectiveCartierDivisor.canonicalSection_divisor_apply`: the coefficients of its
  divisor are `pointOrd` of the residue class of `r_x`; they vanish outside the support of `D`
  (`canonicalSection_divisor_apply_eq_zero`, `support_canonicalSection_divisor_subset`).
* `Curves.EffectiveCartierDivisor.pointFrame_divisor_add_pointGenerator_divisor`: for
  `v ∉ D.support`, `div(frame of O(D) at v) + div(r̄) = div(canonical section along v)`, where
  `r̄ ∈ κ(v)ˣ` is the residue class of the local equation in the canonical chart at `v`.

The declarations about `D` live in the namespace `GromovWitten.AlgebraicGeometry.Curves.
EffectiveCartierDivisor` so that dot notation `D.lineBundleData` is available; the auxiliary
sheaf lemmas live in `GromovWitten.AlgebraicGeometry.IntersectionTheory`.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing Opposite

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open LineBundleInjective

/-! ## Local non-zero-divisors and gluing of ratios -/

section Ratio

variable {X : Scheme.{u}}

/-- Restricting twice is restricting once. -/
theorem cartier_res_res_apply {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom a) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Every open `V` is covered by the affine opens contained in it. -/
theorem cartier_le_iSup_affine (V : X.Opens) :
    V ≤ ⨆ W : {W : X.affineOpens // W.1 ≤ V}, W.1.1 := by
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩

/-- A regular section over an affine open `U` stays a non-zero-divisor after restriction to any
open `V ≤ U` (affine or not). -/
theorem cartier_mul_res_eq_zero {U : X.affineOpens} {r : Γ(X, U.1)} (hr : IsRegular r)
    {V : X.Opens} (hV : V ≤ U.1) (a : Γ(X, V))
    (ha : a * (X.presheaf.map (homOfLE hV).op).hom r = 0) : a = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.1 ≤ V} ↦ W.1.1) V
    (fun W ↦ homOfLE W.2) (cartier_le_iSup_affine V) a 0 (fun W ↦ ?_)
  have hreg : IsRegular ((X.presheaf.map (homOfLE (W.2.trans hV)).op).hom r) :=
    Curves.isRegular_map_of_flat _ (Curves.flat_affineOpenRestriction U W.1 (W.2.trans hV)) hr
  have h := congrArg (X.presheaf.map (homOfLE W.2).op).hom ha
  rw [map_mul, cartier_res_res_apply, map_zero] at h
  change (X.presheaf.map (homOfLE W.2).op).hom a = (X.presheaf.map (homOfLE W.2).op).hom 0
  rw [map_zero]
  exact hreg.2 (by simpa using h)

/-- Cancellation of a restricted regular section. -/
theorem cartier_mul_res_cancel {U : X.affineOpens} {r : Γ(X, U.1)} (hr : IsRegular r)
    {V : X.Opens} (hV : V ≤ U.1) {a b : Γ(X, V)}
    (h : a * (X.presheaf.map (homOfLE hV).op).hom r =
      b * (X.presheaf.map (homOfLE hV).op).hom r) : a = b :=
  sub_eq_zero.1 (cartier_mul_res_eq_zero hr hV _ (by rw [sub_mul, h, sub_self]))

/-- If `b` is a non-zero-divisor on every open `W ≤ V` and `a` is a multiple of `b` on every affine
open `W ≤ V`, then `a` is a multiple of `b` on `V`. -/
theorem cartier_exists_mul_eq_of_affine {V : X.Opens} (a b : Γ(X, V))
    (hb : ∀ (W : X.Opens) (hW : W ≤ V) (t : Γ(X, W)),
      t * (X.presheaf.map (homOfLE hW).op).hom b = 0 → t = 0)
    (hloc : ∀ (W : X.affineOpens) (hW : W.1 ≤ V), ∃ c : Γ(X, W.1),
      (X.presheaf.map (homOfLE hW).op).hom a = c * (X.presheaf.map (homOfLE hW).op).hom b) :
    ∃ c : Γ(X, V), a = c * b := by
  choose c hc using hloc
  let ι := {W : X.affineOpens // W.1 ≤ V}
  let sf : ∀ W : ι, Γ(X, W.1.1) := fun W ↦ c W.1 W.2
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun W : ι ↦ W.1.1) sf := by
    intro W W'
    have hWV : W.1.1 ⊓ W'.1.1 ≤ V := inf_le_left.trans W.2
    change (X.presheaf.map (homOfLE inf_le_left).op).hom (sf W) =
      (X.presheaf.map (homOfLE inf_le_right).op).hom (sf W')
    refine sub_eq_zero.1 (hb _ hWV _ ?_)
    rw [sub_mul]
    have e₁ := congrArg (X.presheaf.map (homOfLE (inf_le_left : W.1.1 ⊓ W'.1.1 ≤ W.1.1)).op).hom
      (hc W.1 W.2)
    have e₂ := congrArg (X.presheaf.map (homOfLE (inf_le_right : W.1.1 ⊓ W'.1.1 ≤ W'.1.1)).op).hom
      (hc W'.1 W'.2)
    rw [map_mul, cartier_res_res_apply, cartier_res_res_apply] at e₁ e₂
    change (X.presheaf.map (homOfLE inf_le_left).op).hom (sf W) *
        (X.presheaf.map (homOfLE hWV).op).hom b -
      (X.presheaf.map (homOfLE inf_le_right).op).hom (sf W') *
        (X.presheaf.map (homOfLE hWV).op).hom b = 0
    rw [← e₁, ← e₂, sub_self]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun W : ι ↦ W.1.1) V
    (fun W ↦ homOfLE W.2) (cartier_le_iSup_affine V) sf hcompat
  let s' : Γ(X, V) := s
  refine ⟨s', X.sheaf.eq_of_locally_eq' (fun W : ι ↦ W.1.1) V
    (fun W ↦ homOfLE W.2) (cartier_le_iSup_affine V) a (s' * b) (fun W ↦ ?_)⟩
  change (X.presheaf.map (homOfLE W.2).op).hom a =
    (X.presheaf.map (homOfLE W.2).op).hom (s' * b)
  rw [map_mul, hc W.1 W.2]
  congr 1
  exact (hs W).symm

end Ratio

end GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## The transition units of `O(D)` -/

namespace GromovWitten.AlgebraicGeometry.Curves.EffectiveCartierDivisor

open GromovWitten.AlgebraicGeometry.IntersectionTheory
open GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjective

variable {X : Scheme.{u}} (D : EffectiveCartierDivisor X)

/-- The local equation `r_x` of `D`, restricted to an open `V ≤ U_x`. -/
noncomputable def equationOn (x : X) {V : X.Opens} (hV : V ≤ (D.localEquationOpen x).1) :
    Γ(X, V) :=
  (X.presheaf.map (homOfLE hV).op).hom (D.localEquation x)

/-- Restricting `equationOn` gives `equationOn`. -/
theorem res_equationOn (x : X) {V W : X.Opens} (hV : V ≤ (D.localEquationOpen x).1)
    (hW : W ≤ V) :
    (X.presheaf.map (homOfLE hW).op).hom (D.equationOn x hV) = D.equationOn x (hW.trans hV) :=
  cartier_res_res_apply _ _ _

/-- The restricted local equations are non-zero-divisors: cancellation. -/
theorem equationOn_cancel (x : X) {V : X.Opens} (hV : V ≤ (D.localEquationOpen x).1)
    {a b : Γ(X, V)} (h : a * D.equationOn x hV = b * D.equationOn x hV) : a = b :=
  cartier_mul_res_cancel (D.localEquation_isRegular x) hV h

/-- On an affine open `W` the ideal of `D` is generated by the restricted local equation. -/
theorem ideal_eq_span_equationOn (x : X) (W : X.affineOpens)
    (hW : W.1 ≤ (D.localEquationOpen x).1) :
    D.idealSheaf.ideal W = Ideal.span {D.equationOn x hW} := by
  rw [← D.idealSheaf.map_ideal (U := W) (V := D.localEquationOpen x) hW,
    D.ideal_localEquationOpen, Ideal.map_span, Set.image_singleton]
  rfl

/-- On any open `V ≤ U_x ⊓ U_y`, the local equation `r_x` is a multiple of `r_y`. -/
theorem exists_equationOn_eq_mul (x y : X) {V : X.Opens} (hx : V ≤ (D.localEquationOpen x).1)
    (hy : V ≤ (D.localEquationOpen y).1) :
    ∃ c : Γ(X, V), D.equationOn x hx = c * D.equationOn y hy := by
  refine cartier_exists_mul_eq_of_affine _ _ (fun W hW t ht ↦ ?_) (fun W hW ↦ ?_)
  · rw [res_equationOn] at ht
    exact cartier_mul_res_eq_zero (D.localEquation_isRegular y) _ t ht
  · rw [res_equationOn, res_equationOn]
    have hmem : D.equationOn x (hW.trans hx) ∈ Ideal.span {D.equationOn y (hW.trans hy)} := by
      rw [← D.ideal_eq_span_equationOn y W, D.ideal_eq_span_equationOn x W (hW.trans hx)]
      exact Ideal.subset_span rfl
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, hc.symm⟩

/-- The ratio `r_x / r_y` on an open `V ≤ U_x ⊓ U_y`. -/
noncomputable def equationRatio (x y : X) {V : X.Opens} (hx : V ≤ (D.localEquationOpen x).1)
    (hy : V ≤ (D.localEquationOpen y).1) : Γ(X, V) :=
  (D.exists_equationOn_eq_mul x y hx hy).choose

/-- The defining property of `equationRatio`: `r_x = (r_x / r_y) * r_y`. -/
theorem equationOn_eq_ratio_mul (x y : X) {V : X.Opens} (hx : V ≤ (D.localEquationOpen x).1)
    (hy : V ≤ (D.localEquationOpen y).1) :
    D.equationOn x hx = D.equationRatio x y hx hy * D.equationOn y hy :=
  (D.exists_equationOn_eq_mul x y hx hy).choose_spec

/-- The ratio `r_x / r_y` is characterised by `r_x = c * r_y`. -/
theorem eq_equationRatio (x y : X) {V : X.Opens} (hx : V ≤ (D.localEquationOpen x).1)
    (hy : V ≤ (D.localEquationOpen y).1) {c : Γ(X, V)}
    (hc : D.equationOn x hx = c * D.equationOn y hy) : c = D.equationRatio x y hx hy :=
  D.equationOn_cancel y hy (hc.symm.trans (D.equationOn_eq_ratio_mul x y hx hy))

/-- `(r_x / r_y) * (r_y / r_x) = 1`. -/
theorem equationRatio_mul_equationRatio (x y : X) {V : X.Opens}
    (hx : V ≤ (D.localEquationOpen x).1) (hy : V ≤ (D.localEquationOpen y).1) :
    D.equationRatio x y hx hy * D.equationRatio y x hy hx = 1 := by
  refine D.equationOn_cancel x hx ?_
  rw [one_mul, mul_assoc, ← D.equationOn_eq_ratio_mul y x hy hx,
    ← D.equationOn_eq_ratio_mul x y hx hy]

/-- Restricting the ratio `r_x / r_y` to a smaller open gives the ratio there. -/
theorem res_equationRatio (x y : X) {V W : X.Opens} (hx : V ≤ (D.localEquationOpen x).1)
    (hy : V ≤ (D.localEquationOpen y).1) (hW : W ≤ V) :
    (X.presheaf.map (homOfLE hW).op).hom (D.equationRatio x y hx hy) =
      D.equationRatio x y (hW.trans hx) (hW.trans hy) := by
  refine D.eq_equationRatio x y _ _ ?_
  rw [← D.res_equationOn x hx hW, ← D.res_equationOn y hy hW, D.equationOn_eq_ratio_mul x y hx hy,
    map_mul]

/-- `(r_x / r_y) * (r_y / r_z) = r_x / r_z`. -/
theorem equationRatio_mul_equationRatio_eq (x y z : X) {V : X.Opens}
    (hx : V ≤ (D.localEquationOpen x).1) (hy : V ≤ (D.localEquationOpen y).1)
    (hz : V ≤ (D.localEquationOpen z).1) :
    D.equationRatio x y hx hy * D.equationRatio y z hy hz = D.equationRatio x z hx hz := by
  refine D.equationOn_cancel z hz ?_
  rw [mul_assoc, ← D.equationOn_eq_ratio_mul y z hy hz, ← D.equationOn_eq_ratio_mul x y hx hy,
    ← D.equationOn_eq_ratio_mul x z hx hz]

/-- The ratio `r_x / r_y` as a unit on `V ≤ U_x ⊓ U_y`. -/
noncomputable def equationRatioUnit (x y : X) {V : X.Opens}
    (hx : V ≤ (D.localEquationOpen x).1) (hy : V ≤ (D.localEquationOpen y).1) : Γ(X, V)ˣ :=
  ⟨D.equationRatio x y hx hy, D.equationRatio y x hy hx,
    D.equationRatio_mul_equationRatio x y hx hy, D.equationRatio_mul_equationRatio y x hy hx⟩

/-- **The Čech data of the line bundle `O(D)`.**  The index type is `X`, the chart of `x` is the
local-equation open `U_x = D.localEquationOpen x`, and the transition unit `g x y` on `U_x ⊓ U_y`
is the ratio `r_x / r_y` of the local equations, characterised by `r_x = g x y * r_y`
(`lineBundleData_g_val`).  In the convention of `LineBundleData` (`e_y = g x y • e_x`, i.e.
coordinates transform by `f_x = g x y * f_y`) the canonical section has coordinate `r_x` in the
chart `x`. -/
noncomputable def lineBundleData : LineBundleData X where
  J := X
  U := D.localEquationOpen
  covers x := ⟨x, D.mem_localEquationOpen x⟩
  g x y := D.equationRatioUnit x y inf_le_left inf_le_right
  g_self x := by
    refine Units.ext ?_
    change D.equationRatio x x _ _ = 1
    exact (D.eq_equationRatio x x _ _ (one_mul _).symm).symm
  g_cocycle x y z := by
    refine Units.ext ?_
    simp only [Units.val_mul, resUnit, Units.coe_map]
    change (X.presheaf.map _).hom (D.equationRatio x y _ _) *
        (X.presheaf.map _).hom (D.equationRatio y z _ _) =
      (X.presheaf.map _).hom (D.equationRatio x z _ _)
    rw [res_equationRatio, res_equationRatio, res_equationRatio,
      equationRatio_mul_equationRatio_eq]

/-- The transition unit `g x y` of `D.lineBundleData` is the ratio `r_x / r_y` on `U_x ⊓ U_y`,
so that `r_x = g x y * r_y` there (`equationOn_eq_ratio_mul`). -/
theorem lineBundleData_g_val (x y : X) :
    (D.lineBundleData.g x y :
        Γ(X, (D.lineBundleData.U x : X.Opens) ⊓ (D.lineBundleData.U y : X.Opens))) =
      D.equationRatio x y inf_le_left inf_le_right :=
  rfl

/-! ## Units at points outside the support -/

/-- At a point `w ∈ U_x` outside the support of `D`, the germ of the local equation `r_x` is a
unit. -/
theorem isUnit_germ_localEquation (x : X) {w : X} (hw : w ∈ (D.localEquationOpen x).1)
    (hns : w ∉ D.support) : IsUnit (X.presheaf.germ _ w hw (D.localEquation x)) := by
  by_contra hu
  apply hns
  change w ∈ D.idealSheaf.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := D.localEquationOpen x) hw,
    D.ideal_localEquationOpen, Scheme.mem_zeroLocus_iff]
  intro f hf hwf
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  rw [X.mem_basicOpen _ w hw, map_mul] at hwf
  exact hu (isUnit_of_mul_isUnit_right hwf)

/-- A generalisation of a point outside the (closed) support is outside the support. -/
theorem not_mem_support_of_specializes {w v : X} (h : w ⤳ v) (hv : v ∉ D.support) :
    w ∉ D.support :=
  fun hw ↦ hv (h.mem_closed D.support.isClosed hw)

/-- The residue class at a point `w ∈ U_x` outside the support of `D` of the local equation
`r_x`, as a unit of `κ(w)`. -/
noncomputable def equationResidueUnit (x : X) {w : X} (hw : w ∈ (D.localEquationOpen x).1)
    (hns : w ∉ D.support) : (X.residueField w)ˣ :=
  ((D.isUnit_germ_localEquation x hw hns).map (X.residue w).hom).unit

/-- The value of `equationResidueUnit`: the residue class of the germ of `r_x`. -/
@[simp]
theorem equationResidueUnit_val (x : X) {w : X} (hw : w ∈ (D.localEquationOpen x).1)
    (hns : w ∉ D.support) :
    (D.equationResidueUnit x hw hns : X.residueField w) =
      X.residue w (X.presheaf.germ _ w hw (D.localEquation x)) :=
  rfl

/-- **Point-stalk units from local equations.**  Let `w ⤳ v` with `v ∈ U_x` and `v` outside
the support of `D`.  Then the residue class of `r_x` in `κ(w)` is the image of a unit `a` of
`pointStalk (w ⤳ v)` whose residue in `κ(v)` is the residue class of `r_x` at `v`. -/
theorem exists_pointStalk_unit_equationResidueUnit {w v : X} (h : w ⤳ v) (x : X)
    (hv : v ∈ (D.localEquationOpen x).1) (hvns : v ∉ D.support) :
    ∃ a : (pointStalk h)ˣ,
      pointStalkUnitIncl h a = D.equationResidueUnit x (h.mem_open (Opens.isOpen _) hv)
        (D.not_mem_support_of_specializes h hvns) ∧
      pointStalkResidueUnit h a = D.equationResidueUnit x hv hvns := by
  refine ⟨((D.isUnit_germ_localEquation x hv hvns).map
    (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h)))).unit, Units.ext ?_, Units.ext ?_⟩
  · change pointStalkMap h (X.presheaf.germ _ v hv (D.localEquation x)) =
      X.residue w (X.presheaf.germ _ w _ (D.localEquation x))
    rw [pointStalkMap_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
  · exact pointStalkResidueEquiv_residue_mk h _

/-- The residue class of `r_x` at `w` is a point-stalk unit along every `w ⤳ v` with `v ∈ U_x`
outside the support of `D`. -/
theorem isPointStalkUnit_equationResidueUnit {w v : X} (h : w ⤳ v) (x : X)
    (hv : v ∈ (D.localEquationOpen x).1) (hvns : v ∉ D.support)
    (hw : w ∈ (D.localEquationOpen x).1) (hwns : w ∉ D.support) :
    IsPointStalkUnit h (D.equationResidueUnit x hw hwns) := by
  obtain ⟨a, ha, -⟩ := D.exists_pointStalk_unit_equationResidueUnit h x hv hvns
  exact ⟨a, ha⟩

/-! ## The canonical rational section -/

/-- The image of the local equation `r_x` in the function field of an integral closed
subscheme `W` whose generic point lies in `U_x` but not in the support of `D` is a unit. -/
theorem isUnit_toFunctionField_localEquation (W : IntegralClosedSubscheme X) (x : X)
    (hx : W.eta ∈ (D.localEquationOpen x).1) (hW : W.genericPointImage ∉ D.support) :
    IsUnit (W.toFunctionField _ hx (D.localEquation x)) :=
  (D.isUnit_germ_localEquation x hx hW).map (W.inclusion.stalkMap (genericPoint W.scheme)).hom

/-- **The canonical rational section of `O(D)`** along an integral closed subscheme `W` whose
generic point is not in the support of `D`: presented in the chart `η_W` (the chart attached to
the generic point of `W`) by the image of the local equation `r_{η_W}` in the function field
of `W`. -/
noncomputable def canonicalSection (W : IntegralClosedSubscheme X)
    (hW : W.genericPointImage ∉ D.support) : D.lineBundleData.RationalSection W where
  j₀ := W.eta
  hj₀ := D.mem_localEquationOpen W.eta
  f := (D.isUnit_toFunctionField_localEquation W W.eta (D.mem_localEquationOpen W.eta) hW).unit

/-- In every chart `x` containing the generic point of `W`, the coordinate of the canonical
section is the image of the local equation `r_x` in the function field of `W`. -/
theorem coord_canonicalSection (W : IntegralClosedSubscheme X)
    (hW : W.genericPointImage ∉ D.support) (x : X) (hx : W.eta ∈ (D.localEquationOpen x).1) :
    ((D.canonicalSection W hW).coord x hx : W.scheme.functionField) =
      W.toFunctionField _ hx (D.localEquation x) := by
  have hxy : W.eta ∈ (D.localEquationOpen x).1 ⊓ (D.localEquationOpen W.eta).1 :=
    memInf hx (D.mem_localEquationOpen W.eta)
  change W.toFunctionField _ hxy (D.equationRatio x W.eta inf_le_left inf_le_right) *
      W.toFunctionField _ (D.mem_localEquationOpen W.eta) (D.localEquation W.eta) = _
  rw [← W.toFunctionField_res inf_le_right hxy (D.mem_localEquationOpen W.eta),
    ← W.toFunctionField_res inf_le_left hxy hx, ← map_mul]
  change _ = W.toFunctionField _ hxy (D.equationOn x inf_le_left)
  rw [D.equationOn_eq_ratio_mul x W.eta inf_le_left inf_le_right]
  rfl

/-- The divisor of a rational section along `W` has coefficient zero at points that are not
specialisations of the generic point of `W`. -/
private theorem divisor_apply_eq_zero_of_not_specializes' {L : LineBundleData X}
    {W : IntegralClosedSubscheme X} (s : L.RationalSection W) (dim : DimensionFunction X)
    {v : X} (h : ¬ W.genericPointImage ⤳ v) : (s.divisor dim : X → ℚ) v = 0 := by
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  by_cases hmem : v ∈ Set.range W.inclusion.base
  · obtain ⟨q, rfl⟩ := hmem
    exact absurd (W.genericPointImage_specializes q) h
  · exact AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range W.inclusion
      (dim : X → ℤ) _ v hmem

/-- **Divisor coefficients of the canonical section.**  For a specialisation `v` of the
generic point `w` of `W` and any chart `x` with `v ∈ U_x`, the coefficient at `v` of the divisor
of the canonical section is `pointOrd (w ⤳ v)` of the residue class of `r_x` in `κ(w)`. -/
theorem canonicalSection_divisor_apply [IsLocallyNoetherian X] (W : IntegralClosedSubscheme X)
    (hW : W.genericPointImage ∉ D.support) (dim : DimensionFunction X) {v : X}
    (h : W.genericPointImage ⤳ v) (x : X) (hv : v ∈ (D.localEquationOpen x).1) :
    ((D.canonicalSection W hW).divisor dim : X → ℚ) v =
      pointOrd h (D.equationResidueUnit x (h.mem_open (Opens.isOpen _) hv) hW) := by
  obtain ⟨q, rfl⟩ := W.mem_range_of_specializes h
  unfold LineBundleData.RationalSection.divisor IntegralClosedSubscheme.pushforward
  rw [AlgebraicCycle.map_closedImmersion_apply_image W.inclusion (dim : X → ℤ),
    LineBundleData.RationalSection.divisorCycle_apply,
    LineBundleData.RationalSection.ord_well_defined _ x q hv, W.ord_eq_pointOrd q]
  congr 2
  refine Units.ext ?_
  change W.functionFieldIso.hom ((D.canonicalSection W hW).coord x _ : W.scheme.functionField) =
    _
  refine (congrArg W.functionFieldIso.hom
    (D.coord_canonicalSection W hW x (W.eta_mem_of_mem_preimage hv))).trans ?_
  exact W.stalkMap_functionFieldIso _

/-- The divisor of the canonical section has coefficient zero at every point outside the
support of `D`. -/
theorem canonicalSection_divisor_apply_eq_zero [IsLocallyNoetherian X]
    (W : IntegralClosedSubscheme X) (hW : W.genericPointImage ∉ D.support)
    (dim : DimensionFunction X) {v : X} (hv : v ∉ D.support) :
    ((D.canonicalSection W hW).divisor dim : X → ℚ) v = 0 := by
  by_cases h : W.genericPointImage ⤳ v
  · rw [D.canonicalSection_divisor_apply W hW dim h v (D.mem_localEquationOpen v),
      (D.isPointStalkUnit_equationResidueUnit h v (D.mem_localEquationOpen v) hv _
        _).pointOrd_eq_zero]
    rfl
  · exact divisor_apply_eq_zero_of_not_specializes' _ dim h

/-- The divisor of the canonical section is supported in the support of `D`. -/
theorem support_canonicalSection_divisor_subset [IsLocallyNoetherian X]
    (W : IntegralClosedSubscheme X) (hW : W.genericPointImage ∉ D.support)
    (dim : DimensionFunction X) :
    Function.support ((D.canonicalSection W hW).divisor dim : X → ℚ) ⊆ D.support :=
  fun _ hv ↦ by_contra fun hns ↦ hv (D.canonicalSection_divisor_apply_eq_zero W hW dim hns)

/-! ## The canonical section along `pointSubscheme w` -/

/-- If `w` is outside the support of `D`, so is the generic point of `pointSubscheme w`. -/
theorem genericPointImage_pointSubscheme_not_mem [IsLocallyNoetherian X] [NoetherianSpace X]
    {w : X} (hw : w ∉ D.support) : (pointSubscheme w).genericPointImage ∉ D.support := by
  rwa [genericPointImage_pointSubscheme]

/-- The coordinate in `κ(w)` of the canonical section along `pointSubscheme w`, in any chart `x`
containing `w`, is the residue class of `r_x` at `w`. -/
theorem pointCoord_canonicalSection [IsLocallyNoetherian X] [NoetherianSpace X] {w : X}
    (hW : (pointSubscheme w).genericPointImage ∉ D.support) (x : X)
    (hj : (pointSubscheme w).eta ∈ (D.localEquationOpen x).1)
    (hw : w ∈ (D.localEquationOpen x).1) (hns : w ∉ D.support) :
    (D.canonicalSection (pointSubscheme w) hW).pointCoord x hj =
      D.equationResidueUnit x hw hns := by
  refine Units.ext ?_
  change pointFieldEquiv w ((D.canonicalSection (pointSubscheme w) hW).coord x hj :
    (pointSubscheme w).scheme.functionField) = _
  rw [coord_canonicalSection, pointFieldEquiv_toFunctionField hj hw]
  rfl

/-- **The Gysin identity at a point outside the support.**  For `v ∉ D.support`, with
`r̄ ∈ κ(v)ˣ` the residue class at `v` of the local equation in the canonical chart
`D.lineBundleData.keyChart v`, the divisor of the frame of `O(D)` at `v` plus the divisor of the
point generator of `r̄` is the divisor of the canonical section along `pointSubscheme v`. -/
theorem pointFrame_divisor_add_pointGenerator_divisor [IsLocallyNoetherian X]
    [NoetherianSpace X] (dim : DimensionFunction X) {v : X} (hv : v ∉ D.support) :
    (D.lineBundleData.pointFrame v).divisor dim +
        (pointGenerator v (D.equationResidueUnit (D.lineBundleData.keyChart v)
          (D.lineBundleData.mem_keyChart v) hv)).divisor dim =
      (D.canonicalSection (pointSubscheme v)
        (D.genericPointImage_pointSubscheme_not_mem hv)).divisor dim := by
  set L := D.lineBundleData
  set r := D.equationResidueUnit (L.keyChart v) (L.mem_keyChart v) hv
  set c := D.canonicalSection (pointSubscheme v) (D.genericPointImage_pointSubscheme_not_mem hv)
  apply Function.locallyFinsuppWithin.coe_injective
  funext Q
  dsimp only
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  by_cases hvQ : v ⤳ Q
  · have hQ := eta_pointSubscheme_mem hvQ (L.mem_keyChart Q)
    have hv' := eta_pointSubscheme_mem (specializes_refl v) (L.mem_keyChart v)
    have hvv : v ∈ (L.U (L.keyChart Q) : X.Opens) ⊓ (L.U (L.keyChart v) : X.Opens) :=
      memInf (hvQ.mem_open (Opens.isOpen _) (L.mem_keyChart Q)) (L.mem_keyChart v)
    rw [(L.pointFrame v).divisor_apply_eq_pointOrd dim hvQ _ hQ (L.mem_keyChart Q),
      c.divisor_apply_eq_pointOrd dim hvQ _ hQ (L.mem_keyChart Q),
      divisor_pointGenerator_apply dim v r hvQ,
      (L.pointFrame v).pointCoord_eq_mul _ _ hQ hv' hvv, L.pointCoord_pointFrame v hv',
      c.pointCoord_eq_mul _ _ hQ hv' hvv,
      D.pointCoord_canonicalSection _ _ hv' (L.mem_keyChart v) hv, mul_one, pointOrd_mul]
    push_cast
    rfl
  · rw [(L.pointFrame v).divisor_apply_eq_zero_of_not_specializes dim hvQ,
      c.divisor_apply_eq_zero_of_not_specializes dim hvQ,
      divisor_pointGenerator_apply_eq_zero dim v r Q hvQ, zero_add]

end GromovWitten.AlgebraicGeometry.Curves.EffectiveCartierDivisor
