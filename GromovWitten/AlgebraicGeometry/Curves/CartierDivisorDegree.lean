/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors
import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree
import Mathlib.RingTheory.RingHom.Flat

/-!
# The degree of a Cartier divisor on a curve (issue #141)

For a field `k` and a scheme `X`, this file constructs the degree of an effective Cartier divisor
`D` on `X` (`GromovWitten.AlgebraicGeometry.Curves.EffectiveCartierDivisor`, ideal-sheaf based, see
`Curves/CartierDivisors.lean`) as the degree, in the sense of
`IntersectionTheory.ZeroCycleDegree.degreeCycle`, of its associated zero-cycle: the coefficient of
a point `x` is the length, as a module over the local ring `𝒪_{X,x}`, of the local ring
`𝒪_{D,x} = 𝒪_{X,x} ⧸ multiplicityIdeal D x` of the divisor itself.

## Main declarations

* `length_quotient_span_singleton_mul` — the commutative-algebra core of additivity: for a regular
  (non-zero-divisor) element `f` of a commutative ring `A`, `Module.length A (A ⧸ (f * g))
  = Module.length A (A ⧸ (g)) + Module.length A (A ⧸ (f))`, via the short exact sequence of
  `A`-modules `0 → A ⧸ (g) --(· * f)--> A ⧸ (f * g) → A ⧸ (f) → 0`.
* `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_germ_eq` — the stalk, at a point, of the
  ideal of an ideal sheaf is independent of the affine chart used to compute it.
* `EffectiveCartierDivisor.multiplicity` — the (`ℕ∞`-valued) length of `𝒪_{D,x}` over `𝒪_{X,x}`
  at every point `x` of `X` (`0` off the support, `multiplicity_eq_zero_of_notMem_support`);
  `multiplicity_sum` — its additivity under `EffectiveCartierDivisor.sum`, unconditionally (no
  finiteness or dimension hypothesis is needed for this `ℕ∞`-valued identity).
* `EffectiveCartierDivisor.HasFiniteDegree` — the two hypotheses needed to turn the multiplicities
  of `D` into an honest `ℚ`-valued zero-cycle: finite length on the support, and local finiteness
  of the support as a set of points (`HasFiniteDegree.sum` — additivity of this hypothesis).
* `EffectiveCartierDivisor.cycle`, `.degree`, `.degree_add`, `.degree_nonneg` — the zero-cycle of
  `D`, its degree (given `HasFiniteDegree` and `[CompactSpace X]`), its additivity under `sum`,
  and its nonnegativity.
* `EffectiveCartierDivisor.degree_sub_eq_of_sum_eq` — the degree of the *formal difference*
  `D₁ - D₂` of two effective divisors depends only on the class of that difference: if
  `D₁ + D₂' = D₁' + D₂` then `deg D₁ - deg D₂ = deg D₁' - deg D₂'`.
* `RelativeLineBundle.IsGeometricDegree` — the bridge to issue #141's acceptance criterion for
  `Curves/RelativeLineBundles.lean`, and `componentDegree_nonneg_of_isGeometricDegree`, the
  consequence that it forces the (a priori free) `componentDegree` labels to be nonnegative.

## What is not proved here

`multiplicity`/`multiplicity_sum` need no hypothesis on `X` at all (they hold for an effective
Cartier divisor on *any* scheme). Turning them into a `ℚ`-valued `degree` needs `HasFiniteDegree`,
which is *not* derived from "`X` integral of dimension one, proper over `k`" here: on such an `X`,
finiteness of the length at a point of the support should follow because a Noetherian local domain
of Krull dimension one, modulo a nonzero regular element, is Artinian (hence of finite length),
and local finiteness of the support should follow because a proper closed subset of an integral
curve is discrete; neither dimension-theoretic fact is established in this file, so
`HasFiniteDegree` is recorded as an explicit hypothesis of `degree`/`degree_add` instead.
Likewise not established: the compatibility of `degree` with the divisors of zeros and poles of a
rational function (`degree_principal_eq_zero`-style, item 1's last clause — this would require
relating `EffectiveCartierDivisor` to the `ord`/`RegularProperCurve` Weil-divisor machinery of
`IntersectionTheory/ProperCurveDegree*.lean`, not attempted here); and, for `IsGeometricDegree`,
the sharper fact that the `componentDegree` labels vanish exactly when the line bundle is trivial
(see the gap recorded in that declaration's docstring).
-/

open CategoryTheory
open _root_.AlgebraicGeometry
open TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ## The commutative-algebra core: length is additive along a regular factorisation -/

/-- **Length is additive under multiplying divisors, for a regular element.**  For a
non-zero-divisor `f` and any `g` in a commutative ring `A`, the length of `A ⧸ (f * g)` as an
`A`-module is the sum of the lengths of `A ⧸ (g)` and `A ⧸ (f)`.  This is the exact sequence of
`A`-modules `0 → A ⧸ (g) --(· * f)--> A ⧸ (f * g) → A ⧸ (f) → 0`: the first map is injective
because `f` is regular, and the composite to `A ⧸ (f)` is exact because the two submodules
`(f * g) ≤ (f)` differ (as submodules of `A ⧸ (f * g)`) by exactly the image of that map. -/
theorem length_quotient_span_singleton_mul {A : Type*} [CommRing A] {f g : A}
    (hf : IsRegular f) :
    Module.length A (A ⧸ Ideal.span ({f * g} : Set A)) =
      Module.length A (A ⧸ Ideal.span ({g} : Set A)) +
      Module.length A (A ⧸ Ideal.span ({f} : Set A)) := by
  set p : Submodule A A := Ideal.span ({g} : Set A) with hp
  set q : Submodule A A := Ideal.span ({f * g} : Set A) with hq
  set r : Submodule A A := Ideal.span ({f} : Set A) with hr
  have hpq : p ≤ Submodule.comap (LinearMap.toSpanSingleton A A f) q := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change (a * g) • f ∈ q
    rw [smul_eq_mul]
    exact Ideal.mem_span_singleton'.mpr ⟨a, by ring⟩
  have hqr : q ≤ r := Ideal.span_singleton_le_span_singleton.mpr ⟨g, rfl⟩
  set φ₁ : A ⧸ p →ₗ[A] A ⧸ q := p.mapQ q (LinearMap.toSpanSingleton A A f) hpq with hφ₁
  set φ₂ : A ⧸ q →ₗ[A] A ⧸ r := Submodule.factor hqr with hφ₂
  have hinj : Function.Injective φ₁ := by
    rw [← LinearMap.ker_eq_bot, hφ₁, Submodule.ker_mapQ, ← LinearMap.le_ker_iff_map,
      Submodule.ker_mkQ]
    intro x hx
    have hxf : x • f ∈ q := hx
    rw [smul_eq_mul] at hxf
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxf
    have hcancel : f * x = f * (a * g) := by rw [mul_comm f x, ← ha]; ring
    exact Ideal.mem_span_singleton'.mpr ⟨a, (hf.left hcancel).symm⟩
  have hsurj : Function.Surjective φ₂ := Submodule.factor_surjective hqr
  have hexact : Function.Exact φ₁ φ₂ := by
    rw [LinearMap.exact_iff, hφ₁, hφ₂, Submodule.range_mapQ, LinearMap.range_toSpanSingleton,
      Submodule.ker_mapQ]
    rfl
  simpa [hp, hq, hr] using Module.length_eq_add_of_exact φ₁ φ₂ hinj hsurj hexact

end


/-! ## Chart-independence of the stalk of an ideal sheaf -/

end GromovWitten.AlgebraicGeometry.Curves

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Pushing the ideal of an affine open `U` of an ideal sheaf `I` forward to the stalk at a
point `x ∈ W` agrees with pushing forward the ideal of a smaller affine open `W ≤ U` also
containing `x`: restricting the section ring from `U` to `W` and then taking the germ at `x`
is the same as taking the germ at `x` directly (`TopCat.Presheaf.germ_res_apply`), and the ideal
of `W` is the image of the ideal of `U` under that restriction (`IdealSheafData.map_ideal`). -/
theorem map_ideal_germ_eq_of_le (I : X.IdealSheafData) {U W : X.affineOpens} (h : W.1 ≤ U.1)
    (x : X) (hxW : x ∈ W.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x (h hxW)).hom =
      (I.ideal W).map (X.presheaf.germ W.1 x hxW).hom := by
  have hcomp : (X.presheaf.germ U.1 x (h hxW)).hom =
      (X.presheaf.germ W.1 x hxW).hom.comp (X.presheaf.map (homOfLE h).op).hom := by
    ext a
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) x hxW a).symm
  calc (I.ideal U).map (X.presheaf.germ U.1 x (h hxW)).hom
      = (I.ideal U).map
          ((X.presheaf.germ W.1 x hxW).hom.comp (X.presheaf.map (homOfLE h).op).hom) :=
        congrArg (Ideal.map · (I.ideal U)) hcomp
    _ = ((I.ideal U).map (X.presheaf.map (homOfLE h).op).hom).map
          (X.presheaf.germ W.1 x hxW).hom :=
        (Ideal.map_map _ _).symm
    _ = (I.ideal W).map (X.presheaf.germ W.1 x hxW).hom :=
        congrArg (Ideal.map (X.presheaf.germ W.1 x hxW).hom) (I.map_ideal h)

/-- **The stalk of an ideal sheaf at a point is independent of the affine chart used to compute
it.**  For two affine opens `U, V` both containing `x`, pushing `I.ideal U` (resp. `I.ideal V`)
forward along the germ map at `x` gives the same ideal of the stalk `𝒪_{X,x}`: refine to a common
affine open `W ≤ U ⊓ V` containing `x` (using that affine opens form a basis of the topology,
`Scheme.isBasis_affineOpens`) and apply `map_ideal_germ_eq_of_le` twice. -/
theorem map_ideal_germ_eq (I : X.IdealSheafData) {U V : X.affineOpens} (x : X)
    (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩) (U.1 ⊓ V.1).2
  set W' : X.affineOpens := ⟨W, hW⟩
  have hWU : W'.1 ≤ U.1 := hWUV.trans inf_le_left
  have hWV : W'.1 ≤ V.1 := hWUV.trans inf_le_right
  rw [I.map_ideal_germ_eq_of_le hWU x hxW, I.map_ideal_germ_eq_of_le hWV x hxW]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace GromovWitten.AlgebraicGeometry.Curves


/-! ## The multiplicity of an effective Cartier divisor at a point -/

/-- **A flat ring map sends regular elements to regular elements, at a stalk.**  The germ map
from an affine open `U` to the stalk at a point `y ∈ U` realises the stalk as a localisation of
`Γ(X, U)` (`IsAffineOpen.isLocalization_stalk`), hence is flat (`IsLocalization.flat`), hence
preserves regularity of elements (`isRegular_map_of_flat`).  Stated with `y : U.1` (rather than a
point of `X` together with a membership proof) so that the `Algebra`/`Module.Flat` instances
needed internally are found directly by unification against `y`, without having to see through
an anonymous-constructor point of `U.1`. -/
theorem isRegular_germ_of_isRegular {X : Scheme.{u}} (U : X.affineOpens) (y : U.1)
    {r : Γ(X, U.1)} (hr : IsRegular r) :
    IsRegular ((X.presheaf.germ U.1 y.1 y.2).hom r) := by
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) (U.2.primeIdealOf y).asIdeal :=
    U.2.isLocalization_stalk y
  have hflat : Module.Flat Γ(X, U.1) (X.presheaf.stalk y) :=
    IsLocalization.flat (X.presheaf.stalk y) (U.2.primeIdealOf y).asIdeal.primeCompl
  have hgermalg : (X.presheaf.germ U.1 y.1 y.2).hom =
      algebraMap Γ(X, U.1) (X.presheaf.stalk y) :=
    (TopCat.Presheaf.stalk_open_algebraMap X.presheaf y).symm
  rw [hgermalg]
  exact isRegular_map_of_flat _ (RingHom.flat_algebraMap_iff.mpr hflat) hr

namespace EffectiveCartierDivisor

variable {X : Scheme.{u}}

/-- The ideal of the stalk `𝒪_{X,x}` cut out by an effective Cartier divisor `D`: the image of
`D`'s ideal sheaf, computed on the canonical affine chart `D.localEquationOpen x`, under the germ
map at `x`.  Independent of the chart used, see `multiplicityIdeal_eq_of_mem`. -/
noncomputable def multiplicityIdeal (D : EffectiveCartierDivisor X) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  (D.idealSheaf.ideal (D.localEquationOpen x)).map
    (X.presheaf.germ (D.localEquationOpen x).1 x (D.mem_localEquationOpen x)).hom

/-- **`multiplicityIdeal` is independent of the affine chart used to compute it.** -/
theorem multiplicityIdeal_eq_of_mem (D : EffectiveCartierDivisor X) {x : X} (U : X.affineOpens)
    (hxU : x ∈ U.1) :
    D.multiplicityIdeal x = (D.idealSheaf.ideal U).map (X.presheaf.germ U.1 x hxU).hom :=
  D.idealSheaf.map_ideal_germ_eq x (D.mem_localEquationOpen x) hxU

/-- **The multiplicity of an effective Cartier divisor `D` at a point `x` of `X`**: the length,
as an `𝒪_{X,x}`-module, of the local ring `𝒪_{D,x} = 𝒪_{X,x} ⧸ multiplicityIdeal D x` of the
divisor itself.  At a point outside the support of `D` the ideal is the unit ideal (the local
equation is a unit there), so the multiplicity there is `0`
(`multiplicity_eq_zero_of_notMem_support`). -/
noncomputable def multiplicity (D : EffectiveCartierDivisor X) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ D.multiplicityIdeal x)

/-- **Additivity of the multiplicity under sums of effective Cartier divisors.**  This is the
commutative-algebra identity `length_quotient_span_singleton_mul` transported to a common affine
chart refining the (a priori unrelated) canonical charts of `D`, `E` and `D.sum E` at `x`. -/
theorem multiplicity_sum (D E : EffectiveCartierDivisor X) (x : X) :
    (D.sum E).multiplicity x = D.multiplicity x + E.multiplicity x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (D.localEquationOpen x).1 ⊓ (E.localEquationOpen x).1 from
        ⟨D.mem_localEquationOpen x, E.mem_localEquationOpen x⟩)
      ((D.localEquationOpen x).1 ⊓ (E.localEquationOpen x).1).2
  set W' : X.affineOpens := ⟨W, hW⟩
  have hWD : W'.1 ≤ (D.localEquationOpen x).1 := hWUV.trans inf_le_left
  have hWE : W'.1 ≤ (E.localEquationOpen x).1 := hWUV.trans inf_le_right
  set a : Γ(X, W) := (X.presheaf.map (homOfLE hWD).op).hom (D.localEquation x) with ha_def
  set b : Γ(X, W) := (X.presheaf.map (homOfLE hWE).op).hom (E.localEquation x) with hb_def
  have haR : IsRegular a := isRegular_map_of_flat _
    (flat_affineOpenRestriction (D.localEquationOpen x) W' hWD) (D.localEquation_isRegular x)
  have hDW : D.idealSheaf.ideal W' = Ideal.span ({a} : Set Γ(X, W)) := by
    rw [← D.idealSheaf.map_ideal hWD, D.ideal_localEquationOpen, Ideal.map_span,
      Set.image_singleton]
    congr 1
  have hEW : E.idealSheaf.ideal W' = Ideal.span ({b} : Set Γ(X, W)) := by
    rw [← E.idealSheaf.map_ideal hWE, E.ideal_localEquationOpen, Ideal.map_span,
      Set.image_singleton]
    congr 1
  have hDEW : (D.sum E).idealSheaf.ideal W' = Ideal.span ({a * b} : Set Γ(X, W)) := by
    rw [sum_idealSheaf]
    change D.idealSheaf.ideal W' * E.idealSheaf.ideal W' = Ideal.span {a * b}
    rw [hDW, hEW, Ideal.span_singleton_mul_span_singleton]
  have hD : D.multiplicityIdeal x = Ideal.span ({(X.presheaf.germ W'.1 x hxW).hom a} :
      Set (X.presheaf.stalk x)) := by
    rw [D.multiplicityIdeal_eq_of_mem W' hxW, hDW, Ideal.map_span, Set.image_singleton]
  have hE : E.multiplicityIdeal x = Ideal.span ({(X.presheaf.germ W'.1 x hxW).hom b} :
      Set (X.presheaf.stalk x)) := by
    rw [E.multiplicityIdeal_eq_of_mem W' hxW, hEW, Ideal.map_span, Set.image_singleton]
  have hDE : (D.sum E).multiplicityIdeal x = Ideal.span
      ({(X.presheaf.germ W'.1 x hxW).hom a * (X.presheaf.germ W'.1 x hxW).hom b} :
        Set (X.presheaf.stalk x)) := by
    rw [(D.sum E).multiplicityIdeal_eq_of_mem W' hxW, hDEW, Ideal.map_span, Set.image_singleton,
      map_mul]
  have hgermA : IsRegular ((X.presheaf.germ W'.1 x hxW).hom a) :=
    isRegular_germ_of_isRegular W' ⟨x, hxW⟩ haR
  change Module.length _ (_ ⧸ (D.sum E).multiplicityIdeal x) =
      Module.length _ (_ ⧸ D.multiplicityIdeal x) + Module.length _ (_ ⧸ E.multiplicityIdeal x)
  rw [hD, hE, hDE]
  exact (length_quotient_span_singleton_mul hgermA).trans (add_comm _ _)


/-- **The multiplicity of an effective Cartier divisor vanishes outside its support.**  Away
from `D.support`, the local equation used to define `D` is, by definition of the support as a
zero locus, a unit at `x`; its image generates the whole ideal of the stalk, whose quotient is
then the zero module. -/
theorem multiplicity_eq_zero_of_notMem_support (D : EffectiveCartierDivisor X) (x : X)
    (hx : x ∉ (D.support : Set X)) : D.multiplicity x = 0 := by
  have hxU : x ∈ (D.localEquationOpen x).1 := D.mem_localEquationOpen x
  have hnotzero : x ∈ X.basicOpen (D.localEquation x) := by
    by_contra hcon
    apply hx
    change x ∈ (D.idealSheaf.support : Set X)
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hxU,
      D.ideal_localEquationOpen, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    exact hcon
  have hunit : IsUnit (X.presheaf.germ (D.localEquationOpen x).1 x hxU (D.localEquation x)) :=
    (Scheme.mem_basicOpen X (D.localEquation x) x hxU).mp hnotzero
  have htop : D.multiplicityIdeal x = ⊤ := by
    unfold multiplicityIdeal
    rw [D.ideal_localEquationOpen, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_eq_top]
    exact hunit
  unfold multiplicity
  rw [htop]
  exact Module.length_eq_zero


/-! ## Assembling multiplicities into a rational-valued degree -/

/-- The hypotheses needed to assemble the multiplicities of an effective Cartier divisor `D`
into a genuine `ℚ`-valued zero-cycle: finite length at every point of the support, and local
finiteness of the support as a set of points.  On an integral scheme of dimension one both hold
automatically -- a Noetherian local domain of Krull dimension one modulo a nonzero regular element
is Artinian (hence of finite length), and a proper closed subset of an integral curve is discrete
-- but *neither fact is established in this file*: they are recorded here as explicit hypotheses
of `cycle`/`degree` rather than silently assumed or derived. -/
structure HasFiniteDegree (D : EffectiveCartierDivisor X) : Prop where
  /-- The multiplicity of `D` is finite at every point of its support. -/
  finite_multiplicity : ∀ x ∈ (D.support : Set X), D.multiplicity x ≠ ⊤
  /-- The support of `D` is a locally finite set of points. -/
  locallyFinite_support : ∀ x : X, ∃ t ∈ nhds x, (t ∩ (D.support : Set X)).Finite

/-- The multiplicity of a divisor with `HasFiniteDegree` is finite everywhere, not just on its
support (it vanishes, in particular, off the support). -/
theorem HasFiniteDegree.finite_multiplicity_all {D : EffectiveCartierDivisor X}
    (h : D.HasFiniteDegree) (x : X) : D.multiplicity x ≠ ⊤ := by
  by_cases hx : x ∈ (D.support : Set X)
  · exact h.finite_multiplicity x hx
  · rw [D.multiplicity_eq_zero_of_notMem_support x hx]
    exact ENat.zero_ne_top

/-- **`HasFiniteDegree` is additive.** -/
theorem HasFiniteDegree.sum {D E : EffectiveCartierDivisor X} (hD : D.HasFiniteDegree)
    (hE : E.HasFiniteDegree) : (D.sum E).HasFiniteDegree where
  finite_multiplicity x hx := by
    rw [multiplicity_sum, Ne, ENat.add_eq_top]
    rintro (hxtop | hxtop)
    · by_cases hxD : x ∈ (D.support : Set X)
      · exact hD.finite_multiplicity x hxD hxtop
      · rw [D.multiplicity_eq_zero_of_notMem_support x hxD] at hxtop
        exact ENat.zero_ne_top hxtop
    · by_cases hxE : x ∈ (E.support : Set X)
      · exact hE.finite_multiplicity x hxE hxtop
      · rw [E.multiplicity_eq_zero_of_notMem_support x hxE] at hxtop
        exact ENat.zero_ne_top hxtop
  locallyFinite_support x := by
    obtain ⟨t, ht, htD⟩ := hD.locallyFinite_support x
    obtain ⟨s, hs, hsE⟩ := hE.locallyFinite_support x
    refine ⟨t ∩ s, Filter.inter_mem ht hs, (htD.union hsE).subset ?_⟩
    rintro y ⟨⟨hyt, hys⟩, hyDE⟩
    rw [sum_support, Closeds.coe_sup] at hyDE
    rcases hyDE with hyD | hyE
    · exact Or.inl ⟨hyt, hyD⟩
    · exact Or.inr ⟨hys, hyE⟩

/-- The zero-cycle of an effective Cartier divisor `D` with `HasFiniteDegree`: the coefficient
of a point `x` is the (finite, by `h`) multiplicity of `D` there. -/
noncomputable def cycle (D : EffectiveCartierDivisor X) (h : D.HasFiniteDegree) :
    _root_.AlgebraicGeometry.AlgebraicCycle X ℚ where
  toFun x := ((D.multiplicity x).toNat : ℚ)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := by
    obtain ⟨t, ht, htfin⟩ := h.locallyFinite_support x
    refine ⟨t, ht, htfin.subset ?_⟩
    rintro y ⟨hyt, hymem⟩
    refine ⟨hyt, ?_⟩
    by_contra hyD
    exact hymem (by simp [D.multiplicity_eq_zero_of_notMem_support y hyD])

@[simp] theorem cycle_apply (D : EffectiveCartierDivisor X) (h : D.HasFiniteDegree) (x : X) :
    D.cycle h x = ((D.multiplicity x).toNat : ℚ) := rfl

/-- **Additivity of the zero-cycle under sums of effective Cartier divisors.** -/
theorem cycle_add {D E : EffectiveCartierDivisor X} (hD : D.HasFiniteDegree)
    (hE : E.HasFiniteDegree) :
    (D.sum E).cycle (hD.sum hE) = D.cycle hD + E.cycle hE := by
  ext x
  have hstep : ((D.sum E).multiplicity x).toNat =
      (D.multiplicity x).toNat + (E.multiplicity x).toNat := by
    rw [multiplicity_sum]
    exact ENat.toNat_add (hD.finite_multiplicity_all x) (hE.finite_multiplicity_all x)
  simp [cycle_apply, hstep]

variable {k : Type u} [Field k]

/-- **The degree of an effective Cartier divisor** on a scheme `X` with a structure morphism
`f` to `Spec k` and `[CompactSpace X]` (the hypotheses under which `ZeroCycleDegree.degreeCycle`
is defined), given `HasFiniteDegree`: the degree of the associated zero-cycle. -/
noncomputable def degree (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (D : EffectiveCartierDivisor X) (h : D.HasFiniteDegree) : ℚ :=
  IntersectionTheory.ZeroCycleDegree.degreeCycle f (D.cycle h)

/-- **Additivity of the degree under sums of effective Cartier divisors.** -/
theorem degree_add (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (D E : EffectiveCartierDivisor X) (hD : D.HasFiniteDegree) (hE : E.HasFiniteDegree) :
    (D.sum E).degree f (hD.sum hE) = D.degree f hD + E.degree f hE := by
  unfold degree
  rw [cycle_add]
  exact map_add (IntersectionTheory.ZeroCycleDegree.degreeCycle f) _ _


/-- The degree of an effective Cartier divisor does not depend on which proof of
`HasFiniteDegree` is supplied (it is a `Prop`, so any two proofs are equal), and is invariant
under replacing `D` by an equal divisor. -/
theorem degree_eq_of_eq {D D' : EffectiveCartierDivisor X} (heq : D = D')
    (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (h : D.HasFiniteDegree) (h' : D'.HasFiniteDegree) :
    D.degree f h = D'.degree f h' := by
  subst heq; rfl

/-- **The degree of a difference of effective Cartier divisors is well defined on the class of
the difference** (the formal analogue, for `EffectiveCartierDivisor`, of well-definedness of the
degree on linear-equivalence classes of a Cartier divisor `D₁ - D₂`): if `D₁ + D₂' = D₁' + D₂`
as effective divisors (so that `D₁ - D₂` and `D₁' - D₂'` are the same formal difference), then
`deg D₁ - deg D₂ = deg D₁' - deg D₂'`.  This is a formal consequence of `degree_add`; it does not
by itself show that two divisors linearly equivalent via a rational function have the same
degree, since the repository does not yet relate rational functions on `X` to sums of effective
Cartier divisors (that bridge is `degree_principal_eq_zero`-shaped compatibility, not established
in this file). -/
theorem degree_sub_eq_of_sum_eq (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    {D₁ D₂ D₁' D₂' : EffectiveCartierDivisor X} (h₁ : D₁.HasFiniteDegree)
    (h₂ : D₂.HasFiniteDegree) (h₁' : D₁'.HasFiniteDegree) (h₂' : D₂'.HasFiniteDegree)
    (heq : D₁.sum D₂' = D₁'.sum D₂) :
    D₁.degree f h₁ - D₂.degree f h₂ = D₁'.degree f h₁' - D₂'.degree f h₂' := by
  have e1 := degree_add f D₁ D₂' h₁ h₂'
  have e2 := degree_add f D₁' D₂ h₁' h₂
  have e3 := degree_eq_of_eq heq f (h₁.sum h₂') (h₁'.sum h₂)
  rw [e1] at e3
  rw [e2] at e3
  linarith

/-- **The degree of an effective Cartier divisor is nonnegative.**  Every coefficient of its
zero-cycle is a cast natural number, and the residue degrees entering `degreeCycle` are natural
numbers too, so the defining `finsum` is a sum of nonnegative terms. -/
theorem degree_nonneg (f : X ⟶ Spec (CommRingCat.of k)) [CompactSpace X]
    (D : EffectiveCartierDivisor X) (h : D.HasFiniteDegree) : 0 ≤ D.degree f h := by
  unfold degree
  rw [IntersectionTheory.ZeroCycleDegree.degreeCycle_apply]
  refine finsum_nonneg fun x => ?_
  rw [cycle_apply]
  positivity

end EffectiveCartierDivisor

/-! ## Bridge to issue #141: a geometric-degree hypothesis for relative line bundles -/

namespace RelativeLineBundle

variable {S : Scheme.{u}} {f : X ⟶ S}

/-- **Bridge to issue #141** (stated with the objects available in the repository, see the
module docstring for what is deliberately weaker than the intended statement): `L` records a
geometric degree if, for every geometric fibre `y : Spec K ⟶ S` and every irreducible component
`C` of that fibre (a compact scheme, e.g. because `f` is proper), `L.componentDegree K y C`
equals the degree of some effective Cartier divisor `D` on the fibre, supported inside `C`,
whose associated line bundle `D.associatedLineBundle` is (abstractly) isomorphic to the
restriction of `L.line` to the fibre.

This is honestly weaker than the geometrically intended statement, which would restrict `L.line`
to the irreducible component `C` itself (as a reduced closed subscheme) rather than merely
confining `D`'s support to `C` on the whole fibre: the repository does not construct the reduced
induced closed-subscheme structure on an irreducible component, nor a restriction operation for
`LineBundle` along a closed immersion, at the time of writing. -/
def IsGeometricDegree (L : RelativeLineBundle f) : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u}))
    (_hcomp : CompactSpace (CategoryTheory.Limits.pullback f y : Scheme.{u})),
    ∃ (D : EffectiveCartierDivisor (CategoryTheory.Limits.pullback f y : Scheme.{u}))
      (h : D.HasFiniteDegree),
      (D.support : Set (CategoryTheory.Limits.pullback f y : Scheme.{u})) ⊆
        (C : Set (CategoryTheory.Limits.pullback f y : Scheme.{u})) ∧
      D.degree (CategoryTheory.Limits.pullback.snd f y) h = (L.degree y C : ℚ) ∧
      Nonempty (LineBundle.Iso
        (L.line.pullback (CategoryTheory.Limits.pullback.fst f y)) D.associatedLineBundle)

/-- **Under `IsGeometricDegree`, the component-degree labels cannot be arbitrary**: they are
forced to be nonnegative, since they equal the degree of an *effective* Cartier divisor
(`EffectiveCartierDivisor.degree_nonneg`).  A finer statement -- that the labels vanish exactly
when `L.line` is trivial -- is not proved here: it would need that a nonzero effective divisor
cannot have trivial associated line bundle on a proper integral curve, which in turn needs that
the global sections of the structure sheaf of such a curve are exactly the base field (a
properness fact not established in this repository) together with a comparison between
`associatedLineBundle`'s global sections and the divisor's support that this file does not
build. -/
theorem componentDegree_nonneg_of_isGeometricDegree {L : RelativeLineBundle f}
    (hL : L.IsGeometricDegree) {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (C : irreducibleComponents (CategoryTheory.Limits.pullback f y : Scheme.{u}))
    (hcomp : CompactSpace (CategoryTheory.Limits.pullback f y : Scheme.{u})) :
    0 ≤ L.degree y C := by
  obtain ⟨D, h, _, hdeg, _⟩ := hL K y C hcomp
  have hq : (0 : ℚ) ≤ D.degree (CategoryTheory.Limits.pullback.snd f y) h :=
    D.degree_nonneg _ h
  rw [hdeg] at hq
  exact_mod_cast hq

end RelativeLineBundle

end GromovWitten.AlgebraicGeometry.Curves
