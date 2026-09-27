/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors
import GromovWitten.AlgebraicGeometry.Curves.ProperCurveTopology
import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegreeUnconditional
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree
import Mathlib.AlgebraicGeometry.OrderOfVanishing
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
* `ord_germToFunctionField_eq_ord` — the order of vanishing `Scheme.ord` (Mathlib, function-field
  valued) of the rational function represented by a regular section agrees, at a point of
  coheight one where the length is finite, with the length-theoretic `Ring.ord` of that section's
  germ (Mathlib, `Module.length`-based).
* `EffectiveCartierDivisor.ofAffineOpen` — glue an effective Cartier divisor given on a single
  affine open `U` of `X` to a genuine effective Cartier divisor on all of `X` (trivial outside
  `U`), given that the image of its support is closed; `ofAffineOpen_multiplicity_eq` and
  `ofAffineOpen_mem_support_iff` identify its multiplicity and support with the length-theoretic
  data of the local generator on `U`. This is the tool used below to build the divisors of zeros
  and poles `D₀`, `D∞` of a rational function `r` on a curve (taking `U` to be the domain of
  regularity of `r`, resp. `r⁻¹`).

* `EffectiveCartierDivisor.ofChartSection` — the divisor cut out on all of `X` by a nonzero section
  over an affine open `V` of a one-dimensional integral scheme.  Here *every* hypothesis of
  `ofAffineOpen` is discharged: `isClosed_image_of_ne_univ`/`isClosed_range_comp_ι` show that a
  closed subset of an open subscheme which is not the whole of it has closed image (its closure is
  a proper closed subset, hence finite by `finite_of_isClosed_of_ne_univ`), and
  `support_ofGlobalEquation_ne_univ` shows the zero locus of a nonzero section is such a subset.
  `multiplicity_ofChartSection`, `mem_support_ofChartSection_iff`, `support_ofChartSection_le`,
  `finite_support_ofChartSection`, `hasFiniteDegree_ofChartSection` and
  `multiplicity_ofChartSection_eq_ord` describe it; the last identifies its multiplicity with
  `AlgebraicGeometry.Scheme.ord`.
* `hasFiniteDegree_of_support_ne_univ` — on a regular one-dimensional integral Noetherian scheme,
  *every* effective Cartier divisor whose support is not the whole space satisfies
  `HasFiniteDegree`, so its degree is defined
  (`hasFiniteDegree_of_support_ne_univ_of_curve` for a `RegularProperCurve`).
* `divisorOfZeros`, `divisorOfPoles` — the divisors of zeros and of poles of a nonzero rational
  function `r` on a regular proper curve, with `hasFiniteDegree_divisorOfZeros`/`_divisorOfPoles`.
  `mem_support_divisorOfZeros_iff` confirms that `divisorOfZeros` really is the divisor of zeros:
  its support is the set of points of the domain of definition of `r` where `r` vanishes.  A
  by-product is `ord_nonneg_of_mem_regularLocus`: the order of vanishing of a rational function is
  nonnegative on its domain of definition.
* `multiplicity_divisorOfZeros_sub_divisorOfPoles` — the pointwise identity
  `div₀(r) - div∞(r) = ord r`, and `cycle_divisorOfZeros_sub_cycle_divisorOfPoles`, its zero-cycle
  form: the difference of the two zero-cycles is `AlgebraicGeometry.Scheme.principalCycle r`.
* `degree_eq_of_multiplicity_sub_eq_ord` — the abstract form of the invariance: any two effective
  Cartier divisors on a regular proper curve whose multiplicities differ by the order of vanishing
  of a rational function have the same degree (no affineness hypothesis at all).
* `degree_divisorOfZeros_eq_degree_divisorOfPoles` — **the divisors of zeros and of poles of a
  rational function have the same degree**, and
  `degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles` — the degree of a formal difference
  `E₁ - E₂` of effective Cartier divisors is unchanged by adding the principal divisor of a
  rational function.  This is issue #141's invariance of the degree under linear equivalence.

## What is not proved here

`multiplicity`/`multiplicity_sum` need no hypothesis on `X` at all (they hold for an effective
Cartier divisor on *any* scheme). Turning them into a `ℚ`-valued `degree` needs `HasFiniteDegree`,
which for a *general* effective Cartier divisor is still an explicit hypothesis of
`degree`/`degree_add` rather than derived: it is derived here only for the divisors actually
constructed in this file, by `hasFiniteDegree_ofChartSection` (finiteness of the lengths from
`ord_ne_top_of_regular`, finiteness of the support from `finite_support_ofChartSection`), which
needs `X` regular and one-dimensional.  For an arbitrary effective Cartier divisor on an arbitrary
integral one-dimensional `X` the two facts are not established.

The invariance of `degree` under adding a principal divisor *is* established here
(`degree_divisorOfZeros_eq_degree_divisorOfPoles`,
`degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles`), but the construction of the divisors of
zeros and poles carries one hypothesis which is not discharged in this file: that the two domains
of definition `Scheme.regularLocus r` and `Scheme.regularLocus r⁻¹` are *affine* opens (`hU₀`,
`hU₁`).  This is exactly the hypothesis under which the repository's curve machinery is organised;
it is supplied by
`IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus` and `..._inv`
as soon as `r` is transcendental over `k`, which gives the unconditional-looking
`degree_divisorOfZeros_eq_degree_divisorOfPoles_of_transcendental`.  For `r` algebraic over `k`
this route does not apply: `IntersectionTheory/ProperCurveDegreeFinal.lean`'s
`mem_regularLocus_inf_of_monic` shows that both domains of definition are then the whole curve,
which is not an affine open of a positive-dimensional proper curve; in that case `ord r` vanishes
identically and both divisors ought to be empty, but this file does not treat that case.  Note that
the *abstract* invariance statement `degree_eq_of_multiplicity_sub_eq_ord` -- any two effective
Cartier divisors whose multiplicities differ by `ord r` have the same degree -- carries no
affineness hypothesis at all; the affineness is needed only to *construct* such a pair of divisors
from `r`.
Finally, for `IsGeometricDegree`, the sharper
fact that the `componentDegree` labels vanish exactly when the line bundle is trivial (see the gap
recorded in that declaration's docstring) is also not established.
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
is Artinian (hence of finite length), and a proper closed subset of an integral curve is discrete.
For an arbitrary effective Cartier divisor neither fact is derived here, so both are recorded as
explicit hypotheses of `cycle`/`degree`; for the divisors of sections constructed below they *are*
derived, see `hasFiniteDegree_ofChartSection`. -/
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
degree; the bridge to rational functions is
`degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles` below, proved for a regular proper
curve. -/
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

/-- **`multiplicity` agrees with Mathlib's `Ring.ord`.**  `Ring.ord R y = Module.length R
(R ⧸ span {y})` (`Mathlib.RingTheory.OrderOfVanishing.Basic`) is *definitionally* the same
formula as `multiplicity`, computed on the canonical chart `D.localEquationOpen x`: this lemma
records the identification explicitly so that `Ring.ord`'s API (`ord_mul`, `ord_of_isUnit`,
`isFiniteLength_quotient_span_singleton`, and the scheme-level `Scheme.ord`/`ordFrac`) becomes
directly available for `multiplicity`. -/
theorem multiplicity_eq_ord (D : EffectiveCartierDivisor X) (x : X) :
    D.multiplicity x = Ring.ord (X.presheaf.stalk x)
      ((X.presheaf.germ (D.localEquationOpen x).1 x (D.mem_localEquationOpen x)).hom
        (D.localEquation x)) := by
  unfold multiplicity multiplicityIdeal Ring.ord
  rw [D.ideal_localEquationOpen, Ideal.map_span, Set.image_singleton]

end EffectiveCartierDivisor

/-- **The order of vanishing of the rational function represented by a regular section agrees
with the length-based `Ring.ord` of that section's germ**, at a point of coheight one where the
germ has finite `Ring.ord` (e.g. because the stalk is Noetherian of Krull dimension `≤ 1`, by
`isFiniteLength_quotient_span_singleton`).  This is the bridge needed to compare
`EffectiveCartierDivisor.multiplicity` (via `multiplicity_eq_ord`) with `Scheme.ord`/
`Scheme.principalCycle`, the Weil-divisor invariants used by
`IntersectionTheory.ProperCurveDegree*.lean` and `degreeCycle_principalCycle_eq_zero'`. -/
theorem ord_germToFunctionField_eq_ord {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (hcx : Order.coheight x = 1)
    (a : Γ(X, U)) (ha : a ≠ 0)
    (hfin : Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a) ≠ ⊤) :
    Scheme.ord (X.germToFunctionField U a) x =
      (Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a)).toNat := by
  set n := (Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a)).toNat with hn
  have hcast : Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a) = (n : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hgerm_ne : (X.presheaf.germ U x hx).hom a ≠ 0 :=
    map_ne_zero_iff _ (germ_injective_of_isIntegral (X := X) x hx) |>.mpr ha
  have hnzd : (X.presheaf.germ U x hx).hom a ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hgerm_ne
  have hfne : X.germToFunctionField U a ≠ 0 :=
    map_ne_zero_iff _ (Scheme.germToFunctionField_injective (X := X) U) |>.mpr ha
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hcx.le
  apply (Scheme.ord_eq_iff hcx (f := X.germToFunctionField U a) hfne).mpr
  calc (Scheme.ordHom x hcx) (X.germToFunctionField U a)
      = (Scheme.ordHom x hcx) (algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ U x hx).hom a)) := by
        rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx a]
    _ = Ring.ordFrac (X.presheaf.stalk x) (algebraMap (X.presheaf.stalk x) X.functionField
          ((X.presheaf.germ U x hx).hom a)) := rfl
    _ = Ring.ordMonoidWithZeroHom (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a) :=
        Ring.ordFrac_eq_ord (R := X.presheaf.stalk x) (K := X.functionField) hgerm_ne
    _ = ENat.recTopCoe 0 (fun m => (WithZero.coe (Multiplicative.ofAdd (m : ℤ))))
          (Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a)) :=
        Ring.ordMonoidWithZeroHom_eq_ord (R := X.presheaf.stalk x) hnzd
    _ = ↑(Multiplicative.ofAdd (n : ℤ)) := by rw [hcast, ENat.recTopCoe_natCast]


/-! ## Toward linear equivalence: gluing a divisor from an affine chart

The declarations below assemble the *general* tool identified while attempting the coordinator's
request (invariance of `degree` under adding a principal divisor, issue #141): given an effective
Cartier divisor `D'` on an affine open `U` of a scheme `X`, together with a proof that the image
of `D'`'s support in `X` is closed, `EffectiveCartierDivisor.ofAffineOpen` glues `D'` to a genuine
effective Cartier divisor on all of `X`, trivial outside `U`; its multiplicity and support agree
with `D'`'s own on `U` (`ofAffineOpen_multiplicity_eq`, `ofAffineOpen_mem_support_iff`), and its
multiplicity is the length-theoretic `Ring.ord` of the generating section
(`ord_ne_top_of_regular`, `ord_eq_zero_iff_isUnit` supply the auxiliary facts about `Ring.ord`
needed to relate it to `Scheme.ord`, via `ord_germToFunctionField_eq_ord` above).

The hypothesis `hclosed` of `ofAffineOpen` is discharged, on a one-dimensional scheme, in the
section "Discharging the closedness hypothesis" below (`isClosed_range_comp_ι`), so that no
closedness hypothesis survives in `EffectiveCartierDivisor.ofChartSection` or in the divisors of
zeros and poles of a rational function built from it. -/

variable {X : Scheme.{u}}

/-- The ideal sheaf of `D'` (on the affine open `U`) is recovered by pulling the extended
kernel ideal sheaf (of the composite `D'.ι ≫ U.ι`, once it is known to be a closed immersion)
back along `U.ι`. -/
theorem ofAffineOpen_comap {U : X.Opens} (D' : EffectiveCartierDivisor U.toScheme)
    (hclosed : IsClosed (Set.range (D'.ι ≫ U.ι))) :
    (D'.ι ≫ U.ι).ker.comap U.ι = D'.idealSheaf := by
  have hci : IsClosedImmersion (D'.ι ≫ U.ι) := IsClosedImmersion.of_isPreimmersion _ hclosed
  have hker : D'.ι.ker = D'.idealSheaf := Scheme.IdealSheafData.ker_subschemeι (I := D'.idealSheaf)
  rw [← hker]
  exact (ker_factorThrough_open (D'.ι ≫ U.ι) U D'.ι rfl).symm

/-- **The kernel ideal sheaf of `D'.ι ≫ U.ι` is effective Cartier**, given that its range is
closed (so that the composite is itself a closed immersion, `IsClosedImmersion.of_isPreimmersion`):
on `U` it agrees with `D'`'s own (effective Cartier) ideal sheaf via `ofAffineOpen_comap`, and
away from the (closed) range it is the unit ideal
(`ker_comap_complementOfClosedImmersion_eq_top`), which is trivially effective Cartier. -/
theorem isEffectiveCartierIdealSheaf_ker_of_isAffineOpen
    {U : X.Opens} (D' : EffectiveCartierDivisor U.toScheme)
    (hclosed : IsClosed (Set.range (D'.ι ≫ U.ι))) :
    IsEffectiveCartierIdealSheaf (D'.ι ≫ U.ι).ker := by
  have hci : IsClosedImmersion (D'.ι ≫ U.ι) := IsClosedImmersion.of_isPreimmersion _ hclosed
  refine isEffectiveCartierIdealSheaf_of_openCover (D'.ι ≫ U.ι).ker
    (fun b : Bool => bif b then U else complementOfClosedImmersion (D'.ι ≫ U.ι)) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hx : x ∈ (U : Set X)
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ (Set.range (D'.ι ≫ U.ι))ᶜ
      intro hxr
      apply hx
      obtain ⟨z, rfl⟩ := hxr
      exact (D'.ι z).2
  · rintro (_ | _)
    · change IsEffectiveCartierIdealSheaf ((D'.ι ≫ U.ι).ker.comap
        (complementOfClosedImmersion (D'.ι ≫ U.ι)).ι)
      rw [ker_comap_complementOfClosedImmersion_eq_top]
      exact top_isEffectiveCartierIdealSheaf
    · change IsEffectiveCartierIdealSheaf ((D'.ι ≫ U.ι).ker.comap U.ι)
      rw [ofAffineOpen_comap D' hclosed]
      exact D'.isEffectiveCartier

/-- **Glue an effective Cartier divisor on an affine open `U` of `X` to a genuine effective
Cartier divisor on all of `X`, trivial (i.e. with empty support) outside `U`.**  This is exactly
the missing tool identified while investigating issue #141's request for divisors of zeros/poles
of a rational function `r`: taking `U` to be the domain of regularity of `r` (or of `r⁻¹`) and
`D'` the divisor cut out there by the regular section representing `r` gives the two divisors
`D₀`, `D∞` that the issue asks for, *given* `hclosed` -- see the module docstring for the
remaining gap (closedness/finiteness of the zero locus) that this file does not discharge. -/
noncomputable def EffectiveCartierDivisor.ofAffineOpen {U : X.Opens}
    (D' : EffectiveCartierDivisor U.toScheme)
    (hclosed : IsClosed (Set.range (D'.ι ≫ U.ι))) : EffectiveCartierDivisor X where
  idealSheaf := (D'.ι ≫ U.ι).ker
  isEffectiveCartier := isEffectiveCartierIdealSheaf_ker_of_isAffineOpen D' hclosed

variable {U : X.Opens} [IsAffine U.toScheme]

/-- The ideal of the glued divisor on the (affine) image of `U`, expressed via `D'`'s own
ideal on `U.toScheme`'s whole space, transported along the (iso) restriction map. -/
theorem ofAffineOpen_ideal_image_top (D' : EffectiveCartierDivisor U.toScheme)
    (hclosed : IsClosed (Set.range (D'.ι ≫ U.ι))) :
    ((D'.ι ≫ U.ι).ker).ideal
      (⟨U.ι ''ᵁ (⊤ : U.toScheme.Opens),
        (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ : X.affineOpens) =
      (D'.idealSheaf.ideal (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)).map
        (U.ι.appIso (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)).inv.hom := by
  have h1 := ofAffineOpen_comap D' hclosed
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
    ((D'.ι ≫ U.ι).ker) U.ι (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)
  rw [h1] at h2
  have hsurj : Function.Surjective
      (U.ι.appIso (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso
      (U.ι.appIso (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)).inv).2
  have h3 := congrArg (Ideal.map
    (U.ι.appIso (⟨⊤, isAffineOpen_top U.toScheme⟩ : U.toScheme.affineOpens)).inv.hom) h2
  rw [Ideal.map_comap_of_surjective _ hsurj] at h3
  simpa using h3.symm

/-- The ideal of the divisor `EffectiveCartierDivisor.ofAffineOpen (ofGlobalEquation ... )`
on the (affine) image of `U` is the span of the (restricted) generating section itself. -/
theorem ofAffineOpen_ideal_image_top_span (a : Γ(X, U)) (ha : IsRegular (U.topIso.inv a))
    (hclosed : IsClosed (Set.range
      ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫ U.ι))) :
    ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫ U.ι).ker.ideal
      (⟨U.ι ''ᵁ (⊤ : U.toScheme.Opens),
        (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ : X.affineOpens) =
      Ideal.span ({X.presheaf.map (eqToHom U.ι_image_top).op a} : Set Γ(X, U.ι ''ᵁ ⊤)) := by
  rw [ofAffineOpen_ideal_image_top _ hclosed,
    EffectiveCartierDivisor.ofGlobalEquation_ideal_top, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- **The multiplicity, at a point of `U`, of the divisor glued from a global equation on `U`
agrees with the length-based `Ring.ord` of that equation's germ there.**  Combined with
`ord_germToFunctionField_eq_ord`, this identifies the multiplicity with the (nonnegative) order of
vanishing, at points of `U`, of the rational function represented by `a`. -/
theorem ofAffineOpen_multiplicity_eq (a : Γ(X, U)) (ha : IsRegular (U.topIso.inv a))
    (hclosed : IsClosed (Set.range
      ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫ U.ι)))
    (x : X) (hx : x ∈ U) :
    (EffectiveCartierDivisor.ofAffineOpen
        (EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha)
        hclosed).multiplicity x =
      Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom a) := by
  have hxbig : x ∈ (U.ι ''ᵁ (⊤ : U.toScheme.Opens) : X.Opens) := by
    rw [Scheme.Opens.ι_image_top]; exact hx
  have hcomp : (X.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x hxbig).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op a) = (X.presheaf.germ U x hx).hom a :=
    TopCat.Presheaf.germ_res_apply X.presheaf (eqToHom U.ι_image_top) x hxbig a
  have hspan := ofAffineOpen_ideal_image_top_span (U := U) a ha hclosed
  have hmid := EffectiveCartierDivisor.multiplicityIdeal_eq_of_mem
    (EffectiveCartierDivisor.ofAffineOpen
      (EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha) hclosed)
    (⟨U.ι ''ᵁ (⊤ : U.toScheme.Opens),
      (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ : X.affineOpens) hxbig
  rw [← hcomp]
  unfold EffectiveCartierDivisor.multiplicity
  have hidealSheaf : (EffectiveCartierDivisor.ofAffineOpen
      (EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha)
      hclosed).idealSheaf =
      ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫ U.ι).ker := rfl
  rw [hmid, hidealSheaf, hspan, Ideal.map_span, Set.image_singleton]
  rfl

/-- **On a regular scheme, `Ring.ord` is finite at a regular element's germ at a codimension-one
point.**  The stalk there is a discrete valuation ring (`isDiscreteValuationRing_stalk`), hence of
Krull dimension `≤ 1`, and (being a stalk of a locally Noetherian scheme) Noetherian; the two
together give `Ring.ord_ne_top`. This is exactly the finiteness hypothesis needed for
`ord_germToFunctionField_eq_ord` to identify `Ring.ord` with `Scheme.ord` (rather than the latter's
junk value) on such a scheme. -/
theorem ord_ne_top_of_regular {X : AlgebraicGeometry.Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (hreg : SchemeIsRegular X) {x : X} (hx : Order.coheight x = 1)
    {b : X.presheaf.stalk x} (hb : b ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    Ring.ord (X.presheaf.stalk x) b ≠ ⊤ := by
  have hdvr := isDiscreteValuationRing_stalk hreg x hx
  exact Ring.ord_ne_top hb

/-- **`Ring.ord` vanishes exactly at units**: `Module.length R (R ⧸ (b)) = 0` iff the quotient
is trivial iff `(b) = ⊤` iff `b` is a unit. No regularity or finiteness hypothesis is needed. -/
theorem ord_eq_zero_iff_isUnit {R : Type*} [CommRing R] (b : R) :
    Ring.ord R b = 0 ↔ IsUnit b := by
  rw [Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

/-- **A point of `U` lies in the support of the glued divisor iff the generating section is
not a unit there** -- the same zero-locus computation as
`EffectiveCartierDivisor.multiplicity_eq_zero_of_notMem_support`, but for the chart `U` (rather
than the divisor's own canonical chart) and stated as a genuine `Iff`. -/
theorem ofAffineOpen_mem_support_iff (a : Γ(X, U)) (ha : IsRegular (U.topIso.inv a))
    (hclosed : IsClosed (Set.range
      ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫ U.ι)))
    (x : X) (hx : x ∈ U) :
    x ∈ (EffectiveCartierDivisor.ofAffineOpen
        (EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha) hclosed).support ↔
      ¬ IsUnit ((X.presheaf.germ U x hx).hom a) := by
  have hxbig : x ∈ (U.ι ''ᵁ (⊤ : U.toScheme.Opens) : X.Opens) := by
    rw [Scheme.Opens.ι_image_top]; exact hx
  have hspan := ofAffineOpen_ideal_image_top_span (U := U) a ha hclosed
  have hcomp : (X.presheaf.germ (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) x hxbig).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op a) = (X.presheaf.germ U x hx).hom a :=
    TopCat.Presheaf.germ_res_apply X.presheaf (eqToHom U.ι_image_top) x hxbig a
  change x ∈ ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).ι ≫
      U.ι).ker.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem
      (U := (⟨U.ι ''ᵁ (⊤ : U.toScheme.Opens),
        (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩ : X.affineOpens)) hxbig,
    hspan, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff,
    SetLike.mem_coe, Scheme.mem_basicOpen, hcomp]
  exact hxbig

/-- **A point of an affine scheme `X` lies in the support of the divisor of a global equation
`r` iff `r` is not a unit there.**  The analogue of `ofAffineOpen_mem_support_iff` before any
gluing (`X` itself affine, no chart/closedness bookkeeping needed). -/
theorem ofGlobalEquation_mem_support_iff {X : AlgebraicGeometry.Scheme.{u}} [IsAffine X]
    (r : Γ(X, ⊤)) (hr : IsRegular r) (z : X) :
    z ∈ (EffectiveCartierDivisor.ofGlobalEquation X r hr).support ↔
      ¬ IsUnit (X.presheaf.germ ⊤ z (Set.mem_univ z) r) := by
  change z ∈ (EffectiveCartierDivisor.ofGlobalEquation X r hr).idealSheaf.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem
      (U := (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens)) (Set.mem_univ z),
    EffectiveCartierDivisor.ofGlobalEquation_ideal_top, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen]
/-! ## Discharging the closedness hypothesis on a one-dimensional scheme

On a scheme whose non-generic points are all closed -- i.e. on a one-dimensional scheme, see
`Curves/ProperCurveTopology.lean` -- the hypothesis `hclosed` of
`EffectiveCartierDivisor.ofAffineOpen` is *automatic* for any divisor on an open subscheme whose
support is not the whole of that open subscheme.  The lemmas of this section prove this, and then
apply it to the divisor cut out by a nonzero section on an affine open. -/

/-- **A closed subset of an open subscheme of a one-dimensional scheme, other than the whole
open subscheme, has closed image in the ambient scheme.**  The closure of the image meets the
open subscheme exactly in the given closed set (`Topology.IsInducing.closure_eq_preimage_
closure_image`), so it is a *proper* closed subset of `X`, hence finite by
`finite_of_isClosed_of_ne_univ`; the image is then a finite union of closed points. -/
theorem isClosed_image_of_ne_univ [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) (Z : Set V.toScheme) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    IsClosed (V.ι.base '' Z) := by
  have hind : Topology.IsInducing V.ι.base := V.ι.isOpenEmbedding.isInducing
  have hpre : V.ι.base ⁻¹' closure (V.ι.base '' Z) = Z := by
    rw [← hind.closure_eq_preimage_closure_image, hZ.closure_eq]
  have hne : closure (V.ι.base '' Z) ≠ Set.univ := by
    intro h
    rw [h, Set.preimage_univ] at hpre
    exact hZne hpre.symm
  have hfin : (closure (V.ι.base '' Z)).Finite :=
    finite_of_isClosed_of_ne_univ hpt _ isClosed_closure hne
  have hfin' : (V.ι.base '' Z).Finite := hfin.subset subset_closure
  have hbig : (V.ι.base '' Z) = ⋃ x ∈ (V.ι.base '' Z), ({x} : Set X) :=
    (Set.biUnion_of_singleton (V.ι.base '' Z)).symm
  rw [hbig]
  refine hfin'.isClosed_biUnion fun x hx => hpt x ?_
  rintro rfl
  apply hne
  have h1 : closure ({genericPoint X} : Set X) ⊆ closure (V.ι.base '' Z) :=
    closure_mono (Set.singleton_subset_iff.mpr hx)
  rw [genericPoint_spec X] at h1
  exact Set.univ_subset_iff.mp h1

/-- **The closedness hypothesis of `EffectiveCartierDivisor.ofAffineOpen` holds automatically on a
one-dimensional scheme**, for any divisor on an open subscheme whose support is not the whole of
that open subscheme. -/
theorem isClosed_range_comp_ι [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) (D' : EffectiveCartierDivisor V.toScheme)
    (hne : (D'.support : Set V.toScheme) ≠ Set.univ) :
    IsClosed (Set.range (D'.ι ≫ V.ι)) := by
  have h1 : Set.range (D'.ι ≫ V.ι) = V.ι.base '' (D'.support : Set V.toScheme) := by
    rw [← D'.range_ι, ← Set.range_comp]
    rfl
  rw [h1]
  exact isClosed_image_of_ne_univ hpt V _ D'.support.isClosed hne

/-- **The support of the glued divisor is contained in the chart it came from.**  The ideal sheaf
of `ofAffineOpen` is the kernel of the (closed immersion) composite `D'.ι ≫ V.ι`, whose support is
the closure of its range (`Scheme.Hom.support_ker`), i.e. the range itself. -/
theorem support_ofAffineOpen_le {V : X.Opens} (D' : EffectiveCartierDivisor V.toScheme)
    (hclosed : IsClosed (Set.range (D'.ι ≫ V.ι))) :
    ((D'.ofAffineOpen hclosed).support : Set X) ⊆ (V : Set X) := by
  have _ : IsClosedImmersion (D'.ι ≫ V.ι) := IsClosedImmersion.of_isPreimmersion _ hclosed
  change (((D'.ι ≫ V.ι).ker.support : Closeds X) : Set X) ⊆ _
  rw [Scheme.Hom.support_ker, hclosed.closure_eq]
  rintro x ⟨z, rfl⟩
  exact (D'.ι z).2

/-- Transporting a section of `X` over an open `V` into the global sections of the open subscheme
`V.toScheme` (`Scheme.Opens.topIso`) does not change whether it vanishes. -/
theorem topIso_inv_eq_zero_iff (V : X.Opens) (a : Γ(X, V)) : V.topIso.inv a = 0 ↔ a = 0 := by
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso V.topIso.inv).1]

/-- **A nonzero section over a nonempty open of an integral scheme is a regular element** of the
global sections of the corresponding open subscheme (which is an integral domain). -/
theorem isRegular_topIso_inv [IsIntegral X] (V : X.Opens) [Nonempty V] (a : Γ(X, V))
    (ha : a ≠ 0) : IsRegular (V.topIso.inv a) := by
  obtain ⟨z⟩ := ‹Nonempty V›
  have _ : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨z, trivial⟩⟩
  have _ : IsDomain Γ(V.toScheme, ⊤) := _root_.AlgebraicGeometry.IsIntegral.component_integral _
  exact IsRegular.of_ne_zero (fun h => ha ((topIso_inv_eq_zero_iff V a).mp h))

/-- **The support of the divisor of a nonzero section on an affine open of a reduced scheme is not
the whole open**: the section is a unit somewhere on it, namely on the (nonempty, because the
scheme is reduced and the section nonzero) basic open subset it defines. -/
theorem support_ofGlobalEquation_ne_univ [IsReduced X] (a : Γ(X, U))
    (ha : IsRegular (U.topIso.inv a)) (ha0 : a ≠ 0) :
    ((EffectiveCartierDivisor.ofGlobalEquation U.toScheme (U.topIso.inv a) ha).support :
      Set U.toScheme) ≠ Set.univ := by
  have hbo : X.basicOpen a ≠ ⊥ := fun h => ha0 ((basicOpen_eq_bot_iff a).mp h)
  obtain ⟨x, hx⟩ : ((X.basicOpen a : X.Opens) : Set X).Nonempty := by
    by_contra hc
    exact hbo ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hc)
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv (U := U) a] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  intro hsupp
  have hzmem : z ∈ (EffectiveCartierDivisor.ofGlobalEquation U.toScheme
      (U.topIso.inv a) ha).support := by
    rw [← SetLike.mem_coe, hsupp]; trivial
  exact (ofGlobalEquation_mem_support_iff (U.topIso.inv a) ha z).mp hzmem
    ((Scheme.mem_basicOpen U.toScheme (U.topIso.inv a) z (Set.mem_univ z)).mp hz)

/-! ## `HasFiniteDegree` is automatic on a regular one-dimensional scheme -/

/-- The generic point of an irreducible scheme lies in the support of an effective Cartier divisor
only if that support is the whole space (the support is closed, and the closure of the generic
point is everything). -/
theorem genericPoint_notMem_support_of_ne_univ [IsIntegral X] (D : EffectiveCartierDivisor X)
    (hne : (D.support : Set X) ≠ Set.univ) : genericPoint X ∉ (D.support : Set X) := by
  intro hmem
  refine hne (Set.univ_subset_iff.mp ?_)
  have h1 : closure ({genericPoint X} : Set X) ⊆ (D.support : Set X) :=
    (D.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hmem)
  rwa [genericPoint_spec X] at h1

/-- **On a regular one-dimensional integral Noetherian scheme, every effective Cartier divisor
whose support is not the whole space has a well-defined degree.**  Both hypotheses recorded in
`HasFiniteDegree` are derived: the support is a proper closed subset, hence finite
(`finite_of_isClosed_of_ne_univ`), and at each of its (necessarily non-generic, hence
coheight-one) points the local equation is a regular element of the stalk
(`isRegular_germ_of_isRegular`) of a discrete valuation ring, so its `Ring.ord` is finite
(`ord_ne_top_of_regular`).  This removes `HasFiniteDegree` as an assumption on
`degree`/`degree_add` for divisors on a curve. -/
theorem hasFiniteDegree_of_support_ne_univ [IsIntegral X] [NoetherianSpace X]
    [IsLocallyNoetherian X] (hreg : SchemeIsRegular X)
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (D : EffectiveCartierDivisor X) (hne : (D.support : Set X) ≠ Set.univ) :
    D.HasFiniteDegree := by
  have hgen := genericPoint_notMem_support_of_ne_univ D hne
  have hfin : (D.support : Set X).Finite :=
    finite_of_isClosed_of_ne_univ hpt _ D.support.isClosed hne
  refine ⟨fun x hx => ?_, fun x => ⟨Set.univ, Filter.univ_mem, by
    rw [Set.univ_inter]; exact hfin⟩⟩
  have hxne : x ≠ genericPoint X := fun h => hgen (h ▸ hx)
  have hco : Order.coheight x = 1 := coheight_eq_one_of_ne_genericPoint hpt x hxne
  rw [D.multiplicity_eq_ord x]
  exact ord_ne_top_of_regular hreg hco
    (isRegular_germ_of_isRegular (D.localEquationOpen x) ⟨x, D.mem_localEquationOpen x⟩
      (D.localEquation_isRegular x)).mem_nonZeroDivisors

/-! ## The divisor of a section on an affine open of a one-dimensional scheme -/

/-- **The effective Cartier divisor cut out on all of `X` by a nonzero section `a` over an affine
open `V`**, trivial outside `V`.  All the hypotheses of `EffectiveCartierDivisor.ofAffineOpen` are
discharged automatically here: the section is a regular element because `X` is integral
(`isRegular_topIso_inv`), its zero locus is not the whole of `V` because `X` is reduced
(`support_ofGlobalEquation_ne_univ`), and the image of that zero locus is therefore closed because
the non-generic points of `X` are closed (`isClosed_range_comp_ι`). -/
noncomputable def EffectiveCartierDivisor.ofChartSection [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0) :
    EffectiveCartierDivisor X :=
  (EffectiveCartierDivisor.ofGlobalEquation V.toScheme (V.topIso.inv a)
      (isRegular_topIso_inv V a ha)).ofAffineOpen
    (isClosed_range_comp_ι hpt V _ (support_ofGlobalEquation_ne_univ (U := V) a _ ha))

/-- The multiplicity of `EffectiveCartierDivisor.ofChartSection` at a point of its chart is the
length-theoretic order of vanishing `Ring.ord` of the section's germ there. -/
theorem multiplicity_ofChartSection [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0)
    (x : X) (hx : x ∈ V) :
    (EffectiveCartierDivisor.ofChartSection hpt V a ha).multiplicity x =
      Ring.ord (X.presheaf.stalk x) ((X.presheaf.germ V x hx).hom a) :=
  ofAffineOpen_multiplicity_eq (U := V) a _ _ x hx

/-- A point of the chart lies in the support of `EffectiveCartierDivisor.ofChartSection` exactly
when the section is not a unit there. -/
theorem mem_support_ofChartSection_iff [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0)
    (x : X) (hx : x ∈ V) :
    x ∈ ((EffectiveCartierDivisor.ofChartSection hpt V a ha).support : Set X) ↔
      ¬ IsUnit ((X.presheaf.germ V x hx).hom a) :=
  ofAffineOpen_mem_support_iff (U := V) a _ _ x hx

/-- The support of `EffectiveCartierDivisor.ofChartSection` is contained in its chart. -/
theorem support_ofChartSection_le [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0) :
    ((EffectiveCartierDivisor.ofChartSection hpt V a ha).support : Set X) ⊆ (V : Set X) :=
  support_ofAffineOpen_le _ _

/-- The generic point is not in the support of `EffectiveCartierDivisor.ofChartSection`: the germ
of a nonzero section at the generic point is a nonzero element of the function field, hence a
unit. -/
theorem genericPoint_notMem_support_ofChartSection [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0) :
    genericPoint X ∉ ((EffectiveCartierDivisor.ofChartSection hpt V a ha).support : Set X) := by
  have hgen : genericPoint X ∈ V := Scheme.genericPoint_mem_of_nonempty V
  rw [mem_support_ofChartSection_iff hpt V a ha _ hgen]
  intro hnu
  exact hnu (isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral (X := X) _ hgen)).mpr ha))

/-- **The support of `EffectiveCartierDivisor.ofChartSection` is finite**: it is a closed subset of
the one-dimensional scheme `X` which misses the generic point. -/
theorem finite_support_ofChartSection [IsIntegral X] [NoetherianSpace X]
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0) :
    ((EffectiveCartierDivisor.ofChartSection hpt V a ha).support : Set X).Finite := by
  refine finite_of_isClosed_of_ne_univ hpt _
    (EffectiveCartierDivisor.ofChartSection hpt V a ha).support.isClosed ?_
  intro hc
  exact genericPoint_notMem_support_ofChartSection hpt V a ha (hc ▸ Set.mem_univ _)

/-- **`EffectiveCartierDivisor.ofChartSection` has a well-defined degree** on a regular
one-dimensional integral scheme: the local rings at the (closed) points of its support are
discrete valuation rings, so the lengths are finite (`ord_ne_top_of_regular`), and the support is
finite (`finite_support_ofChartSection`). -/
theorem hasFiniteDegree_ofChartSection [IsIntegral X] [NoetherianSpace X] [IsLocallyNoetherian X]
    (hreg : SchemeIsRegular X)
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0) :
    (EffectiveCartierDivisor.ofChartSection hpt V a ha).HasFiniteDegree where
  finite_multiplicity x hx := by
    have hxV : x ∈ V := support_ofChartSection_le hpt V a ha hx
    have hne : x ≠ genericPoint X := by
      rintro rfl
      exact genericPoint_notMem_support_ofChartSection hpt V a ha hx
    have hco : Order.coheight x = 1 := coheight_eq_one_of_ne_genericPoint hpt x hne
    rw [multiplicity_ofChartSection hpt V a ha x hxV]
    exact ord_ne_top_of_regular hreg hco (mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral (X := X) x hxV)).mpr ha))
  locallyFinite_support x :=
    ⟨Set.univ, Filter.univ_mem, by
      rw [Set.univ_inter]
      exact finite_support_ofChartSection hpt V a ha⟩

/-- **The multiplicity of `EffectiveCartierDivisor.ofChartSection` is the order of vanishing, in the
sense of `AlgebraicGeometry.Scheme.ord`, of the rational function represented by the section.**
This is the identity that turns the zero-cycle of the divisor into (part of) the principal cycle
of a rational function.  At the generic point both sides vanish; elsewhere the point has coheight
one and `ord_germToFunctionField_eq_ord` applies. -/
theorem multiplicity_ofChartSection_eq_ord [IsIntegral X] [NoetherianSpace X]
    [IsLocallyNoetherian X] (hreg : SchemeIsRegular X)
    (hpt : ∀ x : X, x ≠ genericPoint X → IsClosed ({x} : Set X))
    (V : X.Opens) [IsAffine V.toScheme] [Nonempty V] (a : Γ(X, V)) (ha : a ≠ 0)
    (x : X) (hx : x ∈ V) :
    (((EffectiveCartierDivisor.ofChartSection hpt V a ha).multiplicity x).toNat : ℤ) =
      Scheme.ord (X.germToFunctionField V a) x := by
  have hgerm_ne : (X.presheaf.germ V x hx).hom a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral (X := X) x hx)).mpr ha
  by_cases hgen : x = genericPoint X
  · subst hgen
    have hco : Order.coheight (genericPoint X) ≠ 1 := by
      rw [Order.coheight_eq_zero.mpr
        (IntersectionTheory.HomogeneityLocal.isTop_genericPoint X).isMax]
      exact zero_ne_one
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hco, multiplicity_ofChartSection hpt V a ha _ hx,
      (ord_eq_zero_iff_isUnit _).mpr (isUnit_iff_ne_zero.mpr hgerm_ne)]
    rfl
  · have hco : Order.coheight x = 1 := coheight_eq_one_of_ne_genericPoint hpt x hgen
    rw [multiplicity_ofChartSection hpt V a ha x hx, ord_germToFunctionField_eq_ord hx hco a ha
      (ord_ne_top_of_regular hreg hco (mem_nonZeroDivisors_iff_ne_zero.mpr hgerm_ne))]

/-! ## Divisors of zeros and poles, and invariance of the degree under linear equivalence

Let `C` be a regular proper curve over a field `k` (`RegularProperCurve`, see
`Curves/ProperCurveTopology.lean`) and `r` a nonzero rational function on it.  The divisor of
zeros of `r` is the divisor cut out by `Scheme.regularSection r` on the domain of definition
`Scheme.regularLocus r` of `r` (`Curves/RationalFunctionToProjectiveLine.lean`), and the divisor
of poles is the divisor of zeros of `r⁻¹`.  Both are honest effective Cartier divisors on the whole
curve by `EffectiveCartierDivisor.ofChartSection`.

The one hypothesis that is *not* discharged here is that the two domains of definition are affine
opens (`hU₀`, `hU₁`): this is exactly the hypothesis under which the repository's proof of the
vanishing of the degree of a principal divisor is organised
(`IntersectionTheory.ProperCurveDegreeTranscendental.lean`, `ProperCurveDegreeFinal.lean`), and it
is supplied by `IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus`
and `..._inv` as soon as `r` is transcendental over `k` -- see
`degree_divisorOfZeros_eq_degree_divisorOfPoles_of_transcendental`.  The vanishing statement itself
(`RegularProperCurve.degreeCycle_principalCycle_eq_zero'`) is unconditional. -/

section LinearEquivalence

variable {k : Type u} [Field k]

/-- **The degree of the principal cycle of any rational function on a regular proper curve
vanishes.**  This is `IntersectionTheory.ProperCurveDegree.RegularProperCurve.
degreeCycle_principalCycle_eq_zero'` (which is unconditional in the sense that it needs no chart
presentation), extended to the degenerate value `r = 0`. -/
theorem degreeCycle_principalCycle_eq_zero_of_curve (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] (r : C.W.functionField) :
    IntersectionTheory.ZeroCycleDegree.degreeCycle C.f (C.W.principalCycle r) = 0 := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [Scheme.principalCycle_zero, map_zero]
  exact IntersectionTheory.ProperCurveDegree.RegularProperCurve.degreeCycle_principalCycle_eq_zero'
    C r hr

/-- **Two effective Cartier divisors whose multiplicities differ by the order of vanishing of a
rational function `r` have zero-cycles differing by the principal cycle of `r`.** -/
theorem cycle_sub_cycle_eq_principalCycle (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] (r : C.W.functionField)
    (D₀ D₁ : EffectiveCartierDivisor C.W) (h₀ : D₀.HasFiniteDegree) (h₁ : D₁.HasFiniteDegree)
    (h : ∀ x : C.W, ((D₀.multiplicity x).toNat : ℤ) - ((D₁.multiplicity x).toNat : ℤ) =
      C.W.ord r x) :
    D₀.cycle h₀ - D₁.cycle h₁ = C.W.principalCycle r := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply,
    EffectiveCartierDivisor.cycle_apply, Scheme.principalCycle_apply]
  exact_mod_cast h x

/-- **Two effective Cartier divisors on a regular proper curve whose multiplicities differ by the
order of vanishing of a rational function have the same degree.**  This is the abstract form of the
invariance of the degree under linear equivalence: no hypothesis is needed on the divisors beyond
the pointwise identity `mult D₀ - mult D₁ = ord r` (which says that `D₀ - D₁` *is* the principal
divisor of `r`), in particular no affineness of the domains of definition of `r`. -/
theorem degree_eq_of_multiplicity_sub_eq_ord (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] (r : C.W.functionField)
    (D₀ D₁ : EffectiveCartierDivisor C.W) (h₀ : D₀.HasFiniteDegree) (h₁ : D₁.HasFiniteDegree)
    (h : ∀ x : C.W, ((D₀.multiplicity x).toNat : ℤ) - ((D₁.multiplicity x).toNat : ℤ) =
      C.W.ord r x) :
    D₀.degree C.f h₀ = D₁.degree C.f h₁ := by
  have hzero := degreeCycle_principalCycle_eq_zero_of_curve C r
  have hkey : IntersectionTheory.ZeroCycleDegree.degreeCycle C.f
      (D₀.cycle h₀ - D₁.cycle h₁) = 0 := by
    rw [cycle_sub_cycle_eq_principalCycle C r D₀ D₁ h₀ h₁ h]
    exact hzero
  rw [map_sub] at hkey
  unfold EffectiveCartierDivisor.degree
  linarith

/-- The regular function representing a nonzero rational function on its domain of definition is
itself nonzero: its germ at the generic point is the rational function. -/
theorem regularSection_ne_zero {Y : Scheme.{u}} [IsIntegral Y] {r : Y.functionField}
    (hr : r ≠ 0) : Scheme.regularSection r ≠ 0 := fun h =>
  hr (by rw [← Scheme.germ_regularSection r, h, map_zero])

/-- `Scheme.regularSection r` represents `r` in the function field. -/
theorem germToFunctionField_regularSection {Y : Scheme.{u}} [IsIntegral Y] (r : Y.functionField) :
    Y.germToFunctionField (Scheme.regularLocus r) (Scheme.regularSection r) = r :=
  Scheme.germ_regularSection r

/-- **The divisor of zeros of a nonzero rational function `r` on a regular proper curve**: the
effective Cartier divisor cut out on the whole curve by the regular function representing `r` on
its (assumed affine, `hU`) domain of definition. -/
noncomputable def divisorOfZeros (C : RegularProperCurve k) {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) : EffectiveCartierDivisor C.W :=
  haveI := C.isNoetherian
  haveI : IsAffine (Scheme.regularLocus r).toScheme := hU
  EffectiveCartierDivisor.ofChartSection C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr)

/-- **The divisor of poles of a nonzero rational function `r` on a regular proper curve**: the
divisor of zeros of `r⁻¹`. -/
noncomputable def divisorOfPoles (C : RegularProperCurve k) {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r⁻¹)) : EffectiveCartierDivisor C.W :=
  divisorOfZeros C (inv_ne_zero hr) hU

/-- The divisor of zeros of a rational function on a regular proper curve has a well-defined
degree.  (The instance `[IsNoetherian C.W]` is not an extra assumption: it is supplied by
`RegularProperCurve.isNoetherian`.) -/
theorem hasFiniteDegree_divisorOfZeros (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) : (divisorOfZeros C hr hU).HasFiniteDegree := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  exact hasFiniteDegree_ofChartSection C.regular C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr)

/-- The divisor of poles of a rational function on a regular proper curve has a well-defined
degree. -/
theorem hasFiniteDegree_divisorOfPoles (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r⁻¹)) : (divisorOfPoles C hr hU).HasFiniteDegree :=
  hasFiniteDegree_divisorOfZeros C (inv_ne_zero hr) hU

/-- **On the domain of definition of `r` the multiplicity of the divisor of zeros of `r` is the
order of vanishing of `r`.** -/
theorem multiplicity_divisorOfZeros_eq_ord (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) (hx : x ∈ Scheme.regularLocus r) :
    (((divisorOfZeros C hr hU).multiplicity x).toNat : ℤ) = C.W.ord r x := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  have h := multiplicity_ofChartSection_eq_ord (X := C.W) C.regular C.isClosed_singleton
    (Scheme.regularLocus r) (Scheme.regularSection r) (regularSection_ne_zero hr) x hx
  rw [germToFunctionField_regularSection r] at h
  exact h

/-- Outside the domain of definition of `r` the divisor of zeros of `r` has multiplicity zero: its
support is contained in that domain. -/
theorem multiplicity_divisorOfZeros_eq_zero (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) (hx : x ∉ Scheme.regularLocus r) :
    (divisorOfZeros C hr hU).multiplicity x = 0 := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  refine EffectiveCartierDivisor.multiplicity_eq_zero_of_notMem_support _ x fun hmem => hx ?_
  exact support_ofChartSection_le C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr) hmem

/-- The multiplicity of the divisor of zeros of `r` at a point of the domain of definition of `r`
is the length-theoretic `Ring.ord` of the germ of the representing regular function. -/
theorem multiplicity_divisorOfZeros (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) (hx : x ∈ Scheme.regularLocus r) :
    (divisorOfZeros C hr hU).multiplicity x =
      Ring.ord (C.W.presheaf.stalk x)
        ((C.W.presheaf.germ (Scheme.regularLocus r) x hx).hom (Scheme.regularSection r)) := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  exact multiplicity_ofChartSection C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr) x hx

/-- The divisor of zeros of `r` is supported inside the domain of definition of `r`. -/
theorem support_divisorOfZeros_le (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) :
    ((divisorOfZeros C hr hU).support : Set C.W) ⊆ (Scheme.regularLocus r : Set C.W) := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  exact support_ofChartSection_le C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr)

/-- A point of the domain of definition of `r` lies in the support of the divisor of zeros of `r`
exactly when the representing regular function is not a unit there. -/
theorem mem_support_divisorOfZeros_iff_not_isUnit (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) (hx : x ∈ Scheme.regularLocus r) :
    x ∈ ((divisorOfZeros C hr hU).support : Set C.W) ↔
      ¬ IsUnit ((C.W.presheaf.germ (Scheme.regularLocus r) x hx).hom
        (Scheme.regularSection r)) := by
  have : IsAffine (Scheme.regularLocus r).toScheme := hU
  exact mem_support_ofChartSection_iff C.isClosed_singleton (Scheme.regularLocus r)
    (Scheme.regularSection r) (regularSection_ne_zero hr) x hx

/-- **The order of vanishing of a rational function is nonnegative on its domain of definition**:
there it is the multiplicity (a natural number) of the divisor of zeros. -/
theorem ord_nonneg_of_mem_regularLocus (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) (hx : x ∈ Scheme.regularLocus r) :
    0 ≤ C.W.ord r x := by
  rw [← multiplicity_divisorOfZeros_eq_ord C hr hU x hx]
  exact Int.natCast_nonneg _

/-- **`divisorOfZeros` really is the divisor of zeros of `r`**: its support is exactly the set of
points of the domain of definition of `r` at which `r` vanishes, i.e. at which the order of
vanishing of `r` is nonzero (equivalently, by `ord_nonneg_of_mem_regularLocus`, positive). -/
theorem mem_support_divisorOfZeros_iff (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU : IsAffineOpen (Scheme.regularLocus r)) (x : C.W) :
    x ∈ ((divisorOfZeros C hr hU).support : Set C.W) ↔
      x ∈ Scheme.regularLocus r ∧ C.W.ord r x ≠ 0 := by
  constructor
  · intro hx
    have hxU : x ∈ Scheme.regularLocus r := support_divisorOfZeros_le C hr hU hx
    refine ⟨hxU, ?_⟩
    have hne : (divisorOfZeros C hr hU).multiplicity x ≠ 0 := by
      rw [multiplicity_divisorOfZeros C hr hU x hxU]
      exact fun h => ((mem_support_divisorOfZeros_iff_not_isUnit C hr hU x hxU).mp hx)
        ((ord_eq_zero_iff_isUnit _).mp h)
    have hfin := (hasFiniteDegree_divisorOfZeros C hr hU).finite_multiplicity x hx
    rw [← multiplicity_divisorOfZeros_eq_ord C hr hU x hxU]
    refine Int.natCast_ne_zero.mpr fun h => ?_
    rcases ENat.toNat_eq_zero.mp h with h0 | htop
    · exact hne h0
    · exact hfin htop
  · rintro ⟨hxU, hord⟩
    by_contra hx
    refine hord ?_
    rw [← multiplicity_divisorOfZeros_eq_ord C hr hU x hxU,
      EffectiveCartierDivisor.multiplicity_eq_zero_of_notMem_support _ x hx]
    rfl

/-- **The pointwise identity `div₀(r) - div∞(r) = ord r` at every point of the curve.**  The two
domains of definition cover the curve (`Scheme.regularLocus_sup_regularLocus_inv_eq_top`, using
that all local rings of a regular curve are valuation rings); on their intersection `r` is a unit
and all three quantities vanish
(`IntersectionTheory.ProperCurveDegree.ord_eq_zero_of_mem_regularLocus_inf`); on either difference
one of the two multiplicities vanishes and the other is the order of vanishing of `r`, resp. of
`r⁻¹` (`IntersectionTheory.ProperCurveDegree.ord_inv`). -/
theorem multiplicity_divisorOfZeros_sub_divisorOfPoles (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹)) (x : C.W) :
    (((divisorOfZeros C hr hU₀).multiplicity x).toNat : ℤ) -
      (((divisorOfPoles C hr hU₁).multiplicity x).toNat : ℤ) = C.W.ord r x := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr
  have hpoles : divisorOfPoles C hr hU₁ = divisorOfZeros C hr' hU₁ := rfl
  rw [hpoles]
  by_cases h0 : x ∈ Scheme.regularLocus r
  · by_cases h1 : x ∈ Scheme.regularLocus r⁻¹
    · have hz : C.W.ord r x = 0 :=
        IntersectionTheory.ProperCurveDegree.ord_eq_zero_of_mem_regularLocus_inf r ⟨h0, h1⟩
      rw [multiplicity_divisorOfZeros_eq_ord C hr hU₀ x h0,
        multiplicity_divisorOfZeros_eq_ord C hr' hU₁ x h1,
        IntersectionTheory.ProperCurveDegree.ord_inv r x, hz]
      ring
    · rw [multiplicity_divisorOfZeros_eq_ord C hr hU₀ x h0,
        multiplicity_divisorOfZeros_eq_zero C hr' hU₁ x h1]
      simp
  · by_cases h1 : x ∈ Scheme.regularLocus r⁻¹
    · rw [multiplicity_divisorOfZeros_eq_zero C hr hU₀ x h0,
        multiplicity_divisorOfZeros_eq_ord C hr' hU₁ x h1,
        IntersectionTheory.ProperCurveDegree.ord_inv r x]
      simp
    · refine absurd ?_ (not_or.mpr ⟨h0, h1⟩)
      have htop := Scheme.regularLocus_sup_regularLocus_inv_eq_top C.valuationRing_stalk r
      exact TopologicalSpace.Opens.mem_sup.mp (htop ▸ (Set.mem_univ x : x ∈ (⊤ : C.W.Opens)))

/-- **The difference of the zero-cycles of the divisors of zeros and of poles of `r` is the
principal cycle of `r`** (`AlgebraicGeometry.Scheme.principalCycle`, the Weil divisor of `r`). -/
theorem cycle_divisorOfZeros_sub_cycle_divisorOfPoles (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹)) :
    (divisorOfZeros C hr hU₀).cycle (hasFiniteDegree_divisorOfZeros C hr hU₀) -
        (divisorOfPoles C hr hU₁).cycle (hasFiniteDegree_divisorOfPoles C hr hU₁) =
      C.W.principalCycle r :=
  cycle_sub_cycle_eq_principalCycle C r _ _ _ _
    (multiplicity_divisorOfZeros_sub_divisorOfPoles C hr hU₀ hU₁)

/-- **The divisors of zeros and of poles of a rational function on a regular proper curve have the
same degree.**  This is issue #141's compatibility of the degree with linear equivalence: it
follows from the vanishing of the degree of the principal cycle of `r`
(`IntersectionTheory.ProperCurveDegree.RegularProperCurve.degreeCycle_principalCycle_eq_zero'`,
which is unconditional) and `cycle_divisorOfZeros_sub_cycle_divisorOfPoles`. -/
theorem degree_divisorOfZeros_eq_degree_divisorOfPoles (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹)) :
    (divisorOfZeros C hr hU₀).degree C.f (hasFiniteDegree_divisorOfZeros C hr hU₀) =
      (divisorOfPoles C hr hU₁).degree C.f (hasFiniteDegree_divisorOfPoles C hr hU₁) :=
  degree_eq_of_multiplicity_sub_eq_ord C r _ _ _ _
    (multiplicity_divisorOfZeros_sub_divisorOfPoles C hr hU₀ hU₁)

/-- **Invariance of the degree of a formal difference of effective Cartier divisors under adding
the principal divisor of a rational function.**  Adding the divisor of zeros of `r` to `E₁` and the
divisor of poles of `r` to `E₂` -- that is, adding `div r = div₀ r - div∞ r` to the formal
difference `E₁ - E₂` -- does not change `deg E₁ - deg E₂`.  This is the statement that the degree
descends to linear-equivalence classes on a regular proper curve. -/
theorem degree_sum_divisorOfZeros_sub_degree_sum_divisorOfPoles (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] {r : C.W.functionField} (hr : r ≠ 0)
    (hU₀ : IsAffineOpen (Scheme.regularLocus r))
    (hU₁ : IsAffineOpen (Scheme.regularLocus r⁻¹))
    (E₁ E₂ : EffectiveCartierDivisor C.W) (h₁ : E₁.HasFiniteDegree) (h₂ : E₂.HasFiniteDegree) :
    (E₁.sum (divisorOfZeros C hr hU₀)).degree C.f
          (h₁.sum (hasFiniteDegree_divisorOfZeros C hr hU₀)) -
        (E₂.sum (divisorOfPoles C hr hU₁)).degree C.f
          (h₂.sum (hasFiniteDegree_divisorOfPoles C hr hU₁)) =
      E₁.degree C.f h₁ - E₂.degree C.f h₂ := by
  rw [EffectiveCartierDivisor.degree_add C.f E₁ (divisorOfZeros C hr hU₀) h₁
      (hasFiniteDegree_divisorOfZeros C hr hU₀),
    EffectiveCartierDivisor.degree_add C.f E₂ (divisorOfPoles C hr hU₁) h₂
      (hasFiniteDegree_divisorOfPoles C hr hU₁),
    degree_divisorOfZeros_eq_degree_divisorOfPoles C hr hU₀ hU₁]
  ring

/-- **`degree_divisorOfZeros_eq_degree_divisorOfPoles` with the two affineness hypotheses
discharged**, for a rational function transcendental over the base field: this is the shape in
which the repository's curve machinery proves that the two domains of definition are affine
(`IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus`). -/
theorem degree_divisorOfZeros_eq_degree_divisorOfPoles_of_transcendental
    (C : RegularProperCurve k) [_root_.AlgebraicGeometry.IsNoetherian C.W]
    {r : C.W.functionField} (hr : r ≠ 0)
    (htr : Function.Injective
      (Polynomial.eval₂RingHom (RationalFunction.kFunctionField C.f).hom r)) :
    (divisorOfZeros C hr
          (IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus
            C r hr htr)).degree C.f (hasFiniteDegree_divisorOfZeros C hr _) =
      (divisorOfPoles C hr
          (IntersectionTheory.ProperCurveDegree.RegularProperCurve.isAffineOpen_regularLocus_inv
            C r hr htr)).degree C.f (hasFiniteDegree_divisorOfPoles C hr _) :=
  degree_divisorOfZeros_eq_degree_divisorOfPoles C hr _ _

/-- **On a regular proper curve every effective Cartier divisor whose support is not the whole
curve has a well-defined degree** (`hasFiniteDegree_of_support_ne_univ` specialised to
`RegularProperCurve`). -/
theorem hasFiniteDegree_of_support_ne_univ_of_curve (C : RegularProperCurve k)
    [_root_.AlgebraicGeometry.IsNoetherian C.W] (D : EffectiveCartierDivisor C.W)
    (hne : (D.support : Set C.W) ≠ Set.univ) : D.HasFiniteDegree :=
  hasFiniteDegree_of_support_ne_univ C.regular C.isClosed_singleton D hne

end LinearEquivalence

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
