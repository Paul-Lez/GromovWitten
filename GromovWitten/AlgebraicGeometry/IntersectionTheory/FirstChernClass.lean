/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleData
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjective
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleInjectiveRelation
import GromovWitten.AlgebraicGeometry.IntersectionTheory.HomogeneityLocal

/-!
# The first Chern class on Chow groups

Fulton's Intersection Theory §2.5: the map `c₁(L) ∩ - : A_{i+1}(X) → A_i(X)` attached to a line
bundle `L` on `X`, defined generator-by-generator by choosing a rational section of `L` along
each subvariety and taking its Weil divisor.

Throughout, `X` is required to be locally Noetherian *and* Noetherian as a topological space
(`NoetherianSpace X`, so in particular compact): the point-generator machinery of
`LineBundleInjective.lean` needs `NoetherianSpace X`, and compactness is what makes the defining
sum over all points of `X` a genuine finite sum (rational cycles have merely *locally* finite
support in general).

The construction also needs, for a fixed `dimension : DimensionFunction X`, that the certified
dimension grading is compatible with catenary dimension theory in the precise sense of
`HomogeneityLocal.CovByDimension dimension`: the dimension drops by exactly one along a covering
pair of the specialization order.  Without such a hypothesis the divisor of a rational section of
`L` along a subvariety `V` need not be concentrated in a single dimension at all (this is exactly
the obstruction `HomogeneityLocal.lean` isolates for ordinary principal divisors, and it is not
resolved in this repository except through per-scheme dimension-formula hypotheses).  The
hypothesis is carried explicitly as `hcov` everywhere it is needed; it is automatic whenever `X`
is of finite type over a field, via the `FiniteTypeDimension.lean`/`HomogeneityLocal.lean`
machinery (not re-derived here).

## Main declarations

* `LineBundleData.RationalSection.divisor_mem_cyclesOfDimension` — the divisor of a rational
  section of `L` along a subvariety `V` of dimension `i + 1` is concentrated in dimension `i`
  (given `hcov`); `RationalFunctionGenerator.divisor_mem_cyclesOfDimension` is the analogue for
  a plain principal-divisor generator.
* `chernSummand`, `chernSummand_eq` — the per-point summand of `c₁(L)`, and its independence of
  the chosen rational section (given `hcov`).
* `c1Cycle L dim i` — the linear map `cyclesOfDimension X dim (i + 1) →ₗ[ℚ] ChowGroup_i` sending
  a graded cycle `α` to `∑ᶠ x, α x • [s_x.divisor]`, `s_x` a chosen rational section of `L` along
  the point `x`; `c1Cycle_single` identifies its value on the class of a single point,
  independently of the chosen section (given `hcov`).
* `cyclesOfDimension.pointProj`, `cyclesOfDimension.eq_sum_pointProj`, `c1Cycle_ext` — the
  decomposition of a graded cycle on a Noetherian scheme as a finite sum of point classes, and
  the resulting extensionality principle for `c1Cycle`-shaped linear maps.
* `KillsRelations L dim hcov i` and `c1 h` — the descent condition for `c1Cycle`, and its descent
  to a linear map on Chow groups (`Submodule.liftQ`); `c1_quotientMap_single` relates the two.
* `c1Cycle_trivial`/`killsRelations_trivial`/`c1_trivial`,
  `c1Cycle_tensor`/`killsRelations_tensor`/`c1_tensor` and
  `c1Cycle_dual`/`killsRelations_dual`/`c1_dual` — additivity of `c₁` in the trivial bundle,
  tensor product and dual (`LineBundleData.RationalSection.dual` and its divisor/order lemmas
  are new declarations added here, since `LineBundleData.lean` is not owned by this file).
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open GromovWitten.AlgebraicGeometry.IntersectionTheory
open LineBundleInjective

variable {X : Scheme.{u}} [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X]

/-- The (unique, up to the ambient `Subsingleton`) canonical rational-equivalence system in a
fixed dimension: a shorthand for `RationalEquivalenceSystem.canonical`, spelled out so that
`.ChowGroup`, `.quotientMap` and `.relations` can be accessed without repeating the anonymous
constructor at every call site. -/
noncomputable def chowSystem (dim : DimensionFunction X) (i : ℤ) :
    RationalEquivalenceSystem X dim i :=
  .canonical

namespace LineBundleData

variable {L : LineBundleData X} {V : IntegralClosedSubscheme X}

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- **Goal 1.** The divisor of a rational section of `L` along a subvariety `V` whose generic
point has dimension `i + 1` is concentrated in dimension `i`.  Mirrors the (implicit, per-use-site)
homogeneity statement for `RationalFunctionGenerator.divisor`: the coefficient of the divisor
vanishes off the closed image of `V`, and on that image it is the order of the section at a point
of `V`, nonzero only at points of coheight one, which (via `hcov`) are exactly the points whose
dimension is one less than that of `V`'s generic point. -/
theorem RationalSection.divisor_mem_cyclesOfDimension (s : L.RationalSection V)
    (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ}
    (hV : dim V.genericPointImage = i + 1) :
    s.divisor dim ∈ cyclesOfDimension X dim i := by
  intro y hy
  by_contra hne
  unfold RationalSection.divisor IntegralClosedSubscheme.pushforward at hne
  by_cases hmem : y ∈ Set.range V.inclusion.base
  · obtain ⟨x, rfl⟩ := hmem
    rw [AlgebraicCycle.map_closedImmersion_apply_image V.inclusion (dim : X → ℤ)] at hne
    rw [s.divisorCycle_apply] at hne
    have hordZ : s.ord x ≠ 0 := by exact_mod_cast hne
    obtain ⟨j, hxj⟩ := L.covers (V.inclusion.base x)
    have hjj := s.ord_well_defined j x hxj
    have hco : Order.coheight x = 1 := by
      by_contra hcon
      rw [hjj, _root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcon] at hordZ
      exact hordZ rfl
    have hcovy : x ⋖ genericPoint V.scheme :=
      (HomogeneityLocal.coheight_eq_one_iff_covBy
        (HomogeneityLocal.isTop_genericPoint V.scheme)).1 hco
    have hkey := hcov _ _ (HomogeneityLocal.covBy_map_of_isClosedImmersion V.inclusion hcovy)
    rw [hV] at hkey
    exact hy (by omega)
  · exact hne (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range V.inclusion
      (dim : X → ℤ) _ y hmem)

end LineBundleData

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The analogue of `RationalSection.divisor_mem_cyclesOfDimension` for a plain principal-divisor
generator: mirrors `HomogeneityLocal.principalDivisorsHomogeneous_of_covByDimension`, pinned to
the specific dimension forced by `hg` instead of an unnamed existential witness. -/
theorem RationalFunctionGenerator.divisor_mem_cyclesOfDimension {i : ℤ}
    (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (g : RationalFunctionGenerator X) (hg : dim g.subspace.genericPointImage = i + 1) :
    g.divisor dim ∈ cyclesOfDimension X dim i := by
  intro x hx
  by_contra hne
  unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward at hne
  by_cases hmem : x ∈ Set.range g.subspace.inclusion.base
  · obtain ⟨y, rfl⟩ := hmem
    rw [AlgebraicCycle.map_closedImmersion_apply_image g.subspace.inclusion (dim : X → ℤ)] at hne
    rw [_root_.AlgebraicGeometry.Scheme.principalCycle_apply] at hne
    have hordZ : g.subspace.scheme.ord (g.function : g.subspace.scheme.functionField) y ≠ 0 := by
      exact_mod_cast hne
    have hco : Order.coheight y = 1 := by
      by_contra hcon
      exact hordZ (_root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hcon _)
    have hcovy : y ⋖ genericPoint g.subspace.scheme :=
      (HomogeneityLocal.coheight_eq_one_iff_covBy
        (HomogeneityLocal.isTop_genericPoint g.subspace.scheme)).1 hco
    have hkey := hcov _ _ (HomogeneityLocal.covBy_map_of_isClosedImmersion
      g.subspace.inclusion hcovy)
    rw [hg] at hkey
    exact hx (by omega)
  · exact hne (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range g.subspace.inclusion
      (dim : X → ℤ) _ x hmem)

namespace cyclesOfDimension

variable {dim : DimensionFunction X} {i : ℤ}

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- Projecting a cycle already concentrated in dimension `i'` onto a *different* dimension `i`
gives zero.  (`project_coe`, `LocalizationExact.lean`, is the case `i' = i`.) -/
theorem project_eq_zero_of_mem_ne {i' : ℤ} {z : AlgebraicCycle X ℚ}
    (h : z ∈ cyclesOfDimension X dim i') (hne : i' ≠ i) :
    cyclesOfDimension.project (dimension := dim) (i := i) z = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp only [cyclesOfDimension.project_apply, Submodule.coe_zero]
  by_cases hy : dim y = i
  · rw [if_pos hy]
    exact h y (hy ▸ Ne.symm hne)
  · rw [if_neg hy]
    rfl

end cyclesOfDimension

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] in
/-- A rational cycle on a Noetherian (hence compact) scheme has globally finite support: local
finiteness of the support, intersected with the compact set `Set.univ`, is finiteness. -/
theorem finite_support_univ (c : AlgebraicCycle X ℚ) :
    (Function.support (c : X → ℚ)).Finite := by
  have h := c.locallyFiniteSupport.finite_inter_support_of_isCompact (isCompact_univ (X := X))
  simpa using h

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The support of `x ↦ (c x) • F x` is contained in the support of `c`, hence finite whenever
`c`'s is. -/
theorem finite_support_smul {N : Type*} [AddCommMonoid N] [Module ℚ N] (c : AlgebraicCycle X ℚ)
    (F : X → N) (hc : (Function.support (c : X → ℚ)).Finite) :
    (Function.support (fun x ↦ (c : X → ℚ) x • F x)).Finite :=
  hc.subset (fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [h0, zero_smul]))

/-- **Goal 2, summand.** The value of `c₁(L)` at a single point `x`, computed from a chosen
rational section of `L` along `pointSubscheme x` (unconditionally: the choice-independence and
homogeneity facts are only needed to *identify* this value, in `chernSummand_eq`). -/
noncomputable def chernSummand (L : LineBundleData X) (dim : DimensionFunction X) (i : ℤ)
    (x : X) : (chowSystem dim i).ChowGroup :=
  (chowSystem dim i).quotientMap
    (cyclesOfDimension.project (dimension := dim) (i := i)
      ((Classical.choice
          (LineBundleData.RationalSection.exists_rationalSection
            (L := L) (V := pointSubscheme x))).divisor dim))

/-- **Goal 2, independence.** `chernSummand` computed from *any* rational section of `L` along
`pointSubscheme x`, at a point `x` of dimension `i + 1`. -/
theorem chernSummand_eq {L : LineBundleData X} {dim : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} {x : X} (hx : dim x = i + 1)
    (s : L.RationalSection (pointSubscheme x)) :
    chernSummand L dim i x =
      (chowSystem dim i).quotientMap ⟨s.divisor dim,
        s.divisor_mem_cyclesOfDimension dim hcov
          (by rw [genericPointImage_pointSubscheme]; exact hx)⟩ := by
  set s₀ := Classical.choice
    (LineBundleData.RationalSection.exists_rationalSection (L := L) (V := pointSubscheme x))
    with hs₀def
  have hmem0 : s₀.divisor dim ∈ cyclesOfDimension X dim i :=
    s₀.divisor_mem_cyclesOfDimension dim hcov (by rw [genericPointImage_pointSubscheme]; exact hx)
  have hmem : s.divisor dim ∈ cyclesOfDimension X dim i :=
    s.divisor_mem_cyclesOfDimension dim hcov (by rw [genericPointImage_pointSubscheme]; exact hx)
  have step0 : cyclesOfDimension.project (dimension := dim) (i := i) (s₀.divisor dim) =
      ⟨s₀.divisor dim, hmem0⟩ :=
    cyclesOfDimension.project_coe ⟨s₀.divisor dim, hmem0⟩
  change (chowSystem dim i).quotientMap
      (cyclesOfDimension.project (dimension := dim) (i := i) (s₀.divisor dim)) = _
  rw [step0]
  rw [← sub_eq_zero, ← map_sub]
  refine (Submodule.Quotient.mk_eq_zero (chowSystem dim i).relations).mpr ?_
  change (⟨s₀.divisor dim, hmem0⟩ - ⟨s.divisor dim, hmem⟩ : cyclesOfDimension X dim i).1 ∈
    totalRationalRelations X dim
  rw [Submodule.coe_sub]
  exact LineBundleData.RationalSection.divisor_mem_totalRationalRelations_of_sub dim s₀ s

/-- **Goal 2.** The first Chern class of `L`, on cycles: sends a graded cycle `α` to
`∑ᶠ x, α x • [s_x.divisor]`, `s_x` a chosen rational section of `L` along `pointSubscheme x`. -/
noncomputable def c1Cycle (L : LineBundleData X) (dim : DimensionFunction X) (i : ℤ) :
    cyclesOfDimension X dim (i + 1) →ₗ[ℚ] (chowSystem dim i).ChowGroup where
  toFun α := ∑ᶠ x : X, (α : AlgebraicCycle X ℚ) x • chernSummand L dim i x
  map_add' α β := by
    have hα' := finite_support_smul (α : AlgebraicCycle X ℚ) (chernSummand L dim i)
      (finite_support_univ (α : AlgebraicCycle X ℚ))
    have hβ' := finite_support_smul (β : AlgebraicCycle X ℚ) (chernSummand L dim i)
      (finite_support_univ (β : AlgebraicCycle X ℚ))
    simp_rw [Submodule.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_smul]
    exact finsum_add_distrib hα' hβ'
  map_smul' c α := by
    have hα' := finite_support_smul (α : AlgebraicCycle X ℚ) (chernSummand L dim i)
      (finite_support_univ (α : AlgebraicCycle X ℚ))
    simp_rw [Submodule.coe_smul, Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply,
      smul_eq_mul, mul_smul]
    exact (smul_finsum' c hα').symm

/-- **Goal 2, `c1Cycle_single`.** The value of `c₁(L)` on the class of a single point `x` of
dimension `i + 1`, computed from *any* rational section of `L` along `pointSubscheme x`. -/
theorem c1Cycle_single {L : LineBundleData X} {dim : DimensionFunction X}
    (hcov : HomogeneityLocal.CovByDimension dim) {i : ℤ} {x : X} (hx : dim x = i + 1)
    (s : L.RationalSection (pointSubscheme x)) :
    c1Cycle L dim i (cyclesOfDimension.point x hx) =
      (chowSystem dim i).quotientMap ⟨s.divisor dim,
        s.divisor_mem_cyclesOfDimension dim hcov
          (by rw [genericPointImage_pointSubscheme]; exact hx)⟩ := by
  rw [← chernSummand_eq hcov hx s]
  change (∑ᶠ y : X, (cyclesOfDimension.point x hx : AlgebraicCycle X ℚ) y • chernSummand L dim i y)
    = chernSummand L dim i x
  rw [finsum_eq_single _ x]
  · rw [cyclesOfDimension.point_apply_self, one_smul]
  · intro y hy
    rw [cyclesOfDimension.point_apply_of_ne x y hx hy, zero_smul]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The dimension-`i` projection, bundled as a linear map: additivity and homogeneity are
`cyclesOfDimension.project_add`/`project_smul` (`LocalizationExact.lean`). -/
noncomputable def cyclesOfDimension.projectLinear (dim : DimensionFunction X) (i : ℤ) :
    AlgebraicCycle X ℚ →ₗ[ℚ] cyclesOfDimension X dim i where
  toFun := cyclesOfDimension.project (dimension := dim) (i := i)
  map_add' c d := Subtype.ext (cyclesOfDimension.project_add c d)
  map_smul' c z := Subtype.ext (cyclesOfDimension.project_smul c z)

/-- **Goal 3.** `KillsRelations L dim hcov i`: the descent condition for `c1Cycle`, Fulton
Prop. 2.5 / Cor. 2.4.2 — `c₁(L)` sends the divisor of every rational-function generator whose
subspace has dimension `i + 2` to zero. -/
def KillsRelations (L : LineBundleData X) (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ) : Prop :=
  ∀ (g : RationalFunctionGenerator X) (hg : dim g.subspace.genericPointImage = i + 2),
    c1Cycle L dim i ⟨g.divisor dim, RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim
      hcov g (show dim g.subspace.genericPointImage = (i + 1) + 1 by omega)⟩ = 0

/-- The relations submodule of the domain grade `i + 1` lies in the kernel of `c1Cycle`, given
`KillsRelations`: every element of `totalRationalRelations` is, by `Submodule.mem_span_set'`, a
finite combination of generator divisors; the ones whose own dimension is not `i + 2` project to
`0` in grade `i + 1` (`cyclesOfDimension.project_eq_zero_of_mem_ne`), and the ones whose dimension
is `i + 2` are killed by hypothesis. -/
theorem c1Cycle_relations_le_ker {L : LineBundleData X} {dim : DimensionFunction X}
    {hcov : HomogeneityLocal.CovByDimension dim} {i : ℤ} (h : KillsRelations L dim hcov i) :
    (chowSystem dim (i + 1)).relations ≤ LinearMap.ker (c1Cycle L dim i) := by
  intro z hz
  have hz' : (z : AlgebraicCycle X ℚ) ∈ totalRationalRelations X dim := hz
  rw [totalRationalRelations, Submodule.mem_span_set'] at hz'
  obtain ⟨n, f, gg, hsum⟩ := hz'
  choose G hG using fun k ↦ (gg k).2
  have hzproj : z = cyclesOfDimension.projectLinear dim (i + 1) (z : AlgebraicCycle X ℚ) :=
    (cyclesOfDimension.project_coe z).symm
  have hsum' : (z : AlgebraicCycle X ℚ) = ∑ k : Fin n, f k • (G k).divisor dim := by
    rw [← hsum]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [← hG k])
  have hz_eq : z = ∑ k : Fin n,
      f k • cyclesOfDimension.projectLinear dim (i + 1) ((G k).divisor dim) := by
    rw [hzproj, hsum', map_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ LinearMap.map_smul _ _ _)
  rw [LinearMap.mem_ker, hz_eq, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [LinearMap.map_smul]
  by_cases hk : dim (G k).subspace.genericPointImage = i + 2
  · have hmem := RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov (G k)
      (show dim (G k).subspace.genericPointImage = (i + 1) + 1 by omega)
    have hproj : cyclesOfDimension.projectLinear dim (i + 1) ((G k).divisor dim) =
        ⟨(G k).divisor dim, hmem⟩ :=
      cyclesOfDimension.project_coe ⟨(G k).divisor dim, hmem⟩
    rw [hproj, h (G k) hk, smul_zero]
  · have hmem : (G k).divisor dim ∈
        cyclesOfDimension X dim (dim (G k).subspace.genericPointImage - 1) :=
      RationalFunctionGenerator.divisor_mem_cyclesOfDimension dim hcov (G k) (by omega)
    have hproj : cyclesOfDimension.projectLinear dim (i + 1) ((G k).divisor dim) = 0 :=
      cyclesOfDimension.project_eq_zero_of_mem_ne hmem (by omega)
    rw [hproj, map_zero, smul_zero]

/-- **Goal 3.** The first Chern class of `L`, on Chow groups: the descent of `c1Cycle` through
rational equivalence, granted `KillsRelations`. -/
noncomputable def c1 {L : LineBundleData X} {dim : DimensionFunction X}
    {hcov : HomogeneityLocal.CovByDimension dim} {i : ℤ} (h : KillsRelations L dim hcov i) :
    (chowSystem dim (i + 1)).ChowGroup →ₗ[ℚ] (chowSystem dim i).ChowGroup :=
  Submodule.liftQ (chowSystem dim (i + 1)).relations (c1Cycle L dim i)
    (c1Cycle_relations_le_ker h)

/-- **Goal 3, `c1_quotientMap_single`.** `c1` agrees with `c1Cycle` after taking classes. -/
theorem c1_quotientMap_single {L : LineBundleData X} {dim : DimensionFunction X}
    {hcov : HomogeneityLocal.CovByDimension dim} {i : ℤ} (h : KillsRelations L dim hcov i)
    (α : cyclesOfDimension X dim (i + 1)) :
    c1 h ((chowSystem dim (i + 1)).quotientMap α) = c1Cycle L dim i α :=
  Submodule.liftQ_apply (chowSystem dim (i + 1)).relations (c1Cycle L dim i) α

/-! ## Goal 4: formal properties -/

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The dimension-`i` projection of the indicator cycle at `x`: unlike `cyclesOfDimension.point`
this needs no side condition on `x`, which makes it the right building block for extensionality
arguments (`c1Cycle_ext`). -/
noncomputable def cyclesOfDimension.pointProj (dim : DimensionFunction X) (i : ℤ) (x : X) :
    cyclesOfDimension X dim i := by
  classical
  exact cyclesOfDimension.projectLinear dim i (Function.locallyFinsuppWithin.single x 1)

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
open Classical in
/-- The coefficient of `pointProj dim i x` at a point `y`. -/
theorem cyclesOfDimension.pointProj_apply {dim : DimensionFunction X} {i : ℤ} (x y : X) :
    (cyclesOfDimension.pointProj dim i x : AlgebraicCycle X ℚ) y =
      if x = y ∧ dim y = i then (1 : ℚ) else 0 := by
  change (cyclesOfDimension.project (dimension := dim) (i := i)
    (Function.locallyFinsuppWithin.single x 1) : AlgebraicCycle X ℚ) y = _
  rw [cyclesOfDimension.project_apply, Function.locallyFinsuppWithin.single_apply]
  by_cases hyi : dim y = i
  · rw [if_pos hyi]
    by_cases hxy : y = x
    · rw [if_pos hxy, if_pos ⟨hxy.symm, hyi⟩]
    · rw [if_neg hxy, if_neg (fun h ↦ hxy h.1.symm)]
  · rw [if_neg hyi, if_neg (fun h ↦ hyi h.2)]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- `pointProj` at a point of the right dimension agrees with `cyclesOfDimension.point`. -/
theorem cyclesOfDimension.pointProj_eq_point {dim : DimensionFunction X} {i : ℤ} {x : X}
    (h : dim x = i) :
    cyclesOfDimension.pointProj dim i x = cyclesOfDimension.point x h := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp only [cyclesOfDimension.pointProj_apply]
  by_cases hy : y = x
  · subst hy
    rw [if_pos ⟨rfl, h⟩, cyclesOfDimension.point_apply_self]
  · rw [if_neg (fun hh ↦ hy hh.1.symm), (cyclesOfDimension.point_apply_of_ne x y h hy).symm]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- `pointProj` at a point of the wrong dimension vanishes. -/
theorem cyclesOfDimension.pointProj_eq_zero_of_ne {dim : DimensionFunction X} {i : ℤ} {x : X}
    (h : dim x ≠ i) : cyclesOfDimension.pointProj dim i x = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp only [cyclesOfDimension.pointProj_apply, Submodule.coe_zero,
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  rw [if_neg (fun (hh : x = y ∧ dim y = i) ↦ h (hh.1 ▸ hh.2))]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] in
/-- **Decomposition.** A dimension-`i` graded cycle on a Noetherian scheme is the finite sum,
over its (finite) support, of its coefficients times the corresponding `pointProj`. Purely a fact
about the grading; no homogeneity/`hcov` hypothesis is needed. -/
theorem cyclesOfDimension.eq_sum_pointProj {dim : DimensionFunction X} {i : ℤ}
    (α : cyclesOfDimension X dim i) :
    α = ∑ x ∈ (finite_support_univ (α : AlgebraicCycle X ℚ)).toFinset,
      (α : AlgebraicCycle X ℚ) x • cyclesOfDimension.pointProj dim i x := by
  classical
  set S := (finite_support_univ (α : AlgebraicCycle X ℚ)).toFinset with hSdef
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp only [Submodule.coe_sum, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Function.locallyFinsuppWithin.coe_rational_smul, Pi.smul_apply,
    smul_eq_mul]
  simp_rw [cyclesOfDimension.pointProj_apply]
  by_cases hyi : dim y = i
  · have hcond : ∀ x : X, (x = y ∧ dim y = i) ↔ x = y := fun x ↦ by simp [hyi]
    simp_rw [hcond]
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl, mul_one]
    · intro x _ hxy
      rw [if_neg hxy, mul_zero]
    · intro hyS
      have hy0 : (α : AlgebraicCycle X ℚ) y = 0 := by
        by_contra hc
        exact hyS (hSdef ▸ (finite_support_univ (α : AlgebraicCycle X ℚ)).mem_toFinset.mpr hc)
      rw [if_pos rfl, mul_one, hy0]
  · have hcond2 : ∀ x : X, ¬ (x = y ∧ dim y = i) := fun _ h ↦ hyi h.2
    have hzero : ∀ x : X, (α : AlgebraicCycle X ℚ) x *
        (if x = y ∧ dim y = i then (1 : ℚ) else 0) = 0 := fun x ↦ by
      rw [if_neg (hcond2 x), mul_zero]
    rw [Finset.sum_congr rfl (fun x _ ↦ hzero x), Finset.sum_const_zero]
    exact α.2 y hyi

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] in
/-- **Extensionality for `c1Cycle`-shaped linear maps.** Two `ℚ`-linear maps out of
`cyclesOfDimension X dim (i + 1)` agreeing on every `pointProj` value are equal. -/
theorem c1Cycle_ext {N : Type*} [AddCommMonoid N] [Module ℚ N] {dim : DimensionFunction X}
    {i : ℤ} {f g : cyclesOfDimension X dim (i + 1) →ₗ[ℚ] N}
    (h : ∀ x : X, f (cyclesOfDimension.pointProj dim (i + 1) x) =
      g (cyclesOfDimension.pointProj dim (i + 1) x)) : f = g := by
  ext α
  rw [cyclesOfDimension.eq_sum_pointProj α, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun x _ ↦ by rw [map_smul, map_smul, h x])

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The divisor of the coordinate-`1` section of the trivial line bundle vanishes. -/
theorem trivial_divisor_eq_zero {V : IntegralClosedSubscheme X} (dim : DimensionFunction X)
    (j₀ : (LineBundleData.trivial X).J)
    (hj₀ : V.eta ∈ ((LineBundleData.trivial X).U j₀ : X.Opens)) :
    (⟨j₀, hj₀, 1⟩ : (LineBundleData.trivial X).RationalSection V).divisor dim = 0 := by
  have hdc : (⟨j₀, hj₀, 1⟩ : (LineBundleData.trivial X).RationalSection V).divisorCycle = 0 := by
    rw [LineBundleData.RationalSection.divisorCycle_trivial]
    exact _root_.AlgebraicGeometry.Scheme.principalCycle_one
  change AlgebraicCycle.map V.inclusion (fun z ↦ dim (V.inclusion.base z)) dim
    (⟨j₀, hj₀, 1⟩ : (LineBundleData.trivial X).RationalSection V).divisorCycle = 0
  rw [hdc]
  exact AlgebraicCycle.map_zero _ _ _

/-- **Goal 4, `c1Cycle_trivial`.** `c₁` of the trivial line bundle vanishes on cycles. -/
theorem c1Cycle_trivial (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (i : ℤ) : c1Cycle (LineBundleData.trivial X) dim i = 0 := by
  apply c1Cycle_ext
  intro x
  rw [LinearMap.zero_apply]
  by_cases hx : dim x = i + 1
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    obtain ⟨j₀, hj₀⟩ := (LineBundleData.trivial X).covers (pointSubscheme x).genericPointImage
    set s : (LineBundleData.trivial X).RationalSection (pointSubscheme x) := ⟨j₀, hj₀, 1⟩
      with hsdef
    rw [c1Cycle_single hcov hx s]
    have hz : (⟨s.divisor dim, s.divisor_mem_cyclesOfDimension dim hcov
        (by rw [genericPointImage_pointSubscheme]; exact hx)⟩ : cyclesOfDimension X dim i) = 0 :=
      Subtype.ext (trivial_divisor_eq_zero dim j₀ hj₀)
    rw [hz, map_zero]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero]

/-- **Goal 4.** `KillsRelations` holds trivially for the trivial line bundle. -/
theorem killsRelations_trivial (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ) :
    KillsRelations (LineBundleData.trivial X) dim hcov i := by
  intro g hg
  rw [c1Cycle_trivial dim hcov i, LinearMap.zero_apply]

/-- **Goal 4.** `c₁` of the trivial line bundle vanishes on Chow groups. -/
theorem c1_trivial (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (i : ℤ) : c1 (killsRelations_trivial dim hcov i) = 0 :=
  LinearMap.ext fun α ↦ Submodule.Quotient.induction_on _ α (fun β ↦ by
    change c1 (killsRelations_trivial dim hcov i) ((chowSystem dim (i + 1)).quotientMap β) =
      (0 : (chowSystem dim (i + 1)).ChowGroup →ₗ[ℚ] (chowSystem dim i).ChowGroup)
        ((chowSystem dim (i + 1)).quotientMap β)
    rw [c1_quotientMap_single, c1Cycle_trivial dim hcov i, LinearMap.zero_apply,
      LinearMap.zero_apply])

/-- **Goal 4, `c1Cycle_tensor`.** `c₁` of a tensor product of line bundles is additive on
cycles. -/
theorem c1Cycle_tensor (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (i : ℤ) (L : LineBundleData X) (M : LineBundleData.Cocycle L) :
    c1Cycle (L.tensor M) dim i = c1Cycle L dim i + c1Cycle M.toLineBundleData dim i := by
  apply c1Cycle_ext
  intro x
  rw [LinearMap.add_apply]
  by_cases hx : dim x = i + 1
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    obtain ⟨sL⟩ := LineBundleData.RationalSection.exists_rationalSection
      (L := L) (V := pointSubscheme x)
    obtain ⟨sM⟩ := LineBundleData.RationalSection.exists_rationalSection
      (L := M.toLineBundleData) (V := pointSubscheme x)
    have hxV : dim (pointSubscheme x).genericPointImage = i + 1 := by
      rw [genericPointImage_pointSubscheme]; exact hx
    have hdiv : (sL.tensor M sM).divisor dim = sL.divisor dim + sM.divisor dim := by
      change AlgebraicCycle.map (pointSubscheme x).inclusion
        (fun z ↦ dim ((pointSubscheme x).inclusion.base z)) dim
        (sL.tensor M sM).divisorCycle = _
      rw [sL.tensor_divisorCycle M sM]
      exact AlgebraicCycle.map_add _ _ _ _ _
    have heq : (⟨(sL.tensor M sM).divisor dim,
        (sL.tensor M sM).divisor_mem_cyclesOfDimension dim hcov hxV⟩ : cyclesOfDimension X dim i) =
        (⟨sL.divisor dim, sL.divisor_mem_cyclesOfDimension dim hcov hxV⟩ :
          cyclesOfDimension X dim i) +
        (⟨sM.divisor dim, sM.divisor_mem_cyclesOfDimension dim hcov hxV⟩ :
          cyclesOfDimension X dim i) :=
      Subtype.ext hdiv
    rw [c1Cycle_single hcov hx (sL.tensor M sM), c1Cycle_single hcov hx sL,
      c1Cycle_single hcov hx sM, heq, map_add]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero, map_zero, add_zero]

/-- **Goal 4.** `KillsRelations` is additive under tensor product. -/
theorem killsRelations_tensor (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ) (L : LineBundleData X)
    (M : LineBundleData.Cocycle L) (hL : KillsRelations L dim hcov i)
    (hM : KillsRelations M.toLineBundleData dim hcov i) :
    KillsRelations (L.tensor M) dim hcov i := by
  intro g hg
  rw [c1Cycle_tensor dim hcov i L M, LinearMap.add_apply, hL g hg, hM g hg, add_zero]

/-- **Goal 4.** `c₁` of a tensor product is additive on Chow groups. -/
theorem c1_tensor (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (i : ℤ) (L : LineBundleData X) (M : LineBundleData.Cocycle L)
    (hL : KillsRelations L dim hcov i) (hM : KillsRelations M.toLineBundleData dim hcov i) :
    c1 (killsRelations_tensor dim hcov i L M hL hM) = c1 hL + c1 hM :=
  LinearMap.ext fun α ↦ Submodule.Quotient.induction_on _ α (fun β ↦ by
    change c1 (killsRelations_tensor dim hcov i L M hL hM)
        ((chowSystem dim (i + 1)).quotientMap β) =
      (c1 hL + c1 hM) ((chowSystem dim (i + 1)).quotientMap β)
    rw [c1_quotientMap_single, LinearMap.add_apply, c1_quotientMap_single, c1_quotientMap_single,
      c1Cycle_tensor dim hcov i L M, LinearMap.add_apply])

/-! ## Goal 4, the dual bundle -/

namespace LineBundleData

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The transition unit of the dual bundle, restricted to `V`, is the inverse of `L`'s. -/
theorem dual_unitAt (L : LineBundleData X) (V : IntegralClosedSubscheme X) (j j' : L.J)
    (h : V.eta ∈ (L.U j : X.Opens) ⊓ (L.U j' : X.Opens)) :
    L.dual.unitAt V j j' h = (L.unitAt V j j' h)⁻¹ := by
  change Units.map (V.toFunctionField _ h).toMonoidHom (L.dual.g j j') = _
  have hg : L.dual.g j j' = (L.g j j')⁻¹ := rfl
  rw [hg, map_inv]
  rfl

end LineBundleData

namespace LineBundleData.RationalSection

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The dual of a rational section: same distinguished chart, coordinate inverted. -/
noncomputable def dual {L : LineBundleData X} {V : IntegralClosedSubscheme X}
    (s : L.RationalSection V) : L.dual.RationalSection V :=
  ⟨s.j₀, s.hj₀, s.f⁻¹⟩

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The coordinate of the dual section is the inverse of the coordinate of `s`. -/
theorem dual_coord {L : LineBundleData X} {V : IntegralClosedSubscheme X}
    (s : L.RationalSection V) (j : L.J) (hj : V.eta ∈ (L.U j : X.Opens)) :
    s.dual.coord j hj = (s.coord j hj)⁻¹ := by
  change L.dual.unitAt V j s.j₀ (memInf hj s.hj₀) * s.f⁻¹ = _
  rw [L.dual_unitAt V j s.j₀ (memInf hj s.hj₀), coord, mul_inv_rev, mul_comm]

end LineBundleData.RationalSection

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The order of vanishing of a unit inverse is the negative of the order of vanishing of the
unit. -/
theorem scheme_ord_inv {Y : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral Y]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian Y] (u : Y.functionFieldˣ) (y : Y) :
    Y.ord ((u⁻¹ : Y.functionFieldˣ) : Y.functionField) y = - Y.ord (u : Y.functionField) y := by
  have h1 : (u : Y.functionField) * ((u⁻¹ : Y.functionFieldˣ) : Y.functionField) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmul : Y.ord (u : Y.functionField) y + Y.ord ((u⁻¹ : Y.functionFieldˣ) : Y.functionField) y
      = 0 := by
    rw [← _root_.AlgebraicGeometry.Scheme.ord_mul (Units.ne_zero u) (Units.ne_zero u⁻¹), h1]
    exact congrFun _root_.AlgebraicGeometry.Scheme.ord_one y
  omega

namespace LineBundleData.RationalSection

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The order of the dual section is the negative of the order of `s`. -/
theorem dual_ord {L : LineBundleData X} {V : IntegralClosedSubscheme X} (s : L.RationalSection V)
    (y : V.scheme) : s.dual.ord y = - (s.ord y) := by
  obtain ⟨j, hzj⟩ := L.covers (V.inclusion.base y)
  have hj : V.eta ∈ (L.U j : X.Opens) := V.eta_mem_of_mem_preimage hzj
  rw [s.dual.ord_well_defined j y hzj, s.dual_coord j hj, scheme_ord_inv,
    ← s.ord_well_defined j y hzj]

omit [_root_.AlgebraicGeometry.IsLocallyNoetherian X] [NoetherianSpace X] in
/-- The divisor cycle of the dual section is the negative of the divisor cycle of `s`. -/
theorem dual_divisorCycle {L : LineBundleData X} {V : IntegralClosedSubscheme X}
    (s : L.RationalSection V) : s.dual.divisorCycle = - s.divisorCycle := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp [divisorCycle_apply, dual_ord]

end LineBundleData.RationalSection

/-- **Goal 4, `c1Cycle_dual`.** `c₁` of the dual line bundle is the negative on cycles. -/
theorem c1Cycle_dual (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim)
    (i : ℤ) (L : LineBundleData X) :
    c1Cycle L.dual dim i = - c1Cycle L dim i := by
  apply c1Cycle_ext
  intro x
  rw [LinearMap.neg_apply]
  by_cases hx : dim x = i + 1
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    obtain ⟨sL⟩ := LineBundleData.RationalSection.exists_rationalSection
      (L := L) (V := pointSubscheme x)
    have hxV : dim (pointSubscheme x).genericPointImage = i + 1 := by
      rw [genericPointImage_pointSubscheme]; exact hx
    have hdiv : sL.dual.divisor dim = - sL.divisor dim := by
      change AlgebraicCycle.mapLinear (pointSubscheme x).inclusion
        (fun z ↦ dim ((pointSubscheme x).inclusion.base z)) dim sL.dual.divisorCycle = _
      rw [sL.dual_divisorCycle, map_neg]
      rfl
    have heq : (⟨sL.dual.divisor dim, sL.dual.divisor_mem_cyclesOfDimension dim hcov hxV⟩ :
        cyclesOfDimension X dim i) =
        - (⟨sL.divisor dim, sL.divisor_mem_cyclesOfDimension dim hcov hxV⟩ :
          cyclesOfDimension X dim i) :=
      Subtype.ext hdiv
    rw [c1Cycle_single hcov hx sL.dual, c1Cycle_single hcov hx sL, heq, map_neg]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero, neg_zero]

/-- **Goal 4.** `KillsRelations` transfers to the dual bundle. -/
theorem killsRelations_dual (dim : DimensionFunction X)
    (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ) (L : LineBundleData X)
    (hL : KillsRelations L dim hcov i) : KillsRelations L.dual dim hcov i := by
  intro g hg
  rw [c1Cycle_dual dim hcov i L, LinearMap.neg_apply, hL g hg, neg_zero]

/-- **Goal 4.** `c₁` of the dual bundle is the negative on Chow groups. -/
theorem c1_dual (dim : DimensionFunction X) (hcov : HomogeneityLocal.CovByDimension dim) (i : ℤ)
    (L : LineBundleData X) (hL : KillsRelations L dim hcov i) :
    c1 (killsRelations_dual dim hcov i L hL) = - c1 hL :=
  LinearMap.ext fun α ↦ Submodule.Quotient.induction_on _ α (fun β ↦ by
    change c1 (killsRelations_dual dim hcov i L hL) ((chowSystem dim (i + 1)).quotientMap β) =
      (- c1 hL) ((chowSystem dim (i + 1)).quotientMap β)
    rw [c1_quotientMap_single, LinearMap.neg_apply, c1_quotientMap_single,
      c1Cycle_dual dim hcov i L, LinearMap.neg_apply])

end GromovWitten.AlgebraicGeometry.IntersectionTheory
