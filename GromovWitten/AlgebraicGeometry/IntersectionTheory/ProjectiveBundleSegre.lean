/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleRestrict
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassOpen
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardCurve
import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtaleBaseChange
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartedPullbackChow
import GromovWitten.AlgebraicGeometry.ProjectiveCompletionHyperplane
import GromovWitten.AlgebraicGeometry.ProjectiveCompletionTautological

/-!
# The Segre identity and the injectivity half of the projective bundle formula

Let `q : P ⟶ X` be a proper morphism with affine charts `𝒞 : AffineCharts q ι` (`ι` finite,
`r := Nat.card ι`), `X` locally of finite type over an infinite field `k` with Noetherian
underlying space, and `L` a line bundle on `P`.  Writing `q^* : A_i(X) → A_{i+r}(P)` for the
charted flat pullback `chowPullbackCharted`, `q_*` for `properPushforwardChowOfProper` and
`c₁(L)^m` for the iterated first Chern class `c1Iter`, this file proves, in general, the
vanishing `q_* (c₁(L)^m ∩ q^* α) = 0` for `m < r`, and the **Segre identity**
`q_* (c₁(L)^r ∩ q^* α) = α` under a "generic evaluation" hypothesis on the restrictions to the
integral closed subschemes `P ×_X V`.  For the projective completion `P(E ⊕ 1) ⟶ X` of a graded
vector bundle and `L = O(1)` this hypothesis is verified by an explicit chain of coordinate
points on the trivial piece over a point, using the chart orders of
`ProjectiveCompletionHyperplane.lean`.  The injectivity half of the projective bundle formula
follows by the triangular argument.

## Main results

* `chowCast`, `c1Iter` (with `c1Iter_zero`, `c1Iter_succ`, `c1Iter_succ'`, `c1Iter_c1Iter`,
  `c1Iter_chowCast`): transport along equalities of degrees and the iterated first Chern class
  `c₁(L)^m ∩ - : A_{i+m}(Y) →ₗ[ℚ] A_i(Y)`.
* `closedImmersionPushforward_c1Iter`, `openImmersionPullback_c1Iter`: the projection formula
  and the open-restriction compatibility for `c1Iter`.
* `evalGeneric`, `evalGeneric_injective`: evaluation at the generic point of an integral scheme
  `V` is a well-defined linear map `A_n(V) →ₗ[ℚ] ℚ`, injective in top degree `n = dim V`.
* `properPushforward_point_apply`, `pullbackOpen_map_pullback`: the pushforward of a point and
  the open restriction of a proper pushforward of cycles.
* `properPushforward_c1Iter_chowPullbackCharted_eq_zero_of_lt`: the vanishing
  `q_* (c₁(L)^m ∩ q^* α) = 0` for `m < r` (general charted proper `q`).
* `properPushforward_c1Iter_chowPullbackCharted_of_evalGeneric`,
  `evalGeneric_pushTopIterate_of_open`: the Segre identity from the generic evaluation of
  `(q_V)_* (c₁(L|_{P_V})^r ∩ [P_V])`, and that evaluation from an open piece of `P_V`.
* `projectiveBundleMap`, `projectiveBundleMap_injective_of_segre`: the projective bundle map
  `⨁_{m=0}^{r} A_{i+m-r}(X) → A_i(P)` and its injectivity from the Segre identity.
* `firstChernClassOfField_piecePoint`, `c1Iter_piecePoint`: the chain lemma
  `c₁(O(1)) ∩ [ζ_{S}] = [ζ_{insert t S}]` on the trivial piece of `P(E ⊕ 1)` over a point and its
  iterate `c₁(O(1))^{|S|} ∩ [ζ_∅] = [ζ_S]`.
* `properPushforward_c1Iter_chowPullbackCharted`,
  `properPushforward_c1Iter_chowPullbackCharted_eq_zero`, `projectiveBundleMap_injective`: the
  Segre identity, the vanishing and the injectivity half of the projective bundle formula for
  `P(E ⊕ 1) ⟶ X` with `L = O(1)` (`GradedBundleData.tautological`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

open FiniteTypeDimension

/-! ## Transport along equalities of degrees -/

section Cast

variable {Y : Scheme.{u}} {dim : DimensionFunction Y}

/-- Transport of the dimension-graded cycle groups along an equality of degrees. -/
noncomputable def cyclesCast {i i' : ℤ} (h : i = i') :
    cyclesOfDimension Y dim i ≃ₗ[ℚ] cyclesOfDimension Y dim i' :=
  LinearEquiv.ofEq _ _ (by rw [h])

/-- `cyclesCast` does not change the underlying cycle. -/
@[simp]
theorem cyclesCast_coe {i i' : ℤ} (h : i = i') (z : cyclesOfDimension Y dim i) :
    (cyclesCast h z : AlgebraicCycle Y ℚ) = z := rfl

/-- Transport of rational Chow groups along an equality of degrees. -/
noncomputable def chowCast {i i' : ℤ} (h : i = i') :
    (chowSystem dim i).ChowGroup ≃ₗ[ℚ] (chowSystem dim i').ChowGroup :=
  h ▸ LinearEquiv.refl ℚ _

/-- Point cycles may be rewritten along an equality of points. -/
theorem cyclesOfDimension.point_congr {i : ℤ} {y y' : Y} (h : y = y') (hy : dim y = i) :
    cyclesOfDimension.point y hy = cyclesOfDimension.point y' (h ▸ hy) := by
  subst h
  rfl

/-- The value of a point cycle at a point equal to its support is `1`. -/
theorem cyclesOfDimension.point_apply_of_eq {i : ℤ} {x y : Y} (hx : dim x = i) (h : y = x) :
    (cyclesOfDimension.point x hx : AlgebraicCycle Y ℚ) y = 1 := by
  subst h
  exact cyclesOfDimension.point_apply_self _ _

/-- `cyclesCast` of a point cycle is the point cycle. -/
@[simp]
theorem cyclesCast_point {i i' : ℤ} (h : i = i') (y : Y) (hy : dim y = i) :
    cyclesCast h (cyclesOfDimension.point y hy) = cyclesOfDimension.point y (hy.trans h) :=
  Subtype.ext rfl

/-- `chowCast` is induced by `cyclesCast`. -/
@[simp]
theorem chowCast_quotientMap {i i' : ℤ} (h : i = i') (z : cyclesOfDimension Y dim i) :
    chowCast h ((chowSystem dim i).quotientMap z) =
      (chowSystem dim i').quotientMap (cyclesCast h z) := by
  subst h
  rfl

/-- `chowCast` along `rfl` is the identity. -/
@[simp]
theorem chowCast_rfl {i : ℤ} : (chowCast (dim := dim) (rfl : i = i)) = LinearEquiv.refl ℚ _ :=
  rfl

/-- Two consecutive `chowCast`s compose to a `chowCast`. -/
theorem chowCast_chowCast {i i' i'' : ℤ} (h : i = i') (h' : i' = i'')
    (x : (chowSystem dim i).ChowGroup) :
    chowCast h' (chowCast h x) = chowCast (h.trans h') x := by
  subst h h'
  rfl

/-- `chowCast` commutes with `openImmersionPullback`. -/
theorem openImmersionPullback_chowCast {Y' : Scheme.{u}} (ψ : Y' ⟶ Y) [IsOpenImmersion ψ]
    {dim' : DimensionFunction Y'} (hdim : ∀ y, dim' y = dim (ψ.base y)) {i i' : ℤ} (h : i = i')
    (x : (chowSystem dim i).ChowGroup) :
    RationalEquivalenceSystem.DescendingMap.openImmersionPullback (chowSystem dim i') ψ hdim
        (chowSystem dim' i') (chowCast h x) =
      chowCast h (RationalEquivalenceSystem.DescendingMap.openImmersionPullback (chowSystem dim i)
        ψ hdim (chowSystem dim' i) x) := by
  subst h
  rfl

/-- `chowCast` commutes with `closedImmersionPushforward`. -/
theorem closedImmersionPushforward_chowCast {Z : Scheme.{u}} (ι : Z ⟶ Y) [IsClosedImmersion ι]
    {dimZ : DimensionFunction Z} {i i' : ℤ} (h : i = i') (x : (chowSystem dimZ i).ChowGroup) :
    RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward (chowSystem dimZ i') ι
        (chowSystem dim i') (chowCast h x) =
      chowCast h (RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (chowSystem dimZ i) ι (chowSystem dim i) x) := by
  subst h
  rfl

/-- `chowCast` commutes with `properPushforwardChowOfProper`. -/
theorem properPushforwardChowOfProper_chowCast {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] (sZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY] (dimZ : DimensionFunction Z)
    {i i' : ℤ} (h : i = i') (x : (chowSystem dimZ i).ChowGroup) :
    properPushforwardChowOfProper g sZ sY dimZ dim i' (chowCast h x) =
      chowCast h (properPushforwardChowOfProper g sZ sY dimZ dim i x) := by
  subst h
  rfl

end Cast

/-! ## Iterated first Chern classes -/

section Iter

variable {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace Y] (L : LineBundleData Y)

/-- **The iterated first Chern class** `c₁(L)^m ∩ - : A_{i+m}(Y) →ₗ[ℚ] A_i(Y)`. -/
noncomputable def c1Iter : (m : ℕ) → (i : ℤ) →
    (chowSystem (dimensionFunction f) (i + m)).ChowGroup →ₗ[ℚ]
      (chowSystem (dimensionFunction f) i).ChowGroup
  | 0, i => (chowCast (by simp)).toLinearMap
  | m + 1, i => (c1Iter m i).comp ((firstChernClassOfField f L (i + m)).comp
      (chowCast (by push_cast; ring)).toLinearMap)

/-- `c1Iter 0` is the identity (up to the cast `i + 0 = i`). -/
theorem c1Iter_zero (i : ℤ) : c1Iter f L 0 i = (chowCast (by simp)).toLinearMap := rfl

/-- The recursion of `c1Iter`. -/
theorem c1Iter_succ (m : ℕ) (i : ℤ) :
    c1Iter f L (m + 1) i = (c1Iter f L m i).comp ((firstChernClassOfField f L (i + m)).comp
      (chowCast (by push_cast; ring)).toLinearMap) := rfl

/-- `firstChernClassOfField` commutes with `chowCast`. -/
theorem firstChernClassOfField_chowCast {j j' l : ℤ} (h : j = j') (h' : l = j' + 1)
    (x : (chowSystem (dimensionFunction f) l).ChowGroup) :
    firstChernClassOfField f L j' (chowCast h' x) =
      chowCast h (firstChernClassOfField f L j (chowCast (h'.trans (by rw [h])) x)) := by
  subst h h'
  rfl

/-- `c1Iter` commutes with `chowCast`. -/
theorem c1Iter_chowCast (m : ℕ) {j j' l : ℤ} (h : j = j') (h' : l = j' + m)
    (x : (chowSystem (dimensionFunction f) l).ChowGroup) :
    c1Iter f L m j' (chowCast h' x) =
      chowCast h (c1Iter f L m j (chowCast (h'.trans (by rw [h])) x)) := by
  subst h h'
  rfl

/-- **Iterates of `c1Iter` compose**: `c₁^a ∩ (c₁^b ∩ x) = c₁^{a+b} ∩ x`. -/
theorem c1Iter_c1Iter (a b : ℕ) (j : ℤ)
    (x : (chowSystem (dimensionFunction f) (j + a + b)).ChowGroup) :
    c1Iter f L a j (c1Iter f L b (j + a) x) =
      c1Iter f L (a + b) j (chowCast (by push_cast; ring) x) := by
  induction b with
  | zero =>
    rw [c1Iter_zero, LinearEquiv.coe_coe]
    rfl
  | succ b ih =>
    rw [c1Iter_succ, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ih]
    change _ = c1Iter f L (a + b + 1) j (chowCast _ x)
    rw [c1Iter_succ, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      chowCast_chowCast, firstChernClassOfField_chowCast f L (j := j + a + b)
        (j' := j + (a + b : ℕ)) (by push_cast; ring)]

section Closed

variable {Z : Scheme.{u}} (ι : Z ⟶ Y) [IsClosedImmersion ι]

include ι in
/-- The source of a closed immersion into a scheme with Noetherian underlying space has
Noetherian underlying space. -/
theorem noetherianSpace_of_isClosedImmersion' : NoetherianSpace Z :=
  ι.isClosedEmbedding.isInducing.noetherianSpace

variable [NoetherianSpace Z]

/-- **The projection formula for `firstChernClassOfField`** along a closed immersion `ι : Z ⟶ Y`,
with `Z` given the canonical dimension function of `ι ≫ f`. -/
theorem closedImmersionPushforward_firstChernClassOfField (j : ℤ)
    (β : (chowSystem (dimensionFunction (ι ≫ f)) (j + 1)).ChowGroup) :
    RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (chowSystem (dimensionFunction (ι ≫ f)) j) ι (chowSystem (dimensionFunction f) j)
        (firstChernClassOfField (ι ≫ f) (L.restrict ι) j β) =
      firstChernClassOfField f L j
        (RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
          (chowSystem (dimensionFunction (ι ≫ f)) (j + 1)) ι
          (chowSystem (dimensionFunction f) (j + 1)) β) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f)
  exact closedImmersionPushforward_firstChernClass_restrict ι L _ _ _ _ j β

/-- **The projection formula for `c1Iter`** along a closed immersion:
`ι_* (c₁(L|_Z)^m ∩ β) = c₁(L)^m ∩ ι_* β`. -/
theorem closedImmersionPushforward_c1Iter (m : ℕ) (i : ℤ)
    (β : (chowSystem (dimensionFunction (ι ≫ f)) (i + m)).ChowGroup) :
    RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (chowSystem (dimensionFunction (ι ≫ f)) i) ι (chowSystem (dimensionFunction f) i)
        (c1Iter (ι ≫ f) (L.restrict ι) m i β) =
      c1Iter f L m i (RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
        (chowSystem (dimensionFunction (ι ≫ f)) (i + m)) ι
        (chowSystem (dimensionFunction f) (i + m)) β) := by
  induction m with
  | zero =>
    rw [c1Iter_zero, c1Iter_zero, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      closedImmersionPushforward_chowCast]
  | succ m ih =>
    rw [c1Iter_succ, c1Iter_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ih,
      closedImmersionPushforward_firstChernClassOfField, closedImmersionPushforward_chowCast]

end Closed

section Open

variable {Y' : Scheme.{u}} (ψ : Y' ⟶ Y) [IsOpenImmersion ψ]

/-- **`c1Iter` commutes with restriction to an open subscheme**:
`(c₁(L)^m ∩ β)|_{Y'} = c₁(L|_{Y'})^m ∩ β|_{Y'}`. -/
theorem openImmersionPullback_c1Iter [NoetherianSpace Y'] (m : ℕ) (i : ℤ)
    (β : (chowSystem (dimensionFunction f) (i + m)).ChowGroup) :
    RationalEquivalenceSystem.DescendingMap.openImmersionPullback
        (chowSystem (dimensionFunction f) i) ψ (fun y ↦ dimensionFunction_comp f ψ y)
        (chowSystem (dimensionFunction (ψ ≫ f)) i) (c1Iter f L m i β) =
      c1Iter (ψ ≫ f) (L.pullback ψ) m i
        (RationalEquivalenceSystem.DescendingMap.openImmersionPullback
          (chowSystem (dimensionFunction f) (i + m)) ψ (fun y ↦ dimensionFunction_comp f ψ y)
          (chowSystem (dimensionFunction (ψ ≫ f)) (i + m)) β) := by
  induction m with
  | zero =>
    rw [c1Iter_zero, c1Iter_zero, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      openImmersionPullback_chowCast]
  | succ m ih =>
    rw [c1Iter_succ, c1Iter_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ih,
      openImmersionPullback_firstChernClassOfField, openImmersionPullback_chowCast]

end Open

end Iter

/-! ## Evaluation at the generic point of an integral scheme -/

section Generic

variable {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [NoetherianSpace V]
  (dim : DimensionFunction V) (hcov : HomogeneityLocal.CovByDimension dim)

include hcov in
/-- Every principal divisor on an integral scheme vanishes at the generic point. -/
theorem totalRationalRelations_apply_genericPoint {z : AlgebraicCycle V ℚ}
    (hz : z ∈ totalRationalRelations V dim) : z (genericPoint V) = 0 := by
  refine Submodule.span_induction (p := fun z _ ↦ z (genericPoint V) = 0) ?_ rfl ?_ ?_ hz
  · rintro _ ⟨g, rfl⟩
    by_cases hw : g.subspace.genericPointImage ⤳ genericPoint V
    · have he : g.subspace.genericPointImage = genericPoint V :=
        (hw.antisymm ((genericPoint_spec V).specializes (Set.mem_univ _))).eq
      rw [RationalFunctionGenerator.divisor_apply_eq_pointOrd dim g rfl hw,
        pointOrd_eq_zero_of_dim_ne dim hcov hw (by rw [he]; omega)]
      simp
    · unfold RationalFunctionGenerator.divisor IntegralClosedSubscheme.pushforward
      refine AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range _ (dim : V → ℤ) _ _ ?_
      rintro ⟨q, hq⟩
      exact hw (hq ▸ g.subspace.genericPointImage_specializes q)
  · intro a b _ _ ha hb
    simp [ha, hb]
  · intro c a _ ha
    simp [ha]

/-- Evaluation of a cycle at the generic point of `V`, as a linear map. -/
noncomputable def evalGenericCycle (i : ℤ) : cyclesOfDimension V dim i →ₗ[ℚ] ℚ where
  toFun z := (z : AlgebraicCycle V ℚ) (genericPoint V)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Evaluation at the generic point** `A_i(V) →ₗ[ℚ] ℚ`, `[z] ↦ z (η_V)`, well defined because
principal divisors vanish at the generic point. -/
noncomputable def evalGeneric (i : ℤ) : (chowSystem dim i).ChowGroup →ₗ[ℚ] ℚ :=
  Submodule.liftQ _ (evalGenericCycle dim i) (by
    intro z hz
    exact totalRationalRelations_apply_genericPoint dim hcov hz)

/-- `evalGeneric` on the class of a cycle. -/
@[simp]
theorem evalGeneric_quotientMap (i : ℤ) (z : cyclesOfDimension V dim i) :
    evalGeneric dim hcov i ((chowSystem dim i).quotientMap z) =
      (z : AlgebraicCycle V ℚ) (genericPoint V) :=
  Submodule.liftQ_apply _ _ z

/-- `evalGeneric` of the class of the generic point is `1`. -/
theorem evalGeneric_point_genericPoint (i : ℤ) (h : dim (genericPoint V) = i) :
    evalGeneric dim hcov i ((chowSystem dim i).quotientMap
      (cyclesOfDimension.point (genericPoint V) h)) = 1 := by
  rw [evalGeneric_quotientMap, cyclesOfDimension.point_apply_self]

omit [IsLocallyNoetherian V] [NoetherianSpace V] in
/-- A point of `V` of the same dimension as the generic point is the generic point. -/
theorem eq_genericPoint_of_dim_eq {x : V} (h : dim x = dim (genericPoint V)) :
    x = genericPoint V := by
  by_contra hne
  have hsp : genericPoint V ⤳ x := (genericPoint_spec V).specializes (Set.mem_univ _)
  have := ProperPushforwardDivisor.dim_lt_of_specializes dim hsp (Ne.symm hne)
  omega

/-- **Injectivity of `evalGeneric` in top degree**: for `n := dim η_V`, every cycle of dimension
`n` is a multiple of the generic point, so `evalGeneric` is injective on `A_n(V)`. -/
theorem evalGeneric_injective :
    Function.Injective (evalGeneric dim hcov (dim (genericPoint V))) := by
  intro a b hab
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  change (chowSystem dim _).quotientMap z = (chowSystem dim _).quotientMap w
  have hz : z = (z : AlgebraicCycle V ℚ) (genericPoint V) •
      cyclesOfDimension.point (genericPoint V) rfl := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    by_cases hx : x = genericPoint V
    · subst hx
      simp
    · have hd : dim x ≠ dim (genericPoint V) := fun h ↦ hx (eq_genericPoint_of_dim_eq dim h)
      simp [z.2 x hd, hx]
  have hw : w = (w : AlgebraicCycle V ℚ) (genericPoint V) •
      cyclesOfDimension.point (genericPoint V) rfl := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext x
    by_cases hx : x = genericPoint V
    · subst hx
      simp
    · have hd : dim x ≠ dim (genericPoint V) := fun h ↦ hx (eq_genericPoint_of_dim_eq dim h)
      simp [w.2 x hd, hx]
  change evalGeneric dim hcov _ ((chowSystem dim _).quotientMap z) =
    evalGeneric dim hcov _ ((chowSystem dim _).quotientMap w) at hab
  rw [evalGeneric_quotientMap, evalGeneric_quotientMap] at hab
  rw [hz, hw, hab]

end Generic

/-! ## Pushforward of a single point and open restriction of pushforwards -/

section Pushforward

variable {Z W : Scheme.{u}} {dimZ : DimensionFunction Z} {dimW : DimensionFunction W}

open Classical in
/-- The pushforward of a single point along a proper morphism: a single point at the image, with
coefficient `mapCoeff` (the residue degree when the dimensions agree, else `0`). -/
theorem properPushforward_point_apply (g : Z ⟶ W) [IsProper g] {i : ℤ} (z : Z)
    (hz : dimZ z = i) (y : W) :
    ((cyclesOfDimension.properPushforward (dimensionY := dimW) g
      (cyclesOfDimension.point z hz) : cyclesOfDimension W dimW i) : AlgebraicCycle W ℚ) y =
      if g.base z = y then (AlgebraicCycle.mapCoeff g dimZ dimW z : ℚ) else 0 := by
  rw [cyclesOfDimension.properPushforward_apply, finsum_mem_def, finsum_eq_single _ z]
  · by_cases hy : g.base z = y
    · rw [if_pos hy, Set.indicator_of_mem (show z ∈ g.base ⁻¹' {y} from hy),
        cyclesOfDimension.point_apply_self, one_mul]
    · rw [if_neg hy, Set.indicator_of_notMem (show z ∉ g.base ⁻¹' {y} from hy)]
  · intro x hx
    simp [Set.indicator, cyclesOfDimension.point_apply_of_ne _ _ _ hx]

/-- `mapCoeff` at a point of residue degree one whose dimension is preserved is `1`. -/
theorem mapCoeff_eq_one (g : Z ⟶ W) (z : Z) (hd : dimZ z = dimW (g.base z))
    (hres : g.residueDegree z = 1) :
    AlgebraicCycle.mapCoeff g dimZ dimW z = 1 := by
  simp [AlgebraicCycle.mapCoeff, hd, hres]

/-- **Open restriction of a proper pushforward of cycles.**  For `g : Z ⟶ W` quasi-compact and
`ψ : W' ⟶ W` an open immersion, restricting `g_* c` along `ψ` is the pushforward along
`pullback.snd g ψ` of the restriction of `c` along `pullback.fst g ψ`. -/
theorem pullbackOpen_map_pullback (g : Z ⟶ W) [QuasiCompact g] {W' : Scheme.{u}} (ψ : W' ⟶ W)
    [IsOpenImmersion ψ] (dZ : Z → ℤ) (dW : W → ℤ) (dZ' : ↑(pullback g ψ) → ℤ) (dW' : W' → ℤ)
    (hZ' : ∀ u, dZ' u = dZ (pullback.fst g ψ u)) (hW' : ∀ v, dW' v = dW (ψ.base v))
    (c : AlgebraicCycle Z ℚ) :
    AlgebraicCycle.pullbackOpen ψ (AlgebraicCycle.map g dZ dW c) =
      AlgebraicCycle.map (pullback.snd g ψ) dZ' dW'
        (AlgebraicCycle.pullbackOpen (pullback.fst g ψ) c) := by
  rw [← AlgebraicCycle.pullbackEtale_eq_pullbackOpen,
    ← AlgebraicCycle.pullbackEtale_eq_pullbackOpen]
  exact pullbackEtale_map g ψ dZ dW dZ' dW' hZ' hW' c

end Pushforward

/-! ## The Segre identity from the generic evaluation of the top iterate -/

section Segre

open RationalEquivalenceSystem.DescendingMap ChartedOverSubscheme LineBundleInjective

variable {k : Type u} [Field k] {P X : Scheme.{u}} {q : P ⟶ X} [IsProper q]
  {ι : Type u} (𝒞 : AffineCharts q ι) (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X]

omit [IsProper q] in
/-- The underlying space of an integral closed subscheme of a Noetherian space is Noetherian. -/
instance noetherianSpace_integralClosedSubscheme_scheme (V : IntegralClosedSubscheme X) :
    NoetherianSpace V.scheme :=
  V.inclusion.isClosedEmbedding.isInducing.noetherianSpace

omit [IsProper q] [NoetherianSpace X] in
/-- The underlying space of the restriction `P ×_X V` is Noetherian. -/
instance noetherianSpace_restrictScheme [NoetherianSpace P] (V : IntegralClosedSubscheme X) :
    NoetherianSpace (restrictScheme 𝒞 V) :=
  (restrictι 𝒞 V).isClosedEmbedding.isInducing.noetherianSpace

omit [NoetherianSpace X] in
/-- The projection `P ×_X V ⟶ V` is proper, as a base change of `q`. -/
instance isProper_restrictProj (V : IntegralClosedSubscheme X) : IsProper (restrictProj 𝒞 V) :=
  MorphismProperty.of_isPullback (isPullback_restrict 𝒞 V) inferInstance

omit [NoetherianSpace X] in
/-- Any element of a rational Chow group in a degree not attained by the dimension function
vanishes. -/
theorem chowGroup_eq_zero_of_forall_dim_ne {Y : Scheme.{u}} {dim : DimensionFunction Y} {j : ℤ}
    (h : ∀ y : Y, dim y ≠ j) (a : (chowSystem dim j).ChowGroup) : a = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have hz : z = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext y
    exact z.2 y (h y)
  rw [hz, Submodule.Quotient.mk_zero]

omit [NoetherianSpace X] in
/-- The cycle-level proper pushforward only depends on the morphism, so it may be rewritten
along an equality of morphisms. -/
theorem properPushforward_congr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} [IsProper g] [IsProper g']
    (h : g = g') {dimZ : DimensionFunction Z} {dimY : DimensionFunction Y} {i : ℤ} :
    cyclesOfDimension.properPushforward (dimension := dimZ) (dimensionY := dimY) (i := i) g =
      cyclesOfDimension.properPushforward g' := by
  subst h
  rfl

omit [NoetherianSpace X] in
/-- `properPushforwardChowOfProper` only depends on the morphism (not on the proof that it is
proper), so it may be rewritten along an equality of morphisms. -/
theorem properPushforwardChowOfProper_congr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} [IsProper g]
    [IsProper g'] (h : g = g') (sZ : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sZ]
    (sY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sY] (dimZ : DimensionFunction Z)
    (dimY : DimensionFunction Y) (i : ℤ) :
    properPushforwardChowOfProper g sZ sY dimZ dimY i =
      properPushforwardChowOfProper g' sZ sY dimZ dimY i := by
  subst h
  rfl

variable (hshift : ∀ x, dimensionFunction (q ≫ f) (𝒞.fibrePoint x) =
    dimensionFunction f x + (Nat.card ι : ℤ))

omit [NoetherianSpace X] in
include hshift in
/-- The dimension of the generic point of `P ×_X V` is the dimension of `V` plus the rank. -/
theorem dim_genericPoint_restrictScheme (V : IntegralClosedSubscheme X) :
    dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)) (genericPoint (restrictScheme 𝒞 V)) =
      dimensionFunction f V.genericPointImage + (Nat.card ι : ℤ) := by
  rw [DimensionFunction.apply_eq_of_isClosedImmersion _ (dimensionFunction (q ≫ f))
    (restrictι 𝒞 V), restrictι_genericPoint, hshift]

omit [NoetherianSpace X] in
/-- The dimension of the generic point of `V` is the dimension of its image in `X`. -/
theorem dim_genericPoint_scheme (V : IntegralClosedSubscheme X) :
    dimensionFunction (V.inclusion ≫ f) (genericPoint V.scheme) =
      dimensionFunction f V.genericPointImage :=
  DimensionFunction.apply_eq_of_isClosedImmersion _ (dimensionFunction f) V.inclusion _

omit [NoetherianSpace X] in
/-- Every point of `V` has dimension at most the dimension of `V`. -/
theorem dim_le_of_integralClosedSubscheme (V : IntegralClosedSubscheme X) (v : V.scheme) :
    dimensionFunction (V.inclusion ≫ f) v ≤ dimensionFunction f V.genericPointImage := by
  rw [← dim_genericPoint_scheme]
  exact dimensionFunction_le_of_specializes _ ((genericPoint_spec V.scheme).specializes
    (Set.mem_univ v))

omit [NoetherianSpace X] in
/-- The class of the generic point of `P ×_X V`, in degree `dim V + rank`. -/
noncomputable def genericRestrictClass (V : IntegralClosedSubscheme X) :
    (chowSystem (dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)))
      (dimensionFunction f V.genericPointImage + (Nat.card ι : ℤ))).ChowGroup :=
  (chowSystem _ _).quotientMap (cyclesOfDimension.point (genericPoint (restrictScheme 𝒞 V))
    (dim_genericPoint_restrictScheme 𝒞 f hshift V))

variable [Infinite k] [Finite ι] [IsLocallyNoetherian X] [NoetherianSpace P] (L : LineBundleData P)

omit [NoetherianSpace X] [Infinite k] [Finite ι] [IsLocallyNoetherian X] [NoetherianSpace P] in
/-- **Proper pushforward along `q` after pushforward from `P ×_X V`** is pushforward along
`V.inclusion` after pushforward along `P ×_X V ⟶ V`. -/
theorem properPushforwardChowOfProper_closedImmersionPushforward_restrictι
    (V : IntegralClosedSubscheme X) (l : ℤ)
    (y : (chowSystem (dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f))) l).ChowGroup) :
    properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f))
        (dimensionFunction f) l
        (closedImmersionPushforward (chowSystem _ l) (restrictι 𝒞 V) (chowSystem _ l) y) =
      closedImmersionPushforward (chowSystem (dimensionFunction (V.inclusion ≫ f)) l)
        V.inclusion (chowSystem _ l)
        (properPushforwardChowOfProper (restrictProj 𝒞 V) (restrictι 𝒞 V ≫ (q ≫ f))
          (V.inclusion ≫ f) (dimensionFunction _) (dimensionFunction _) l y) := by
  obtain ⟨z⟩ := y
  change (chowSystem _ l).quotientMap (cyclesOfDimension.properPushforward q
      (cyclesOfDimension.properPushforward (restrictι 𝒞 V) z)) =
    (chowSystem _ l).quotientMap (cyclesOfDimension.properPushforward V.inclusion
      (cyclesOfDimension.properPushforward (restrictProj 𝒞 V) z))
  have e1 := LinearMap.congr_fun (cyclesOfDimension.properPushforward_comp
    (dimension := dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)))
    (dimensionY := dimensionFunction (q ≫ f)) (dimensionZ := dimensionFunction f) (i := l)
    (restrictι 𝒞 V) q) z
  have e2 := LinearMap.congr_fun (cyclesOfDimension.properPushforward_comp
    (dimension := dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)))
    (dimensionY := dimensionFunction (V.inclusion ≫ f)) (dimensionZ := dimensionFunction f)
    (i := l) (restrictProj 𝒞 V) V.inclusion) z
  rw [LinearMap.comp_apply] at e1 e2
  refine (congrArg (chowSystem (dimensionFunction f) l).quotientMap e1.symm).trans
    ((congrArg (chowSystem (dimensionFunction f) l).quotientMap ?_).trans
      (congrArg (chowSystem (dimensionFunction f) l).quotientMap e2))
  have hc : restrictι 𝒞 V ≫ q = restrictProj 𝒞 V ≫ V.inclusion :=
    pullback.condition (f := q) (g := V.inclusion)
  exact LinearMap.congr_fun (properPushforward_congr
    (dimZ := dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f))) (dimY := dimensionFunction f)
    (i := l) hc) z

omit [Infinite k] [NoetherianSpace P] in
include hshift in
/-- The flat pullback of the class of a point `x` is the pushforward of the class of the
generic point of `P ×_X pointSubscheme x`. -/
theorem chowPullbackCharted_point {i : ℤ} (x : X) (hx : dimensionFunction f x = i) :
    chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
        (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ)))
        ((chowSystem (dimensionFunction f) i).quotientMap (cyclesOfDimension.point x hx)) =
      closedImmersionPushforward (chowSystem (dimensionFunction
          (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f))) (i + (Nat.card ι : ℤ)))
        (restrictι 𝒞 (pointSubscheme x)) (chowSystem _ (i + (Nat.card ι : ℤ)))
        (chowCast (by rw [genericPointImage_pointSubscheme, hx])
          (genericRestrictClass 𝒞 f hshift (pointSubscheme x))) := by
  rw [chowPullbackCharted_quotientMap, genericRestrictClass, chowCast_quotientMap,
    cyclesCast_point, closedImmersionPushforward_quotientMap,
    properPushforward_point_of_isClosedImmersion]
  congr 1
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  beta_reduce
  rw [AffineCharts.flatPullbackCharted_apply]
  have hg : (restrictι 𝒞 (pointSubscheme x)).base
      (genericPoint (restrictScheme 𝒞 (pointSubscheme x))) = 𝒞.fibrePoint x := by
    rw [restrictι_genericPoint]
    exact congrArg _ (genericPointImage_pointSubscheme x)
  by_cases hp : p = (restrictι 𝒞 (pointSubscheme x)).base
      (genericPoint (restrictScheme 𝒞 (pointSubscheme x)))
  · subst hp
    rw [cyclesOfDimension.point_apply_self]
    conv_lhs => rw [hg]
    rw [AffineCharts.pullbackCharted_apply_fibrePoint, cyclesOfDimension.point_apply_self]
  · rw [cyclesOfDimension.point_apply_of_ne _ _ _ hp]
    by_cases hr : p ∈ Set.range (𝒞.fibrePoint)
    · obtain ⟨y, rfl⟩ := hr
      rw [AffineCharts.pullbackCharted_apply_fibrePoint]
      exact cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hp (by rw [h, hg]))
    · exact AffineCharts.pullbackCharted_eq_zero_of_notMem 𝒞 _ hr

include hshift in
/-- `q_* ∘ c₁(L)^m ∘ q^*` on the class of a point `x` factors through the restriction to
`V := pointSubscheme x`: it is the pushforward along `V.inclusion` of
`(q_V)_* (c₁(L|_{P_V})^m ∩ [P_V])`. -/
theorem properPushforward_c1Iter_chowPullbackCharted_point (m : ℕ) {i j : ℤ}
    (hj : j + m = i + (Nat.card ι : ℤ)) (x : X) (hx : dimensionFunction f x = i) :
    properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f)) (dimensionFunction f)
        j (c1Iter (q ≫ f) L m j (chowCast hj.symm
          (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
            (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ)))
            ((chowSystem (dimensionFunction f) i).quotientMap
              (cyclesOfDimension.point x hx))))) =
      closedImmersionPushforward (chowSystem (dimensionFunction ((pointSubscheme x).inclusion ≫ f))
          j) (pointSubscheme x).inclusion (chowSystem _ _)
        (properPushforwardChowOfProper (restrictProj 𝒞 (pointSubscheme x))
          (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f)) ((pointSubscheme x).inclusion ≫ f)
          (dimensionFunction _) (dimensionFunction _) j
          (c1Iter (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f))
            (L.restrict (restrictι 𝒞 (pointSubscheme x))) m j
            (chowCast (by rw [genericPointImage_pointSubscheme, hx, hj])
              (genericRestrictClass 𝒞 f hshift (pointSubscheme x))))) := by
  rw [chowPullbackCharted_point 𝒞 f hshift x hx]
  rw [← closedImmersionPushforward_chowCast, chowCast_chowCast,
    ← closedImmersionPushforward_c1Iter,
    properPushforwardChowOfProper_closedImmersionPushforward_restrictι]

include hshift in
/-- **Vanishing of the lower Segre terms**: for `m < rank`, `q_* (c₁(L)^m ∩ q^* α) = 0`. -/
theorem properPushforward_c1Iter_chowPullbackCharted_eq_zero_of_lt (m : ℕ) (hm : m < Nat.card ι)
    {i j : ℤ} (hj : j + m = i + (Nat.card ι : ℤ))
    (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f)) (dimensionFunction f)
        j (c1Iter (q ≫ f) L m j (chowCast hj.symm
          (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
            (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ))) α))) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f))
    (dimensionFunction f) j
    (c1Iter (q ≫ f) L m j (chowCast hj.symm
      (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
        (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ)))
        ((chowSystem (dimensionFunction f) i).quotientMap z)))) = 0
  rw [cyclesOfDimension.eq_sum_pointProj z]
  simp only [map_sum, map_smul]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  by_cases hx : dimensionFunction f x = i
  · rw [cyclesOfDimension.pointProj_eq_point hx,
      properPushforward_c1Iter_chowPullbackCharted_point 𝒞 f hshift L m hj x hx]
    have h0 : ∀ a : (chowSystem (dimensionFunction ((pointSubscheme x).inclusion ≫ f))
        j).ChowGroup, a = 0 := by
      refine chowGroup_eq_zero_of_forall_dim_ne fun v hv ↦ ?_
      have := dim_le_of_integralClosedSubscheme f (pointSubscheme x) v
      rw [genericPointImage_pointSubscheme, hx] at this
      omega
    rw [h0 (properPushforwardChowOfProper (restrictProj 𝒞 (pointSubscheme x))
      (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f)) ((pointSubscheme x).inclusion ≫ f)
      (dimensionFunction _) (dimensionFunction _) j _), map_zero, smul_zero]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx]
    simp only [map_zero, smul_zero]

include hshift in
/-- **The Segre identity, from the generic evaluation of the top iterate.**  If for every point
`x` of dimension `i`, with `V := pointSubscheme x`, the class
`(q_V)_* (c₁(L|_{P_V})^r ∩ [P_V]) ∈ A_i(V)` evaluates to `1` at the generic point of `V`, then
`q_* (c₁(L)^r ∩ q^* α) = α` for every `α ∈ A_i(X)`. -/
theorem properPushforward_c1Iter_chowPullbackCharted_of_evalGeneric (i : ℤ)
    (hkey : ∀ x : X, (hx : dimensionFunction f x = i) →
      evalGeneric (dimensionFunction ((pointSubscheme x).inclusion ≫ f))
        (covByDimension_finiteTypeDimension _) i
        (properPushforwardChowOfProper (restrictProj 𝒞 (pointSubscheme x))
          (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f)) ((pointSubscheme x).inclusion ≫ f)
          (dimensionFunction _) (dimensionFunction _) i
          (c1Iter (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f))
            (L.restrict (restrictι 𝒞 (pointSubscheme x))) (Nat.card ι) i
            (chowCast (by rw [genericPointImage_pointSubscheme, hx])
              (genericRestrictClass 𝒞 f hshift (pointSubscheme x))))) = 1)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f)) (dimensionFunction f)
        i (c1Iter (q ≫ f) L (Nat.card ι) i
          (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
            (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ))) α)) = α := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  change properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f))
    (dimensionFunction f) i
    (c1Iter (q ≫ f) L (Nat.card ι) i
      (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift i
        (chowSystem _ i) (chowSystem _ (i + (Nat.card ι : ℤ)))
        ((chowSystem (dimensionFunction f) i).quotientMap z))) =
    (chowSystem (dimensionFunction f) i).quotientMap z
  rw [cyclesOfDimension.eq_sum_pointProj z]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : dimensionFunction f x = i
  · rw [cyclesOfDimension.pointProj_eq_point hx]
    congr 1
    have h := properPushforward_c1Iter_chowPullbackCharted_point 𝒞 f hshift L (Nat.card ι)
      (i := i) (j := i) rfl x hx
    rw [chowCast_rfl, LinearEquiv.refl_apply] at h
    rw [h]
    have hgen : dimensionFunction ((pointSubscheme x).inclusion ≫ f)
        (genericPoint (pointSubscheme x).scheme) = i := by
      rw [dim_genericPoint_scheme, genericPointImage_pointSubscheme, hx]
    have h2 := evalGeneric_injective (dimensionFunction ((pointSubscheme x).inclusion ≫ f))
      (covByDimension_finiteTypeDimension _)
    rw [hgen] at h2
    have h3 : properPushforwardChowOfProper (restrictProj 𝒞 (pointSubscheme x))
        (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f)) ((pointSubscheme x).inclusion ≫ f)
        (dimensionFunction _) (dimensionFunction _) i
        (c1Iter (restrictι 𝒞 (pointSubscheme x) ≫ (q ≫ f))
          (L.restrict (restrictι 𝒞 (pointSubscheme x))) (Nat.card ι) i
          (chowCast (by rw [genericPointImage_pointSubscheme, hx])
            (genericRestrictClass 𝒞 f hshift (pointSubscheme x)))) =
        (chowSystem _ i).quotientMap
          (cyclesOfDimension.point (genericPoint (pointSubscheme x).scheme) hgen) := by
      apply h2
      rw [hkey x hx, evalGeneric_point_genericPoint]
    rw [h3, closedImmersionPushforward_quotientMap, properPushforward_point_of_isClosedImmersion]
    congr 1
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.coe_injective
    funext y
    beta_reduce
    have hη : (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme) = x :=
      genericPointImage_pointSubscheme x
    by_cases hy : y = x
    · rw [cyclesOfDimension.point_apply_of_eq _ hy,
        cyclesOfDimension.point_apply_of_eq _ (hy.trans hη.symm)]
    · rw [cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hy (h.trans hη)),
        cyclesOfDimension.point_apply_of_ne _ _ _ hy]
  · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx]
    simp only [map_zero, smul_zero]

end Segre

/-! ## Evaluating the top iterate on an open subscheme of `V` -/

section OpenEval

open RationalEquivalenceSystem.DescendingMap ChartedOverSubscheme

/-- An open immersion of integral schemes sends the generic point to the generic point. -/
theorem base_genericPoint_of_isOpenImmersion {W Y : Scheme.{u}} (ψ : W ⟶ Y) [IsOpenImmersion ψ]
    [IsIntegral W] [IsIntegral Y] : ψ.base (genericPoint W) = genericPoint Y := by
  have h1 : genericPoint Y ⤳ ψ.base (genericPoint W) :=
    (genericPoint_spec Y).specializes (Set.mem_univ _)
  have hmem : genericPoint Y ∈ Set.range ψ.base := by
    rw [(genericPoint_spec Y).mem_open_set_iff ψ.isOpenEmbedding.isOpen_range]
    exact ⟨ψ.base (genericPoint W), Set.mem_univ _, ⟨_, rfl⟩⟩
  obtain ⟨w, hw⟩ := hmem
  have h2 : ψ.base (genericPoint W) ⤳ genericPoint Y := by
    rw [← hw]
    exact ((genericPoint_spec W).specializes (Set.mem_univ w)).map ψ.continuous
  exact (h2.antisymm h1).eq

variable {k : Type u} [Field k] [Infinite k] {P X : Scheme.{u}} {q : P ⟶ X} [IsProper q]
  {ι : Type u} [Finite ι] (𝒞 : AffineCharts q ι) (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] [NoetherianSpace P]
  (hshift : ∀ x, dimensionFunction (q ≫ f) (𝒞.fibrePoint x) =
    dimensionFunction f x + (Nat.card ι : ℤ))
  (L : LineBundleData P) (V : IntegralClosedSubscheme X) {W : Scheme.{u}} (ψ : W ⟶ V.scheme)
  [IsOpenImmersion ψ] [IsIntegral W]

/-- The restriction `P_V ×_V W` of `P ×_X V` to the open subscheme `W` of `V`. -/
noncomputable abbrev restrictOpen : Scheme.{u} := pullback (restrictProj 𝒞 V) ψ

/-- The open immersion `P_V ×_V W ⟶ P_V`. -/
noncomputable abbrev restrictOpenι : restrictOpen 𝒞 V ψ ⟶ restrictScheme 𝒞 V :=
  pullback.fst (restrictProj 𝒞 V) ψ

/-- The projection `P_V ×_V W ⟶ W`. -/
noncomputable abbrev restrictOpenProj : restrictOpen 𝒞 V ψ ⟶ W := pullback.snd (restrictProj 𝒞 V) ψ

/-- The line bundle on `P_V ×_V W` obtained from `L` by restriction to `P_V` and pullback along
the open immersion. -/
noncomputable abbrev restrictOpenBundle : LineBundleData (restrictOpen 𝒞 V ψ) :=
  (L.restrict (restrictι 𝒞 V)).pullback (restrictOpenι 𝒞 V ψ)

omit [Infinite k] [Finite ι] [IsLocallyNoetherian X] [NoetherianSpace X] [IsIntegral W]
  [NoetherianSpace P] in
/-- The dimension functions of `P_V ×_V W` and `P_V` are compatible. -/
theorem dim_restrictOpenι (u : restrictOpen 𝒞 V ψ) :
    dimensionFunction (restrictOpenι 𝒞 V ψ ≫ (restrictι 𝒞 V ≫ (q ≫ f))) u =
      dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)) ((restrictOpenι 𝒞 V ψ).base u) :=
  dimensionFunction_comp _ _ u

omit [Infinite k] [Finite ι] [IsLocallyNoetherian X] [NoetherianSpace X] [IsIntegral W]
  [NoetherianSpace P] [IsProper q] in
/-- The dimension functions of `W` and `V` are compatible. -/
theorem dim_restrictOpen_base (w : W) :
    dimensionFunction (ψ ≫ (V.inclusion ≫ f)) w =
      dimensionFunction (V.inclusion ≫ f) (ψ.base w) :=
  dimensionFunction_comp _ _ w

omit [Finite ι] [IsLocallyNoetherian X] in
include hshift in
/-- **Generic evaluation of the top iterate from an open piece.**  Suppose that on the open
subscheme `P_V ×_V W` of `P_V` the class `c₁^r ∩ [P_V ×_V W]` is the class of a point `ζ` lying
over the generic point of `W` with residue degree one.  Then `(q_V)_* (c₁(L|_{P_V})^r ∩ [P_V])`
evaluates to `1` at the generic point of `V`. -/
theorem evalGeneric_pushTopIterate_of_open (i : ℤ)
    (hi : dimensionFunction f V.genericPointImage = i)
    (ζ : restrictOpen 𝒞 V ψ)
    (hζ : dimensionFunction (restrictOpenι 𝒞 V ψ ≫ (restrictι 𝒞 V ≫ (q ≫ f))) ζ = i)
    (hζq : (restrictOpenProj 𝒞 V ψ).base ζ = genericPoint W)
    (hζres : (restrictOpenProj 𝒞 V ψ).residueDegree ζ = 1)
    (hc1 : haveI := noetherianSpace_of_isOpenImmersion (restrictOpenι 𝒞 V ψ)
      c1Iter (restrictOpenι 𝒞 V ψ ≫ (restrictι 𝒞 V ≫ (q ≫ f))) (restrictOpenBundle 𝒞 L V ψ)
        (Nat.card ι) i
        (openImmersionPullback (chowSystem _ (i + (Nat.card ι : ℤ))) (restrictOpenι 𝒞 V ψ)
          (dim_restrictOpenι 𝒞 f V ψ) (chowSystem _ (i + (Nat.card ι : ℤ)))
          (chowCast (by rw [hi]) (genericRestrictClass 𝒞 f hshift V))) =
      (chowSystem _ i).quotientMap (cyclesOfDimension.point ζ hζ)) :
    evalGeneric (dimensionFunction (V.inclusion ≫ f)) (covByDimension_finiteTypeDimension _) i
      (properPushforwardChowOfProper (restrictProj 𝒞 V) (restrictι 𝒞 V ≫ (q ≫ f))
        (V.inclusion ≫ f) (dimensionFunction _) (dimensionFunction _) i
        (c1Iter (restrictι 𝒞 V ≫ (q ≫ f)) (L.restrict (restrictι 𝒞 V)) (Nat.card ι) i
          (chowCast (by rw [hi]) (genericRestrictClass 𝒞 f hshift V)))) = 1 := by
  have := noetherianSpace_of_isOpenImmersion (restrictOpenι 𝒞 V ψ)
  have := noetherianSpace_of_isOpenImmersion ψ
  have := LocallyOfFiniteType.isLocallyNoetherian (ψ ≫ (V.inclusion ≫ f))
  obtain ⟨γ, hγ⟩ := Submodule.Quotient.mk_surjective _
    (c1Iter (restrictι 𝒞 V ≫ (q ≫ f)) (L.restrict (restrictι 𝒞 V)) (Nat.card ι) i
      (chowCast (by rw [hi]) (genericRestrictClass 𝒞 f hshift V)))
  change (chowSystem _ i).quotientMap γ = _ at hγ
  have hgen : ψ.base (genericPoint W) = genericPoint V.scheme :=
    base_genericPoint_of_isOpenImmersion ψ
  -- the restriction of `γ` to the open piece represents the class of `ζ`
  have hopen : (chowSystem _ i).quotientMap (cyclesOfDimension.flatPullbackOpen
      (restrictOpenι 𝒞 V ψ) (dim_restrictOpenι 𝒞 f V ψ) γ) =
      (chowSystem _ i).quotientMap (cyclesOfDimension.point ζ hζ) := by
    rw [← hc1, ← openImmersionPullback_c1Iter, ← hγ, openImmersionPullback_quotientMap]
  -- push forward along `restrictOpenProj` and evaluate at the generic point of `W`
  have hpush : ((cyclesOfDimension.properPushforward
      (dimensionY := dimensionFunction (ψ ≫ (V.inclusion ≫ f))) (restrictOpenProj 𝒞 V ψ)
      (cyclesOfDimension.flatPullbackOpen (restrictOpenι 𝒞 V ψ) (dim_restrictOpenι 𝒞 f V ψ) γ) :
        cyclesOfDimension W _ i) : AlgebraicCycle W ℚ) (genericPoint W) =
      ((cyclesOfDimension.properPushforward
        (dimensionY := dimensionFunction (ψ ≫ (V.inclusion ≫ f))) (restrictOpenProj 𝒞 V ψ)
        (cyclesOfDimension.point ζ hζ) : cyclesOfDimension W _ i) : AlgebraicCycle W ℚ)
        (genericPoint W) := by
    have h := congrArg (fun a ↦ evalGeneric (dimensionFunction (ψ ≫ (V.inclusion ≫ f)))
      (covByDimension_finiteTypeDimension _) i
      (properPushforwardChowOfProper (restrictOpenProj 𝒞 V ψ)
        (restrictOpenι 𝒞 V ψ ≫ (restrictι 𝒞 V ≫ (q ≫ f))) (ψ ≫ (V.inclusion ≫ f))
        (dimensionFunction _) (dimensionFunction _) i a)) hopen
    exact h
  rw [← hγ, properPushforwardChowOfProper_quotientMap, evalGeneric_quotientMap,
    cyclesOfDimension.properPushforward_apply, ← hgen]
  change (AlgebraicCycle.map (restrictProj 𝒞 V) (dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)))
    (dimensionFunction (V.inclusion ≫ f)) (γ : AlgebraicCycle _ ℚ)) (ψ.base (genericPoint W)) = 1
  rw [← AlgebraicCycle.pullbackOpen_apply ψ, pullbackOpen_map_pullback (restrictProj 𝒞 V) ψ
    (dimensionFunction (restrictι 𝒞 V ≫ (q ≫ f)) : _ → ℤ) (dimensionFunction (V.inclusion ≫ f))
    (dimensionFunction (restrictOpenι 𝒞 V ψ ≫ (restrictι 𝒞 V ≫ (q ≫ f))))
    (dimensionFunction (ψ ≫ (V.inclusion ≫ f))) (dim_restrictOpenι 𝒞 f V ψ)
    (dim_restrictOpen_base f V ψ)]
  change ((cyclesOfDimension.properPushforward
    (dimensionY := dimensionFunction (ψ ≫ (V.inclusion ≫ f))) (restrictOpenProj 𝒞 V ψ)
    (cyclesOfDimension.flatPullbackOpen (restrictOpenι 𝒞 V ψ) (dim_restrictOpenι 𝒞 f V ψ) γ) :
      cyclesOfDimension _ _ i) : AlgebraicCycle W ℚ) (genericPoint W) = 1
  rw [hpush, properPushforward_point_apply, if_pos hζq, mapCoeff_eq_one _ _ _ hζres,
    Nat.cast_one]
  rw [hζ, hζq, dim_restrictOpen_base, hgen, dim_genericPoint_scheme, hi]

end OpenEval

/-! ## The injectivity half of the projective bundle formula -/

section Injective

open RationalEquivalenceSystem.DescendingMap ChartedOverSubscheme

variable {k : Type u} [Field k] [Infinite k] {P X : Scheme.{u}} {q : P ⟶ X} [IsProper q]
  {ι : Type u} [Finite ι] (𝒞 : AffineCharts q ι) (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] [NoetherianSpace P]
  (hshift : ∀ x, dimensionFunction (q ≫ f) (𝒞.fibrePoint x) =
    dimensionFunction f x + (Nat.card ι : ℤ))
  (L : LineBundleData P)

omit [IsProper q] [NoetherianSpace X] [NoetherianSpace P] in
/-- `chowCast` along a proof of `i = i` is the identity. -/
theorem chowCast_self {Y : Scheme.{u}} {dim : DimensionFunction Y} {i : ℤ} (h : i = i)
    (x : (chowSystem dim i).ChowGroup) : chowCast h x = x := rfl

omit [IsProper q] [NoetherianSpace X] [NoetherianSpace P] [Finite ι] in
/-- `c1Iter` may be rewritten along an equality of exponents. -/
theorem c1Iter_congr_exponent {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] [NoetherianSpace Y] (N : LineBundleData Y) {a b : ℕ} (h : a = b)
    {j l : ℤ} (hl : l = j + a) (x : (chowSystem (dimensionFunction g) l).ChowGroup) :
    c1Iter g N a j (chowCast hl x) = c1Iter g N b j (chowCast (by rw [hl, h]) x) := by
  subst h
  rfl

/-- **The projective bundle map** `⨁_{m = 0}^{r} A_{i + m - r}(X) → A_i(P)`,
`(α_m)_m ↦ ∑_m c₁(L)^m ∩ q^* α_m`. -/
noncomputable def projectiveBundleMap (i : ℤ) :
    (∀ m : Fin (Nat.card ι + 1),
      (chowSystem (dimensionFunction f) (i + ((m : ℕ) : ℤ) - Nat.card ι)).ChowGroup) →ₗ[ℚ]
      (chowSystem (dimensionFunction (q ≫ f)) i).ChowGroup :=
  ∑ m : Fin (Nat.card ι + 1),
    ((c1Iter (q ≫ f) L m i).comp ((chowCast (by ring)).toLinearMap.comp
      (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift
        (i + ((m : ℕ) : ℤ) - Nat.card ι) (chowSystem _ _) (chowSystem _ _)))).comp
      (LinearMap.proj m)

omit [NoetherianSpace X] in
/-- The value of the projective bundle map. -/
theorem projectiveBundleMap_apply (i : ℤ) (α : ∀ m : Fin (Nat.card ι + 1),
    (chowSystem (dimensionFunction f) (i + ((m : ℕ) : ℤ) - Nat.card ι)).ChowGroup) :
    projectiveBundleMap 𝒞 f hshift L i α = ∑ m : Fin (Nat.card ι + 1),
      c1Iter (q ≫ f) L m i (chowCast (by ring)
        (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift
          (i + ((m : ℕ) : ℤ) - Nat.card ι) (chowSystem _ _) (chowSystem _ _) (α m))) := by
  rw [projectiveBundleMap, LinearMap.sum_apply]
  rfl

include hshift in
/-- **Injectivity of the projective bundle map**, given the Segre identity
`q_* (c₁(L)^r ∩ q^* α) = α` in every degree (the vanishing of the lower terms is proved in
`properPushforward_c1Iter_chowPullbackCharted_eq_zero_of_lt`). -/
theorem projectiveBundleMap_injective_of_segre [IsLocallyNoetherian X]
    (hseg : ∀ (j : ℤ) (α : (chowSystem (dimensionFunction f) j).ChowGroup),
      properPushforwardChowOfProper q (q ≫ f) f (dimensionFunction (q ≫ f))
        (dimensionFunction f) j (c1Iter (q ≫ f) L (Nat.card ι) j
          (chowPullbackCharted 𝒞 (dimensionFunction f) (dimensionFunction (q ≫ f)) hshift j
            (chowSystem _ j) (chowSystem _ (j + (Nat.card ι : ℤ))) α)) = α)
    (i : ℤ) : Function.Injective (projectiveBundleMap 𝒞 f hshift L i) := by
  set r := Nat.card ι with hr
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α hα
  rw [projectiveBundleMap_apply] at hα
  -- the key step: `α n = 0` once all higher `α m` vanish
  have key : ∀ n : Fin (r + 1), (∀ m : Fin (r + 1), n < m → α m = 0) → α n = 0 := by
    intro n hn
    have hnr : (n : ℕ) ≤ r := Nat.lt_succ_iff.mp n.2
    have h0 := congrArg (fun a ↦ properPushforwardChowOfProper q (q ≫ f) f
      (dimensionFunction (q ≫ f)) (dimensionFunction f) (i + (n : ℕ) - r)
      (c1Iter (q ≫ f) L (r - n) (i + (n : ℕ) - r) (chowCast (by omega) a))) hα
    simp only [map_sum, map_zero] at h0
    rw [Finset.sum_eq_single n] at h0
    · -- the `n`-th term is `α n` by the Segre identity
      rw [c1Iter_chowCast (q ≫ f) L (n : ℕ) (j := i + (n : ℕ) - r + (r - n : ℕ))
        (by omega) (by omega), chowCast_chowCast, chowCast_self,
        c1Iter_c1Iter, c1Iter_congr_exponent (q ≫ f) L (Nat.sub_add_cancel hnr)
        (by push_cast; omega), chowCast_chowCast, chowCast_self, hseg] at h0
      exact h0
    · -- the other terms vanish
      intro m _ hmn
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have hlt' : (m : ℕ) < n := hlt
        rw [c1Iter_chowCast (q ≫ f) L (m : ℕ) (j := i + (n : ℕ) - r + (r - n : ℕ))
          (by omega) (by omega), chowCast_chowCast, chowCast_self,
          c1Iter_c1Iter, chowCast_chowCast]
        exact properPushforward_c1Iter_chowPullbackCharted_eq_zero_of_lt 𝒞 f hshift L
          (r - n + m) (by omega) (by push_cast; omega) (α m)
      · rw [hn m hgt]
        simp only [map_zero]
    · intro hn'
      exact absurd (Finset.mem_univ n) hn'
  -- downward induction on the index
  have hall : ∀ d : ℕ, ∀ n : Fin (r + 1), r - (n : ℕ) ≤ d → α n = 0 := by
    intro d
    induction d with
    | zero =>
      intro n hn
      refine key n fun m hm ↦ ?_
      have : (n : ℕ) < m := hm
      have := Nat.lt_succ_iff.mp m.2
      omega
    | succ d ih =>
      intro n hn
      refine key n fun m hm ↦ ?_
      have : (n : ℕ) < m := hm
      exact ih m (by omega)
  funext n
  exact hall _ n le_rfl

end Injective

/-! ## The projective completion: Noetherianity and chart lemmas -/

section Completion

open GradedBundleData ChartedOverSubscheme

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- A point of `P(E ⊕ 1)` over `U_j` lies in one of the charts `(j, i)`. -/
theorem exists_mem_range_completionChart_of_mem (j : 𝓔.bundle.J) {p : 𝓔.projectiveCompletion}
    (hp : 𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1) :
    ∃ i : Option ι, p ∈ Set.range (𝓔.completionChart (j, i)).base := by
  obtain ⟨y, rfl⟩ := 𝓔.mem_range_chartProjι_of_mem j hp
  obtain ⟨i, z, rfl⟩ := exists_mem_range_projOptionChart y
  exact ⟨i, z, rfl⟩

/-- Membership in the open `D₊(x_a)` of `tautological` is membership in the chart `a`. -/
theorem mem_tautOpen_iff (a : 𝓔.TautIndex) (p : 𝓔.projectiveCompletion) :
    p ∈ (𝓔.tautOpen a : 𝓔.projectiveCompletion.Opens) ↔
      p ∈ Set.range (𝓔.completionChart a).base := by
  rw [← 𝓔.opensRange_completionChart a]
  exact Iff.rfl

end Completion

/-! ## Transport of residue units of restricted and pulled-back line bundles -/

section UnitTransport

/-- The residue at `z` of a transition unit of `L.restrict ι` is the image under the residue
field map of `ι` of the residue at `ι z` of the transition unit of `L`. -/
theorem sectionResidueUnit_restrict_g {Y Z : Scheme.{u}} (L : LineBundleData Y) (ι : Z ⟶ Y)
    [IsClosedImmersion ι] (a b : L.J) {z : Z}
    (hz : z ∈ ((L.restrict ι).U a : Z.Opens) ⊓ ((L.restrict ι).U b : Z.Opens)) :
    sectionResidueUnit hz ((L.restrict ι).g a b) =
      Units.map (ι.residueFieldMap z).hom.toMonoidHom
        (sectionResidueUnit (U := (L.U a : Y.Opens) ⊓ (L.U b : Y.Opens)) ⟨hz.1, hz.2⟩
          (L.g a b)) := by
  rw [LineBundleData.restrict_g]
  exact (closedResidueFieldEquiv_sectionResidueUnit ι
    (LineBundleData.inf_preimage_le_preimage_inf ι _ _) hz (L.g a b)).symm

/-- `Units.map` along the residue field map of a composite. -/
theorem units_map_residueFieldMap_comp {Y Z W : Scheme.{u}} (g : W ⟶ Z) (ι : Z ⟶ Y) (w : W)
    (u : (Y.residueField ((g ≫ ι).base w))ˣ) :
    Units.map ((g ≫ ι).residueFieldMap w).hom.toMonoidHom u =
      Units.map (g.residueFieldMap w).hom.toMonoidHom
        (Units.map (ι.residueFieldMap (g.base w)).hom.toMonoidHom u) := by
  apply Units.ext
  simp only [Units.coe_map]
  rw [Scheme.residueFieldMap_comp]
  rfl

end UnitTransport

/-! ## The chain of coordinate points on the trivial piece -/

section Chain

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  LineBundleInjective

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- The coordinate point of `P(E ⊕ 1)` over `𝔭 ∈ Spec Γ(U_j)` attached to a finite set `S₀` of
coordinates of the bundle: the generic point of `{x_s = 0 : s ∈ S₀}` in the fibre, computed in
the chart `(j, none)`. -/
noncomputable abbrev coordClassPoint (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) :
    𝓔.projectiveCompletion :=
  𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) none

omit [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The coordinate point lies in the chart `(j, i)` iff `i` is not one of its coordinates. -/
theorem coordClassPoint_mem_range_completionChart_iff (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) (i : Option ι) :
    coordClassPoint 𝓔 j 𝔭 S₀ ∈ Set.range (𝓔.completionChart (j, i)).base ↔
      i ∉ some '' (S₀ : Set ι) :=
  𝓔.coordPoint_mem_range_completionChart_iff j 𝔭 _ (by simp) i

omit [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The coordinate points specialise along inclusions of coordinate sets. -/
theorem coordClassPoint_specializes (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) {S₀ S₁ : Finset ι}
    (h : S₀ ⊆ S₁) : coordClassPoint 𝓔 j 𝔭 S₀ ⤳ coordClassPoint 𝓔 j 𝔭 S₁ :=
  𝓔.coordPoint_specializes_of_subset j 𝔭 (Set.image_mono (Finset.coe_subset.mpr h))
    (by simp) (by simp)

omit [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The coordinate point lies over the base point. -/
theorem completionToBase_coordClassPoint (j : 𝓔.bundle.J)
    (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1)))) (S₀ : Finset ι) :
    𝓔.completionToBase.base (coordClassPoint 𝓔 j 𝔭 S₀) = (𝓔.chartBaseι j).base 𝔭 :=
  𝓔.completionToBase_coordPoint j 𝔭 _ none

omit [Infinite k] [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] in
open Classical in
/-- **Orders of the coordinate functions along the coordinate points** (P1's
`pointOrd_coordPoint`, in the form used here): for `t ∉ S₀`, a chart `(j, i)` with `i ≠ some t`
containing `Q`, and `coordClassPoint S₀ ⤳ Q`, the order along `coordClassPoint S₀ ⤳ Q` of the
residue of the transition unit `x_t / x_i` of `O(1)` is `1` if `Q` is the coordinate point of
`insert t S₀` and `0` otherwise. -/
theorem pointOrd_coordClassPoint [IsLocallyNoetherian X]
    [IsLocallyNoetherian 𝓔.projectiveCompletion]
    (j : 𝓔.bundle.J) (𝔭 : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1))))
    (S₀ : Finset ι) {t : ι} (ht : t ∉ S₀) {i : Option ι} (hi : i ≠ some t)
    {Q : 𝓔.projectiveCompletion} (hQ : Q ∈ Set.range (𝓔.completionChart (j, i)).base)
    (hw : coordClassPoint 𝓔 j 𝔭 S₀ ⤳ Q)
    (hmem : coordClassPoint 𝓔 j 𝔭 S₀ ∈ (𝓔.tautOpen (j, i) : 𝓔.projectiveCompletion.Opens) ⊓
      (𝓔.tautOpen (j, some t) : 𝓔.projectiveCompletion.Opens)) :
    pointOrd hw (sectionResidueUnit hmem ((𝓔.tautological hX).g (j, i) (j, some t))) =
      if Q = coordClassPoint 𝓔 j 𝔭 (insert t S₀) then 1 else 0 := by
  have := IsLocallyNoetherian.component_noetherian (𝓔.bundle.chart j)
  have hiS : i ∉ some '' (S₀ : Set ι) := by
    have h := hw.mem_open (𝓔.completionChart (j, i)).isOpenEmbedding.isOpen_range hQ
    exact (coordClassPoint_mem_range_completionChart_iff 𝓔 j 𝔭 S₀ i).1 h
  have hw₀ : coordClassPoint 𝓔 j 𝔭 S₀ = 𝓔.coordPoint j 𝔭 (some '' (S₀ : Set ι)) i :=
    𝓔.coordPoint_congr j 𝔭 _ (by simp) hiS
  rw [𝓔.pointOrd_coordPoint hX j 𝔭 (S := some '' (S₀ : Set ι)) (by simpa using ht) hi hw₀ hQ
    hw hmem]
  have heq : 𝓔.coordPoint j 𝔭 (insert (some t) (some '' (S₀ : Set ι))) i =
      coordClassPoint 𝓔 j 𝔭 (insert t S₀) := by
    change _ = 𝓔.coordPoint j 𝔭 (some '' ((insert t S₀ : Finset ι) : Set ι)) none
    rw [Finset.coe_insert, Set.image_insert_eq]
    exact 𝓔.coordPoint_congr j 𝔭 _ (by rw [Set.mem_insert_iff, not_or]; exact ⟨hi, hiS⟩)
      (by simp)
  rw [heq]

end Chain

/-! ## The trivial piece over a point and the chain lemma -/

section TrivialPiece

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  LineBundleInjective

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

variable (x : X) (j : 𝓔.bundle.J) (hx : x ∈ (𝓔.bundle.chart j).1)

/-- The prime of `Γ(U_j)` corresponding to the point `x ∈ U_j`. -/
noncomputable abbrev basePrime : ↥(Spec (CommRingCat.of Γ(X, (𝓔.bundle.chart j).1))) :=
  𝓔.bundle.chartBasePoint j ⟨x, hx⟩

omit [Infinite k] [NoetherianSpace X] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι]
  [IsLocallyNoetherian X] in
/-- `basePrime` lies under `x`. -/
theorem chartBaseι_basePrime : (𝓔.chartBaseι j).base (basePrime 𝓔 x j hx) = x :=
  𝓔.chartBaseι_chartBasePoint' j hx

/-- The open subscheme `V ∩ U_j` of `V := pointSubscheme x`. -/
noncomputable abbrev pieceBase : Scheme.{u} :=
  ((pointSubscheme x).inclusion ⁻¹ᵁ (𝓔.bundle.chart j).1).toScheme

/-- The open immersion `V ∩ U_j ⟶ V`. -/
noncomputable abbrev pieceBaseι : pieceBase 𝓔 x j ⟶ (pointSubscheme x).scheme :=
  ((pointSubscheme x).inclusion ⁻¹ᵁ (𝓔.bundle.chart j).1).ι

/-- The trivial piece `P_V ×_V (V ∩ U_j)` of `P(E ⊕ 1) ×_X V` over `V ∩ U_j`. -/
noncomputable abbrev piece : Scheme.{u} :=
  restrictOpen 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)

/-- The immersion of the trivial piece into `P(E ⊕ 1)`: the open immersion into
`P(E ⊕ 1) ×_X V` followed by the closed immersion into `P(E ⊕ 1)`. -/
noncomputable abbrev pieceι : piece 𝓔 x j ⟶ 𝓔.projectiveCompletion :=
  restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
    restrictι 𝓔.completionCharts (pointSubscheme x)

/-- The structure morphism of the trivial piece over `k`. -/
noncomputable abbrev pieceStructure : piece 𝓔 x j ⟶ Spec (CommRingCat.of k) :=
  restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
    (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))

/-- The line bundle `O(1)` restricted to the trivial piece. -/
noncomputable abbrev pieceBundle : LineBundleData (piece 𝓔 x j) :=
  restrictOpenBundle 𝓔.completionCharts (𝓔.tautological hX) (pointSubscheme x) (pieceBaseι 𝓔 x j)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The immersion of the trivial piece is injective. -/
theorem pieceι_injective : Function.Injective (pieceι 𝓔 x j).base := by
  change Function.Injective ((restrictι 𝓔.completionCharts (pointSubscheme x)).base ∘
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base)
  exact (restrictι 𝓔.completionCharts (pointSubscheme x)).isClosedEmbedding.injective.comp
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x)
      (pieceBaseι 𝓔 x j)).isOpenEmbedding.injective

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- Specialisation on the trivial piece is detected in `P(E ⊕ 1)`. -/
theorem pieceι_specializes_iff {a b : piece 𝓔 x j} :
    (pieceι 𝓔 x j).base a ⤳ (pieceι 𝓔 x j).base b ↔ a ⤳ b := by
  change ((restrictι 𝓔.completionCharts (pointSubscheme x)).base ∘
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base) a ⤳
    ((restrictι 𝓔.completionCharts (pointSubscheme x)).base ∘
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base) b ↔ _
  exact ((restrictι 𝓔.completionCharts (pointSubscheme x)).isClosedEmbedding.isInducing.comp
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x)
      (pieceBaseι 𝓔 x j)).isOpenEmbedding.isInducing).specializes_iff

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- A point of `P(E ⊕ 1)` lies in the trivial piece iff it lies over `V` and over `U_j`. -/
theorem mem_range_pieceι_iff (p : 𝓔.projectiveCompletion) :
    p ∈ Set.range (pieceι 𝓔 x j).base ↔
      𝓔.completionToBase.base p ∈ Set.range (pointSubscheme x).inclusion.base ∧
        𝓔.completionToBase.base p ∈ (𝓔.bundle.chart j).1 := by
  have hcond : ∀ b : restrictScheme 𝓔.completionCharts (pointSubscheme x),
      𝓔.completionToBase.base ((restrictι 𝓔.completionCharts (pointSubscheme x)).base b) =
        (pointSubscheme x).inclusion.base
          ((restrictProj 𝓔.completionCharts (pointSubscheme x)).base b) := by
    intro b
    have h := congrArg (fun g : restrictScheme 𝓔.completionCharts (pointSubscheme x) ⟶ X ↦
      g.base b) (pullback.condition (f := 𝓔.completionToBase) (g := (pointSubscheme x).inclusion))
    exact h
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(mem_range_restrictι_iff _ _ _).1 ⟨_, rfl⟩, ?_⟩
    have h1 : (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a ∈
        Set.range (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base :=
      ⟨a, rfl⟩
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι] at h1
    change 𝓔.completionToBase.base ((restrictι 𝓔.completionCharts (pointSubscheme x)).base
      ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a)) ∈ _
    rw [hcond]
    exact h1
  · rintro ⟨h1, h2⟩
    obtain ⟨a, rfl⟩ := (mem_range_restrictι_iff 𝓔.completionCharts (pointSubscheme x) p).2 h1
    have h3 : a ∈ Set.range
        (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι]
      change (pointSubscheme x).inclusion.base
        ((restrictProj 𝓔.completionCharts (pointSubscheme x)).base a) ∈
          ((𝓔.bundle.chart j).1 : Set X)
      rw [← hcond]
      exact h2
    obtain ⟨b, rfl⟩ := h3
    exact ⟨b, rfl⟩

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
include hx in
/-- The coordinate points over `x` lie in the trivial piece. -/
theorem coordClassPoint_mem_range_pieceι (S₀ : Finset ι) :
    coordClassPoint 𝓔 j (basePrime 𝓔 x j hx) S₀ ∈
      Set.range (pieceι 𝓔 x j).base := by
  rw [mem_range_pieceι_iff, completionToBase_coordClassPoint, chartBaseι_basePrime]
  exact ⟨⟨genericPoint (pointSubscheme x).scheme, genericPointImage_pointSubscheme x⟩, hx⟩

/-- The coordinate point over `x` for the coordinate set `S₀`, as a point of the trivial
piece. -/
noncomputable def piecePoint (S₀ : Finset ι) : piece 𝓔 x j :=
  (coordClassPoint_mem_range_pieceι 𝓔 x j hx S₀).choose

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The image in `P(E ⊕ 1)` of `piecePoint` is the coordinate point. -/
@[simp]
theorem pieceι_piecePoint (S₀ : Finset ι) :
    (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) =
      coordClassPoint 𝓔 j (basePrime 𝓔 x j hx) S₀ :=
  (coordClassPoint_mem_range_pieceι 𝓔 x j hx S₀).choose_spec

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The points of the trivial piece specialise along inclusions of coordinate sets. -/
theorem piecePoint_specializes {S₀ S₁ : Finset ι} (h : S₀ ⊆ S₁) :
    piecePoint 𝓔 x j hx S₀ ⤳ piecePoint 𝓔 x j hx S₁ := by
  rw [← pieceι_specializes_iff, pieceι_piecePoint, pieceι_piecePoint]
  exact coordClassPoint_specializes 𝓔 j _ h

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The dimension of a point of the trivial piece is its dimension in `P(E ⊕ 1)`. -/
theorem dim_piece (a : piece 𝓔 x j) :
    dimensionFunction (pieceStructure f 𝓔 x j) a =
      dimensionFunction (𝓔.completionToBase ≫ f) ((pieceι 𝓔 x j).base a) := by
  rw [dimensionFunction_comp, DimensionFunction.apply_eq_of_isClosedImmersion
    (dimensionFunction (restrictι 𝓔.completionCharts (pointSubscheme x) ≫
      (𝓔.completionToBase ≫ f))) (dimensionFunction (𝓔.completionToBase ≫ f))
    (restrictι 𝓔.completionCharts (pointSubscheme x))]
  rfl

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- A point of the trivial piece lying in the preimage of a chart `(j, i)` has its image in the
chart; conversely every point of the trivial piece lies in the preimage of some chart `(j, i)`. -/
theorem exists_chart_piece (a : piece 𝓔 x j) :
    ∃ i : Option ι, (pieceι 𝓔 x j).base a ∈ Set.range (𝓔.completionChart (j, i)).base :=
  exists_mem_range_completionChart_of_mem 𝓔 j ((mem_range_pieceι_iff 𝓔 x j _).1 ⟨a, rfl⟩).2

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- Membership in the chart of `pieceBundle` built from the chart `a` of `O(1)`. -/
theorem mem_pieceBundle_chart_iff (a : 𝓔.TautIndex) (p : piece 𝓔 x j) :
    p ∈ (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ⁻¹ᵁ
      (((𝓔.tautological hX).restrict (restrictι 𝓔.completionCharts (pointSubscheme x))).U a :
        (restrictScheme 𝓔.completionCharts (pointSubscheme x)).Opens)) ↔
      (pieceι 𝓔 x j).base p ∈ Set.range (𝓔.completionChart a).base := by
  rw [← mem_tautOpen_iff]
  exact Iff.rfl

/-- A chart of `pieceBundle` around a point `p` of the trivial piece whose image lies in the
chart `a` of `O(1)`: an affine open neighbourhood of `p` inside the preimage of `D₊(x_a)`. -/
noncomputable def pieceChart (a : 𝓔.TautIndex) (p : piece 𝓔 x j)
    (hp : (pieceι 𝓔 x j).base p ∈ Set.range (𝓔.completionChart a).base) :
    (pieceBundle 𝓔 hX x j).J :=
  ⟨(a, ⟨_, (Opens.isBasis_iff_nbhd.mp (piece 𝓔 x j).isBasis_affineOpens
      ((mem_pieceBundle_chart_iff 𝓔 hX x j a p).2 hp)).choose_spec.1⟩),
    (Opens.isBasis_iff_nbhd.mp (piece 𝓔 x j).isBasis_affineOpens
      ((mem_pieceBundle_chart_iff 𝓔 hX x j a p).2 hp)).choose_spec.2.2⟩

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The point lies in its chart. -/
theorem mem_pieceChart (a : 𝓔.TautIndex) (p : piece 𝓔 x j)
    (hp : (pieceι 𝓔 x j).base p ∈ Set.range (𝓔.completionChart a).base) :
    p ∈ ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j a p hp) : (piece 𝓔 x j).Opens) :=
  (Opens.isBasis_iff_nbhd.mp (piece 𝓔 x j).isBasis_affineOpens
    ((mem_pieceBundle_chart_iff 𝓔 hX x j a p).2 hp)).choose_spec.2.1

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The underlying chart of `O(1)` of `pieceChart`. -/
theorem pieceChart_fst (a : 𝓔.TautIndex) (p : piece 𝓔 x j)
    (hp : (pieceι 𝓔 x j).base p ∈ Set.range (𝓔.completionChart a).base) :
    (pieceChart 𝓔 hX x j a p hp).1.1 = a := rfl

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- **Transport of the residue of a transition unit of `pieceBundle`** to `P(E ⊕ 1)`: at a point
`w` of the trivial piece, the residue of `(pieceBundle).g bW aW` is the image under the residue
field map of `pieceι` of the residue at `pieceι w` of `O(1).g b a`. -/
theorem sectionResidueUnit_pieceBundle_g
    (aW bW : ((𝓔.tautological hX).restrict
      (restrictι 𝓔.completionCharts (pointSubscheme x))).PullbackIndex
        (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)))
    {w : piece 𝓔 x j}
    (hw : w ∈ ((pieceBundle 𝓔 hX x j).U bW : (piece 𝓔 x j).Opens) ⊓
      ((pieceBundle 𝓔 hX x j).U aW : (piece 𝓔 x j).Opens))
    (hw' : (pieceι 𝓔 x j).base w ∈
      (𝓔.tautOpen bW.1.1 : 𝓔.projectiveCompletion.Opens) ⊓
        (𝓔.tautOpen aW.1.1 : 𝓔.projectiveCompletion.Opens)) :
    sectionResidueUnit hw ((pieceBundle 𝓔 hX x j).g bW aW) =
      Units.map ((pieceι 𝓔 x j).residueFieldMap w).hom.toMonoidHom
        (sectionResidueUnit hw' ((𝓔.tautological hX).g bW.1.1 aW.1.1)) := by
  refine (LineBundleData.sectionResidueUnit_pullback_g _ _ bW aW hw).trans ?_
  rw [units_map_residueFieldMap_comp]
  exact congrArg _ (sectionResidueUnit_restrict_g (𝓔.tautological hX)
    (restrictι 𝓔.completionCharts (pointSubscheme x)) bW.1.1 aW.1.1 _)

end TrivialPiece

/-! ## The chain lemma on the trivial piece -/

section ChainLemma

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  LineBundleInjective

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
  (x : X) (j : 𝓔.bundle.J) (hx : x ∈ (𝓔.bundle.chart j).1)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The point `piecePoint S₀` lies in the preimage of the chart `(j, i)` iff `i` is not one of
the coordinates `S₀`. -/
theorem pieceι_piecePoint_mem_range_completionChart_iff (S₀ : Finset ι) (i : Option ι) :
    (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) ∈
      Set.range (𝓔.completionChart (j, i)).base ↔ i ∉ some '' (S₀ : Set ι) := by
  rw [pieceι_piecePoint, coordClassPoint_mem_range_completionChart_iff]

/-- `chowCast` of the class of a point is the class of the point. -/
theorem chowCast_point {Y : Scheme.{u}} {dim : DimensionFunction Y} {i i' : ℤ} (h : i = i')
    (y : Y) (hy : dim y = i) :
    chowCast h ((chowSystem dim i).quotientMap (cyclesOfDimension.point y hy)) =
      (chowSystem dim i').quotientMap (cyclesOfDimension.point y (hy.trans h)) := by
  rw [chowCast_quotientMap, cyclesCast_point]

open Classical in
/-- **The chain lemma.**  On the trivial piece over `x ∈ U_j`, the first Chern class of `O(1)`
sends the class of the coordinate point of `S₀` to the class of the coordinate point of
`insert t S₀`, for `t ∉ S₀` (the rational section `x_t` of `O(1)` has divisor
`{x_t = 0}` along the coordinate subspace of `S₀`). -/
theorem firstChernClassOfField_piecePoint (S₀ : Finset ι) {t : ι} (ht : t ∉ S₀) {jj : ℤ}
    (hw : dimensionFunction (pieceStructure f 𝓔 x j) (piecePoint 𝓔 x j hx S₀) = jj + 1)
    (hv : dimensionFunction (pieceStructure f 𝓔 x j) (piecePoint 𝓔 x j hx (insert t S₀)) = jj) :
    haveI := noetherianSpace_of_isOpenImmersion
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
    firstChernClassOfField (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) jj
        ((chowSystem _ (jj + 1)).quotientMap
          (cyclesOfDimension.point (piecePoint 𝓔 x j hx S₀) hw)) =
      (chowSystem _ jj).quotientMap
        (cyclesOfDimension.point (piecePoint 𝓔 x j hx (insert t S₀)) hv) := by
  have := noetherianSpace_of_isOpenImmersion
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
  have := LocallyOfFiniteType.isLocallyNoetherian (pieceStructure f 𝓔 x j)
  have := LocallyOfFiniteType.isLocallyNoetherian (𝓔.completionToBase ≫ f)
  -- the chart `(j, some t)` contains the point of `S₀`
  have hwt : (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) ∈
      Set.range (𝓔.completionChart (j, some t)).base := by
    rw [pieceι_piecePoint_mem_range_completionChart_iff]
    simpa using ht
  have hj : (pointSubscheme (piecePoint 𝓔 x j hx S₀)).eta ∈
      ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, some t) _ hwt) :
        (piece 𝓔 x j).Opens) := by
    change (pointSubscheme (piecePoint 𝓔 x j hx S₀)).genericPointImage ∈ _
    rw [genericPointImage_pointSubscheme]
    exact mem_pieceChart 𝓔 hX x j (j, some t) _ hwt
  unfold firstChernClassOfField
  rw [firstChernClass_quotientMap, c1Cycle_single (covByDimension_finiteTypeDimension _) hw
    ⟨pieceChart 𝓔 hX x j (j, some t) _ hwt, hj, 1⟩]
  congr 1
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext Q
  beta_reduce
  by_cases hwQ : piecePoint 𝓔 x j hx S₀ ⤳ Q
  · obtain ⟨i, hQi⟩ := exists_chart_piece 𝓔 x j Q
    have hQb : Q ∈ ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, i) Q hQi) :
        (piece 𝓔 x j).Opens) := mem_pieceChart 𝓔 hX x j (j, i) Q hQi
    have hwb : piecePoint 𝓔 x j hx S₀ ∈
        ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, i) Q hQi) : (piece 𝓔 x j).Opens) :=
      hwQ.mem_open ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, i) Q hQi)).1.isOpen hQb
    have hwab : piecePoint 𝓔 x j hx S₀ ∈
        ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, i) Q hQi) : (piece 𝓔 x j).Opens) ⊓
          ((pieceBundle 𝓔 hX x j).U (pieceChart 𝓔 hX x j (j, some t) _ hwt) :
            (piece 𝓔 x j).Opens) :=
      ⟨hwb, mem_pieceChart 𝓔 hX x j (j, some t) _ hwt⟩
    rw [LineBundleData.divisor_frame_apply (pieceBundle 𝓔 hX x j) _ (piecePoint 𝓔 x j hx S₀)
      (pieceChart 𝓔 hX x j (j, some t) _ hwt) (pieceChart 𝓔 hX x j (j, i) Q hQi) hj hwQ hQb hwab]
    have hwQ' : (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) ⤳ (pieceι 𝓔 x j).base Q :=
      (pieceι_specializes_iff 𝓔 x j).2 hwQ
    have hwi : (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) ∈
        Set.range (𝓔.completionChart (j, i)).base :=
      hwQ'.mem_open (𝓔.completionChart (j, i)).isOpenEmbedding.isOpen_range hQi
    have hw' : (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx S₀) ∈
        (𝓔.tautOpen (j, i) : 𝓔.projectiveCompletion.Opens) ⊓
          (𝓔.tautOpen (j, some t) : 𝓔.projectiveCompletion.Opens) :=
      ⟨(mem_tautOpen_iff 𝓔 (j, i) _).2 hwi, (mem_tautOpen_iff 𝓔 (j, some t) _).2 hwt⟩
    rw [sectionResidueUnit_pieceBundle_g 𝓔 hX x j _ _ hwab hw',
      ← pointOrd_preimmersion (pieceι 𝓔 x j) hwQ hwQ']
    change ((pointOrd hwQ' (sectionResidueUnit hw'
      ((𝓔.tautological hX).g (j, i) (j, some t))) : ℤ) : ℚ) = _
    by_cases hit : i = some t
    · subst hit
      erw [(𝓔.tautological hX).g_self]
      have h1 : sectionResidueUnit hw' (1 : Γ(𝓔.projectiveCompletion, _)ˣ) = 1 :=
        Units.ext (by rw [sectionResidueUnit_val, Units.val_one, map_one, map_one]; rfl)
      erw [h1]
      rw [pointOrd_one, Int.cast_zero, cyclesOfDimension.point_apply_of_ne _ _ _ ?_]
      intro hQv
      rw [hQv, pieceι_piecePoint_mem_range_completionChart_iff] at hQi
      exact hQi ⟨t, by simp, rfl⟩
    · have hwQ'' : coordClassPoint 𝓔 j (basePrime 𝓔 x j hx) S₀ ⤳
          (pieceι 𝓔 x j).base Q := by
        rw [← pieceι_piecePoint 𝓔 x j hx S₀]
        exact hwQ'
      have hw'' : coordClassPoint 𝓔 j (basePrime 𝓔 x j hx) S₀ ∈
          (𝓔.tautOpen (j, i) : 𝓔.projectiveCompletion.Opens) ⊓
            (𝓔.tautOpen (j, some t) : 𝓔.projectiveCompletion.Opens) := by
        rw [← pieceι_piecePoint 𝓔 x j hx S₀]
        exact hw'
      erw [pointOrd_sectionResidueUnit_congr (pieceι_piecePoint 𝓔 x j hx S₀) hwQ' hwQ'' hw' hw'',
        pointOrd_coordClassPoint 𝓔 hX j _ S₀ ht hit hQi hwQ'' hw'']
      by_cases hQv : Q = piecePoint 𝓔 x j hx (insert t S₀)
      · rw [hQv, if_pos (pieceι_piecePoint 𝓔 x j hx (insert t S₀)), Int.cast_one,
          cyclesOfDimension.point_apply_self]
      · rw [if_neg (fun h ↦ hQv (pieceι_injective 𝓔 x j
          (h.trans (pieceι_piecePoint 𝓔 x j hx (insert t S₀)).symm))), Int.cast_zero,
          cyclesOfDimension.point_apply_of_ne _ _ _ hQv]
  · rw [LineBundleData.RationalSection.divisor_apply_eq_zero_of_not_specializes _ _ hwQ,
      cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hwQ (by
        rw [h]
        exact piecePoint_specializes 𝓔 x j hx (Finset.subset_insert t S₀)))]

end ChainLemma

/-! ## Iterating the chain lemma and the Segre identity for the projective completion -/

section Assembly

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  LineBundleInjective

/-- The recursion of `c1Iter`, applying `c₁` last: `c₁^{m+1} ∩ x = c₁ ∩ (c₁^m ∩ x)`. -/
theorem c1Iter_succ' {k : Type u} [Field k] [Infinite k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [NoetherianSpace Y]
    (N : LineBundleData Y) (m : ℕ) (i : ℤ)
    (x : (chowSystem (dimensionFunction g) (i + (m + 1 : ℕ))).ChowGroup) :
    c1Iter g N (m + 1) i x = firstChernClassOfField g N i
      (c1Iter g N m (i + 1) (chowCast (by push_cast; ring) x)) := by
  have h1 : ∀ z : (chowSystem (dimensionFunction g) (i + (1 : ℕ))).ChowGroup,
      c1Iter g N 1 i z = firstChernClassOfField g N i (chowCast (by push_cast; ring) z) := by
    intro z
    rw [c1Iter_succ, c1Iter_zero, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      firstChernClassOfField_chowCast g N (j := i) (j' := i + ((0 : ℕ) : ℤ)) (by simp),
      chowCast_chowCast, chowCast_self]
  have h2 : chowCast (by push_cast; ring : i + (m + 1 : ℕ) = i + (1 + m : ℕ)) x =
      chowCast (by push_cast; ring : i + 1 + m = i + (1 + m : ℕ))
        (chowCast (by push_cast; ring : i + (m + 1 : ℕ) = i + 1 + m) x) := by
    rw [chowCast_chowCast]
  rw [← chowCast_self (rfl : i + (m + 1 : ℕ) = i + (m + 1 : ℕ)) x,
    c1Iter_congr_exponent g N (Nat.add_comm m 1) (by push_cast; ring), h2,
    ← c1Iter_c1Iter g N 1 m i, h1, chowCast_self,
    c1Iter_chowCast g N m (j := i + ((1 : ℕ) : ℤ)) (j' := i + 1) (by simp), chowCast_chowCast]
  rfl

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
  (x : X) (j : 𝓔.bundle.J) (hx : x ∈ (𝓔.bundle.chart j).1)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] in
/-- The dimension of the coordinate point of `S₀` on the trivial piece over `x`. -/
theorem dim_piecePoint (S₀ : Finset ι) :
    dimensionFunction (pieceStructure f 𝓔 x j) (piecePoint 𝓔 x j hx S₀) =
      dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card := by
  rw [dim_piece, pieceι_piecePoint]
  exact 𝓔.dimensionFunction_coordPoint f j hx S₀ (by simp)

open Classical in
/-- **The iterated chain lemma**: `c₁(O(1))^{|S₀|} ∩ [ζ_∅] = [ζ_{S₀}]` on the trivial piece. -/
theorem c1Iter_piecePoint (S₀ : Finset ι) :
    haveI := noetherianSpace_of_isOpenImmersion
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
    c1Iter (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) S₀.card
        (dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card)
        (chowCast (by simp) ((chowSystem _ _).quotientMap
          (cyclesOfDimension.point (piecePoint 𝓔 x j hx ∅) (dim_piecePoint f 𝓔 x j hx ∅)))) =
      (chowSystem _ _).quotientMap
        (cyclesOfDimension.point (piecePoint 𝓔 x j hx S₀) (dim_piecePoint f 𝓔 x j hx S₀)) := by
  have := noetherianSpace_of_isOpenImmersion
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
  induction S₀ using Finset.induction_on with
  | empty =>
    rw [c1Iter_congr_exponent (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j)
      Finset.card_empty (by simp), c1Iter_zero, LinearEquiv.coe_coe, chowCast_chowCast,
      chowCast_self]
  | insert t S₀ ht ih =>
    have hcard : (insert t S₀).card = S₀.card + 1 := Finset.card_insert_of_notMem ht
    rw [c1Iter_congr_exponent (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) hcard (by simp),
      c1Iter_succ', c1Iter_chowCast (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) S₀.card
        (j := dimensionFunction f x + (Nat.card ι : ℤ) - S₀.card) (by rw [hcard]; push_cast; ring),
      chowCast_chowCast, ih, chowCast_point]
    exact firstChernClassOfField_piecePoint f 𝓔 hX x j hx S₀ ht _ _

end Assembly

/-! ## The Segre identity and the projective bundle map for `P(E ⊕ 1)` -/

section Main

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap
  LineBundleInjective

/-- The residue degree only depends on the morphism. -/
theorem residueDegree_congr {Y Z : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') (z : Z) :
    g.residueDegree z = g'.residueDegree z := by
  subst h
  rfl

/-- The open restriction of the class of a point in the image is the class of its preimage. -/
theorem flatPullbackOpen_point {U Y : Scheme.{u}} (ψ : U ⟶ Y) [IsOpenImmersion ψ]
    {dimU : DimensionFunction U} {dimY : DimensionFunction Y}
    (hdim : ∀ u, dimU u = dimY (ψ.base u)) {i : ℤ} (y' : U) (hy : dimY (ψ.base y') = i) :
    cyclesOfDimension.flatPullbackOpen (i := i) ψ hdim (cyclesOfDimension.point (ψ.base y') hy) =
      cyclesOfDimension.point y' ((hdim y').trans hy) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext Q
  beta_reduce
  rw [cyclesOfDimension.flatPullbackOpen_apply]
  by_cases hQ : Q = y'
  · subst hQ
    rw [cyclesOfDimension.point_apply_self, cyclesOfDimension.point_apply_self]
  · rw [cyclesOfDimension.point_apply_of_ne _ _ _ (fun h ↦ hQ (ψ.isOpenEmbedding.injective h)),
      cyclesOfDimension.point_apply_of_ne _ _ _ hQ]

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [IsLocallyNoetherian X] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) [NoetherianSpace 𝓔.projectiveCompletion]
  (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
  (x : X) (j : 𝓔.bundle.J) (hx : x ∈ (𝓔.bundle.chart j).1)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
include hx in
/-- The base of the trivial piece is nonempty (it contains the generic point of `V`). -/
theorem nonempty_pieceBase : Nonempty (pieceBase 𝓔 x j) := by
  have hη : (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme) = x :=
    genericPointImage_pointSubscheme x
  exact ⟨⟨genericPoint (pointSubscheme x).scheme,
    show (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme) ∈
      (𝓔.bundle.chart j).1 by rw [hη]; exact hx⟩⟩

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
include hx in
/-- The base of the trivial piece is integral. -/
theorem isIntegral_pieceBase : IsIntegral (pieceBase 𝓔 x j) :=
  have := nonempty_pieceBase 𝓔 x j hx
  isIntegral_of_isOpenImmersion (pieceBaseι 𝓔 x j)

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The coordinate point of `∅` on the trivial piece is the generic point of `P ×_X V`. -/
theorem restrictOpenι_piecePoint_empty :
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base
        (piecePoint 𝓔 x j hx ∅) =
      genericPoint (restrictScheme 𝓔.completionCharts (pointSubscheme x)) := by
  have hη : (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme) = x :=
    genericPointImage_pointSubscheme x
  apply (restrictι 𝓔.completionCharts (pointSubscheme x)).isClosedEmbedding.injective
  rw [restrictι_genericPoint, hη]
  change (pieceι 𝓔 x j).base (piecePoint 𝓔 x j hx ∅) = _
  rw [pieceι_piecePoint]
  change 𝓔.coordPoint j (basePrime 𝓔 x j hx) (some '' ((∅ : Finset ι) : Set ι)) none = _
  rw [Finset.coe_empty, Set.image_empty, ← 𝓔.fibrePoint_eq_coordPoint j ⟨x, hx⟩ none]
  rfl

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The projection of a point of the trivial piece lying over `x` is the generic point of the
base of the piece. -/
theorem restrictOpenProj_eq_genericPoint (a : piece 𝓔 x j)
    (ha : 𝓔.completionToBase.base ((pieceι 𝓔 x j).base a) = x) :
    haveI := isIntegral_pieceBase 𝓔 x j hx
    (restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a =
      genericPoint (pieceBase 𝓔 x j) := by
  have := isIntegral_pieceBase 𝓔 x j hx
  apply (pieceBaseι 𝓔 x j).isOpenEmbedding.injective
  rw [base_genericPoint_of_isOpenImmersion]
  apply (pointSubscheme x).inclusion.isClosedEmbedding.injective
  have h1 := congrArg (fun g : piece 𝓔 x j ⟶ (pointSubscheme x).scheme ↦ g.base a)
    (pullback.condition (f := restrictProj 𝓔.completionCharts (pointSubscheme x))
      (g := pieceBaseι 𝓔 x j))
  have h2 := congrArg (fun g : restrictScheme 𝓔.completionCharts (pointSubscheme x) ⟶ X ↦
    g.base ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a))
    (pullback.condition (f := 𝓔.completionToBase) (g := (pointSubscheme x).inclusion))
  change (pointSubscheme x).inclusion.base ((pieceBaseι 𝓔 x j).base
    ((restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a)) =
    (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme)
  change (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
    restrictProj 𝓔.completionCharts (pointSubscheme x)).base a =
    (restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
      pieceBaseι 𝓔 x j).base a at h1
  change (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ 𝓔.completionToBase).base
      ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a) =
    (restrictProj 𝓔.completionCharts (pointSubscheme x) ≫ (pointSubscheme x).inclusion).base
      ((restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).base a) at h2
  have hη : (pointSubscheme x).inclusion.base (genericPoint (pointSubscheme x).scheme) = x :=
    genericPointImage_pointSubscheme x
  rw [hη]
  exact ((congrArg (pointSubscheme x).inclusion.base h1.symm).trans h2.symm).trans ha

omit [Infinite k] [NoetherianSpace 𝓔.projectiveCompletion] [Finite ι] in
/-- The residue degree of the projection of the trivial piece at a point is the residue degree
of `P(E ⊕ 1) ⟶ X` at its image. -/
theorem residueDegree_restrictOpenProj (a : piece 𝓔 x j) :
    (restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)).residueDegree a =
      𝓔.completionToBase.residueDegree ((pieceι 𝓔 x j).base a) := by
  have hcomm : pieceι 𝓔 x j ≫ 𝓔.completionToBase =
      restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
        (pieceBaseι 𝓔 x j ≫ (pointSubscheme x).inclusion) := by
    have hc1 : restrictι 𝓔.completionCharts (pointSubscheme x) ≫ 𝓔.completionToBase =
        restrictProj 𝓔.completionCharts (pointSubscheme x) ≫ (pointSubscheme x).inclusion :=
      pullback.condition
    have hc2 : restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
        restrictProj 𝓔.completionCharts (pointSubscheme x) =
        restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
          pieceBaseι 𝓔 x j :=
      pullback.condition
    change (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j) ≫
      restrictι 𝓔.completionCharts (pointSubscheme x)) ≫ 𝓔.completionToBase = _
    rw [Category.assoc, hc1, ← Category.assoc, hc2, Category.assoc]
  have h1 := residueDegree_comp (pieceι 𝓔 x j) 𝓔.completionToBase a
  rw [residueDegree_congr hcomm, residueDegree_comp
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (restrictι 𝓔.completionCharts (pointSubscheme x)),
    residueDegree_comp (restrictOpenProj 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
      (pieceBaseι 𝓔 x j ≫ (pointSubscheme x).inclusion),
    residueDegree_comp (pieceBaseι 𝓔 x j) (pointSubscheme x).inclusion,
    residueDegree_eq_one_of_isClosedImmersion (restrictι 𝓔.completionCharts (pointSubscheme x)),
    ProperPushforwardDivisor.residueDegree_eq_one_of_isOpenImmersion
      (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j)),
    residueDegree_eq_one_of_isClosedImmersion (pointSubscheme x).inclusion,
    ProperPushforwardDivisor.residueDegree_eq_one_of_isOpenImmersion (pieceBaseι 𝓔 x j)] at h1
  omega

include j hx in
/-- **The generic evaluation of the top iterate for `P(E ⊕ 1)`**: the key hypothesis of
`properPushforward_c1Iter_chowPullbackCharted_of_evalGeneric`, for `x ∈ U_j`. -/
theorem evalGeneric_pushTopIterate_projectiveCompletion (i : ℤ) (hi : dimensionFunction f x = i) :
    evalGeneric (dimensionFunction ((pointSubscheme x).inclusion ≫ f))
      (covByDimension_finiteTypeDimension _) i
      (properPushforwardChowOfProper (restrictProj 𝓔.completionCharts (pointSubscheme x))
        (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))
        ((pointSubscheme x).inclusion ≫ f) (dimensionFunction _) (dimensionFunction _) i
        (c1Iter (restrictι 𝓔.completionCharts (pointSubscheme x) ≫ (𝓔.completionToBase ≫ f))
          ((𝓔.tautological hX).restrict (restrictι 𝓔.completionCharts (pointSubscheme x)))
          (Nat.card ι) i
          (chowCast (by rw [genericPointImage_pointSubscheme, hi])
            (genericRestrictClass 𝓔.completionCharts f
              (𝓔.dimensionFunction_fibrePoint_completionCharts f) (pointSubscheme x))))) = 1 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have := isIntegral_pieceBase 𝓔 x j hx
  have hN := noetherianSpace_of_isOpenImmersion
    (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
  have hcard : (Finset.univ : Finset ι).card = Nat.card ι := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hζ : dimensionFunction (pieceStructure f 𝓔 x j) (piecePoint 𝓔 x j hx Finset.univ) = i := by
    rw [dim_piecePoint, hcard, hi]
    ring
  refine evalGeneric_pushTopIterate_of_open 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) (pointSubscheme x)
    (pieceBaseι 𝓔 x j) i (by rw [genericPointImage_pointSubscheme, hi])
    (piecePoint 𝓔 x j hx Finset.univ) hζ ?_ ?_ ?_
  · refine restrictOpenProj_eq_genericPoint 𝓔 x j hx _ ?_
    rw [pieceι_piecePoint, completionToBase_coordClassPoint, chartBaseι_basePrime]
  · rw [residueDegree_restrictOpenProj, pieceι_piecePoint]
    have h := 𝓔.residueDegree_coordPoint_univ j (basePrime 𝓔 x j hx)
    rwa [← Finset.coe_univ] at h
  · -- the class of the generic point restricts to the class of `piecePoint ∅`
    have hgen : openImmersionPullback (chowSystem _ (i + (Nat.card ι : ℤ)))
        (restrictOpenι 𝓔.completionCharts (pointSubscheme x) (pieceBaseι 𝓔 x j))
        (dim_restrictOpenι 𝓔.completionCharts f (pointSubscheme x) (pieceBaseι 𝓔 x j))
        (chowSystem _ (i + (Nat.card ι : ℤ)))
        (chowCast (by rw [genericPointImage_pointSubscheme, hi])
          (genericRestrictClass 𝓔.completionCharts f
            (𝓔.dimensionFunction_fibrePoint_completionCharts f) (pointSubscheme x))) =
        (chowSystem _ _).quotientMap (cyclesOfDimension.point (piecePoint 𝓔 x j hx ∅)
          (by rw [dim_piecePoint, hi]; simp)) := by
      rw [genericRestrictClass, chowCast_point, openImmersionPullback_quotientMap,
        cyclesOfDimension.point_congr (restrictOpenι_piecePoint_empty 𝓔 x j hx).symm,
        flatPullbackOpen_point]
    rw [hgen]
    have hdeg : i =
        dimensionFunction f x + (Nat.card ι : ℤ) - ((Finset.univ : Finset ι).card : ℤ) := by
      rw [hcard, hi]
      ring
    have h := c1Iter_piecePoint f 𝓔 hX x j hx Finset.univ
    rw [c1Iter_congr_exponent (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) hcard
      (by simp), c1Iter_chowCast (pieceStructure f 𝓔 x j) (pieceBundle 𝓔 hX x j) (Nat.card ι)
      hdeg, chowCast_point] at h
    have h2 := congrArg (chowCast hdeg.symm) h
    rw [chowCast_chowCast, chowCast_self, chowCast_point] at h2
    exact h2

end Main

/-! ## Main theorems for `P(E ⊕ 1)` -/

section Final

open GradedBundleData ChartedOverSubscheme RationalEquivalenceSystem.DescendingMap

variable {k : Type u} [Field k] [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] [NoetherianSpace X] {ι : Type u} [Finite ι]
  (𝓔 : GradedBundleData X ι) (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))

/-- **The Segre identity** for the projective completion `q : P(E ⊕ 1) ⟶ X` of a graded vector
bundle of rank `r = |ι|` over a scheme `X` locally of finite type over an infinite field with
Noetherian underlying space: for every `α ∈ A_i(X)`,
`q_* (c₁(O(1))^r ∩ q^* α) = α`. -/
theorem properPushforward_c1Iter_chowPullbackCharted (i : ℤ)
    (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    properPushforwardChowOfProper 𝓔.completionToBase (𝓔.completionToBase ≫ f) f
        (dimensionFunction (𝓔.completionToBase ≫ f)) (dimensionFunction f) i
        (c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) (Nat.card ι) i
          (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
            (dimensionFunction (𝓔.completionToBase ≫ f))
            (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
            (chowSystem _ (i + (Nat.card ι : ℤ))) α)) = α := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := 𝓔.noetherianSpace_projectiveCompletion f
  refine properPushforward_c1Iter_chowPullbackCharted_of_evalGeneric 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i
    (fun x hx ↦ ?_) α
  obtain ⟨j, hj⟩ : ∃ j, x ∈ (𝓔.bundle.chart j).1 := by
    have hx' : x ∈ ⨆ j, (𝓔.bundle.chart j).1 := by
      rw [𝓔.bundle.iSup_chart]
      trivial
    exact Opens.mem_iSup.mp hx'
  exact evalGeneric_pushTopIterate_projectiveCompletion f 𝓔 hX x j hj i hx

/-- **Vanishing of the lower Segre terms** for `P(E ⊕ 1)`: for `m < r`,
`q_* (c₁(O(1))^m ∩ q^* α) = 0` in `A_{i + r - m}(X)`. -/
theorem properPushforward_c1Iter_chowPullbackCharted_eq_zero (m : ℕ) (hm : m < Nat.card ι)
    (i : ℤ) (α : (chowSystem (dimensionFunction f) i).ChowGroup) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    properPushforwardChowOfProper 𝓔.completionToBase (𝓔.completionToBase ≫ f) f
        (dimensionFunction (𝓔.completionToBase ≫ f)) (dimensionFunction f)
        (i + (Nat.card ι : ℤ) - m)
        (c1Iter (𝓔.completionToBase ≫ f) (𝓔.tautological hX) m (i + (Nat.card ι : ℤ) - m)
          (chowCast (by ring)
            (chowPullbackCharted 𝓔.completionCharts (dimensionFunction f)
              (dimensionFunction (𝓔.completionToBase ≫ f))
              (𝓔.dimensionFunction_fibrePoint_completionCharts f) i (chowSystem _ i)
              (chowSystem _ (i + (Nat.card ι : ℤ))) α))) = 0 :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := 𝓔.noetherianSpace_projectiveCompletion f
  properPushforward_c1Iter_chowPullbackCharted_eq_zero_of_lt 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) m hm (by ring) α

/-- **The injectivity half of the projective bundle formula** (Fulton, Theorem 3.3(b), injectivity)
for `P(E ⊕ 1)`: the map `⨁_{m = 0}^{r} A_{i + m - r}(X) → A_i(P(E ⊕ 1))`,
`(α_m)_m ↦ ∑_m c₁(O(1))^m ∩ q^* α_m`, is injective. -/
theorem projectiveBundleMap_injective (i : ℤ) :
    haveI := 𝓔.noetherianSpace_projectiveCompletion f
    Function.Injective (projectiveBundleMap 𝓔.completionCharts f
      (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX) i) :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := 𝓔.noetherianSpace_projectiveCompletion f
  projectiveBundleMap_injective_of_segre 𝓔.completionCharts f
    (𝓔.dimensionFunction_fibrePoint_completionCharts f) (𝓔.tautological hX)
    (fun j α ↦ properPushforward_c1Iter_chowPullbackCharted f 𝓔 hX j α) i

end Final

end GromovWitten.AlgebraicGeometry.IntersectionTheory
