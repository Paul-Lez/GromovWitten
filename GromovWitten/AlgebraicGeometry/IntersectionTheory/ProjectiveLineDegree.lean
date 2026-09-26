/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroupLocalization
import GromovWitten.AlgebraicGeometry.ProjectiveLine

/-!
# The degree of a principal divisor on the projective line is zero

For `k` a field and `r` a nonzero rational function on `ℙ¹_k` (the scheme constructed in
`GromovWitten/AlgebraicGeometry/ProjectiveLine.lean` by gluing two affine lines), the degree of the
principal cycle `div r` vanishes:

`ZeroCycleDegree.degreeCycle (structureMap k) ((ProjectiveLine.scheme k).principalCycle r) = 0`

This is the key input for Fulton's Proposition 1.4 in the case of a proper curve, and the first
nontrivial instance of "the degree of a principal divisor on a proper variety is zero".

## Proof outline

* `ℙ¹_k` is covered by the first chart `𝔸¹_k = Spec k[t]` and the single extra point `∞`
  (`ProjectiveLine.range_chartZero_eq_compl_infty`), so the (finite, by quasi-compactness) sum
  defining the degree splits as a sum over the chart plus the contribution of `∞`
  (`degreeCycle_split`).
* Orders of vanishing and residue degrees are unchanged by restriction along an open immersion
  (`Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion` from `ChowGroupLocalization.lean`, and
  `residueDegree_openImmersion` proved here), so the sum over the chart is the affine degree of the
  restriction `p/q` of `r`, which is `deg p - deg q` by the scheme form of Fulton's affine length
  formula (`AffineDegreeScheme.degreeCycle_principalCycle_eq_finrank`) together with
  `Module.finrank k (k[t]/(p)) = deg p` (`finrank_quotient_span`).
* The restrictions of `r` to the two charts agree on the overlap `Spec k[t,t⁻¹]`
  (`restrict_agree`, via the functoriality `Scheme.dominantFunctionFieldMap_comp` proved here), and
  the transition map is `t ↦ t⁻¹`.  Hence the restriction of `r` to the second chart is
  `(tᵈᵉᵍ q · reverse p)/(tᵈᵉᵍ p · reverse q)` (`restrictOne_mul_eq`), whose order at the origin of
  the second chart is `deg q - deg p` because `reverse p` and `reverse q` have nonzero constant
  term.  The residue degree at `∞` is `1` (`residueDegree_infty`).

## Main results

* `Scheme.dominantFunctionFieldMap_comp`, `Scheme.dominantFunctionFieldMap_Spec_map_algebraMap`:
  functoriality of the function-field pullback, and its computation for a morphism of affine
  schemes (both are general facts, not specific to `ℙ¹`).
* `residueDegree_openImmersion`: invariance of the residue degree under an open immersion.
* `degreeCycle_split`, `restrictOne_mul_eq`, `residueDegree_infty`.
* `degreeCycle_principalCycle_eq_zero`: the main theorem.
-/

open CategoryTheory Limits AlgebraicGeometry GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- **The canonical function-field pullback is functorial.**  For composable dominant morphisms of
integral schemes, the function-field pullback of the composite is the composite of the pullbacks.
The proof compares the two induced morphisms `Spec K(Z) ⟶ Spec K(X)` after composing with the
monomorphism `Z.fromSpecStalk (genericPoint Z)`, using
`Spec_map_dominantFunctionFieldMap_fromSpecStalk`, and then uses that `Spec` is faithful. -/
lemma dominantFunctionFieldMap_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (g : X ⟶ Y) [IsDominant g] (h : Y ⟶ Z) [IsDominant h] :
    dominantFunctionFieldMap (g ≫ h) =
      (dominantFunctionFieldMap g).comp (dominantFunctionFieldMap h) := by
  have key : Spec.map (CommRingCat.ofHom (dominantFunctionFieldMap (g ≫ h))) =
      Spec.map (CommRingCat.ofHom ((dominantFunctionFieldMap g).comp
        (dominantFunctionFieldMap h))) := by
    rw [← cancel_mono (Z.fromSpecStalk (genericPoint Z)),
      Spec_map_dominantFunctionFieldMap_fromSpecStalk (g ≫ h), CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, Spec_map_dominantFunctionFieldMap_fromSpecStalk h,
      ← Category.assoc, ← Category.assoc, Spec_map_dominantFunctionFieldMap_fromSpecStalk g]
  exact CommRingCat.hom_ext_iff.mp (Spec.map_injective key)

/-- A variant of `dominantFunctionFieldMap_comp` for a morphism given as a composite by an
equation, avoiding a rewrite under the `IsDominant` instance argument. -/
lemma dominantFunctionFieldMap_comp' {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (g : X ⟶ Y) [IsDominant g] (h : Y ⟶ Z) [IsDominant h] (gh : X ⟶ Z)
    [IsDominant gh] (hgh : g ≫ h = gh) :
    dominantFunctionFieldMap gh =
      (dominantFunctionFieldMap g).comp (dominantFunctionFieldMap h) := by
  subst hgh
  exact dominantFunctionFieldMap_comp g h

/-- The canonical map from an integral ring into the function field of its spectrum, as a
morphism of `CommRingCat` with syntactically correct source and target (unlike
`StructureSheaf.toStalk`, whose source is `CommRingCat.of ↑B`). -/
noncomputable def toFunctionFieldHom (B : CommRingCat.{u}) [IsDomain B] :
    B ⟶ (Spec B).functionField :=
  CommRingCat.ofHom (algebraMap B (Spec B).functionField)

@[simp] lemma toFunctionFieldHom_hom (B : CommRingCat.{u}) [IsDomain B] (b : B) :
    (toFunctionFieldHom B).hom b = algebraMap B (Spec B).functionField b := rfl

-- The equality of the two morphisms below holds only up to definitional unfolding of the types
-- `CommRingCat.of ↑B` and `B`, exactly as in the Mathlib declaration of `Spec.map_comp`.
set_option backward.isDefEq.respectTransparency false in
/-- `toFunctionFieldHom` is the structure-sheaf map to the stalk at the generic point. -/
lemma toFunctionFieldHom_eq_toStalk (B : CommRingCat.{u}) [IsDomain B] :
    toFunctionFieldHom B = StructureSheaf.toStalk B (genericPoint (Spec B)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Spec` of `toFunctionFieldHom` is the canonical morphism from the spectrum of the stalk at the
generic point. -/
lemma spec_map_toFunctionFieldHom (B : CommRingCat.{u}) [IsDomain B] :
    Spec.map (toFunctionFieldHom B) = (Spec B).fromSpecStalk (genericPoint (Spec B)) := by
  rw [toFunctionFieldHom_eq_toStalk, ← Spec.fromSpecStalk_eq']

set_option backward.isDefEq.respectTransparency false in
/-- **The function-field pullback along a morphism of affine schemes extends the given ring map.**
For `φ : B₁ ⟶ B₂` a homomorphism of integral rings with `Spec.map φ` dominant, the induced map on
function fields extends `φ`.  Proved by comparing the two morphisms `Spec K(B₁) ⟶ Spec B₂` obtained
from `Spec_map_dominantFunctionFieldMap_fromSpecStalk` and using that `Spec` is faithful. -/
lemma dominantFunctionFieldMap_Spec_map_algebraMap {B₁ B₂ : CommRingCat.{u}} [IsDomain B₁]
    [IsDomain B₂] (φ : B₁ ⟶ B₂) [IsDominant (Spec.map φ)] (b : B₁) :
    dominantFunctionFieldMap (Spec.map φ) (algebraMap B₁ (Spec B₁).functionField b) =
      algebraMap B₂ (Spec B₂).functionField (φ.hom b) := by
  have key : toFunctionFieldHom B₁ ≫
      CommRingCat.ofHom (dominantFunctionFieldMap (Spec.map φ)) =
      φ ≫ toFunctionFieldHom B₂ := by
    apply Spec.map_injective
    simp only [Spec.map_comp, spec_map_toFunctionFieldHom]
    exact Spec_map_dominantFunctionFieldMap_fromSpecStalk (Spec.map φ)
  have h0 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp key) b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    toFunctionFieldHom_hom] at h0
  exact h0

end AlgebraicGeometry.Scheme

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveLineDegree

open ProjectiveLine

variable {k : Type u} [Field k]

/-- **The residue degree at a point is unchanged by pulling back along an open immersion.**
The open-immersion counterpart of `AffineDegreeScheme.residueDegree_closedImmersion`, with the same
proof: an open immersion induces an isomorphism on residue fields. -/
theorem residueDegree_openImmersion {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) :
    ZeroCycleDegree.residueDegree (i ≫ f) z = ZeroCycleDegree.residueDegree f (i.base z) := by
  apply (AffineDegreeScheme.finrank_congr'' (FiniteTypeDimension.residueMap f (i.base z))
    (FiniteTypeDimension.residueMap (i ≫ f) z)
    (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv _).symm
  intro c
  change (asIso (i.residueFieldMap z)).hom.hom
      (FiniteTypeDimension.residueMap f (i.base z) c) = FiniteTypeDimension.residueMap (i ≫ f) z c
  exact FiniteTypeDimension.residueFieldMap_residueMap f i z c

section ProjectiveLine

variable (k : Type u) [Field k]

/-! ## Dominance and algebra instances for the charts of `ℙ¹_k` -/

instance : IsDominant (chartZero k) := Scheme.isDominant_of_isOpenImmersion _

instance : IsDominant (chartOne k) := Scheme.isDominant_of_isOpenImmersion _

instance : IsDominant (overlapToChartZero k) := Scheme.isDominant_of_isOpenImmersion _

instance : IsDominant (overlapToChartOne k) := Scheme.isDominant_of_isOpenImmersion _

/-- The gluing map of the overlap into `ℙ¹_k` is dominant. -/
instance instIsDominantOverlapι : IsDominant (overlapι k) :=
  Scheme.isDominant_of_isOpenImmersion _

/-- The `k[t]`-algebra structure on the function field of a chart.  This is Mathlib's instance
specialised by hand: instance search does not find it for the concrete ring
`CommRingCat.of (Polynomial k)`. -/
noncomputable instance chartFunctionFieldAlgebra :
    Algebra (Polynomial k) ((chart k).functionField) :=
  _root_.AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial k))

/-- The `k[t,t⁻¹]`-algebra structure on the function field of the overlap. -/
noncomputable instance overlapFunctionFieldAlgebra :
    Algebra (overlapRing k) ((overlap k).functionField) :=
  _root_.AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (overlapRing k))

instance : IsFractionRing (Polynomial k) ((chart k).functionField) :=
  _root_.AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial k))

instance : IsFractionRing (overlapRing k) ((overlap k).functionField) :=
  _root_.AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (overlapRing k))

/-! ## Restriction of rational functions to the charts -/

/-- Restriction of a rational function on `ℙ¹_k` to the first chart. -/
noncomputable def restrictZero :
    (ProjectiveLine.scheme k).functionField →+* (chart k).functionField :=
  Scheme.dominantFunctionFieldMap (chartZero k)

/-- Restriction of a rational function on `ℙ¹_k` to the second chart. -/
noncomputable def restrictOne :
    (ProjectiveLine.scheme k).functionField →+* (chart k).functionField :=
  Scheme.dominantFunctionFieldMap (chartOne k)

/-- **The two restrictions of a rational function agree on the overlap.** -/
theorem restrict_agree (r : (ProjectiveLine.scheme k).functionField) :
    Scheme.dominantFunctionFieldMap (overlapToChartZero k) (restrictZero k r) =
      Scheme.dominantFunctionFieldMap (overlapToChartOne k) (restrictOne k r) := by
  have h0 := Scheme.dominantFunctionFieldMap_comp' (overlapToChartZero k) (chartZero k)
    (overlapι k) (overlapToChartZero_comp k)
  have h1 := Scheme.dominantFunctionFieldMap_comp' (overlapToChartOne k) (chartOne k)
    (overlapι k) (overlapToChartOne_comp k)
  exact RingHom.congr_fun (h0.symm.trans h1) r

/-- Restricting to the overlap through the first chart is the localization map. -/
theorem overlapZero_algebraMap (p : Polynomial k) :
    Scheme.dominantFunctionFieldMap (overlapToChartZero k)
        (algebraMap (Polynomial k) ((chart k).functionField) p) =
      algebraMap (overlapRing k) ((overlap k).functionField)
        (algebraMap (Polynomial k) (overlapRing k) p) :=
  Scheme.dominantFunctionFieldMap_Spec_map_algebraMap
    (CommRingCat.ofHom (algebraMap (Polynomial k) (overlapRing k))) p

/-- Restricting to the overlap through the second chart is the transition map. -/
theorem overlapOne_algebraMap (p : Polynomial k) :
    Scheme.dominantFunctionFieldMap (overlapToChartOne k)
        (algebraMap (Polynomial k) ((chart k).functionField) p) =
      algebraMap (overlapRing k) ((overlap k).functionField) (flipHom k p) :=
  Scheme.dominantFunctionFieldMap_Spec_map_algebraMap (CommRingCat.ofHom (flipHom k)) p

/-! ## The transition map and reversed polynomials -/

/-- The image of the coordinate in `k[t,t⁻¹]` is invertible, with inverse `tInv`. -/
noncomputable instance invertibleAlgebraMapX :
    Invertible (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) :=
  ⟨tInv k, (mul_comm _ _).trans (algebraMap_X_mul_tInv k), algebraMap_X_mul_tInv k⟩

/-- Evaluating a polynomial at the image of the coordinate reproduces the localization map. -/
theorem eval₂_algebraMap (s : Polynomial k) :
    Polynomial.eval₂ ((algebraMap (Polynomial k) (overlapRing k)).comp Polynomial.C)
        (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) s =
      algebraMap (Polynomial k) (overlapRing k) s := by
  have h : Polynomial.eval₂RingHom
      ((algebraMap (Polynomial k) (overlapRing k)).comp Polynomial.C)
      (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) =
      algebraMap (Polynomial k) (overlapRing k) := by
    apply Polynomial.ringHom_ext <;> simp
  exact RingHom.congr_fun h s

/-- **The transition map sends the reverse of a polynomial to the polynomial divided by `t` to
the degree.**  This is Mathlib's `Polynomial.eval₂_reverse_mul_pow` for the localization map. -/
theorem flipHom_reverse_mul_pow (s : Polynomial k) :
    flipHom k s.reverse *
        (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) ^ s.natDegree =
      algebraMap (Polynomial k) (overlapRing k) s := by
  have h := @Polynomial.eval₂_reverse_mul_pow k _ (overlapRing k) _
    ((algebraMap (Polynomial k) (overlapRing k)).comp Polynomial.C)
    (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) (invertibleAlgebraMapX k) s
  rw [eval₂_algebraMap] at h
  exact h

/-- The transition map applied to `tⁿ * (reverse s)`, cleared of denominators. -/
theorem flipHom_pow_mul_reverse (n : ℕ) (s : Polynomial k) :
    flipHom k (Polynomial.X ^ n * s.reverse) *
        (algebraMap (Polynomial k) (overlapRing k) Polynomial.X) ^ (n + s.natDegree) =
      algebraMap (Polynomial k) (overlapRing k) s := by
  rw [map_mul, map_pow, flipHom_X, pow_add, ← mul_assoc, mul_comm (tInv k ^ n),
    mul_assoc, mul_assoc, ← mul_assoc (tInv k ^ n), ← mul_pow,
    mul_comm (tInv k) (algebraMap (Polynomial k) (overlapRing k) Polynomial.X),
    algebraMap_X_mul_tInv, one_pow, one_mul, flipHom_reverse_mul_pow]

/-! ## Orders of vanishing at the origin of a chart -/

/-- A polynomial with nonzero constant term does not lie in the prime of the origin. -/
theorem notMem_origin_of_coeff_ne_zero (s : Polynomial k) (hs : s.coeff 0 ≠ 0) :
    s ∉ (origin k).asIdeal := by
  intro hmem
  change s ∈ Ideal.span {(Polynomial.X : Polynomial k)} at hmem
  exact hs (Polynomial.X_dvd_iff.mp (Ideal.mem_span_singleton.mp hmem))

/-- The prime of the origin is nonzero. -/
theorem origin_asIdeal_ne_bot : (origin k).asIdeal ≠ ⊥ := by
  have hmem : (Polynomial.X : Polynomial k) ∈ (origin k).asIdeal :=
    Ideal.mem_span_singleton_self _
  intro h
  rw [h] at hmem
  exact Polynomial.X_ne_zero (Ideal.mem_bot.mp hmem)

/-- **A polynomial with nonzero constant term has order of vanishing zero at the origin.** -/
theorem ord_origin_eq_zero (s : Polynomial k) (hs : s.coeff 0 ≠ 0) :
    (chart k).ord (algebraMap (Polynomial k) ((chart k).functionField) s) (origin k) = 0 :=
  VectorBundle.ord_algebraMap_eq_zero_of_notMem (CommRingCat.of (Polynomial k)) (origin k) s
    (notMem_origin_of_coeff_ne_zero k s hs)

/-- **The coordinate has order of vanishing one at the origin.** -/
theorem ord_origin_X :
    (chart k).ord (algebraMap (Polynomial k) ((chart k).functionField) Polynomial.X)
      (origin k) = 1 := by
  refine VectorBundle.ord_algebraMap_eq_one (CommRingCat.of (Polynomial k)) (origin k)
    Polynomial.X Polynomial.X_ne_zero
    (AffineDegreeScheme.coheight_eq_one_of_ne_bot (A := Polynomial k) (origin k)
      (origin_asIdeal_ne_bot k)) ?_
  intro S _ _ _
  change Ideal.map _ (Ideal.span {(Polynomial.X : Polynomial k)}) = _
  rw [Ideal.map_span, Set.image_singleton]

/-! ## The degree of a principal cycle on a chart -/

/-- The `k`-dimension of `k[t]/(p)` is the degree of `p`. -/
theorem finrank_quotient_span (p : Polynomial k) (hp : p ≠ 0) :
    Module.finrank k (Polynomial k ⧸ Ideal.span {p}) = p.natDegree := by
  have h1 : Module.finrank k (AdjoinRoot p) = p.natDegree := by
    rw [(AdjoinRoot.powerBasis hp).finrank, AdjoinRoot.powerBasis_dim]
  exact h1

/-- **The degree of the principal cycle of a polynomial on the chart `𝔸¹_k` is its degree.** -/
theorem degreeCycle_chart_algebraMap (p : Polynomial k) (hp : p ≠ 0) :
    ZeroCycleDegree.degreeCycle (chartToSpecK k)
        ((chart k).principalCycle (algebraMap (Polynomial k) ((chart k).functionField) p)) =
      (p.natDegree : ℚ) := by
  have h := AffineDegreeScheme.degreeCycle_principalCycle_eq_finrank (k := k) (A := Polynomial k)
    p hp
  rw [finrank_quotient_span k p hp] at h
  exact h

/-! ## The order of vanishing of a power -/

/-- The order of vanishing of a power of a nonzero rational function. -/
theorem ord_pow {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X.functionField} (hf : f ≠ 0) (x : X) (n : ℕ) :
    X.ord (f ^ n) x = n * X.ord f x := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero m hf) hf, ih]
    push_cast
    ring

/-- A nonzero polynomial has nonzero image in the function field of a chart. -/
theorem algebraMap_ne_zero (s : Polynomial k) (hs : s ≠ 0) :
    algebraMap (Polynomial k) ((chart k).functionField) s ≠ 0 := fun h =>
  hs (IsFractionRing.injective (Polynomial k) ((chart k).functionField) (by rw [h, map_zero]))

/-- **The order of vanishing of `tⁿ * s` at the origin is `n`,** provided `s` has nonzero constant
term. -/
theorem ord_origin_X_pow_mul (n : ℕ) (s : Polynomial k) (hs : s.coeff 0 ≠ 0) :
    (chart k).ord (algebraMap (Polynomial k) ((chart k).functionField) (Polynomial.X ^ n * s))
      (origin k) = n := by
  have hs0 : s ≠ 0 := fun h => hs (by rw [h, Polynomial.coeff_zero])
  have hX : algebraMap (Polynomial k) ((chart k).functionField) Polynomial.X ≠ 0 :=
    algebraMap_ne_zero k Polynomial.X Polynomial.X_ne_zero
  rw [map_mul, map_pow,
    Scheme.ord_mul (pow_ne_zero n hX) (algebraMap_ne_zero k s hs0),
    ord_pow hX (origin k) n, ord_origin_X, ord_origin_eq_zero k s hs, mul_one, add_zero]

/-! ## Splitting the degree over the first chart and the point at infinity -/

/-- **The degree of a principal cycle on `ℙ¹_k` splits as the degree of its restriction to the
first chart plus the contribution of the point at infinity.** -/
theorem degreeCycle_split (r : (ProjectiveLine.scheme k).functionField) :
    ZeroCycleDegree.degreeCycle (structureMap k)
        ((ProjectiveLine.scheme k).principalCycle r) =
      ZeroCycleDegree.degreeCycle (chartToSpecK k)
          ((chart k).principalCycle (restrictZero k r)) +
        ((ProjectiveLine.scheme k).ord r (infty k) : ℚ) *
          (ZeroCycleDegree.residueDegree (structureMap k) (infty k) : ℚ) := by
  classical
  set α := (ProjectiveLine.scheme k).principalCycle r with hα
  set g : ProjectiveLine.scheme k → ℚ :=
    fun x => α x * (ZeroCycleDegree.residueDegree (structureMap k) x : ℚ) with hg
  have hsupp : (Function.support g).Finite :=
    (ZeroCycleDegree.finite_support α).subset
      (Function.support_mul_subset_left _ _)
  have huniv : (Set.univ : Set (ProjectiveLine.scheme k)) =
      Set.range (chartZero k).base ∪ {infty k} := by
    rw [range_chartZero_eq_compl_infty]
    exact (Set.compl_union_self _).symm
  have hdisj : Disjoint (Set.range (chartZero k).base) ({infty k} : Set _) := by
    rw [range_chartZero_eq_compl_infty]
    exact disjoint_compl_left
  have hinj : Function.Injective (chartZero k).base :=
    (chartZero k).isOpenEmbedding.injective
  have hpt : ∀ y : chart k, g ((chartZero k).base y) =
      ((chart k).principalCycle (restrictZero k r)) y *
        (ZeroCycleDegree.residueDegree (chartToSpecK k) y : ℚ) := by
    intro y
    have hord : (chart k).ord (restrictZero k r) y =
        (ProjectiveLine.scheme k).ord r ((chartZero k).base y) :=
      Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion (chartZero k) y r
    have hres : ZeroCycleDegree.residueDegree (chartZero k ≫ structureMap k) y =
        ZeroCycleDegree.residueDegree (structureMap k) ((chartZero k).base y) :=
      residueDegree_openImmersion (structureMap k) (chartZero k) y
    rw [chartZero_comp_structureMap] at hres
    rw [hg]
    simp only [hα, Scheme.principalCycle_apply, ← hord, ← hres]
  rw [ZeroCycleDegree.degreeCycle_apply, ZeroCycleDegree.degreeCycle_apply]
  rw [show (∑ᶠ x, α x * (ZeroCycleDegree.residueDegree (structureMap k) x : ℚ)) = ∑ᶠ x, g x from
    rfl, ← finsum_mem_univ g, huniv,
    finsum_mem_union' hdisj (hsupp.subset Set.inter_subset_right)
      (hsupp.subset Set.inter_subset_right),
    finsum_mem_range hinj, finsum_mem_singleton, finsum_congr hpt]
  rw [hg]
  simp only [hα, Scheme.principalCycle_apply]

/-! ## The point at infinity has residue degree one -/

/-- The origin of a chart, as a point of the maximal spectrum of `k[t]`. -/
noncomputable def originMax : MaximalSpectrum (Polynomial k) :=
  ⟨Ideal.span {(Polynomial.X : Polynomial k)},
    PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X⟩

@[simp] theorem originMax_asIdeal :
    (originMax k).asIdeal = Ideal.span {(Polynomial.X : Polynomial k)} := rfl

/-- **The residue field of the origin of a chart is `k` itself.** -/
theorem residueDegree_origin :
    ZeroCycleDegree.residueDegree (chartToSpecK k) (origin k) = 1 := by
  have h := AffineDegreeScheme.residueDegree_eq_finrank_quotient (k := k) (A := Polynomial k)
    (originMax k)
  rw [originMax_asIdeal, finrank_quotient_span k Polynomial.X Polynomial.X_ne_zero,
    Polynomial.natDegree_X] at h
  exact h

/-- **The residue field of the point at infinity is `k` itself.** -/
theorem residueDegree_infty :
    ZeroCycleDegree.residueDegree (structureMap k) (infty k) = 1 := by
  have h := residueDegree_openImmersion (structureMap k) (chartOne k) (origin k)
  rw [chartOne_comp_structureMap, residueDegree_origin] at h
  exact h.symm

/-- The order of vanishing at the point at infinity is computed on the second chart. -/
theorem ord_infty (r : (ProjectiveLine.scheme k).functionField) :
    (ProjectiveLine.scheme k).ord r (infty k) =
      (chart k).ord (restrictOne k r) (origin k) :=
  (Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion (chartOne k) (origin k) r).symm

/-! ## The transition identity -/

/-- **The transition identity.**  If the restriction of `r` to the first chart is `p/q`, then its
restriction to the second chart is `(reverse p · tᵈᵉᵍ q)/(tᵈᵉᵍ p · reverse q)`.  This is the
substitution `t ↦ t⁻¹` written without denominators. -/
theorem restrictOne_mul_eq (r : (ProjectiveLine.scheme k).functionField) (p q : Polynomial k)
    (hw : restrictZero k r * algebraMap (Polynomial k) ((chart k).functionField) q =
      algebraMap (Polynomial k) ((chart k).functionField) p) :
    restrictOne k r *
        algebraMap (Polynomial k) ((chart k).functionField)
          (Polynomial.X ^ p.natDegree * q.reverse) =
      algebraMap (Polynomial k) ((chart k).functionField)
        (Polynomial.X ^ q.natDegree * p.reverse) := by
  have e1 : ∀ (n : ℕ) (s : Polynomial k),
      algebraMap (overlapRing k) ((overlap k).functionField)
            (flipHom k (Polynomial.X ^ n * s.reverse)) *
          algebraMap (overlapRing k) ((overlap k).functionField)
            ((algebraMap (Polynomial k) (overlapRing k) Polynomial.X) ^ (n + s.natDegree)) =
        algebraMap (overlapRing k) ((overlap k).functionField)
          (algebraMap (Polynomial k) (overlapRing k) s) := by
    intro n s
    rw [← map_mul, flipHom_pow_mul_reverse]
  have hψ : Scheme.dominantFunctionFieldMap (overlapToChartZero k) (restrictZero k r) *
      algebraMap (overlapRing k) ((overlap k).functionField)
        (algebraMap (Polynomial k) (overlapRing k) q) =
      algebraMap (overlapRing k) ((overlap k).functionField)
        (algebraMap (Polynomial k) (overlapRing k) p) := by
    rw [← overlapZero_algebraMap k q, ← map_mul, hw, overlapZero_algebraMap k p]
  have hc : algebraMap (overlapRing k) ((overlap k).functionField)
      ((algebraMap (Polynomial k) (overlapRing k) Polynomial.X) ^
        (p.natDegree + q.natDegree)) ≠ 0 := by
    refine fun h => ?_
    have hzero : ((algebraMap (Polynomial k) (overlapRing k) Polynomial.X) ^
        (p.natDegree + q.natDegree) : overlapRing k) = 0 :=
      IsFractionRing.injective (overlapRing k) ((overlap k).functionField) (by rw [h, map_zero])
    exact (pow_ne_zero _ (IsUnit.ne_zero ⟨⟨_, tInv k, algebraMap_X_mul_tInv k,
      (mul_comm _ _).trans (algebraMap_X_mul_tInv k)⟩, rfl⟩)) hzero
  apply (Scheme.dominantFunctionFieldMap (overlapToChartOne k)).injective
  rw [map_mul, ← restrict_agree, overlapOne_algebraMap, overlapOne_algebraMap]
  refine mul_right_cancel₀ hc ?_
  rw [mul_assoc, e1 p.natDegree q, hψ, add_comm p.natDegree q.natDegree, e1 q.natDegree p]

/-! ## The main theorem -/

/-- **The degree of a principal divisor on `ℙ¹_k` is zero.**  For every nonzero rational function
`r` on the projective line over a field `k`, the degree of the associated principal cycle (the
divisor of `r`) vanishes: the zeros and poles of `r` on the affine chart contribute
`deg p - deg q`, and the point at infinity contributes `deg q - deg p`. -/
theorem degreeCycle_principalCycle_eq_zero (r : (ProjectiveLine.scheme k).functionField)
    (hr : r ≠ 0) :
    ZeroCycleDegree.degreeCycle (structureMap k)
      ((ProjectiveLine.scheme k).principalCycle r) = 0 := by
  obtain ⟨p, q, hqmem, hpq⟩ :=
    IsFractionRing.div_surjective (A := Polynomial k) (restrictZero k r)
  have hq : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hqmem
  have hAq : algebraMap (Polynomial k) ((chart k).functionField) q ≠ 0 :=
    algebraMap_ne_zero k q hq
  have hw : restrictZero k r * algebraMap (Polynomial k) ((chart k).functionField) q =
      algebraMap (Polynomial k) ((chart k).functionField) p := by
    rw [← hpq, div_mul_cancel₀ _ hAq]
  have hwne : restrictZero k r ≠ 0 := fun h =>
    hr ((restrictZero k).injective (by rw [h, map_zero]))
  have hvne : restrictOne k r ≠ 0 := fun h =>
    hr ((restrictOne k).injective (by rw [h, map_zero]))
  have hp : p ≠ 0 := by
    intro h
    rw [h, map_zero] at hw
    exact hwne ((mul_eq_zero.mp hw).resolve_right hAq)
  have hchart : ZeroCycleDegree.degreeCycle (chartToSpecK k)
      ((chart k).principalCycle (restrictZero k r)) = (p.natDegree : ℚ) - q.natDegree := by
    have hcyc : (chart k).principalCycle (restrictZero k r) =
        (chart k).principalCycle (algebraMap (Polynomial k) ((chart k).functionField) p) -
          (chart k).principalCycle (algebraMap (Polynomial k) ((chart k).functionField) q) := by
      rw [← hpq, div_eq_mul_inv,
        Scheme.principalCycle_mul (algebraMap_ne_zero k p hp) (inv_ne_zero hAq),
        Scheme.principalCycle_inv hAq, ← sub_eq_add_neg]
    rw [hcyc, map_sub, degreeCycle_chart_algebraMap k p hp, degreeCycle_chart_algebraMap k q hq]
  have hrevq : (q.reverse).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have hrevp : (p.reverse).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hmulne : (Polynomial.X ^ p.natDegree * q.reverse : Polynomial k) ≠ 0 := by
    intro h
    exact hrevq (by rw [(mul_eq_zero.mp h).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero),
      Polynomial.coeff_zero])
  have hord : (ProjectiveLine.scheme k).ord r (infty k) =
      (q.natDegree : ℤ) - p.natDegree := by
    have hkey := restrictOne_mul_eq k r p q hw
    have hordeq := congrArg (fun z : (chart k).functionField =>
      (chart k).ord z (origin k)) hkey
    rw [Scheme.ord_mul hvne (algebraMap_ne_zero k _ hmulne),
      ord_origin_X_pow_mul k p.natDegree q.reverse hrevq,
      ord_origin_X_pow_mul k q.natDegree p.reverse hrevp] at hordeq
    rw [ord_infty]
    omega
  rw [degreeCycle_split, hchart, hord, residueDegree_infty]
  push_cast
  ring

/-- **The degree of the principal divisor of a unit of the function field of `ℙ¹_k` is zero.**
The version of `degreeCycle_principalCycle_eq_zero` for a unit of the function field, which is the
form in which rational functions are packaged elsewhere in this library. -/
theorem degreeCycle_principalCycle_units_eq_zero
    (r : (ProjectiveLine.scheme k).functionFieldˣ) :
    ZeroCycleDegree.degreeCycle (structureMap k)
      ((ProjectiveLine.scheme k).principalCycle
        (r : (ProjectiveLine.scheme k).functionField)) = 0 :=
  degreeCycle_principalCycle_eq_zero k r r.ne_zero

end ProjectiveLine

end GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveLineDegree
