/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProjectiveLineDegree
import GromovWitten.AlgebraicGeometry.IntersectionTheory.NormPushforward
import GromovWitten.AlgebraicGeometry.Curves.RationalFunctionToProjectiveLine

/-!
# The degree of a principal divisor on a proper curve

Let `k` be a field and `W` an integral curve, proper over `k`.  The goal of this file is the
statement that the degree of a principal divisor on `W` vanishes:

`ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0`

for every nonzero `r : W.functionField`.

## Strategy

`W` is covered by the two opens `U₀` (where `r` is regular) and `U₁` (where `r⁻¹` is regular);
this is `Scheme.regularLocus_sup_regularLocus_inv_eq_top` for a regular curve.  Writing `dᵢ` for
the degree of the principal cycle of the restriction of `r` (resp. `r⁻¹`) to `Uᵢ`, the degree
splits as

`deg (div r) = d₀ - d₁`

(`degreeCycle_principalCycle_eq_sub`): the terms over `U₀ ⊓ U₁` cancel because `r` is a unit
there.  Each `dᵢ` is computed by the affine length formula of `AffineDegreeScheme`
(`degreeCycle_principalCycle_eq_finrank`) once `Uᵢ` is known to be affine; over the first chart of
`ℙ¹` the affine coordinate ring `Bᵢ` is a finite free `k[t]`-module and `dᵢ` is its rank, so
`d₀ = d₁ = [K(W) : k(t)]`.

## Main declarations

* `degreeCycle_eq_finsum_add_finsum`, `degreeCycle_comp_eq_finsum_range`,
  `degreeCycle_restrict_eq_finsum`, `degreeCycle_split_opens` — the degree of a principal cycle as
  a sum of partial degrees over an open subset (or the image of a dominant open immersion) and its
  complement.
* `degreeCycle_principalCycle_eq_sub_finsum` / `degreeCycle_principalCycle_eq_sub` — for two opens
  covering `W` on which `r` and `r⁻¹` are regular, `deg (div r) = d₀ - d₁`.
* `ord_eq_zero_of_mem_regularLocus_inf` — `r` is a unit, hence has order of vanishing zero, on the
  overlap of the domains of definition of `r` and `r⁻¹`.
* `finsum_eq_finrank_of_openImmersion` — the partial degree over an affine chart
  `j : Spec B ⟶ W` is `dim_k (B ⧸ (b))`, where `b : B` represents `r`.
* `degreeCycle_principalCycle_eq_zero_of_finsum_eq`,
  `degreeCycle_principalCycle_eq_zero_of_degreeCycle_eq`,
  `degreeCycle_principalCycle_eq_zero_of_finsum_eq_of_isDiscreteValuationRing` and
  `degreeCycle_principalCycle_eq_zero_of_affineCharts` — `deg (div r) = 0` as soon as the two
  partial degrees agree, the last one in terms of two affine charts.
* `degreeCycle_principalCycle_eq_zero_of_isUnit` — the trivial case of a global unit.
* `finrank_tensorProduct_eq_finrank`, `finrank_quotient_smul_eq_finrank`,
  `finrank_quotient_map_eq_finrank`, `finrank_quotient_span_X_eq_finrank`,
  `finrank_localization_eq_finrank`, `free_of_finite_of_injective` — the algebra needed to identify
  the two chart dimensions with `[K(W) : k(t)]`.

-/

universe u

open CategoryTheory AlgebraicGeometry Topology

open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree

open GromovWitten.AlgebraicGeometry.IntersectionTheory

variable {k : Type u} [Field k]

/-! ## The order of vanishing of an inverse -/

/-- The order of vanishing of the inverse of a nonzero rational function is the negative of the
order of vanishing of the function. -/
theorem ord_inv {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian W] (r : W.functionField) (x : W) :
    W.ord r⁻¹ x = -W.ord r x := by
  rcases eq_or_ne r 0 with hr | hr
  · simp [hr]
  have hinv : r⁻¹ ≠ 0 := inv_ne_zero hr
  have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  have := AlgebraicGeometry.Scheme.ord_mul (X := W) (x := x) hr hinv
  rw [h1] at this
  have h0 : W.ord (1 : W.functionField) x = 0 := congrFun AlgebraicGeometry.Scheme.ord_one x
  omega

/-! ## Splitting the degree of a principal cycle over an open subscheme -/

/-- **The degree of a principal cycle splits over an open subset and its complement.** -/
theorem degreeCycle_eq_finsum_add_finsum {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (r : W.functionField) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) =
      (∑ᶠ x ∈ (U : Set W), (W.ord r x : ℚ) * (ZeroCycleDegree.residueDegree f x : ℚ)) +
        ∑ᶠ x ∈ ((U : Set W)ᶜ), (W.ord r x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ) := by
  classical
  set g : W → ℚ := fun x => (W.ord r x : ℚ) *
    (ZeroCycleDegree.residueDegree f x : ℚ) with hg
  have hsupp : (Function.support g).Finite :=
    (ZeroCycleDegree.finite_support (W.principalCycle r)).subset
      (Function.support_mul_subset_left _ _)
  rw [ZeroCycleDegree.degreeCycle_apply,
    show (∑ᶠ x, (W.principalCycle r) x * (ZeroCycleDegree.residueDegree f x : ℚ)) =
      ∑ᶠ x, g x from rfl, ← finsum_mem_univ g,
    show (Set.univ : Set W) = (U : Set W) ∪ ((U : Set W)ᶜ) from (Set.union_compl_self _).symm,
    finsum_mem_union' disjoint_compl_right (hsupp.subset Set.inter_subset_right)
      (hsupp.subset Set.inter_subset_right)]

/-- **The degree of the principal cycle pulled back along a dominant open immersion is the partial
sum of the degree of `div r` over the image.**  The order of vanishing and the residue degree are
both unchanged by a dominant open immersion, so this is just a reindexing of the defining sum. -/
theorem degreeCycle_comp_eq_finsum_range {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of k)) {Z : Scheme.{u}} (j : Z ⟶ W) [IsOpenImmersion j]
    [IsDominant j] [_root_.AlgebraicGeometry.IsIntegral Z]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian Z] [CompactSpace Z] (r : W.functionField) :
    ZeroCycleDegree.degreeCycle (j ≫ f)
        (Z.principalCycle (Scheme.dominantFunctionFieldMap j r)) =
      ∑ᶠ x ∈ Set.range j.base, (W.ord r x : ℚ) *
        (ZeroCycleDegree.residueDegree f x : ℚ) := by
  rw [ZeroCycleDegree.degreeCycle_apply, finsum_mem_range j.isOpenEmbedding.injective]
  refine finsum_congr fun y => ?_
  have hord : Z.ord (Scheme.dominantFunctionFieldMap j r) y = W.ord r (j.base y) :=
    Scheme.ord_dominantFunctionFieldMap_of_isOpenImmersion j y r
  have hres : ZeroCycleDegree.residueDegree (j ≫ f) y =
      ZeroCycleDegree.residueDegree f (j.base y) :=
    ProjectiveLineDegree.residueDegree_openImmersion f j y
  simp only [Scheme.principalCycle_apply, hord, hres]

/-- **The degree of the principal cycle of the restriction of `r` to an open subscheme `U` is the
partial sum of the degree of `div r` over the points of `U`.** -/
theorem degreeCycle_restrict_eq_finsum {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) [Nonempty U] [CompactSpace U]
    (r : W.functionField) :
    ZeroCycleDegree.degreeCycle (U.ι ≫ f)
        ((U.toScheme).principalCycle (Scheme.dominantFunctionFieldMap U.ι r)) =
      ∑ᶠ x ∈ (U : Set W), (W.ord r x : ℚ) *
        (ZeroCycleDegree.residueDegree f x : ℚ) := by
  rw [degreeCycle_comp_eq_finsum_range f U.ι r, U.range_ι]

/-- **The degree of a principal cycle splits as the degree of its restriction to an open
subscheme plus the contribution of the complement.**  This is the general form of
`ProjectiveLineDegree.degreeCycle_split` (where the open subscheme is the first chart of `ℙ¹` and
the complement is the single point at infinity). -/
theorem degreeCycle_split_opens {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian W] [CompactSpace W]
    (f : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) [Nonempty U] [CompactSpace U]
    (r : W.functionField) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) =
      ZeroCycleDegree.degreeCycle (U.ι ≫ f)
          ((U.toScheme).principalCycle (Scheme.dominantFunctionFieldMap U.ι r)) +
        ∑ᶠ x ∈ ((U : Set W)ᶜ), (W.ord r x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ) := by
  rw [degreeCycle_restrict_eq_finsum f U r, degreeCycle_eq_finsum_add_finsum f U r]

/-! ## The degree as the difference of the contributions of two covering opens -/

/-- **The degree of `div r` is the difference of the two partial degrees attached to a pair of
opens covering `W`.**  If `U₀ ⊔ U₁ = ⊤` and `r` is a unit at every point of `U₀ ⊓ U₁` (`hz`) then
the degree of `div r` is the partial sum over `U₀` of `ord_x(r) · [κ(x):k]` minus the partial sum
over `U₁` of `ord_x(r⁻¹) · [κ(x):k]`.  The point is that the two partial sums are computable by the
affine length formula when the `Uᵢ` are affine. -/
theorem degreeCycle_principalCycle_eq_sub_finsum {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (U₀ U₁ : W.Opens) (hcov : U₀ ⊔ U₁ = ⊤)
    (hz : ∀ x : W, x ∈ U₀ → x ∈ U₁ → W.ord r x = 0) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) =
      (∑ᶠ x ∈ (U₀ : Set W), (W.ord r x : ℚ) * (ZeroCycleDegree.residueDegree f x : ℚ)) -
        ∑ᶠ x ∈ (U₁ : Set W), (W.ord r⁻¹ x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ) := by
  classical
  set gr : W → ℚ := fun x => (W.ord r x : ℚ) *
    (ZeroCycleDegree.residueDegree f x : ℚ) with hgr
  set gi : W → ℚ := fun x => (W.ord r⁻¹ x : ℚ) *
    (ZeroCycleDegree.residueDegree f x : ℚ) with hgi
  have hsuppr : (Function.support gr).Finite :=
    (ZeroCycleDegree.finite_support (W.principalCycle r)).subset
      (Function.support_mul_subset_left _ _)
  have hsuppi : (Function.support gi).Finite :=
    (ZeroCycleDegree.finite_support (W.principalCycle r⁻¹)).subset
      (Function.support_mul_subset_left _ _)
  have hsub : ((U₀ : Set W)ᶜ) ⊆ (U₁ : Set W) := by
    intro x hx
    have hmem : x ∈ (⊤ : W.Opens) := trivial
    rw [← hcov] at hmem
    rcases hmem with h | h
    · exact absurd h hx
    · exact h
  have hU₁ : (U₁ : Set W) = ((U₁ : Set W) ∩ (U₀ : Set W)) ∪ ((U₀ : Set W)ᶜ) := by
    refine Set.eq_of_subset_of_subset (fun x hx => ?_) ?_
    · by_cases h : x ∈ (U₀ : Set W)
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro x (⟨hx, -⟩ | hx)
      · exact hx
      · exact hsub hx
  have hdisj : Disjoint ((U₁ : Set W) ∩ (U₀ : Set W)) ((U₀ : Set W)ᶜ) :=
    Disjoint.mono_left Set.inter_subset_right disjoint_compl_right
  have hvan : ∑ᶠ x ∈ ((U₁ : Set W) ∩ (U₀ : Set W)), gi x = 0 := by
    refine finsum_mem_of_eqOn_zero fun x hx => ?_
    have h0 : W.ord r x = 0 := hz x hx.2 hx.1
    simp [hgi, ord_inv r x, h0]
  have hcancel : (∑ᶠ x ∈ ((U₀ : Set W)ᶜ), gr x) + ∑ᶠ x ∈ ((U₀ : Set W)ᶜ), gi x = 0 := by
    rw [← finsum_mem_add_distrib' (hsuppr.inter_of_right _) (hsuppi.inter_of_right _)]
    refine finsum_mem_of_eqOn_zero fun x _ => ?_
    change gr x + gi x = 0
    simp only [hgr, hgi, ord_inv r x]
    push_cast
    ring
  have hd₁ : (∑ᶠ x ∈ (U₁ : Set W), gi x) = ∑ᶠ x ∈ ((U₀ : Set W)ᶜ), gi x := by
    rw [hU₁, finsum_mem_union' hdisj (hsuppi.inter_of_right _) (hsuppi.inter_of_right _), hvan,
      zero_add]
  rw [degreeCycle_eq_finsum_add_finsum f U₀ r]
  change (∑ᶠ x ∈ (U₀ : Set W), gr x) + (∑ᶠ x ∈ ((U₀ : Set W)ᶜ), gr x) =
    (∑ᶠ x ∈ (U₀ : Set W), gr x) - ∑ᶠ x ∈ (U₁ : Set W), gi x
  rw [hd₁]
  linarith [hcancel]

/-- **The degree of `div r` is the difference of the degrees over two opens covering `W`.**
The `degreeCycle` form of `degreeCycle_principalCycle_eq_sub_finsum`. -/
theorem degreeCycle_principalCycle_eq_sub {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (U₀ U₁ : W.Opens) [Nonempty U₀] [Nonempty U₁] [CompactSpace U₀] [CompactSpace U₁]
    (hcov : U₀ ⊔ U₁ = ⊤) (hz : ∀ x : W, x ∈ U₀ → x ∈ U₁ → W.ord r x = 0) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) =
      ZeroCycleDegree.degreeCycle (U₀.ι ≫ f)
          ((U₀.toScheme).principalCycle (Scheme.dominantFunctionFieldMap U₀.ι r)) -
        ZeroCycleDegree.degreeCycle (U₁.ι ≫ f)
          ((U₁.toScheme).principalCycle (Scheme.dominantFunctionFieldMap U₁.ι r⁻¹)) := by
  rw [degreeCycle_restrict_eq_finsum f U₀ r, degreeCycle_restrict_eq_finsum f U₁ r⁻¹]
  exact degreeCycle_principalCycle_eq_sub_finsum f r U₀ U₁ hcov hz

/-! ## A rational function is a unit on the overlap of the two domains of definition -/

/-- **On the intersection of the domains of definition of `r` and of `r⁻¹` the order of vanishing
of `r` is zero.**  Indeed both `r` and `r⁻¹` are regular there, so `r` is represented by a unit of
the sections over the intersection, and `AlgebraicGeometry.Scheme.ord_of_isUnit` applies. -/
theorem ord_eq_zero_of_mem_regularLocus_inf {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (r : W.functionField) {x : W}
    (hx : x ∈ Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹) : W.ord r x = 0 := by
  rcases eq_or_ne r 0 with hr | hr
  · simp [hr]
  set V : W.Opens := Scheme.regularLocus r ⊓ Scheme.regularLocus r⁻¹ with hVdef
  have hgen : genericPoint W ∈ V :=
    ⟨Scheme.genericPoint_mem_regularLocus r, Scheme.genericPoint_mem_regularLocus r⁻¹⟩
  have hne : Nonempty V := ⟨⟨genericPoint W, hgen⟩⟩
  set σ : Γ(W, V) := W.presheaf.map (homOfLE (inf_le_left : V ≤ Scheme.regularLocus r)).op
    (Scheme.regularSection r) with hσ
  set τ : Γ(W, V) := W.presheaf.map (homOfLE (inf_le_right : V ≤ Scheme.regularLocus r⁻¹)).op
    (Scheme.regularSection r⁻¹) with hτ
  have hgσ : W.presheaf.germ V (genericPoint W) hgen σ = r := by
    rw [hσ, W.presheaf.germ_res_apply (homOfLE (inf_le_left : V ≤ Scheme.regularLocus r))
      (genericPoint W) hgen, Scheme.germ_regularSection]
  have hgτ : W.presheaf.germ V (genericPoint W) hgen τ = r⁻¹ := by
    rw [hτ, W.presheaf.germ_res_apply (homOfLE (inf_le_right : V ≤ Scheme.regularLocus r⁻¹))
      (genericPoint W) hgen, Scheme.germ_regularSection]
  have h1 : σ * τ = 1 := by
    refine germ_injective_of_isIntegral W (U := V) (genericPoint W) hgen ?_
    rw [map_mul, map_one, hgσ, hgτ, mul_inv_cancel₀ hr]
  have hu : IsUnit σ := IsUnit.of_mul_eq_one τ h1
  rw [← hgσ]
  exact AlgebraicGeometry.Scheme.ord_of_isUnit hu hx

/-! ## Ranks of finite free modules under base change, quotients and localization -/

section Algebra

/-- **Base change preserves the rank of a finite free module.**  If `M` is a finite free
`R`-module and `S` is any nontrivial `R`-algebra then `S ⊗[R] M` is free of the same rank
over `S`. -/
theorem finrank_tensorProduct_eq_finrank (R : Type u) [CommRing R] [Nontrivial R]
    (S : Type u) [CommRing S] [Nontrivial S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Module.finrank S (S ⊗[R] M) = Module.finrank R M := by
  rw [Module.finrank_eq_card_basis
      (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R M)),
    Module.finrank_eq_card_basis (Module.Free.chooseBasis R M)]

/-- **Reducing a finite free module modulo a proper ideal of the base ring preserves the rank.**
For `M` finite free over `R` and `I ≠ ⊤` an ideal of `R`, the `R ⧸ I`-module `M ⧸ I • M` is free
of the same rank. -/
theorem finrank_quotient_smul_eq_finrank {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R)
    (hI : I ≠ ⊤) (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] :
    Module.finrank (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) = Module.finrank R M := by
  have hnt : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have e : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  rw [← e.finrank_eq, finrank_tensorProduct_eq_finrank R (R ⧸ I) M]

/-- **Localizing the base ring preserves the rank of a finite free algebra.**  If `A` is a finite
free `R`-algebra, `Rₛ` is the localization of `R` at `S` and `Aₛ` is the localization of `A` at the
image of `S`, then `Aₛ` is free of the same rank over `Rₛ`. -/
theorem finrank_localization_eq_finrank {R : Type u} [CommRing R] [Nontrivial R] (S : Submonoid R)
    (Rₛ : Type u) [CommRing Rₛ] [Nontrivial Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (Aₛ : Type u) [CommRing Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [Algebra Rₛ Aₛ]
    [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]
    [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] :
    Module.finrank Rₛ Aₛ = Module.finrank R A := by
  rw [Module.finrank_eq_card_basis
      ((Module.Free.chooseBasis R A).localizationLocalization Rₛ S Aₛ),
    Module.finrank_eq_card_basis (Module.Free.chooseBasis R A)]

/-- **Reducing a finite free algebra modulo a proper ideal of the base ring preserves the rank.**
The `Ideal.map` form of `finrank_quotient_smul_eq_finrank`, via
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`. -/
theorem finrank_quotient_map_eq_finrank (R : Type u) [CommRing R] [Nontrivial R] (I : Ideal R)
    (hI : I ≠ ⊤) (B : Type u) [CommRing B] [Algebra R B] [Module.Free R B] [Module.Finite R B] :
    Module.finrank (R ⧸ I) (B ⧸ (I.map (algebraMap R B))) = Module.finrank R B := by
  have hnt : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  rw [(Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv.finrank_eq,
    finrank_tensorProduct_eq_finrank R (R ⧸ I) B]

/-- **The fibre of a finite free `k[t]`-algebra over the origin has dimension the rank.**
If `B` is a finite free `k[t]`-algebra then `dim_k (B ⧸ (t)) = rank_{k[t]} B`.  This is the
computation of the degree of the divisor of `t` on the chart `Spec B` of a curve mapping finitely to
`ℙ¹_k`: `finrank_quotient_map_eq_finrank` for `I = (t)`, followed by the change of base ring
`k[t] ⧸ (t) ≃ₐ[k] k` (`Polynomial.quotientSpanXSubCAlgEquiv`) via
`Algebra.finrank_eq_of_equiv_equiv`. -/
theorem finrank_quotient_span_X_eq_finrank (B : Type u) [CommRing B]
    [Algebra k B] [Algebra (Polynomial k) B] [IsScalarTower k (Polynomial k) B]
    [Module.Free (Polynomial k) B] [Module.Finite (Polynomial k) B] :
    Module.finrank k (B ⧸ Ideal.span {algebraMap (Polynomial k) B Polynomial.X}) =
      Module.finrank (Polynomial k) B := by
  set I : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k)} with hIdef
  have hI : I ≠ ⊤ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_top]
    exact Polynomial.not_isUnit_X
  have hmap : I.map (algebraMap (Polynomial k) B) =
      Ideal.span {algebraMap (Polynomial k) B Polynomial.X} := by
    rw [hIdef, Ideal.map_span, Set.image_singleton]
  have hspan : I = Ideal.span {(Polynomial.X - Polynomial.C (0 : k))} := by
    rw [map_zero, sub_zero, hIdef]
  have e : (Polynomial k ⧸ I) ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hspan).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))
  have hi : ∀ c : k, e.symm c = algebraMap k (Polynomial k ⧸ I) c := fun c => by
    simpa using e.symm.commutes c
  rw [Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv
    (Ideal.quotEquivOfEq hmap.symm) ?hc, finrank_quotient_map_eq_finrank (Polynomial k) I hI B]
  case hc =>
    refine RingHom.ext fun c => ?_
    have h2 : (algebraMap (Polynomial k) B) (algebraMap k (Polynomial k) c) = algebraMap k B c :=
      (IsScalarTower.algebraMap_apply k (Polynomial k) B c).symm
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, hi, ← h2,
      ← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk,
      Ideal.Quotient.algebraMap_quotient_map_quotient]

/-- **A module-finite extension of domains over a principal ideal domain is free.**  This supplies
the freeness hypothesis of `finrank_quotient_smul_eq_finrank` and
`finrank_localization_eq_finrank` for the coordinate ring of an affine chart of a curve, which is
module-finite over `k[t]`. -/
theorem free_of_finite_of_injective {R B : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) : Module.Free R B := by
  have htf : Module.IsTorsionFree R B :=
    Module.IsTorsionFree.comap (S := B) (algebraMap R B)
      (fun r hr => IsRegular.of_ne_zero fun h => (isRegular_iff_ne_zero.mp hr)
        (hinj (h.trans (map_zero (algebraMap R B)).symm)))
      (fun r m => by simp [Algebra.smul_def])
  infer_instance

end Algebra

/-! ## The partial degree over an affine chart -/

/-- **The partial degree of `div r` over an affine chart is the `k`-dimension of the quotient.**
Let `j : Spec B ⟶ W` be a dominant open immersion which is a morphism of `k`-schemes (`hj`) and let
`b : B` be a nonzero element whose image in the function field is `r` (`hbr`).  Then the partial sum
`∑ ord_x(r) · [κ(x):k]` over the image of `j` equals `dim_k (B ⧸ (b))`.  This is the scheme form of
Fulton's affine length formula (`AffineDegreeScheme.degreeCycle_principalCycle_eq_finrank`) together
with the invariance of the order of vanishing and of the residue degree under open immersions. -/
theorem finsum_eq_finrank_of_openImmersion {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of k)) {B : Type u} [CommRing B] [Algebra k B] [IsDomain B]
    [Ring.KrullDimLE 1 B] [Algebra.FiniteType k B] [IsNoetherianRing B]
    (j : Spec (CommRingCat.of B) ⟶ W) [IsOpenImmersion j] [IsDominant j]
    (hj : j ≫ f = AffineDegreeScheme.structureMorphism (k := k) (A := B))
    (r : W.functionField) (b : B) (hb : b ≠ 0)
    (hbr : Scheme.dominantFunctionFieldMap j r =
      (VectorBundle.functionFieldUnit (CommRingCat.of B) b hb :
        (Spec (CommRingCat.of B)).functionField)) :
    (∑ᶠ x ∈ Set.range j.base, (W.ord r x : ℚ) *
        (ZeroCycleDegree.residueDegree f x : ℚ)) =
      (Module.finrank k (B ⧸ Ideal.span {b}) : ℚ) := by
  rw [← degreeCycle_comp_eq_finsum_range f j r, hbr, hj,
    AffineDegreeScheme.degreeCycle_principalCycle_eq_finrank b hb]

/-! ## The reduction of the main theorem to the two chart degrees -/

/-- **A rational function which is a global unit has vanishing principal cycle.**  This is the easy
case of "the degree of a principal divisor vanishes". -/
theorem degreeCycle_principalCycle_eq_zero_of_isUnit {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) [Nonempty U] (hU : U = ⊤)
    (σ : Γ(W, U)) (hσ : IsUnit σ) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle (W.germToFunctionField U σ)) = 0 := by
  have hzero : W.principalCycle (W.germToFunctionField U σ) = 0 := by
    refine Function.locallyFinsuppWithin.coe_injective (funext fun x => ?_)
    have hx : x ∈ U := by rw [hU]; trivial
    simp only [Scheme.principalCycle_apply, AlgebraicGeometry.Scheme.ord_of_isUnit hσ hx]
    rfl
  rw [hzero, map_zero]

/-- **The degree of a principal divisor on a curve vanishes as soon as the two chart
contributions agree.**  Here `W` is an integral scheme all of whose local rings are valuation rings
(e.g. a regular curve, by `Scheme.valuationRing_stalk`), so that the domains of definition
`Scheme.regularLocus r` and `Scheme.regularLocus r⁻¹` cover `W` and `r` is a unit on their overlap;
`hdeg` says that the partial degree `∑ ord_x(r)·[κ(x):k]` over the first equals the partial degree
`∑ ord_x(r⁻¹)·[κ(x):k]` over the second.  For a proper curve `hdeg` holds because both sides equal
the degree `[K(W) : k(t)]` of the morphism to `ℙ¹` determined by `r`. -/
theorem degreeCycle_principalCycle_eq_zero_of_finsum_eq {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x))
    (hdeg : (∑ᶠ x ∈ ((Scheme.regularLocus r : W.Opens) : Set W), (W.ord r x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ)) =
        ∑ᶠ x ∈ ((Scheme.regularLocus r⁻¹ : W.Opens) : Set W), (W.ord r⁻¹ x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ)) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  rw [degreeCycle_principalCycle_eq_sub_finsum f r (Scheme.regularLocus r)
      (Scheme.regularLocus r⁻¹) (Scheme.regularLocus_sup_regularLocus_inv_eq_top hv r)
      (fun _ h0 h1 => ord_eq_zero_of_mem_regularLocus_inf r ⟨h0, h1⟩),
    hdeg, sub_self]

/-- **The `degreeCycle` form of `degreeCycle_principalCycle_eq_zero_of_finsum_eq`**: the two
partial degrees are the degrees of the principal cycles of `r` and `r⁻¹` on the two domains of
definition, which are quasi-compact (e.g. affine). -/
theorem degreeCycle_principalCycle_eq_zero_of_degreeCycle_eq {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    [CompactSpace (Scheme.regularLocus r : W.Opens)]
    [CompactSpace (Scheme.regularLocus r⁻¹ : W.Opens)]
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x))
    (hdeg : ZeroCycleDegree.degreeCycle ((Scheme.regularLocus r : W.Opens).ι ≫ f)
        (((Scheme.regularLocus r : W.Opens).toScheme).principalCycle
          (Scheme.dominantFunctionFieldMap (Scheme.regularLocus r : W.Opens).ι r)) =
      ZeroCycleDegree.degreeCycle ((Scheme.regularLocus r⁻¹ : W.Opens).ι ≫ f)
        (((Scheme.regularLocus r⁻¹ : W.Opens).toScheme).principalCycle
          (Scheme.dominantFunctionFieldMap (Scheme.regularLocus r⁻¹ : W.Opens).ι r⁻¹))) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  refine degreeCycle_principalCycle_eq_zero_of_finsum_eq f r hv ?_
  rw [← degreeCycle_restrict_eq_finsum f (Scheme.regularLocus r) r,
    ← degreeCycle_restrict_eq_finsum f (Scheme.regularLocus r⁻¹) r⁻¹]
  exact hdeg

/-- **The degree of a principal divisor on a curve vanishes if it admits two affine charts of the
same degree.**  Concretely: `W` is an integral scheme over `k` all of whose local rings are
valuation rings, `r` is a rational function, and `j₀ : Spec B₀ ⟶ W`, `j₁ : Spec B₁ ⟶ W` are
dominant open immersions of `k`-schemes identifying the domains of definition of `r` and of `r⁻¹`
with affine schemes, on which `r` (resp. `r⁻¹`) is the regular function `b₀` (resp. `b₁`).  If the
two "fibre dimensions" `dim_k (B₀ ⧸ (b₀))` and `dim_k (B₁ ⧸ (b₁))` agree, then the degree of
`div r` vanishes.  For a proper curve both dimensions equal `[K(W) : k(t)]`, `Bᵢ` being finite and
free over `k[t]` (resp. `k[t⁻¹]`) and `bᵢ` the image of the coordinate; see
`finrank_quotient_smul_eq_finrank` and `finrank_localization_eq_finrank`. -/
theorem degreeCycle_principalCycle_eq_zero_of_affineCharts {W : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsIntegral W] [_root_.AlgebraicGeometry.IsLocallyNoetherian W]
    [CompactSpace W] (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (hv : ∀ x : W, ValuationRing (W.presheaf.stalk x))
    {B₀ B₁ : Type u} [CommRing B₀] [Algebra k B₀] [IsDomain B₀] [Ring.KrullDimLE 1 B₀]
    [Algebra.FiniteType k B₀] [IsNoetherianRing B₀]
    [CommRing B₁] [Algebra k B₁] [IsDomain B₁] [Ring.KrullDimLE 1 B₁]
    [Algebra.FiniteType k B₁] [IsNoetherianRing B₁]
    (j₀ : Spec (CommRingCat.of B₀) ⟶ W) [IsOpenImmersion j₀] [IsDominant j₀]
    (j₁ : Spec (CommRingCat.of B₁) ⟶ W) [IsOpenImmersion j₁] [IsDominant j₁]
    (hj₀ : j₀ ≫ f = AffineDegreeScheme.structureMorphism (k := k) (A := B₀))
    (hj₁ : j₁ ≫ f = AffineDegreeScheme.structureMorphism (k := k) (A := B₁))
    (hr₀ : Set.range j₀.base = ((Scheme.regularLocus r : W.Opens) : Set W))
    (hr₁ : Set.range j₁.base = ((Scheme.regularLocus r⁻¹ : W.Opens) : Set W))
    (b₀ : B₀) (hb₀ : b₀ ≠ 0) (b₁ : B₁) (hb₁ : b₁ ≠ 0)
    (hbr₀ : Scheme.dominantFunctionFieldMap j₀ r =
      (VectorBundle.functionFieldUnit (CommRingCat.of B₀) b₀ hb₀ :
        (Spec (CommRingCat.of B₀)).functionField))
    (hbr₁ : Scheme.dominantFunctionFieldMap j₁ r⁻¹ =
      (VectorBundle.functionFieldUnit (CommRingCat.of B₁) b₁ hb₁ :
        (Spec (CommRingCat.of B₁)).functionField))
    (hrank : Module.finrank k (B₀ ⧸ Ideal.span {b₀}) =
      Module.finrank k (B₁ ⧸ Ideal.span {b₁})) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 := by
  refine degreeCycle_principalCycle_eq_zero_of_finsum_eq f r hv ?_
  rw [← hr₀, ← hr₁, finsum_eq_finrank_of_openImmersion f j₀ hj₀ r b₀ hb₀ hbr₀,
    finsum_eq_finrank_of_openImmersion f j₁ hj₁ r⁻¹ b₁ hb₁ hbr₁, hrank]

/-- **The regular-curve form of `degreeCycle_principalCycle_eq_zero_of_finsum_eq`.**  Instead of
assuming that all local rings are valuation rings it suffices to assume that the local ring at
every non-generic point is a discrete valuation ring, i.e. that `W` is a regular curve
(`Scheme.valuationRing_stalk`). -/
theorem degreeCycle_principalCycle_eq_zero_of_finsum_eq_of_isDiscreteValuationRing
    {W : Scheme.{u}} [_root_.AlgebraicGeometry.IsIntegral W]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian W] [CompactSpace W]
    (f : W ⟶ Spec (CommRingCat.of k)) (r : W.functionField)
    (hdvr : ∀ x : W, x ≠ genericPoint W → IsDiscreteValuationRing (W.presheaf.stalk x))
    (hdeg : (∑ᶠ x ∈ ((Scheme.regularLocus r : W.Opens) : Set W), (W.ord r x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ)) =
        ∑ᶠ x ∈ ((Scheme.regularLocus r⁻¹ : W.Opens) : Set W), (W.ord r⁻¹ x : ℚ) *
          (ZeroCycleDegree.residueDegree f x : ℚ)) :
    ZeroCycleDegree.degreeCycle f (W.principalCycle r) = 0 :=
  degreeCycle_principalCycle_eq_zero_of_finsum_eq f r (Scheme.valuationRing_stalk hdvr) hdeg

end GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperCurveDegree
