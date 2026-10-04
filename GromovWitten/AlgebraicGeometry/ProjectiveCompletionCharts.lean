/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.ProjectiveCompletion
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChartedPullback
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Affine charts on the projective completion

For a graded vector bundle `𝓔 : GradedBundleData X ι` the projective completion
`P(E ⊕ 1) = 𝓔.projectiveCompletion` is, over a trivialising open `U_j` of the bundle, the
projective space `Proj Γ(U_j)[x_i : i ∈ Option ι]` (`GradedBundleData.isPullback_chartProjIso`).
Its standard affine charts `D₊(x_i) ≅ 𝔸^ι_{U_j}` give `P(E ⊕ 1) → X` the structure of
`IntersectionTheory.AffineCharts` (charts indexed by `𝓔.bundle.J × Option ι`), so that the flat
pullback of cycles of `IntersectionTheory/ChartedPullback.lean` applies to it.  The charts do not
contain whole fibres, but any two of them over a common base point `x` contain the image in
`P(E ⊕ 1)` of the generic point of the fibre of the total space `E` over `x`.

The dehomogenisation at the variable `x_i` is obtained from the round-25 dehomogenisation
`dehomogenise` at the homogenising variable `t = x_none`, after exchanging `x_none` and `x_i` by
`rename (Equiv.swap none i)`.

## Main results

* `dehomAt R i : R[x_j : j ∈ Option ι]_(x_i) ≃+* R[x_k : k ∈ ι]` (degree-zero homogeneous
  localisation at `x_i`), with `dehomAt_mk`: on `p / x_iⁿ` it exchanges `x_none` and `x_i` in `p`
  and sets `x_none = 1`; swap-free values on coordinates: `dehomAt_mk_X_self`,
  `dehomAt_none_mk_X_some`, `dehomAt_some_mk_X_none`, `dehomAt_some_mk_X_some`.
* `projOptionChart R ι i : Spec R[x_k : k ∈ ι] ⟶ Proj R[x_j : j ∈ Option ι]`, an open immersion
  onto `D₊(x_i)` (`opensRange_projOptionChart`, `range_projOptionChart`) over `Spec R`
  (`projOptionChart_projection`); these charts cover `Proj`
  (`exists_mem_range_projOptionChart`), and a point of the chart at `x_none` whose prime
  contains no variable lies in every chart (`projOptionChart_none_mem_range`).
* `GradedBundleData.completionChart (j, i)`: the chart `D₊(x_i)` over `U_j` of `P(E ⊕ 1)`, an
  open immersion over `U_j` (`completionChart_toBase`); the charts cover `P(E ⊕ 1)`
  (`exists_mem_range_completionChart`).
* `GradedBundleData.bundleOpenEmbedding_chartι_none`: the bundle chart `j` of `E` followed by
  `E ⊆ P(E ⊕ 1)` is the chart `(j, none)`.
* `GradedBundleData.bundlePoint_mem_range_chartι`: the image in `P(E ⊕ 1)` of the generic point
  of the fibre of `E` over `x ∈ U_j` lies in every chart `(j, i)`.
* `GradedBundleData.completionCharts : AffineCharts 𝓔.completionToBase ι`.
* `GradedBundleData.fibrePoint_completionCharts`: the generic fibre point of `P(E ⊕ 1)` over `x`
  is the image of the generic fibre point of `E` over `x`.
* `GradedBundleData.pullbackOpen_bundleOpenEmbedding_pullbackCharted`: the charted flat pullback
  of a cycle to `P(E ⊕ 1)`, restricted to `E`, is the bundle flat pullback
  `BundlePullbackGlobal.pullbackBundle`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace HomogeneousLocalization

namespace GromovWitten.AlgebraicGeometry

open GromovWitten.Algebra MvPolynomial

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Dehomogenisation of `R[x_i : i ∈ Option ι]` at a variable -/

section Dehom

variable {R : Type u} [CommRing R] {ι : Type u}

/-- The homogeneous localisation map `𝒜_(s) → ℬ_(s')` along a graded ring isomorphism
`f : 𝒜 → ℬ` (with two-sided graded inverse `g`) and an element `s'` equal to `f s` is
bijective. -/
theorem awayMapOfEq_bijective {A B S T : Type u} [CommRing A] [CommRing B] [CommRing S]
    [CommRing T] [Algebra A S] [Algebra B T] {𝒜 : ℕ → Submodule A S} [GradedAlgebra 𝒜]
    {ℬ : ℕ → Submodule B T} [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b) {d : ℕ} (s : S) (hs : s ∈ 𝒜 d) (s' : T)
    (hs' : f s = s') :
    Function.Bijective (awayMapOfEq f s s' hs') := by
  have hs'' : s' ∈ ℬ d := hs' ▸ f.map_mem hs
  have hgs : g s' = s := by rw [← hs', hgf]
  have key : ∀ {𝒜' : ℕ → Submodule A S} [GradedAlgebra 𝒜'] {t : S} (ht : t ∈ 𝒜' d) (n : ℕ)
      (a a' : S) (ha : a ∈ 𝒜' (n • d)) (ha' : a' ∈ 𝒜' (n • d)), a = a' →
      Away.mk 𝒜' ht n a ha = Away.mk 𝒜' ht n a' ha' := by
    rintro _ _ _ _ _ _ _ _ _ rfl
    rfl
  have key' : ∀ {t : T} (ht : t ∈ ℬ d) (n : ℕ)
      (a a' : T) (ha : a ∈ ℬ (n • d)) (ha' : a' ∈ ℬ (n • d)), a = a' →
      Away.mk ℬ ht n a ha = Away.mk ℬ ht n a' ha' := by
    rintro _ _ _ _ _ _ _ rfl
    rfl
  refine Function.bijective_iff_has_inverse.mpr ⟨awayMapOfEq g s' s hgs, fun x ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
    rw [awayMapOfEq_mk f s s' hs' hs hs'', awayMapOfEq_mk g s' s hgs hs'' hs]
    exact key hs n _ _ _ _ (hgf a)
  · obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ hs'' y
    rw [awayMapOfEq_mk g s' s hgs hs'' hs, awayMapOfEq_mk f s s' hs' hs hs'']
    exact key' hs'' n _ _ _ _ (hfg b)

variable (R) in
open Classical in
/-- The graded ring automorphism of `R[x_i : i ∈ Option ι]` exchanging the variables `x_none`
and `x_i`. -/
def optionSwapGraded (i : Option ι) :
    homogeneousSubmodule (Option ι) R →+*ᵍ homogeneousSubmodule (Option ι) R where
  toRingHom := (rename (Equiv.swap none i) : MvPolynomial (Option ι) R →ₐ[R] _).toRingHom
  map_mem {_ _} hp := (mem_homogeneousSubmodule _ _).mpr
    (IsHomogeneous.rename_isHomogeneous ((mem_homogeneousSubmodule _ _).mp hp))

open Classical in
/-- `optionSwapGraded` is `rename` along the transposition. -/
theorem optionSwapGraded_apply (i : Option ι) (p : MvPolynomial (Option ι) R) :
    optionSwapGraded R i p = rename (Equiv.swap none i) p := rfl

open Classical in
/-- `optionSwapGraded` is an involution. -/
theorem optionSwapGraded_optionSwapGraded (i : Option ι) (p : MvPolynomial (Option ι) R) :
    optionSwapGraded R i (optionSwapGraded R i p) = p := by
  rw [optionSwapGraded_apply, optionSwapGraded_apply, rename_rename]
  have : ⇑(Equiv.swap (none : Option ι) i) ∘ ⇑(Equiv.swap none i) = id := by
    funext k
    exact Equiv.swap_apply_self _ _ _
  rw [this, rename_id_apply]

variable (R) in
/-- The graded ring isomorphism `R[x_i : i ∈ Option ι] ≅ R[x_i : i ∈ ι][t]` sending `x_i` to
`t`: the exchange of `x_none` and `x_i` followed by `homogEquivOption⁻¹`. -/
def dehomGraded (i : Option ι) :
    homogeneousSubmodule (Option ι) R →+*ᵍ homog (homogeneousSubmodule ι R) :=
  (optionToHomogGraded R ι).comp (optionSwapGraded R i)

/-- The inverse of `dehomGraded`. -/
def dehomGradedInv (i : Option ι) :
    homog (homogeneousSubmodule ι R) →+*ᵍ homogeneousSubmodule (Option ι) R :=
  (optionSwapGraded R i).comp (homogToOptionGraded R ι)

open Classical in
/-- `dehomGraded` on elements. -/
theorem dehomGraded_apply (i : Option ι) (p : MvPolynomial (Option ι) R) :
    dehomGraded R i p = optionEquivLeft R ι (rename (Equiv.swap none i) p) := rfl

open Classical in
/-- `dehomGraded i` sends `x_i` to the homogenising variable `t`. -/
theorem dehomGraded_X (i : Option ι) :
    dehomGraded R i (X i) = (Polynomial.X : Polynomial (MvPolynomial ι R)) := by
  rw [dehomGraded_apply, rename_X, Equiv.swap_apply_right, optionEquivLeft_X_none]

/-- `dehomGradedInv` is a left inverse of `dehomGraded`. -/
theorem dehomGradedInv_dehomGraded (i : Option ι) (p : MvPolynomial (Option ι) R) :
    dehomGradedInv i (dehomGraded R i p) = p := by
  change optionSwapGraded R i ((homogEquivOption R ι) ((homogEquivOption R ι).symm
    (optionSwapGraded R i p))) = p
  rw [AlgEquiv.apply_symm_apply, optionSwapGraded_optionSwapGraded]

/-- `dehomGradedInv` is a right inverse of `dehomGraded`. -/
theorem dehomGraded_dehomGradedInv (i : Option ι) (p : Polynomial (MvPolynomial ι R)) :
    dehomGraded R i (dehomGradedInv i p) = p := by
  change (homogEquivOption R ι).symm (optionSwapGraded R i (optionSwapGraded R i
    (homogEquivOption R ι p))) = p
  rw [optionSwapGraded_optionSwapGraded, AlgEquiv.symm_apply_apply]

/-- The variables have degree one. -/
theorem X_mem_homogeneousSubmodule_one (i : Option ι) :
    (X i : MvPolynomial (Option ι) R) ∈ homogeneousSubmodule (Option ι) R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)

variable (R) in
/-- The dehomogenisation isomorphism `R[x_j : j ∈ Option ι]_(x_i) ≅ R[x_k : k ∈ ι]` at the
variable `x_i`: on `p / x_iⁿ` it exchanges `x_none` and `x_i` in `p` and sets `x_none = 1`. -/
def dehomAt (i : Option ι) :
    Away (homogeneousSubmodule (Option ι) R) (X i : MvPolynomial (Option ι) R) ≃+*
      MvPolynomial ι R :=
  RingEquiv.ofBijective ((dehomogenise (homogeneousSubmodule ι R)).toRingHom.comp
      (awayMapOfEq (dehomGraded R i) (X i) Polynomial.X (dehomGraded_X i)))
    ((dehomogenise _).bijective.comp (awayMapOfEq_bijective _ (dehomGradedInv i)
      (dehomGradedInv_dehomGraded i) (dehomGraded_dehomGradedInv i) _
      (X_mem_homogeneousSubmodule_one i) _ _))

open Classical in
/-- The value of `dehomAt i` on `p / x_iⁿ`. -/
theorem dehomAt_mk (i : Option ι) (n : ℕ) (p : MvPolynomial (Option ι) R)
    (hp : p ∈ homogeneousSubmodule (Option ι) R (n • 1)) :
    dehomAt R i (Away.mk _ (X_mem_homogeneousSubmodule_one i) n p hp) =
      (optionEquivLeft R ι (rename (Equiv.swap none i) p)).eval 1 := by
  change dehomogenise _ (awayMapOfEq (dehomGraded R i) _ _ _ (Away.mk _ _ n p hp)) = _
  rw [awayMapOfEq_mk (dehomGraded R i) _ _ _ _ X_mem_homog, dehomogenise_mk]
  rfl

/-- A variable lies in the degree-`1 • 1` part (the form required by `Away.mk` with `n = 1`). -/
theorem X_mem_homogeneousSubmodule_one_smul (i : Option ι) :
    (X i : MvPolynomial (Option ι) R) ∈ homogeneousSubmodule (Option ι) R (1 • 1) := by
  rw [one_smul]
  exact X_mem_homogeneousSubmodule_one i

/-! The following computation lemmas of `dehomAt` on the coordinate functions `x_{i'} / x_i`
do not mention `Equiv.swap`, so they can be used whatever decidability instance on `ι` is in
scope. -/

/-- `dehomAt i (x_i / x_i) = 1`. -/
theorem dehomAt_mk_X_self (i : Option ι) :
    dehomAt R i (Away.mk _ (X_mem_homogeneousSubmodule_one i) 1 (X i)
      (X_mem_homogeneousSubmodule_one_smul i)) = 1 := by
  classical
  rw [dehomAt_mk, rename_X, Equiv.swap_apply_right, optionEquivLeft_X_none, Polynomial.eval_X]

/-- On the chart at `x_none`: `dehomAt none (x_{some k} / x_none) = X k`. -/
theorem dehomAt_none_mk_X_some (k : ι) :
    dehomAt R none (Away.mk _ (X_mem_homogeneousSubmodule_one none) 1 (X (some k))
      (X_mem_homogeneousSubmodule_one_smul (some k))) = X k := by
  classical
  rw [dehomAt_mk, rename_X, Equiv.swap_self, Equiv.coe_refl, id, optionEquivLeft_X_some,
    Polynomial.eval_C]

/-- On the chart at `x_{some k}`: `dehomAt (some k) (x_none / x_{some k}) = X k`. -/
theorem dehomAt_some_mk_X_none (k : ι) :
    dehomAt R (some k) (Away.mk _ (X_mem_homogeneousSubmodule_one (some k)) 1 (X none)
      (X_mem_homogeneousSubmodule_one_smul none)) = X k := by
  classical
  rw [dehomAt_mk, rename_X, Equiv.swap_apply_left, optionEquivLeft_X_some, Polynomial.eval_C]

/-- On the chart at `x_{some k}`: `dehomAt (some k) (x_{some k'} / x_{some k}) = X k'` for
`k' ≠ k`. -/
theorem dehomAt_some_mk_X_some {k k' : ι} (h : k' ≠ k) :
    dehomAt R (some k) (Away.mk _ (X_mem_homogeneousSubmodule_one (some k)) 1 (X (some k'))
      (X_mem_homogeneousSubmodule_one_smul (some k'))) = X k' := by
  classical
  rw [dehomAt_mk, rename_X, Equiv.swap_apply_of_ne_of_ne (Option.some_ne_none k')
    (fun h' ↦ h (Option.some_injective _ h')), optionEquivLeft_X_some, Polynomial.eval_C]

end Dehom

/-! ### The standard affine charts of `Proj R[x_i : i ∈ Option ι]` -/

section ProjChart

open ProjBaseChange

variable {R : Type u} [CommRing R] {ι : Type u}

variable (R ι) in
/-- The standard chart `𝔸^ι_R = Spec R[x_k : k ∈ ι] ≅ D₊(x_i) ⊆ Proj R[x_j : j ∈ Option ι]`,
through the dehomogenisation isomorphism `dehomAt R i`. -/
def projOptionChart (i : Option ι) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ Proj (homogeneousSubmodule (Option ι) R) :=
  Spec.map (CommRingCat.ofHom (dehomAt R i).toRingHom) ≫
    Proj.awayι _ (X i) (X_mem_homogeneousSubmodule_one i) one_pos

/-- `Spec` of the dehomogenisation isomorphism is an isomorphism. -/
instance isIso_specMap_dehomAt (i : Option ι) :
    IsIso (Spec.map (CommRingCat.ofHom (dehomAt R i).toRingHom)) := by
  rw [isIso_SpecMap_iff]
  exact (dehomAt R i).bijective

/-- The standard charts are open immersions. -/
instance isOpenImmersion_projOptionChart (i : Option ι) :
    IsOpenImmersion (projOptionChart R ι i) := by
  unfold projOptionChart
  infer_instance

/-- The standard chart at `x_i` is the basic open `D₊(x_i)`, as an open subscheme. -/
theorem opensRange_projOptionChart (i : Option ι) :
    (projOptionChart R ι i).opensRange =
      Proj.basicOpen (homogeneousSubmodule (Option ι) R) (X i) := by
  unfold projOptionChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The image of the standard chart at `x_i` is the basic open `D₊(x_i)`. -/
theorem range_projOptionChart (i : Option ι) :
    Set.range (projOptionChart R ι i).base =
      (Proj.basicOpen (homogeneousSubmodule (Option ι) R) (X i) :
        Set (Proj (homogeneousSubmodule (Option ι) R))) := by
  change ((projOptionChart R ι i).opensRange : Set (Proj (homogeneousSubmodule (Option ι) R))) =
    _
  rw [opensRange_projOptionChart]

/-- `dehomAt` is compatible with the structure maps from `R`. -/
theorem dehomAt_fromZeroRingHom_algebraMap (i : Option ι) (a : R) :
    dehomAt R i (fromZeroRingHom (homogeneousSubmodule (Option ι) R) _
      (algebraMap R (homogeneousSubmodule (Option ι) R 0) a)) = algebraMap R _ a := by
  have h0 : (algebraMap R (MvPolynomial (Option ι) R) a) ∈
      homogeneousSubmodule (Option ι) R (0 • 1) := by
    rw [zero_smul]
    exact (algebraMap R (homogeneousSubmodule (Option ι) R 0) a).2
  have : fromZeroRingHom (homogeneousSubmodule (Option ι) R) _
      (algebraMap R (homogeneousSubmodule (Option ι) R 0) a) =
      Away.mk _ (X_mem_homogeneousSubmodule_one i) 0 _ h0 := by
    apply val_injective
    rw [Away.val_mk]
    change Localization.mk _ 1 = _
    congr 1
  rw [this, dehomAt_mk, AlgHom.commutes, AlgEquiv.commutes, Polynomial.algebraMap_apply,
    Polynomial.eval_C]

/-- The standard charts lie over `Spec R`. -/
theorem projOptionChart_projection (i : Option ι) :
    projOptionChart R ι i ≫ projection (homogeneousSubmodule (Option ι) R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))) := by
  rw [projOptionChart, projection, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  exact dehomAt_fromZeroRingHom_algebraMap i a

/-- The variables span the irrelevant ideal of `R[x_j : j ∈ Option ι]`. -/
theorem irrelevant_le_span_range_X :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Option ι) R)).toIdeal ≤
      Ideal.span (Set.range (X : Option ι → MvPolynomial (Option ι) R)) := by
  intro a ha
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
  change (decomposition.decompose' a 0 : MvPolynomial (Option ι) R) = 0 at ha
  rw [decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at ha
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (mem_support_iff.mp hm) ha
  obtain ⟨k, hk⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨k, Set.mem_univ _, hk⟩

/-- The standard charts cover `Proj R[x_j : j ∈ Option ι]`. -/
theorem exists_mem_range_projOptionChart (y : Proj (homogeneousSubmodule (Option ι) R)) :
    ∃ i, y ∈ Set.range (projOptionChart R ι i).base := by
  have hy : y ∈ (⨆ i, Proj.basicOpen (homogeneousSubmodule (Option ι) R) (X i)) := by
    rw [Proj.iSup_basicOpen_eq_top _ _ irrelevant_le_span_range_X]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, by rw [range_projOptionChart]; exact hi⟩

open Classical in
/-- A point of the chart at `x_none` whose prime contains none of the variables lies in every
standard chart. -/
theorem projOptionChart_none_mem_range (q : Spec (CommRingCat.of (MvPolynomial ι R)))
    (hq : ∀ k, (X k : MvPolynomial ι R) ∉ q.asIdeal) (i : Option ι) :
    (projOptionChart R ι none).base q ∈ Set.range (projOptionChart R ι i).base := by
  cases i with
  | none => exact ⟨q, rfl⟩
  | some k =>
    rw [range_projOptionChart]
    change (Spec.map (CommRingCat.ofHom (dehomAt R none).toRingHom)).base q ∈
      Proj.awayι _ (X none) (X_mem_homogeneousSubmodule_one none) one_pos ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Option ι) R) (X (some k))
    rw [Proj.awayι_preimage_basicOpen _ _ _ (X_mem_homogeneousSubmodule_one (some k)) one_pos]
    change Away.isLocalizationElem _ _ ∉ Ideal.comap (dehomAt R none).toRingHom q.asIdeal
    rw [Ideal.mem_comap, Away.isLocalizationElem]
    change dehomAt R none (Away.mk _ (X_mem_homogeneousSubmodule_one none) 1 _ _) ∉ _
    rw [dehomAt_mk, Equiv.swap_self, Equiv.coe_refl, pow_one, rename_id_apply,
      optionEquivLeft_X_some, Polynomial.eval_C]
    exact hq k

/-- The variables do not lie in the extension `p · R[x_k : k ∈ ι]` of a proper ideal of
`R`. -/
theorem X_notMem_map_C {p : Ideal R} (hp : p ≠ ⊤) (k : ι) :
    (X k : MvPolynomial ι R) ∉ Ideal.map (C : R →+* MvPolynomial ι R) p := by
  rw [mem_map_C_iff, not_forall]
  refine ⟨Finsupp.single k 1, ?_⟩
  rw [coeff_X_same]
  exact fun h ↦ hp ((Ideal.eq_top_iff_one p).mpr h)

open Classical in
/-- Dehomogenisation at `x_none` after a graded identification `𝒜[t] ≅ R[x_j : j ∈ Option ι]`
induced by a graded map `τ : 𝒜 → R[x_k : k ∈ ι]` is `τ` after the dehomogenisation of
`𝒜[t]` at `t`. -/
theorem dehomAt_none_awayMapOfEq {A : Type u} [CommRing A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (τ : 𝒜 →+*ᵍ homogeneousSubmodule ι R)
    (h : ((homogToOptionGraded R ι).comp (homogMap τ)) Polynomial.X = X none)
    (x : Away (homog 𝒜) (Polynomial.X : Polynomial A)) :
    dehomAt R none (awayMapOfEq ((homogToOptionGraded R ι).comp (homogMap τ)) Polynomial.X
      (X none) h x) = τ (dehomogenise 𝒜 x) := by
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (homog 𝒜) X_mem_homog x
  rw [awayMapOfEq_mk _ _ _ _ X_mem_homog (X_mem_homogeneousSubmodule_one none), dehomAt_mk,
    dehomogenise_mk, Equiv.swap_self, Equiv.coe_refl, rename_id_apply]
  change Polynomial.eval 1 (optionEquivLeft R ι ((optionEquivLeft R ι).symm
    (p.map τ.toRingHom))) = _
  rw [AlgEquiv.apply_symm_apply, Polynomial.eval_one_map]
  rfl

end ProjChart

/-! ### The affine charts of the projective completion -/

namespace GradedBundleData

open RelativeProj ProjBaseChange VectorBundleTotalSpace IntersectionTheory
open GlobalBlowup (isAffineOpen)

variable {X : Scheme.{u}} {ι : Type u} (𝓔 : GradedBundleData X ι)

/-- The chart `(j, i)` of `P(E ⊕ 1)`: the affine space `𝔸^ι` over the trivialising open
`U_j`, embedded as the basic open `D₊(x_i)` of `Proj Γ(U_j)[x_i : i ∈ Option ι]`, which is the
part of `P(E ⊕ 1)` over `U_j` (`isPullback_chartProjIso`). -/
def completionChart (k : 𝓔.bundle.J × Option ι) :
    Spec (CommRingCat.of (MvPolynomial ι Γ(X, (𝓔.bundle.chart k.1).1))) ⟶
      𝓔.projectiveCompletion :=
  projOptionChart _ ι k.2 ≫ (𝓔.chartProjIso k.1).hom ≫
    affineι X 𝓔.homogData (𝓔.bundle.chart k.1)

/-- The charts of `P(E ⊕ 1)` are open immersions. -/
instance isOpenImmersion_completionChart (k : 𝓔.bundle.J × Option ι) :
    IsOpenImmersion (𝓔.completionChart k) := by
  unfold completionChart
  infer_instance

/-- The chart `(j, i)` lies over `U_j`. -/
theorem completionChart_toBase (k : 𝓔.bundle.J × Option ι) :
    𝓔.completionChart k ≫ 𝓔.completionToBase =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (𝓔.bundle.chart k.1).1)
        (MvPolynomial ι Γ(X, (𝓔.bundle.chart k.1).1)))) ≫
        (isAffineOpen X (𝓔.bundle.chart k.1)).isoSpec.inv ≫ (𝓔.bundle.chart k.1).1.ι := by
  rw [completionChart, Category.assoc, ← (𝓔.isPullback_chartProjIso k.1).w, ← Category.assoc,
    ← Category.assoc, projOptionChart_projection, Category.assoc]

/-- The charts of `P(E ⊕ 1)` cover it. -/
theorem exists_mem_range_completionChart (p : 𝓔.projectiveCompletion) :
    ∃ k, p ∈ Set.range (𝓔.completionChart k).base := by
  have hx : 𝓔.completionToBase.base p ∈ (⨆ j, (𝓔.bundle.chart j).1) := by
    rw [𝓔.bundle.iSup_chart]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hrange := Scheme.range_fst_of_isPullback (𝓔.isPullback_chartProjIso j).flip
  have hp : p ∈ Set.range ((𝓔.chartProjIso j).hom ≫
      affineι X 𝓔.homogData (𝓔.bundle.chart j)) := by
    rw [hrange]
    exact ⟨⟨_, hj⟩, rfl⟩
  obtain ⟨y, rfl⟩ := hp
  obtain ⟨i, z, rfl⟩ := exists_mem_range_projOptionChart y
  exact ⟨(j, i), z, rfl⟩

/-- Unfolds the base map of `completionChart (j, i)`: the base map of `projOptionChart` at
`x_i` followed by that of the open immersion `Proj Γ(U_j)[x_i : i ∈ Option ι] → P(E ⊕ 1)`. -/
theorem completionChart_base_apply (k : 𝓔.bundle.J × Option ι) (z) :
    (𝓔.completionChart k).base z = ((𝓔.chartProjIso k.1).hom ≫
      affineι X 𝓔.homogData (𝓔.bundle.chart k.1)).base ((projOptionChart _ ι k.2).base z) :=
  rfl

/-- The graded identification of a chart sends `t` to `x_none`. -/
theorem chartGraded_X (j : 𝓔.bundle.J) :
    𝓔.chartGraded j Polynomial.X =
      (MvPolynomial.X none : MvPolynomial (Option ι) Γ(X, (𝓔.bundle.chart j).1)) := by
  change homogEquivOption _ ι (Polynomial.X.map _) = _
  rw [Polynomial.map_X]
  exact optionEquivLeft_symm_X _ _

/-- On the total space `E ⊆ P(E ⊕ 1)`, the bundle chart `j` is the chart `(j, none)` of
`P(E ⊕ 1)`. -/
theorem bundleOpenEmbedding_chartι_none (j : 𝓔.bundle.J) :
    𝓔.bundle.chartι j ≫ 𝓔.bundleOpenEmbedding = 𝓔.completionChart (j, none) := by
  let D := 𝓔.toGradedAlgebraData.awayChartData 𝓔.bundle.algebra (fun _ ↦ RingEquiv.refl _)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have h := D.affineι_map (𝓔.bundle.chart j)
  change Spec.map (CommRingCat.ofHom (𝓔.bundle.triv j).toRingHom) ≫
    (RelativeSpec.affineι X 𝓔.bundle.algebra (𝓔.bundle.chart j) ≫ D.map) = _
  rw [h, AwayChartData.chart, completionChart, projOptionChart]
  change _ = _ ≫ Proj.awayι _ _ _ _ ≫ Proj.map (𝓔.chartGraded j) _ ≫ _
  dsimp only
  rw [reassoc_of% (awayι_comp_projMap_of_eq (𝓔.chartGraded j) _ one_pos Polynomial.X
    X_mem_homog (MvPolynomial.X none) (𝓔.chartGraded_X j)
    (X_mem_homogeneousSubmodule_one none))]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact (dehomAt_none_awayMapOfEq (𝓔.trivGraded j) (𝓔.chartGraded_X j) x).symm

/-- The image in `P(E ⊕ 1)` of the generic point of the fibre of `E` over a point `x` of the
trivialising open `U_j` lies in every chart `(j, i)`, `i : Option ι`. -/
theorem bundlePoint_mem_range_chartι (j : 𝓔.bundle.J) (i : Option ι) {x : X}
    (hx : x ∈ (𝓔.bundle.chart j).1) :
    𝓔.bundleOpenEmbedding.base (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) ∈
      Set.range (𝓔.completionChart (j, i)).base := by
  have h1 : BundlePullbackGlobal.bundlePoint 𝓔.bundle x =
      𝓔.bundle.chartBundlePoint j ⟨x, hx⟩ :=
    BundlePullbackGlobal.bundlePoint_chart 𝓔.bundle j ⟨x, hx⟩
  let q := VectorBundle.bundlePoint
    (AlgEquiv.refl (A₁ := MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)))
    (𝓔.bundle.chartBasePoint j ⟨x, hx⟩)
  have h2 : 𝓔.bundleOpenEmbedding.base (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) =
      (𝓔.completionChart (j, none)).base q := by
    rw [h1, ← bundleOpenEmbedding_chartι_none]
    rfl
  have hq : ∀ k, (MvPolynomial.X k : MvPolynomial ι Γ(X, (𝓔.bundle.chart j).1)) ∉ q.asIdeal := by
    intro k
    change _ ∉ Ideal.map (algebraMap _ _) _
    rw [MvPolynomial.algebraMap_eq]
    exact X_notMem_map_C Ideal.IsPrime.ne_top' k
  obtain ⟨z, hz⟩ := projOptionChart_none_mem_range q hq i
  refine ⟨z, ?_⟩
  rw [h2, completionChart_base_apply, completionChart_base_apply]
  exact congrArg _ hz

/-- The image in `P(E ⊕ 1)` of the generic point of the fibre of `E` over `x` lies over `x`. -/
theorem completionToBase_bundleOpenEmbedding_bundlePoint (x : X) :
    𝓔.completionToBase.base
      (𝓔.bundleOpenEmbedding.base (BundlePullbackGlobal.bundlePoint 𝓔.bundle x)) = x := by
  change (𝓔.bundleOpenEmbedding ≫ 𝓔.completionToBase).base _ = x
  rw [bundleOpenEmbedding_toBase]
  exact BundlePullbackGlobal.proj_bundlePoint _ x

/-- The affine charts of the projective completion `P(E ⊕ 1) → X`: indexed by pairs `(j, i)` of
a trivialising open `U_j` of the bundle and a homogeneous coordinate `i : Option ι`, the chart
`(j, i)` is the basic open `D₊(x_i)` of the part `Proj Γ(U_j)[x_i : i ∈ Option ι]` of
`P(E ⊕ 1)` over `U_j`.  Any two charts over a common base point `x` both contain the image of the
generic point of the fibre of `E` over `x`. -/
abbrev completionCharts : AffineCharts 𝓔.completionToBase ι where
  J := 𝓔.bundle.J × Option ι
  base k := 𝓔.bundle.chart k.1
  iSup_base := by
    refine top_le_iff.mp fun x _ ↦ ?_
    have hx : x ∈ ⨆ j, (𝓔.bundle.chart j).1 := by
      rw [𝓔.bundle.iSup_chart]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(j, none), hj⟩
  chartι := 𝓔.completionChart
  chartι_comp := 𝓔.completionChart_toBase
  exists_mem_range := 𝓔.exists_mem_range_completionChart
  meets k k' x hx hx' := ⟨_, 𝓔.completionToBase_bundleOpenEmbedding_bundlePoint x,
    𝓔.bundlePoint_mem_range_chartι k.1 k.2 hx,
    𝓔.bundlePoint_mem_range_chartι k'.1 k'.2 hx'⟩

/-- The base open of the chart `(j, i)` is the trivialising open `U_j`. -/
@[simp]
theorem completionCharts_base (k : 𝓔.completionCharts.J) :
    𝓔.completionCharts.base k = 𝓔.bundle.chart k.1 := rfl

/-- The chart `(j, i)` of `completionCharts` is `completionChart (j, i)`. -/
@[simp]
theorem completionCharts_chartι (k : 𝓔.completionCharts.J) :
    𝓔.completionCharts.chartι k = 𝓔.completionChart k := rfl

/-- The generic point of the fibre of `P(E ⊕ 1)` over `x` (computed in the affine charts
`completionCharts`) is the image of the generic point of the fibre of `E` over `x`. -/
theorem fibrePoint_completionCharts (x : X) :
    AffineCharts.fibrePoint 𝓔.completionCharts x =
      𝓔.bundleOpenEmbedding.base (BundlePullbackGlobal.bundlePoint 𝓔.bundle x) := by
  have hx : x ∈ ⨆ j, (𝓔.bundle.chart j).1 := by
    rw [𝓔.bundle.iSup_chart]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have h1 : AffineCharts.fibrePoint 𝓔.completionCharts x =
      AffineCharts.chartPoint 𝓔.completionCharts (j, none) ⟨x, hj⟩ :=
    AffineCharts.fibrePoint_chart 𝓔.completionCharts (j, none) ⟨x, hj⟩
  have h2 : BundlePullbackGlobal.bundlePoint 𝓔.bundle x =
      𝓔.bundle.chartBundlePoint j ⟨x, hj⟩ :=
    BundlePullbackGlobal.bundlePoint_chart 𝓔.bundle j ⟨x, hj⟩
  rw [h1, h2]
  change (𝓔.completionChart (j, none)).base _ =
    𝓔.bundleOpenEmbedding.base ((𝓔.bundle.chartι j).base _)
  rw [← bundleOpenEmbedding_chartι_none]
  rfl

/-- The charted flat pullback of cycles to `P(E ⊕ 1)` restricts on the open subscheme `E` to the
flat pullback of cycles along the bundle projection `E → X`. -/
theorem pullbackOpen_bundleOpenEmbedding_pullbackCharted
    (c : IntersectionTheory.AlgebraicCycle X ℚ) :
    AlgebraicCycle.pullbackOpen 𝓔.bundleOpenEmbedding
        (AffineCharts.pullbackCharted 𝓔.completionCharts c) =
      BundlePullbackGlobal.pullbackBundle 𝓔.bundle c := by
  refine BundlePullbackGlobal.pullbackBundle_unique 𝓔.bundle c _ fun j ↦ ?_
  have h : AlgebraicCycle.pullbackOpen (𝓔.bundle.chartι j)
      (AlgebraicCycle.pullbackOpen 𝓔.bundleOpenEmbedding
        (AffineCharts.pullbackCharted 𝓔.completionCharts c)) =
      AlgebraicCycle.pullbackOpen (𝓔.completionChart (j, none))
        (AffineCharts.pullbackCharted 𝓔.completionCharts c) := by
    apply Function.locallyFinsuppWithin.ext
    intro a
    rw [AlgebraicCycle.pullbackOpen_apply, AlgebraicCycle.pullbackOpen_apply,
      AlgebraicCycle.pullbackOpen_apply, ← bundleOpenEmbedding_chartι_none]
    rfl
  exact h.trans (AffineCharts.pullbackOpen_chartι_pullbackCharted 𝓔.completionCharts (j, none) c)

end GradedBundleData

end

end GromovWitten.AlgebraicGeometry
