/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.SmoothAmbientEtale
import GromovWitten.AlgebraicGeometry.Cones.RefinementNormalSheaf

/-!
# The tangent action on the normal cone of a formally étale chart

`Cones/SmoothAmbientEtale.lean` constructs, for a formally étale algebra `R` over the polynomial
ambient ring `P = Amb A σ = A[x_σ]` and an *arbitrary* ideal `J ⊆ R`, the tangent coaction

`coactionEtale : gr_J(R) →+* gr_J(R)[z_σ]`

out of the Taylor expansions `taylor n : R →ₐ[P] R[ε_σ]/(ε)^{n+1}`, together with the counit law.
This file completes it to an honest action of the additive group `𝔸^σ` on the affine normal cone
`C = Spec gr_J(R)`:

* `translatePointEtale φ v` translates a `B`-point `φ` of the cone by a tangent vector
  `v : σ → B`, and `translatePointEtale_zero`, `translatePointEtale_add` are the action axioms;
* `coactionEtale_coassoc` is the resulting coassociativity of the coaction;
* `EtaleConeGroupoid` is the action groupoid `[C/T](B)`, a `Groupoid`;
* `nsCoactionEtale` is the induced coaction on the normal sheaf `N = Spec Ns_R(J)`, with its own
  action axioms (`nsTranslatePointEtale_zero`, `nsTranslatePointEtale_add`) and groupoid
  `EtaleNsGroupoid`, and `coactionEtale_comp_nsToGr`, `nsTranslatePointEtale_comp_nsToGr`,
  `coneToNsFunctorEtale` are the equivariance of the closed immersion `C ⊆ N` (Vistoli);
* for the polynomial model `R = P` all of this agrees with `Cones/ConeTranslation.lean`
  (`coactionEtale_eq_coaction`, `translatePointEtale_eq_translatePoint`,
  `modelConeEquivalence`).

## The linear part

The technical ingredient is the explicit description of the degree-one part of the coaction.  An
element `x ∈ J` has a first-order Taylor expansion `taylor 1 x`, any lift `y ∈ R[ε]` of which
satisfies `constantCoeff y = x`; the *linear part* `grLinearPart σ J y` — the degree-one
homogeneous component of `y`, with coefficients read in `gr_J(R)` — is then the derivative term
of the coaction:

`coactionEtale [x] = C [x] + grLinearPart σ J y`   (`coactionEtale_degreeOneRaw`).

This rests on the decomposition `prodMap_degreeOne_decomp` of the degree-one classes of
`gr_{I'}(R[ε])`, `I' = polyExt σ J`, in the coordinates of `ConeRefinement.prodEquiv`.  Since the
linear part is a linear polynomial in `ε`, evaluating it is additive in the tangent vector
(`eval₂_add_of_mem_span_X`), which is exactly what the action axiom `translatePointEtale_add`
needs.
-/

namespace GromovWitten.AlgebraicGeometry

namespace EtaleAmbient

universe u

noncomputable section

open MvPolynomial ConeTranslation ConeRefinement AffineNormalCone

/-! ### Linear polynomials -/

section Linear

variable {S : Type u} [CommRing S] {σ : Type u}

/-- The degree-one homogeneous component of a polynomial is a *linear* polynomial: it lies in
the span of the variables. -/
theorem homogeneousComponent_one_mem_span (p : MvPolynomial σ S) :
    homogeneousComponent 1 p ∈ Submodule.span S (Set.range (X : σ → MvPolynomial σ S)) := by
  rw [← homogeneousSubmodule_one_eq_span_X]
  exact homogeneousComponent_isHomogeneous 1 p

/-- Taking the degree-one part commutes with a change of coefficients. -/
theorem map_homogeneousComponent_one {S' : Type u} [CommRing S'] (f : S →+* S')
    (p : MvPolynomial σ S) :
    map f (homogeneousComponent 1 p) = homogeneousComponent 1 (map f p) := by
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs with h
  · rfl
  · exact map_zero _

/-- A linear polynomial has no constant term. -/
theorem constantCoeff_homogeneousComponent_one (p : MvPolynomial σ S) :
    constantCoeff (homogeneousComponent 1 p) = 0 := by
  rw [constantCoeff_eq, coeff_homogeneousComponent, if_neg (by simp)]

variable {B : Type u} [CommRing B]

/-- **Evaluating a linear polynomial is additive in the point.**  This is the linearity of the
derivative term of the tangent coaction in the tangent direction. -/
theorem eval₂_add_of_mem_span_X (φ : S →+* B) (v w : σ → B) {p : MvPolynomial σ S}
    (hp : p ∈ Submodule.span S (Set.range (X : σ → MvPolynomial σ S))) :
    eval₂ φ (fun i ↦ v i + w i) p = eval₂ φ v p + eval₂ φ w p := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨t, rfl⟩ := hq
    rw [eval₂_X, eval₂_X, eval₂_X]
  | zero => rw [eval₂_zero, eval₂_zero, eval₂_zero, add_zero]
  | add a b _ _ ha hb =>
    rw [eval₂_add, eval₂_add, eval₂_add, ha, hb]
    ring
  | smul c a _ ha =>
    simp only [smul_eq_C_mul, eval₂_mul, eval₂_C, ha]
    ring

end Linear

/-! ### The degree-one classes of the refined ideal in the product coordinates -/

section DegreeOne

variable {R : Type u} [CommRing R] (σ : Type u) (J : Ideal R)

/-- **The linear part of a polynomial over `R`**: its degree-one homogeneous component, with
coefficients read in `gr_J(R)`.  For a lift `y` of the first-order Taylor expansion of `x ∈ J`
this is the derivative term `Σ_i [∂_i x]·z_i` of the tangent coaction. -/
def grLinearPart (y : MvPolynomial σ R) : MvPolynomial σ (associatedGradedRing R J) :=
  map (algebraMap R (associatedGradedRing R J)) (homogeneousComponent 1 y)

/-- Taking the linear part commutes with reducing the coefficients. -/
theorem grLinearPart_eq (y : MvPolynomial σ R) :
    grLinearPart σ J y =
      homogeneousComponent 1 (map (algebraMap R (associatedGradedRing R J)) y) := by
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [grLinearPart, coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs with h
  · rfl
  · exact map_zero _

/-- The linear part is additive. -/
theorem grLinearPart_add (y z : MvPolynomial σ R) :
    grLinearPart σ J (y + z) = grLinearPart σ J y + grLinearPart σ J z := by
  rw [grLinearPart, grLinearPart, grLinearPart, map_add, map_add]

/-- The linear part respects differences. -/
theorem grLinearPart_sub (y z : MvPolynomial σ R) :
    grLinearPart σ J (y - z) = grLinearPart σ J y - grLinearPart σ J z := by
  rw [grLinearPart, grLinearPart, grLinearPart, map_sub, map_sub]

/-- A constant has no linear part. -/
theorem grLinearPart_C (r : R) : grLinearPart σ J (C r) = 0 := by
  rw [grLinearPart, homogeneousComponent_one_C, map_zero]

/-- The linear part of a variable. -/
theorem grLinearPart_X (t : σ) : grLinearPart σ J (X t) = X t := by
  rw [grLinearPart, homogeneousComponent_one_X, map_X]

/-- The linear part, expanded over the support. -/
theorem grLinearPart_eq_sum (y : MvPolynomial σ R) :
    grLinearPart σ J y = ∑ m ∈ y.support with m.degree = 1,
      monomial m (algebraMap R (associatedGradedRing R J) (coeff m y)) := by
  rw [grLinearPart_eq, homogeneousComponent_apply]
  have hcongr : ∀ m : σ →₀ ℕ,
      (monomial m (coeff m (map (algebraMap R (associatedGradedRing R J)) y)) :
        MvPolynomial σ (associatedGradedRing R J)) =
      monomial m (algebraMap R (associatedGradedRing R J) (coeff m y)) := by
    intro m
    rw [coeff_map]
  rw [Finset.sum_congr rfl fun m _ ↦ hcongr m]
  refine Finset.sum_subset (Finset.filter_subset_filter _ (support_map_subset _ _)) ?_
  intro m _ hnot
  have hcoeff : coeff m (map (algebraMap R (associatedGradedRing R J)) y) = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hne,
      (Finset.mem_filter.mp ‹m ∈ Finset.filter _ y.support›).2⟩)
  rw [coeff_map] at hcoeff
  rw [hcoeff, map_zero]

/-- **The degree-one class of a polynomial with vanishing constant term is its linear part.** -/
theorem prodMap_grLinearPart (g : MvPolynomial σ R) (hg : constantCoeff g = 0)
    (hg' : g ∈ polyExt σ J) :
    prodMap σ J (grLinearPart σ J g) =
      degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨g, hg'⟩ := by
  have hx : ∀ m : σ →₀ ℕ, (monomial m (coeff m g) : MvPolynomial σ R) ∈ polyExt σ J := by
    classical
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [congrFun monomial_zero' (coeff 0 g)]
      refine C_mem_polyExt ?_
      rw [← constantCoeff_eq, hg]
      exact Ideal.zero_mem _
    · rw [mem_polyExt_iff, constantCoeff_monomial, if_neg hm]
      exact Ideal.zero_mem _
  have hsum : (⟨g, hg'⟩ : ↥(polyExt σ J)) =
      ∑ m ∈ g.support, (⟨monomial m (coeff m g), hx m⟩ : ↥(polyExt σ J)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (support_sum_monomial_coeff g).symm
  have hzero : ∀ m ∈ g.support, m ∉ g.support.filter (fun m ↦ m.degree = 1) →
      degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨monomial m (coeff m g), hx m⟩ = 0 := by
    intro m hm hnot
    have hm1 : m.degree ≠ 1 := fun h ↦ hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
    have hm0 : m ≠ 0 := by
      intro h
      rw [h, mem_support_iff, ← constantCoeff_eq, hg] at hm
      exact hm rfl
    have hd0 : m.degree ≠ 0 := fun h ↦ hm0 ((Finsupp.degree_eq_zero_iff m).mp h)
    have h2 : 2 ≤ m.degree := by omega
    exact degreeOneRaw_monomial_eq_zero h2 _ _
  rw [hsum, map_sum, grLinearPart_eq_sum, map_sum,
    ← Finset.sum_subset (Finset.filter_subset _ g.support) hzero]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨_, hdeg⟩ := Finset.mem_filter.mp hm
  obtain ⟨t, rfl⟩ := (Finsupp.range_single_one (σ := σ)).ge hdeg
  rw [← C_mul_X_eq_monomial, map_mul, prodMap_C, prodMap_X, grIncl_algebraMap, zVar,
    ← degreeOneRaw_smul]
  congr 1
  apply Subtype.ext
  rw [SetLike.val_smul, smul_eq_mul, C_mul_X_eq_monomial]

/-- **The degree-one classes of `gr_{I'}(R[ε])` in the product coordinates
`gr_{I'}(R[ε]) ≅ gr_J(R)[z_σ]`**: the class of `y` is the class of its constant term plus its
linear part. -/
theorem prodMap_degreeOne_decomp (y : MvPolynomial σ R) (hy : y ∈ polyExt σ J) :
    prodMap σ J (C (degreeOneRaw R J ⟨constantCoeff y, mem_polyExt_iff.mp hy⟩) +
        grLinearPart σ J y) =
      degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨y, hy⟩ := by
  have hC : (C (constantCoeff y) : MvPolynomial σ R) ∈ polyExt σ J :=
    C_mem_polyExt (mem_polyExt_iff.mp hy)
  have hgmem : y - C (constantCoeff y) ∈ polyExt σ J := Ideal.sub_mem _ hy hC
  have hg : constantCoeff (y - C (constantCoeff y)) = 0 := by
    rw [map_sub, constantCoeff_C, sub_self]
  have hsplit : (⟨y, hy⟩ : ↥(polyExt σ J)) =
      ⟨C (constantCoeff y), hC⟩ + ⟨y - C (constantCoeff y), hgmem⟩ := by
    apply Subtype.ext
    change y = C (constantCoeff y) + (y - C (constantCoeff y))
    ring
  have hlin : grLinearPart σ J (y - C (constantCoeff y)) = grLinearPart σ J y := by
    rw [grLinearPart_sub, grLinearPart_C, sub_zero]
  rw [hsplit, map_add, map_add, ← hlin, prodMap_grLinearPart σ J _ hg hgmem, prodMap_C,
    grIncl_degreeOneRaw]

/-- The degree-one classes in the coordinates `gr_J(R)[z_σ]` of `ConeRefinement.prodEquiv`. -/
theorem prodEquiv_symm_degreeOneRaw (y : MvPolynomial σ R) (hy : y ∈ polyExt σ J) :
    (ConeRefinement.prodEquiv (τ := σ) (I := J)).symm
        (degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨y, hy⟩) =
      C (degreeOneRaw R J ⟨constantCoeff y, mem_polyExt_iff.mp hy⟩) + grLinearPart σ J y := by
  rw [RingEquiv.symm_apply_eq, ConeRefinement.prodEquiv_apply]
  exact (prodMap_degreeOne_decomp σ J y hy).symm

end DegreeOne

/-! ### The counit law in the product coordinates -/

section Counit

variable (σ : Type u) (R : Type u) [CommRing R] (J : Ideal R)

/-- Setting `ε = 0` is a left inverse of the inclusion `gr_J(R) → gr_{I'}(R[ε])`. -/
theorem counitMap_comp_grIncl :
    (counitMap σ R J).comp (grIncl σ J) = RingHom.id (associatedGradedRing R J) := by
  refine ConeRefinement.gr_ringHom_ext (J := J) (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [RingHom.comp_apply, grIncl_algebraMap, counitMap, grMapOfLe_algebraMap,
      constantCoeff_C, RingHom.id_apply]
  · rw [RingHom.comp_apply, grIncl_degreeOneRaw, counitMap,
      show degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨C (x : R), C_mem_polyExt x.2⟩ =
        Ideal.Quotient.mk _ (degreeOneRees (MvPolynomial σ R) (polyExt σ J)
          ⟨C (x : R), C_mem_polyExt x.2⟩) from rfl, grMapOfLe_degreeOneRees, RingHom.id_apply]
    have hxeq : ∀ h : constantCoeff (C (x : R) : MvPolynomial σ R) ∈ J,
        (⟨constantCoeff (C (x : R) : MvPolynomial σ R), h⟩ : ↥J) = x :=
      fun _ ↦ Subtype.ext (constantCoeff_C _ _)
    rw [hxeq]
    rfl

/-- Setting `ε = 0` kills the extra coordinates. -/
theorem counitMap_zVar (t : σ) : counitMap σ R J (zVar σ J t) = 0 := by
  rw [zVar, counitMap,
    show degreeOneRaw (MvPolynomial σ R) (polyExt σ J) ⟨X t, X_mem_polyExt t⟩ =
      Ideal.Quotient.mk _ (degreeOneRees (MvPolynomial σ R) (polyExt σ J)
        ⟨X t, X_mem_polyExt t⟩) from rfl, grMapOfLe_degreeOneRees]
  have hxeq : ∀ h : constantCoeff (X t : MvPolynomial σ R) ∈ J,
      (⟨constantCoeff (X t : MvPolynomial σ R), h⟩ : ↥J) = 0 :=
    fun _ ↦ Subtype.ext (constantCoeff_X _ _)
  rw [hxeq]
  change degreeOneRaw R J 0 = 0
  exact map_zero _

/-- **The counit in the product coordinates**: setting `ε = 0` in `gr_{I'}(R[ε]) ≅ gr_J(R)[z_σ]`
is setting the extra coordinates `z` to zero. -/
theorem counitMap_comp_prodMap :
    (counitMap σ R J).comp (prodMap σ J) =
      (constantCoeff : MvPolynomial σ (associatedGradedRing R J) →+*
        associatedGradedRing R J) := by
  refine MvPolynomial.ringHom_ext (fun w ↦ ?_) (fun t ↦ ?_)
  · rw [RingHom.comp_apply, prodMap_C, constantCoeff_C]
    exact RingHom.congr_fun (counitMap_comp_grIncl σ R J) w
  · rw [RingHom.comp_apply, prodMap_X, counitMap_zVar, constantCoeff_X]

end Counit

/-! ### The tangent action on the `B`-points of the normal cone -/

section Action

variable (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R)

/-- **The counit law in the coordinates `gr_J(R)[z_σ]`**: the constant term of the tangent
coaction is the identity. -/
theorem constantCoeff_coactionEtale (z : associatedGradedRing R J) :
    constantCoeff (coactionEtale A σ R J z) = z := by
  have h := RingHom.congr_fun (counitMap_comp_prodMap σ R J) (coactionEtale A σ R J z)
  rw [RingHom.comp_apply] at h
  rw [← h, ← ConeRefinement.prodEquiv_apply, coactionEtale_apply, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (counitMap_comp_grPhi A σ R J) z

/-- **The degree-one part of the tangent coaction is the derivative**: for `x ∈ J` and any lift
`y` of its first-order Taylor expansion, the class of `x` goes to `[x] + Σ_i [∂_i x]·z_i`. -/
theorem coactionEtale_degreeOneRaw (x : R) (hx : x ∈ J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 x) :
    coactionEtale A σ R J (degreeOneRaw R J ⟨x, hx⟩) =
      C (degreeOneRaw R J ⟨x, hx⟩) + grLinearPart σ J y := by
  rw [coactionEtale_apply, grPhi_degreeOneRaw A σ R J x hx y hy hmk,
    prodEquiv_symm_degreeOneRaw]
  have hcc : ∀ h : constantCoeff y ∈ J, (⟨constantCoeff y, h⟩ : ↥J) = ⟨x, hx⟩ :=
    fun _ ↦ Subtype.ext (constantCoeff_of_taylor A σ R 1 x y hmk)
  rw [hcc]

/-- **Translating a `B`-point of the affine normal cone by a tangent vector** `v : σ → B`, in a
formally étale chart: the analogue of `ConeTranslation.translatePoint`. -/
def translatePointEtale {B : Type u} [CommRing B] (φ : associatedGradedRing R J →+* B)
    (v : σ → B) : associatedGradedRing R J →+* B :=
  (eval₂Hom φ v).comp (coactionEtale A σ R J)

variable {B : Type u} [CommRing B]

theorem translatePointEtale_apply (φ : associatedGradedRing R J →+* B) (v : σ → B)
    (z : associatedGradedRing R J) :
    translatePointEtale A σ R J φ v z = eval₂Hom φ v (coactionEtale A σ R J z) :=
  rfl

/-- The translation does not move the degree-zero part: it is an action over `Spec (R/J)`. -/
theorem translatePointEtale_algebraMap (φ : associatedGradedRing R J →+* B) (v : σ → B) (r : R) :
    translatePointEtale A σ R J φ v (algebraMap R (associatedGradedRing R J) r) =
      φ (algebraMap R (associatedGradedRing R J) r) := by
  rw [translatePointEtale_apply, coactionEtale_algebraMap, eval₂Hom_C]

theorem translatePointEtale_comp_algebraMap (φ : associatedGradedRing R J →+* B) (v : σ → B) :
    (translatePointEtale A σ R J φ v).comp (algebraMap R (associatedGradedRing R J)) =
      φ.comp (algebraMap R (associatedGradedRing R J)) :=
  RingHom.ext fun r ↦ translatePointEtale_algebraMap A σ R J φ v r

/-- The translation of a degree-one point is the derivative evaluated at the tangent vector. -/
theorem translatePointEtale_degreeOneRaw (φ : associatedGradedRing R J →+* B) (v : σ → B)
    (x : R) (hx : x ∈ J) (y : MvPolynomial σ R) (hy : y ∈ ConeRefinement.polyExt σ J)
    (hmk : shiftMk A σ R 1 y = taylor A σ R 1 x) :
    translatePointEtale A σ R J φ v (degreeOneRaw R J ⟨x, hx⟩) =
      φ (degreeOneRaw R J ⟨x, hx⟩) +
        eval₂ (φ.comp (algebraMap R (associatedGradedRing R J))) v (homogeneousComponent 1 y) := by
  rw [translatePointEtale_apply, coactionEtale_degreeOneRaw A σ R J x hx y hy hmk, map_add,
    eval₂Hom_C, grLinearPart, coe_eval₂Hom, eval₂_map]

/-- **Translating by the zero tangent vector does nothing.** -/
theorem translatePointEtale_zero (φ : associatedGradedRing R J →+* B) :
    translatePointEtale A σ R J φ 0 = φ := by
  refine RingHom.ext fun z ↦ ?_
  rw [translatePointEtale_apply]
  change eval₂Hom φ (fun _ : σ ↦ (0 : B)) (coactionEtale A σ R J z) = φ z
  rw [eval₂Hom_zero'_apply, constantCoeff_coactionEtale]

/-- **Translating twice is translating by the sum**: the action axiom. -/
theorem translatePointEtale_add (φ : associatedGradedRing R J →+* B) (v w : σ → B) :
    translatePointEtale A σ R J (translatePointEtale A σ R J φ v) w =
      translatePointEtale A σ R J φ (v + w) := by
  refine ConeRefinement.gr_ringHom_ext (J := J) (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [translatePointEtale_algebraMap, translatePointEtale_algebraMap,
      translatePointEtale_algebraMap]
  · obtain ⟨y, hy, hmk⟩ := exists_taylor_lift A σ R J 1 (x : R) (by rw [pow_one]; exact x.2)
    have hy' : y ∈ ConeRefinement.polyExt σ J := by rwa [pow_one] at hy
    rw [show degreeOneRaw R J x = degreeOneRaw R J ⟨(x : R), x.2⟩ from rfl,
      translatePointEtale_degreeOneRaw A σ R J _ w (x : R) x.2 y hy' hmk,
      translatePointEtale_degreeOneRaw A σ R J φ v (x : R) x.2 y hy' hmk,
      translatePointEtale_degreeOneRaw A σ R J φ (v + w) (x : R) x.2 y hy' hmk,
      translatePointEtale_comp_algebraMap,
      show (v + w : σ → B) = fun i ↦ v i + w i from rfl,
      eval₂_add_of_mem_span_X _ v w (homogeneousComponent_one_mem_span y), add_assoc]

/-- **Coassociativity of the tangent coaction**: translating by `z` and then by `z'` is
translating by `z + z'`. -/
theorem coactionEtale_coassoc :
    (MvPolynomial.map (coactionEtale A σ R J)).comp (coactionEtale A σ R J) =
      (eval₂Hom (C.comp C) fun i : σ ↦
          C (X i : MvPolynomial σ (associatedGradedRing R J)) + X i).comp
        (coactionEtale A σ R J) := by
  have hC : (eval₂Hom (C.comp C) fun i : σ ↦
      C (X i : MvPolynomial σ (associatedGradedRing R J))) =
      (C : MvPolynomial σ (associatedGradedRing R J) →+*
        MvPolynomial σ (MvPolynomial σ (associatedGradedRing R J))) :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  have h := translatePointEtale_add A σ R J (C.comp C)
    (fun i : σ ↦ C (X i : MvPolynomial σ (associatedGradedRing R J)))
    (fun i : σ ↦ X i)
  unfold translatePointEtale at h
  rw [hC, show ((fun i : σ ↦ C (X i : MvPolynomial σ (associatedGradedRing R J))) +
    fun i ↦ X i) = fun i ↦ C (X i) + X i from rfl] at h
  have hmap : MvPolynomial.map (σ := σ) (coactionEtale A σ R J) =
      eval₂Hom (C.comp (coactionEtale A σ R J)) fun i ↦ X i :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by simp)
  rw [hmap]
  exact h

end Action

/-! ### The coaction on the normal sheaf and Vistoli's lemma -/

section NormalSheaf

variable (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R)

/-- The tangent coaction in the form `gr_J(R) → gr_{I'}(R[ε])`, on a degree-one class: it is the
degree-one class of any lift of the first-order Taylor expansion. -/
theorem coactionEtale_degreeOneRaw' (x : R) (hx : x ∈ J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 x) :
    coactionEtale A σ R J (degreeOneRaw R J ⟨x, hx⟩) =
      (ConeRefinement.prodEquiv (τ := σ) (I := J)).symm
        (degreeOneRaw (MvPolynomial σ R) (ConeRefinement.polyExt σ J) ⟨y, hy⟩) := by
  rw [coactionEtale_apply, grPhi_degreeOneRaw A σ R J x hx y hy hmk]

/-- A choice of lift to `R[ε_σ]` of the first-order Taylor expansion of an element of `J`. -/
def taylorLift (x : R) (hx : x ∈ J) : MvPolynomial σ R :=
  (exists_taylor_lift A σ R J 1 x (by rwa [pow_one])).choose

theorem taylorLift_mem (x : R) (hx : x ∈ J) :
    taylorLift A σ R J x hx ∈ ConeRefinement.polyExt σ J :=
  (pow_one (ConeRefinement.polyExt σ J)).le
    (exists_taylor_lift A σ R J 1 x (by rwa [pow_one])).choose_spec.1

theorem shiftMk_taylorLift (x : R) (hx : x ∈ J) :
    shiftMk A σ R 1 (taylorLift A σ R J x hx) = taylor A σ R 1 x :=
  (exists_taylor_lift A σ R J 1 x (by rwa [pow_one])).choose_spec.2

theorem constantCoeff_taylorLift (x : R) (hx : x ∈ J) :
    constantCoeff (taylorLift A σ R J x hx) = x :=
  constantCoeff_of_taylor A σ R 1 x _ (shiftMk_taylorLift A σ R J x hx)

omit [Algebra.FormallyEtale (Amb A σ) R] in
/-- **The degree-one class of the Taylor expansion does not depend on the lift**: two lifts of
the same first-order expansion differ by an element of `(ε)^2 ⊆ (I')^2`. -/
theorem nsClass_eq_of_shiftMk_eq (y y' : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hy' : y' ∈ ConeRefinement.polyExt σ J)
    (h : shiftMk A σ R 1 y = shiftMk A σ R 1 y') :
    nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩ =
      nsClass (ConeRefinement.polyExt σ J) ⟨y', hy'⟩ := by
  have hsub : y - y' ∈ epsIdeal σ R ^ 2 := (shiftMk_eq_iff A σ R 1).mp h
  have hsq : y - y' ∈ ConeRefinement.polyExt σ J ^ 2 :=
    epsIdeal_pow_le_polyExt_pow J 2 hsub
  have hzero : nsClass (ConeRefinement.polyExt σ J)
      ((⟨y, hy⟩ : ↥(ConeRefinement.polyExt σ J)) - ⟨y', hy'⟩) = 0 :=
    ConeRefinement.nsClass_eq_zero_of_mem_sq (ConeRefinement.polyExt σ J) _ hsq
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- **The degree-one part of the normal-sheaf coaction**: the class in `N_{U/M'}` of a lift of
the first-order Taylor expansion of `x ∈ J`. -/
def nsTaylorClass (x : ↥J) :
    normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J) :=
  nsClass (ConeRefinement.polyExt σ J)
    ⟨taylorLift A σ R J (x : R) x.2, taylorLift_mem A σ R J (x : R) x.2⟩

/-- Any lift of the first-order Taylor expansion computes `nsTaylorClass`. -/
theorem nsTaylorClass_eq (x : ↥J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 (x : R)) :
    nsTaylorClass A σ R J x = nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩ :=
  nsClass_eq_of_shiftMk_eq A σ R J _ y _ hy
    (by rw [shiftMk_taylorLift, hmk])

/-- The degree-one part of the normal-sheaf coaction is additive. -/
theorem nsTaylorClass_add (x x' : ↥J) :
    nsTaylorClass A σ R J (x + x') = nsTaylorClass A σ R J x + nsTaylorClass A σ R J x' := by
  have hy : taylorLift A σ R J (x : R) x.2 ∈ ConeRefinement.polyExt σ J :=
    taylorLift_mem A σ R J (x : R) x.2
  have hy' : taylorLift A σ R J (x' : R) x'.2 ∈ ConeRefinement.polyExt σ J :=
    taylorLift_mem A σ R J (x' : R) x'.2
  have hsum : taylorLift A σ R J (x : R) x.2 + taylorLift A σ R J (x' : R) x'.2 ∈
      ConeRefinement.polyExt σ J := Ideal.add_mem _ hy hy'
  rw [nsTaylorClass_eq A σ R J (x + x') _ hsum (by
      rw [map_add, shiftMk_taylorLift, shiftMk_taylorLift]
      exact (map_add (taylor A σ R 1) (x : R) (x' : R)).symm),
    nsTaylorClass_eq A σ R J x _ hy (shiftMk_taylorLift A σ R J (x : R) x.2),
    nsTaylorClass_eq A σ R J x' _ hy' (shiftMk_taylorLift A σ R J (x' : R) x'.2),
    show (⟨taylorLift A σ R J (x : R) x.2 + taylorLift A σ R J (x' : R) x'.2, hsum⟩ :
        ↥(ConeRefinement.polyExt σ J)) =
      ⟨taylorLift A σ R J (x : R) x.2, hy⟩ + ⟨taylorLift A σ R J (x' : R) x'.2, hy'⟩ from rfl,
    map_add]

/-- The degree-zero part of the normal-sheaf coaction: `r ↦ [C r]`. -/
def nsPhiBase : R →+* normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J) :=
  (algebraMap (MvPolynomial σ R)
    (normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J))).comp
      (C : R →+* MvPolynomial σ R)

theorem nsPhiBase_apply (r : R) :
    nsPhiBase σ R J r = algebraMap (MvPolynomial σ R)
      (normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J)) (C r) :=
  rfl

/-- The degree-zero part kills `J`, as it must. -/
theorem nsPhiBase_eq_zero (a : R) (ha : a ∈ J) : nsPhiBase σ R J a = 0 :=
  ConeRefinement.algebraMap_ns_eq_zero (ConeRefinement.polyExt σ J)
    (ConeRefinement.C_mem_polyExt ha)

/-- The degree-one part of the normal-sheaf coaction is semilinear over the degree-zero part. -/
theorem nsTaylorClass_smul (a : R) (x : ↥J) :
    nsTaylorClass A σ R J (a • x) = nsPhiBase σ R J a * nsTaylorClass A σ R J x := by
  obtain ⟨ya, hya⟩ := shiftMk_surjective A σ R 1 (taylor A σ R 1 a)
  have hyx : taylorLift A σ R J (x : R) x.2 ∈ ConeRefinement.polyExt σ J :=
    taylorLift_mem A σ R J (x : R) x.2
  have hmul : ya * taylorLift A σ R J (x : R) x.2 ∈ ConeRefinement.polyExt σ J :=
    Ideal.mul_mem_left _ _ hyx
  rw [nsTaylorClass_eq A σ R J (a • x) _ hmul (by
      rw [map_mul, hya, shiftMk_taylorLift]
      change taylor A σ R 1 a * taylor A σ R 1 (x : R) = taylor A σ R 1 (a * (x : R))
      rw [map_mul]),
    nsTaylorClass_eq A σ R J x _ hyx (shiftMk_taylorLift A σ R J (x : R) x.2),
    show (⟨ya * taylorLift A σ R J (x : R) x.2, hmul⟩ : ↥(ConeRefinement.polyExt σ J)) =
      ya • ⟨taylorLift A σ R J (x : R) x.2, hyx⟩ from rfl,
    ConeRefinement.nsClass_smul, ConeRefinement.algebraMap_ns_polyExt_eq,
    constantCoeff_of_taylor A σ R 1 a ya hya, nsPhiBase_apply]

/-- The universal property of the normal-sheaf ring produces the coaction on `N_{U/M}`. -/
theorem exists_nsPhi :
    ∃ ψ : normalSheafRing R J →+*
        normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J),
      (∀ r : R, ψ (algebraMap R (normalSheafRing R J) r) = nsPhiBase σ R J r) ∧
        (∀ x : ↥J, ψ (nsClass J x) = nsTaylorClass A σ R J x) :=
  ConeRefinement.exists_nsRingHom J (nsPhiBase σ R J) (nsTaylorClass A σ R J)
    (nsTaylorClass_add A σ R J) (nsTaylorClass_smul A σ R J) (nsPhiBase_eq_zero σ R J)

/-- **The tangent coaction on the normal sheaf**, in the form `N_{U/M} → N_{U/M'}`. -/
def nsPhi : normalSheafRing R J →+*
    normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J) :=
  (exists_nsPhi A σ R J).choose

theorem nsPhi_algebraMap (r : R) :
    nsPhi A σ R J (algebraMap R (normalSheafRing R J) r) = nsPhiBase σ R J r :=
  (exists_nsPhi A σ R J).choose_spec.1 r

theorem nsPhi_nsClass (x : ↥J) :
    nsPhi A σ R J (nsClass J x) = nsTaylorClass A σ R J x :=
  (exists_nsPhi A σ R J).choose_spec.2 x

/-- **The tangent coaction on the normal sheaf** `N_{U/M} → N_{U/M}[z_σ]`, in the coordinates of
the product formula `ConeRefinement.nsProdEquiv`. -/
def nsCoactionEtale : normalSheafRing R J →+* MvPolynomial σ (normalSheafRing R J) :=
  RingHom.comp ((ConeRefinement.nsProdEquiv σ J).symm :
    normalSheafRing (MvPolynomial σ R) (ConeRefinement.polyExt σ J) ≃+* _).toRingHom
      (nsPhi A σ R J)

theorem nsCoactionEtale_apply (z : normalSheafRing R J) :
    nsCoactionEtale A σ R J z = (ConeRefinement.nsProdEquiv σ J).symm (nsPhi A σ R J z) :=
  rfl

/-- The normal-sheaf coaction is the identity in degree zero. -/
theorem nsCoactionEtale_algebraMap (r : R) :
    nsCoactionEtale A σ R J (algebraMap R (normalSheafRing R J) r) =
      C (algebraMap R (normalSheafRing R J) r) := by
  rw [nsCoactionEtale_apply, nsPhi_algebraMap]
  refine (ConeRefinement.nsProdEquiv σ J).injective ?_
  rw [RingEquiv.apply_symm_apply, ConeRefinement.nsProdEquiv_apply, ConeRefinement.nsProdMap_C,
    ConeRefinement.nsIncl_algebraMap, nsPhiBase_apply]

/-- The normal-sheaf coaction on a degree-one class, in the product coordinates. -/
theorem nsCoactionEtale_nsClass (x : ↥J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 (x : R)) :
    nsCoactionEtale A σ R J (nsClass J x) =
      (ConeRefinement.nsProdEquiv σ J).symm
        (nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩) := by
  rw [nsCoactionEtale_apply, nsPhi_nsClass, nsTaylorClass_eq A σ R J x y hy hmk]

/-- **Vistoli's lemma for a formally étale chart**: the closed immersion `C_{U/M} ⊆ N_{U/M}` is
equivariant for the tangent translation.  The tangent coaction on the normal cone is the
restriction of the tangent coaction on the normal sheaf along the surjection
`Sym_R(J/J²) ↠ gr_J(R)`. -/
theorem coactionEtale_comp_nsToGr :
    (coactionEtale A σ R J).comp (nsToGr R J).toRingHom =
      (MvPolynomial.map (nsToGr R J).toRingHom).comp (nsCoactionEtale A σ R J) := by
  refine ConeRefinement.ns_ringHom_ext J (fun r ↦ ?_) (fun x ↦ ?_)
  · change coactionEtale A σ R J (nsToGr R J (algebraMap R (normalSheafRing R J) r)) =
      MvPolynomial.map (nsToGr R J).toRingHom
        (nsCoactionEtale A σ R J (algebraMap R (normalSheafRing R J) r))
    rw [AlgHom.commutes, coactionEtale_algebraMap, nsCoactionEtale_algebraMap,
      MvPolynomial.map_C]
    change C (algebraMap R (associatedGradedRing R J) r) =
      C (nsToGr R J (algebraMap R (normalSheafRing R J) r))
    rw [AlgHom.commutes]
  · have hy : taylorLift A σ R J (x : R) x.2 ∈ ConeRefinement.polyExt σ J :=
      taylorLift_mem A σ R J (x : R) x.2
    change coactionEtale A σ R J (nsToGr R J (nsClass J x)) =
      MvPolynomial.map (nsToGr R J).toRingHom (nsCoactionEtale A σ R J (nsClass J x))
    rw [ConeRefinement.nsToGr_nsClass,
      show degreeOneRaw R J x = degreeOneRaw R J ⟨(x : R), x.2⟩ from rfl,
      coactionEtale_degreeOneRaw' A σ R J (x : R) x.2 _ hy
        (shiftMk_taylorLift A σ R J (x : R) x.2),
      nsCoactionEtale_nsClass A σ R J x _ hy (shiftMk_taylorLift A σ R J (x : R) x.2)]
    refine (ConeRefinement.prodEquiv (τ := σ) (I := J)).injective ?_
    rw [RingEquiv.apply_symm_apply, ConeRefinement.prodEquiv_apply, ← RingHom.comp_apply,
      ← ConeRefinement.nsToGr_comp_nsProdMap, RingHom.comp_apply,
      ← ConeRefinement.nsProdEquiv_apply, RingEquiv.apply_symm_apply]
    change _ = nsToGr (MvPolynomial σ R) (ConeRefinement.polyExt σ J)
      (nsClass (ConeRefinement.polyExt σ J) ⟨taylorLift A σ R J (x : R) x.2, hy⟩)
    rw [ConeRefinement.nsToGr_nsClass]

/-- The linear term of `Cones/RefinementNormalSheaf.lean`, with the coefficient change pulled
out. -/
theorem nsInvLin_eq (y : MvPolynomial σ R) :
    ConeRefinement.nsInvLin σ J y =
      map (algebraMap R (normalSheafRing R J)) (homogeneousComponent 1 y) := by
  rw [ConeRefinement.nsInvLin, map_homogeneousComponent_one]

omit [Algebra.FormallyEtale (Amb A σ) R] in
/-- **The inverse of the normal-sheaf product formula on a degree-one class**: the class of `y`
in `N_{U/M'}` is the class of its constant term plus its linear term. -/
theorem nsProdEquiv_symm_nsClass (y : MvPolynomial σ R) (hy : y ∈ ConeRefinement.polyExt σ J) :
    (ConeRefinement.nsProdEquiv σ J).symm (nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩) =
      C (nsClass J ⟨constantCoeff y, ConeRefinement.mem_polyExt_iff.mp hy⟩) +
        ConeRefinement.nsInvLin σ J y := by
  obtain ⟨ψ, hψ0, hψ1⟩ := ConeRefinement.exists_nsProdInv σ J
  have hcomp : ψ.comp (ConeRefinement.nsProdMap σ J) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_
    · have key : ψ.comp (ConeRefinement.nsIncl σ J) =
          (C : normalSheafRing R J →+* MvPolynomial σ (normalSheafRing R J)) := by
        refine ConeRefinement.ns_ringHom_ext J (fun r ↦ ?_) fun x ↦ ?_
        · change ψ (ConeRefinement.nsIncl σ J (algebraMap R (normalSheafRing R J) r)) = C _
          rw [ConeRefinement.nsIncl_algebraMap, hψ0, ConeRefinement.nsInvBase_apply,
            constantCoeff_C]
        · change ψ (ConeRefinement.nsIncl σ J (nsClass J x)) = C _
          rw [ConeRefinement.nsIncl_nsClass, hψ1, ConeRefinement.nsInvLin_C, add_zero]
          congr 2
          exact Subtype.ext (constantCoeff_C _ _)
      rw [RingHom.comp_apply, ConeRefinement.nsProdMap_C, RingHom.id_apply]
      exact DFunLike.congr_fun key w
    · rw [RingHom.comp_apply, ConeRefinement.nsProdMap_X, RingHom.id_apply,
        ConeRefinement.nsZVar, hψ1]
      have hzero : ∀ h : constantCoeff (X t : MvPolynomial σ R) ∈ J,
          (⟨constantCoeff (X t : MvPolynomial σ R), h⟩ : ↥J) = 0 :=
        fun _ ↦ Subtype.ext (constantCoeff_X _ _)
      rw [hzero, map_zero, map_zero, zero_add]
      exact ConeRefinement.nsInvLin_X t
  have hsymm : (ConeRefinement.nsProdEquiv σ J).symm
      (nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩) =
      ψ (nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩) := by
    obtain ⟨w, hw⟩ := (ConeRefinement.nsProdEquiv σ J).surjective
      (nsClass (ConeRefinement.polyExt σ J) ⟨y, hy⟩)
    rw [← hw, RingEquiv.symm_apply_apply, ConeRefinement.nsProdEquiv_apply]
    exact (DFunLike.congr_fun hcomp w).symm
  rw [hsymm, hψ1]

/-- **The degree-one part of the normal-sheaf coaction is the derivative**: for `x ∈ J` and any
lift `y` of its first-order Taylor expansion, the class of `x` goes to `[x] + Σ_i [∂_i x]·z_i`. -/
theorem nsCoactionEtale_nsClass' (x : ↥J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 (x : R)) :
    nsCoactionEtale A σ R J (nsClass J x) =
      C (nsClass J x) +
        map (algebraMap R (normalSheafRing R J)) (homogeneousComponent 1 y) := by
  rw [nsCoactionEtale_nsClass A σ R J x y hy hmk, nsProdEquiv_symm_nsClass, nsInvLin_eq]
  have hcc : ∀ h : constantCoeff y ∈ J, (⟨constantCoeff y, h⟩ : ↥J) = x :=
    fun _ ↦ Subtype.ext (constantCoeff_of_taylor A σ R 1 (x : R) y hmk)
  rw [hcc]

/-- **The counit law for the normal-sheaf coaction.** -/
theorem constantCoeff_nsCoactionEtale (z : normalSheafRing R J) :
    constantCoeff (nsCoactionEtale A σ R J z) = z := by
  have key : (constantCoeff : MvPolynomial σ (normalSheafRing R J) →+*
      normalSheafRing R J).comp (nsCoactionEtale A σ R J) = RingHom.id _ := by
    refine ConeRefinement.ns_ringHom_ext J (fun r ↦ ?_) (fun x ↦ ?_)
    · rw [RingHom.comp_apply, nsCoactionEtale_algebraMap, constantCoeff_C, RingHom.id_apply]
    · rw [RingHom.comp_apply, nsCoactionEtale_nsClass' A σ R J x _
        (taylorLift_mem A σ R J (x : R) x.2) (shiftMk_taylorLift A σ R J (x : R) x.2),
        map_add, constantCoeff_C, RingHom.id_apply, MvPolynomial.constantCoeff_map,
        constantCoeff_homogeneousComponent_one, map_zero, add_zero]
  exact RingHom.congr_fun key z

/-- Translating a `B`-point of the normal sheaf by a tangent vector, in an étale chart. -/
def nsTranslatePointEtale {B : Type u} [CommRing B] (φ : normalSheafRing R J →+* B)
    (v : σ → B) : normalSheafRing R J →+* B :=
  (eval₂Hom φ v).comp (nsCoactionEtale A σ R J)

theorem nsTranslatePointEtale_apply {B : Type u} [CommRing B] (φ : normalSheafRing R J →+* B)
    (v : σ → B) (z : normalSheafRing R J) :
    nsTranslatePointEtale A σ R J φ v z = eval₂Hom φ v (nsCoactionEtale A σ R J z) :=
  rfl

/-- The translation of the normal sheaf does not move the degree-zero part. -/
theorem nsTranslatePointEtale_algebraMap {B : Type u} [CommRing B]
    (φ : normalSheafRing R J →+* B) (v : σ → B) (r : R) :
    nsTranslatePointEtale A σ R J φ v (algebraMap R (normalSheafRing R J) r) =
      φ (algebraMap R (normalSheafRing R J) r) := by
  rw [nsTranslatePointEtale_apply, nsCoactionEtale_algebraMap, eval₂Hom_C]

theorem nsTranslatePointEtale_comp_algebraMap {B : Type u} [CommRing B]
    (φ : normalSheafRing R J →+* B) (v : σ → B) :
    (nsTranslatePointEtale A σ R J φ v).comp (algebraMap R (normalSheafRing R J)) =
      φ.comp (algebraMap R (normalSheafRing R J)) :=
  RingHom.ext fun r ↦ nsTranslatePointEtale_algebraMap A σ R J φ v r

/-- The translation of a degree-one point of the normal sheaf. -/
theorem nsTranslatePointEtale_nsClass {B : Type u} [CommRing B]
    (φ : normalSheafRing R J →+* B) (v : σ → B) (x : ↥J) (y : MvPolynomial σ R)
    (hy : y ∈ ConeRefinement.polyExt σ J) (hmk : shiftMk A σ R 1 y = taylor A σ R 1 (x : R)) :
    nsTranslatePointEtale A σ R J φ v (nsClass J x) =
      φ (nsClass J x) +
        eval₂ (φ.comp (algebraMap R (normalSheafRing R J))) v (homogeneousComponent 1 y) := by
  rw [nsTranslatePointEtale_apply, nsCoactionEtale_nsClass' A σ R J x y hy hmk, map_add,
    eval₂Hom_C, coe_eval₂Hom, eval₂_map]

/-- **Translating a point of the normal sheaf by zero does nothing.** -/
theorem nsTranslatePointEtale_zero {B : Type u} [CommRing B] (φ : normalSheafRing R J →+* B) :
    nsTranslatePointEtale A σ R J φ 0 = φ := by
  refine RingHom.ext fun z ↦ ?_
  rw [nsTranslatePointEtale_apply]
  change eval₂Hom φ (fun _ : σ ↦ (0 : B)) (nsCoactionEtale A σ R J z) = φ z
  rw [eval₂Hom_zero'_apply, constantCoeff_nsCoactionEtale]

/-- **Translating a point of the normal sheaf twice is translating by the sum.** -/
theorem nsTranslatePointEtale_add {B : Type u} [CommRing B] (φ : normalSheafRing R J →+* B)
    (v w : σ → B) :
    nsTranslatePointEtale A σ R J (nsTranslatePointEtale A σ R J φ v) w =
      nsTranslatePointEtale A σ R J φ (v + w) := by
  refine ConeRefinement.ns_ringHom_ext J (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [nsTranslatePointEtale_algebraMap, nsTranslatePointEtale_algebraMap,
      nsTranslatePointEtale_algebraMap]
  · have hy : taylorLift A σ R J (x : R) x.2 ∈ ConeRefinement.polyExt σ J :=
      taylorLift_mem A σ R J (x : R) x.2
    have hmk : shiftMk A σ R 1 (taylorLift A σ R J (x : R) x.2) = taylor A σ R 1 (x : R) :=
      shiftMk_taylorLift A σ R J (x : R) x.2
    rw [nsTranslatePointEtale_nsClass A σ R J _ w x _ hy hmk,
      nsTranslatePointEtale_nsClass A σ R J φ v x _ hy hmk,
      nsTranslatePointEtale_nsClass A σ R J φ (v + w) x _ hy hmk,
      nsTranslatePointEtale_comp_algebraMap,
      show (v + w : σ → B) = fun i ↦ v i + w i from rfl,
      eval₂_add_of_mem_span_X _ v w
        (homogeneousComponent_one_mem_span (taylorLift A σ R J (x : R) x.2)), add_assoc]

/-- **Vistoli's lemma on `B`-points**: translating a point of the affine normal cone, viewed as a
point of the normal sheaf, is translating it in the normal sheaf. -/
theorem nsTranslatePointEtale_comp_nsToGr {B : Type u} [CommRing B]
    (φ : associatedGradedRing R J →+* B) (v : σ → B) :
    nsTranslatePointEtale A σ R J (φ.comp (nsToGr R J).toRingHom) v =
      (translatePointEtale A σ R J φ v).comp (nsToGr R J).toRingHom := by
  rw [nsTranslatePointEtale, translatePointEtale, RingHom.comp_assoc,
    coactionEtale_comp_nsToGr, ← RingHom.comp_assoc]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp
  · simp

end NormalSheaf

/-! ### The action groupoid of the étale chart -/

section Groupoid

open CategoryTheory

/-- The `B`-points of the quotient stack `[C_{U/M}/T_M|_U]` for a formally étale chart
`Spec R → 𝔸^σ_A` and an arbitrary ideal `J ⊆ R`: the action groupoid of the translation action
of the tangent vectors `σ → B` on the `B`-points of the affine normal cone. -/
@[ext]
structure EtaleConeGroupoid (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
    [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R) (B : Type u)
    [CommRing B] where
  /-- The underlying `B`-point of the affine normal cone. -/
  point : associatedGradedRing R J →+* B

namespace EtaleConeGroupoid

variable {A : Type u} [CommRing A] {σ : Type u} {R : Type u} [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] {J : Ideal R} {B : Type u}
  [CommRing B]

/-- An arrow of the quotient groupoid: a tangent vector carrying the source to the target. -/
@[ext]
structure Hom (x y : EtaleConeGroupoid A σ R J B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : translatePointEtale A σ R J x.point val = y.point

/-- The action groupoid structure on the `B`-points of `[C/T]`. -/
instance instCategory : Category (EtaleConeGroupoid A σ R J B) where
  Hom := Hom
  id x := ⟨0, translatePointEtale_zero A σ R J x.point⟩
  comp f g := ⟨f.val + g.val, by
    rw [← translatePointEtale_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

/-- The identity arrow translates by the zero tangent vector. -/
@[simp]
theorem id_val (x : EtaleConeGroupoid A σ R J B) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

/-- Composition of arrows adds the tangent vectors. -/
@[simp]
theorem comp_val {x y z : EtaleConeGroupoid A σ R J B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- **Every arrow of the action groupoid is invertible.** -/
instance instGroupoid : Groupoid (EtaleConeGroupoid A σ R J B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, translatePointEtale_add, add_neg_cancel, translatePointEtale_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

end EtaleConeGroupoid

/-- The `B`-points of the quotient stack `[N_{U/M}/T_M|_U]` of the normal sheaf by the same
translation action. -/
@[ext]
structure EtaleNsGroupoid (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
    [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R) (B : Type u)
    [CommRing B] where
  /-- The underlying `B`-point of the normal sheaf. -/
  point : normalSheafRing R J →+* B

namespace EtaleNsGroupoid

variable {A : Type u} [CommRing A] {σ : Type u} {R : Type u} [CommRing R]
  [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] {J : Ideal R} {B : Type u}
  [CommRing B]

/-- An arrow of the quotient groupoid of the normal sheaf. -/
@[ext]
structure Hom (x y : EtaleNsGroupoid A σ R J B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : nsTranslatePointEtale A σ R J x.point val = y.point

/-- The action groupoid structure on the `B`-points of `[N/T]`. -/
instance instCategory : Category (EtaleNsGroupoid A σ R J B) where
  Hom := Hom
  id x := ⟨0, nsTranslatePointEtale_zero A σ R J x.point⟩
  comp f g := ⟨f.val + g.val, by
    rw [← nsTranslatePointEtale_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

/-- The identity arrow translates by the zero tangent vector. -/
@[simp]
theorem id_val (x : EtaleNsGroupoid A σ R J B) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

/-- Composition of arrows adds the tangent vectors. -/
@[simp]
theorem comp_val {x y z : EtaleNsGroupoid A σ R J B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Every arrow of the action groupoid of the normal sheaf is invertible. -/
instance instGroupoid : Groupoid (EtaleNsGroupoid A σ R J B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, nsTranslatePointEtale_add, add_neg_cancel,
      nsTranslatePointEtale_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

end EtaleNsGroupoid

/-- **The closed immersion `C_{U/M} ⊆ N_{U/M}` as a functor of quotient groupoids**: this is
Vistoli's lemma in the form `[C/T] ⊆ [N/T]`. -/
def coneToNsFunctorEtale (A : Type u) [CommRing A] (σ : Type u) (R : Type u) [CommRing R]
    [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R) (B : Type u)
    [CommRing B] : EtaleConeGroupoid A σ R J B ⥤ EtaleNsGroupoid A σ R J B where
  obj x := ⟨x.point.comp (nsToGr R J).toRingHom⟩
  map f := ⟨f.val, by
    rw [nsTranslatePointEtale_comp_nsToGr, f.translate_eq]⟩
  map_id _ := EtaleNsGroupoid.Hom.ext rfl
  map_comp _ _ := EtaleNsGroupoid.Hom.ext rfl

/-- The comparison functor is faithful: it does not change the tangent vectors. -/
instance instFaithfulConeToNsFunctorEtale (A : Type u) [CommRing A] (σ : Type u) (R : Type u)
    [CommRing R] [Algebra (Amb A σ) R] [Algebra.FormallyEtale (Amb A σ) R] (J : Ideal R)
    (B : Type u) [CommRing B] : (coneToNsFunctorEtale A σ R J B).Faithful where
  map_injective h := EtaleConeGroupoid.Hom.ext (congrArg EtaleNsGroupoid.Hom.val h)

end Groupoid

/-! ### Comparison with the polynomial model -/

section Model

open CategoryTheory

variable (A : Type u) [CommRing A] (σ : Type u)

/-- **In the polynomial model the linear part of the shift is the Taylor derivation**: the
first-order part of `x_i ↦ x_i + ε_i` is `f ↦ Σ_i ∂_i f · ε_i`. -/
theorem homogeneousComponent_one_shiftHom (f : Amb A σ) :
    homogeneousComponent 1 (shiftHom A σ (Amb A σ) f) = ConeTranslation.taylor A σ f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [shiftHom_C, homogeneousComponent_one_C, ConeTranslation.taylor_C]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | mul_X f i hf =>
    rw [map_mul, shiftHom_X, mul_add, map_add,
      show shiftHom A σ (Amb A σ) f * C (algebraMap (Amb A σ) (Amb A σ) (X i)) =
        C (algebraMap (Amb A σ) (Amb A σ) (X i)) * shiftHom A σ (Amb A σ) f from mul_comm _ _,
      homogeneousComponent_C_mul, hf,
      homogeneousComponent_one_mul (shiftHom A σ (Amb A σ) f) (X i) (constantCoeff_X _ _),
      homogeneousComponent_one_X, constantCoeff_shiftHom, ConeTranslation.taylor_mul,
      ConeTranslation.taylor_X, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply,
      add_comm]

variable (J : Ideal (Amb A σ))

/-- **In the polynomial model the étale tangent coaction is the translation coaction** of
`Cones/ConeTranslation.lean`. -/
theorem coactionEtale_eq_coaction :
    coactionEtale A σ (Amb A σ) J = (ConeTranslation.coaction J).toRingHom := by
  refine ConeRefinement.gr_ringHom_ext (J := J) (fun r ↦ ?_) (fun x ↦ ?_)
  · rw [coactionEtale_algebraMap]
    exact (ConeTranslation.coaction_algebraMap J r).symm
  · have hy : shiftHom A σ (Amb A σ) (x : Amb A σ) ∈ ConeRefinement.polyExt σ J := by
      rw [ConeRefinement.mem_polyExt_iff, constantCoeff_shiftHom, Algebra.algebraMap_self_apply]
      exact x.2
    have hmk : shiftMk A σ (Amb A σ) 1 (shiftHom A σ (Amb A σ) (x : Amb A σ)) =
        taylor A σ (Amb A σ) 1 (x : Amb A σ) := by
      rw [taylor_self]
      exact (algebraMap_shift_eq A σ (Amb A σ) 1 (x : Amb A σ)).symm
    rw [show degreeOneRaw (Amb A σ) J x = degreeOneRaw (Amb A σ) J ⟨(x : Amb A σ), x.2⟩ from rfl,
      coactionEtale_degreeOneRaw A σ (Amb A σ) J (x : Amb A σ) x.2 _ hy hmk, grLinearPart,
      homogeneousComponent_one_shiftHom, ConeRefinement.degreeOneRaw_eq_mk]
    exact (ConeTranslation.coaction_degreeOne J ⟨(x : Amb A σ), x.2⟩).symm

/-- In the polynomial model the étale translation of points is the translation of
`Cones/ConeTranslation.lean`. -/
theorem translatePointEtale_eq_translatePoint {B : Type u} [CommRing B]
    (φ : associatedGradedRing (Amb A σ) J →+* B) (v : σ → B) :
    translatePointEtale A σ (Amb A σ) J φ v = ConeTranslation.translatePoint J φ v := by
  rw [translatePointEtale, coactionEtale_eq_coaction]
  rfl

variable (B : Type u) [CommRing B]

/-- The comparison functor from the action groupoid of the étale formalism, applied to the
polynomial model itself, to the action groupoid of `Cones/RefinementQuotient.lean`. -/
def modelConeFunctor :
    EtaleConeGroupoid A σ (Amb A σ) J B ⥤ ConeRefinement.ConeGroupoid J B where
  obj x := ⟨x.point⟩
  map f := ⟨f.val, by
    rw [← translatePointEtale_eq_translatePoint]
    exact f.translate_eq⟩
  map_id _ := ConeRefinement.ConeGroupoid.Hom.ext rfl
  map_comp _ _ := ConeRefinement.ConeGroupoid.Hom.ext rfl

/-- The comparison functor is faithful. -/
instance instFaithfulModelConeFunctor : (modelConeFunctor A σ J B).Faithful where
  map_injective h := EtaleConeGroupoid.Hom.ext (congrArg ConeRefinement.ConeGroupoid.Hom.val h)

/-- The comparison functor is full. -/
instance instFullModelConeFunctor : (modelConeFunctor A σ J B).Full where
  map_surjective g := ⟨⟨g.val, by
    rw [translatePointEtale_eq_translatePoint]
    exact g.translate_eq⟩, rfl⟩

/-- The comparison functor is essentially surjective: it is the identity on points. -/
instance instEssSurjModelConeFunctor : (modelConeFunctor A σ J B).EssSurj where
  mem_essImage y := ⟨⟨y.point⟩, ⟨eqToIso (ConeRefinement.ConeGroupoid.ext rfl)⟩⟩

/-- The comparison functor is an equivalence. -/
instance instIsEquivalenceModelConeFunctor : (modelConeFunctor A σ J B).IsEquivalence where

/-- **The étale formalism computes the polynomial-model quotient groupoid.**  For `R = P` the
action groupoid `[C/T](B)` built from the Taylor expansions is equivalent to the one built in
`Cones/RefinementQuotient.lean` from the translation coaction. -/
def modelConeEquivalence :
    EtaleConeGroupoid A σ (Amb A σ) J B ≌ ConeRefinement.ConeGroupoid J B :=
  (modelConeFunctor A σ J B).asEquivalence

end Model

end

end EtaleAmbient

end GromovWitten.AlgebraicGeometry
