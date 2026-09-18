/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.EmbeddingIndependence

/-!
# The refinement lemma for the normal sheaf

`Cones/RefinementQuotient.lean` proves the refinement lemma for the affine normal *cone* in the
polynomial model: the associated graded ring of `I' = polyExt τ I = I·R[y_τ] + (y_τ)` is the
polynomial ring `gr_I(R)[z_τ]` (`prodEquiv`), and the induced functor of quotient groupoids
`[C_{U/M'}/T_{M'}](B) → [C_{U/M}/T_M](B)` is an equivalence (`refinementQuotientEquivalence`).
For the normal *sheaf* `N_{U/M} = Sym_{R/I}(I/I²)` only the comparison map `nsProdMap` and its
surjectivity were available.  This file completes the picture.

## The product formula for the normal sheaf

`exists_nsRingHom` is the universal property of `normalSheafRing A J = Sym_A(J)/J·Sym_A(J)` in
the form needed here: a ring map `β : A →+* T` killing `J` together with an additive,
`β`-semilinear map `L : J → T` defines a ring map `normalSheafRing A J →+* T`.  Applying it to
`T = N_{U/M}[z_τ]`, to `β v = [v(0)]` and to

`L f = [f(0)] + Σ_t [∂_{y_t} f (0)] z_t`

(the constant and the linear term of `f` in the extra variables, read in `N_{U/M}`) produces a
left inverse of `nsProdMap` (`nsProdMap_leftInverse`), whence

* `nsProdMap_injective` and `nsProdEquiv : N_{U/M}[z_τ] ≃+* N_{U/M'}`, the normal-sheaf product
  formula `N_{U/M × 𝔸^τ} = N_{U/M} × 𝔸^τ`.

## The quotient groupoids

`nsRefinementEquiv` transports `nsProdEquiv` along `sumRingEquiv` to the polynomial model, and
`nsTranslatePoint_comp_nsRefinementEquiv` is the equivariance statement for the translation
action on the normal sheaf (whose action axioms are `nsTranslatePoint_zero` and
`nsTranslatePoint_add`).  `NsGroupoid I B` is the action groupoid `[N_{U/M}/T_M|_U](B)` and
`nsRefinementFunctor` the functor induced by the projection `M' = 𝔸^{σ⊕τ} → M = 𝔸^σ`;
`nsRefinementQuotientEquivalence` proves that it is an equivalence of groupoids for every test
algebra `B`.  The closed immersion `C ⊆ N` is the functor `coneToNsFunctor`, and
`nsToGr_comp_nsRefinementEquiv` and `coneToNsRefinementIso` record that the two refinement
equivalences are compatible with it.

## Independence of the presentation

The same groupoids satisfy the normal-sheaf analogue of `Cones/EmbeddingIndependence.lean`:
`nsCompareFunctor` is the comparison functor attached to a lift `h` of one presentation into
another (built from `EmbeddingIndependence.nsPresMap` and the Jacobian `nsCompareVec`),
`nsCompareFunctorIdIso` and `nsCompareFunctorCompIso` are its functoriality, `nsLiftIso` its
canonicity in the lift (the computation behind it being `point_nsClass_sub`), and
`nsCompareEquivalence` / `nsPresentationEquivalence` the resulting equivalence of quotient
groupoids, with the cocycle condition `nsCocycleIso`.
-/

namespace GromovWitten.AlgebraicGeometry

namespace ConeRefinement

universe u

noncomputable section

open AffineNormalCone MvPolynomial

/-! ### A universal property for the normal-sheaf ring -/

section UniversalProperty

variable {A T : Type u} [CommRing A] [CommRing T]

/-- **The universal property of `N = Sym_A(J)/J·Sym_A(J)`.**  A ring map `β : A →+* T` which
kills `J`, together with an additive map `L : J → T` which is semilinear over `β`, defines a
ring map out of the normal-sheaf ring, sending the degree-zero elements to `β` and the
degree-one classes `nsClass J x` to `L x`. -/
theorem exists_nsRingHom (J : Ideal A) (β : A →+* T) (L : J → T)
    (hadd : ∀ x y : J, L (x + y) = L x + L y)
    (hsmul : ∀ (a : A) (x : J), L (a • x) = β a * L x)
    (hβ : ∀ a ∈ J, β a = 0) :
    ∃ ψ : normalSheafRing A J →+* T,
      (∀ a : A, ψ (algebraMap A (normalSheafRing A J) a) = β a) ∧
        (∀ x : J, ψ (nsClass J x) = L x) := by
  let _ := β.toAlgebra
  let Ll : J →ₗ[A] T :=
    { toFun := L
      map_add' := hadd
      map_smul' := fun a x ↦ by
        rw [hsmul]
        rfl }
  have hker : ∀ a ∈ Ideal.map (algebraMap A (SymmetricAlgebra A J)) J,
      SymmetricAlgebra.lift Ll a = 0 := by
    intro a ha
    have hle : Ideal.map (algebraMap A (SymmetricAlgebra A J)) J ≤
        RingHom.ker (SymmetricAlgebra.lift Ll).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change SymmetricAlgebra.lift Ll (algebraMap A (SymmetricAlgebra A J) r) = 0
      rw [AlgHom.commutes]
      exact hβ r hr
    exact RingHom.mem_ker.mp (hle ha)
  refine ⟨Ideal.Quotient.lift _ (SymmetricAlgebra.lift Ll).toRingHom hker, fun a ↦ ?_, fun x ↦ ?_⟩
  · change SymmetricAlgebra.lift Ll (algebraMap A (SymmetricAlgebra A J) a) = β a
    rw [AlgHom.commutes]
    rfl
  · rw [nsClass_eq_mk]
    change SymmetricAlgebra.lift Ll (SymmetricAlgebra.ι A J x) = L x
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl

end UniversalProperty

/-! ### The linear term of a polynomial in the extra variables -/

section LinearTerm

variable {S : Type u} [CommRing S] {τ : Type u}

/-- The coefficient of `y_t` in a product, when the second factor has no constant term. -/
theorem coeff_single_one_mul (g h : MvPolynomial τ S) (t : τ) (hh : constantCoeff h = 0) :
    coeff (Finsupp.single t 1) (g * h) = constantCoeff g * coeff (Finsupp.single t 1) h := by
  classical
  have key : ∀ p : MvPolynomial τ S,
      coeff (Finsupp.single t 1) p = constantCoeff (pderiv t p) := by
    intro p
    rw [constantCoeff_eq]
    simp [coeff_pderiv]
  rw [key, key, pderiv_mul, map_add, map_mul, map_mul, hh, mul_zero, zero_add]

/-- The linear part of a product, when the second factor has no constant term. -/
theorem homogeneousComponent_one_mul (g h : MvPolynomial τ S) (hh : constantCoeff h = 0) :
    homogeneousComponent 1 (g * h) = C (constantCoeff g) * homogeneousComponent 1 h := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_homogeneousComponent, coeff_C_mul, coeff_homogeneousComponent]
  split_ifs with hm
  · obtain ⟨t, ht⟩ := (Finsupp.range_single_one (σ := τ)).ge hm
    subst ht
    exact coeff_single_one_mul g h t hh
  · rw [mul_zero]

/-- The linear part of a constant vanishes. -/
theorem homogeneousComponent_one_C (s : S) :
    homogeneousComponent 1 (C s : MvPolynomial τ S) = 0 :=
  homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; norm_num)

/-- A variable is its own linear part. -/
theorem homogeneousComponent_one_X (t : τ) :
    homogeneousComponent 1 (X t : MvPolynomial τ S) = X t := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  rw [coeff_homogeneousComponent]
  split_ifs with hm
  · rfl
  · rw [coeff_X]
    refine (if_neg fun hmt ↦ hm ?_).symm
    rw [← hmt]
    simp

end LinearTerm

/-! ### The inverse of the comparison map of normal sheaves -/

section NormalSheafProduct

variable {R : Type u} [CommRing R] (τ : Type u) (I : Ideal R)

/-- The degree-zero part of the left inverse of `nsProdMap`: the ring map
`R[y_τ] → N_{U/M}[z_τ]` sending `v` to the class of its constant term. -/
def nsInvBase : MvPolynomial τ R →+* MvPolynomial τ (normalSheafRing R I) :=
  (C : normalSheafRing R I →+* MvPolynomial τ (normalSheafRing R I)).comp
    ((algebraMap R (normalSheafRing R I)).comp
      (constantCoeff : MvPolynomial τ R →+* R))

theorem nsInvBase_apply (v : MvPolynomial τ R) :
    nsInvBase τ I v = C (algebraMap R (normalSheafRing R I) (constantCoeff v)) :=
  rfl

theorem nsInvBase_eq_zero {v : MvPolynomial τ R} (hv : v ∈ polyExt τ I) :
    nsInvBase τ I v = 0 := by
  rw [nsInvBase_apply, algebraMap_ns_eq_zero I (mem_polyExt_iff.mp hv), map_zero]

/-- The linear term of a polynomial in the extra variables, with coefficients read in the
normal-sheaf ring `N_{U/M}`. -/
def nsInvLin (v : MvPolynomial τ R) : MvPolynomial τ (normalSheafRing R I) :=
  homogeneousComponent 1 (MvPolynomial.map (algebraMap R (normalSheafRing R I)) v)

variable {τ I}

theorem nsInvLin_add (v w : MvPolynomial τ R) :
    nsInvLin τ I (v + w) = nsInvLin τ I v + nsInvLin τ I w := by
  rw [nsInvLin, nsInvLin, nsInvLin, map_add, map_add]

theorem nsInvLin_C (r : R) : nsInvLin τ I (C r) = 0 := by
  rw [nsInvLin, MvPolynomial.map_C, homogeneousComponent_one_C]

theorem nsInvLin_X (t : τ) : nsInvLin τ I (X t) = X t := by
  rw [nsInvLin, MvPolynomial.map_X, homogeneousComponent_one_X]

theorem nsInvLin_mul (v w : MvPolynomial τ R) (hw : w ∈ polyExt τ I) :
    nsInvLin τ I (v * w) = nsInvBase τ I v * nsInvLin τ I w := by
  have hcc : constantCoeff (MvPolynomial.map (algebraMap R (normalSheafRing R I)) w) = 0 := by
    rw [MvPolynomial.constantCoeff_map, algebraMap_ns_eq_zero I (mem_polyExt_iff.mp hw)]
  rw [nsInvLin, map_mul, homogeneousComponent_one_mul _ _ hcc, MvPolynomial.constantCoeff_map,
    nsInvBase_apply, nsInvLin]

variable (τ I)

/-- The left inverse of `nsProdMap`, characterised by its values on the degree-zero elements and
on the degree-one classes: the constant and the linear term in the extra variables. -/
theorem exists_nsProdInv :
    ∃ ψ : normalSheafRing (MvPolynomial τ R) (polyExt τ I) →+*
        MvPolynomial τ (normalSheafRing R I),
      (∀ v : MvPolynomial τ R,
          ψ (algebraMap (MvPolynomial τ R) (normalSheafRing (MvPolynomial τ R) (polyExt τ I)) v) =
            nsInvBase τ I v) ∧
        (∀ f : polyExt τ I, ψ (nsClass (polyExt τ I) f) =
          C (nsClass I ⟨constantCoeff (f : MvPolynomial τ R), mem_polyExt_iff.mp f.2⟩) +
            nsInvLin τ I (f : MvPolynomial τ R)) := by
  refine exists_nsRingHom (polyExt τ I) (nsInvBase τ I) _ (fun f g ↦ ?_) (fun v f ↦ ?_)
    fun v hv ↦ nsInvBase_eq_zero τ I hv
  · have hclass : (⟨constantCoeff ((f + g : polyExt τ I) : MvPolynomial τ R),
        mem_polyExt_iff.mp (f + g).2⟩ : I) =
        ⟨constantCoeff (f : MvPolynomial τ R), mem_polyExt_iff.mp f.2⟩ +
          ⟨constantCoeff (g : MvPolynomial τ R), mem_polyExt_iff.mp g.2⟩ := by
      apply Subtype.ext
      change constantCoeff ((f : MvPolynomial τ R) + (g : MvPolynomial τ R)) = _
      rw [map_add]
      rfl
    have hcoe : ((f + g : polyExt τ I) : MvPolynomial τ R) =
        (f : MvPolynomial τ R) + (g : MvPolynomial τ R) := rfl
    rw [hclass, map_add, map_add, hcoe, nsInvLin_add]
    ring
  · have hclass : (⟨constantCoeff ((v • f : polyExt τ I) : MvPolynomial τ R),
        mem_polyExt_iff.mp (v • f).2⟩ : I) =
        constantCoeff v • ⟨constantCoeff (f : MvPolynomial τ R), mem_polyExt_iff.mp f.2⟩ := by
      apply Subtype.ext
      change constantCoeff (v * (f : MvPolynomial τ R)) = _
      rw [map_mul]
      rfl
    have hlin : ((v • f : polyExt τ I) : MvPolynomial τ R) = v * (f : MvPolynomial τ R) := rfl
    rw [hclass, nsClass_smul, hlin, nsInvLin_mul v (f : MvPolynomial τ R) f.2, nsInvBase_apply,
      map_mul]
    ring

/-- The comparison map `N_{U/M}[z_τ] → N_{U/M'}` of normal sheaves has a left inverse. -/
theorem nsProdMap_leftInverse :
    ∃ ψ : normalSheafRing (MvPolynomial τ R) (polyExt τ I) →+*
      MvPolynomial τ (normalSheafRing R I), ψ.comp (nsProdMap τ I) = RingHom.id _ := by
  obtain ⟨ψ, hψ0, hψ1⟩ := exists_nsProdInv τ I
  refine ⟨ψ, MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_⟩
  · have key : ψ.comp (nsIncl τ I) =
        (C : normalSheafRing R I →+* MvPolynomial τ (normalSheafRing R I)) := by
      refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
      · change ψ (nsIncl τ I (algebraMap R (normalSheafRing R I) r)) = C _
        rw [nsIncl_algebraMap, hψ0, nsInvBase_apply, constantCoeff_C]
      · change ψ (nsIncl τ I (nsClass I x)) = C _
        rw [nsIncl_nsClass, hψ1, nsInvLin_C, add_zero]
        congr 2
        exact Subtype.ext (constantCoeff_C _ _)
    rw [RingHom.comp_apply, nsProdMap_C, RingHom.id_apply]
    exact DFunLike.congr_fun key w
  · rw [RingHom.comp_apply, nsProdMap_X, RingHom.id_apply, nsZVar, hψ1]
    have hzero : (⟨constantCoeff (X t : MvPolynomial τ R), mem_polyExt_iff.mp
        (X_mem_polyExt (I := I) t)⟩ : I) = 0 := by
      apply Subtype.ext
      exact constantCoeff_X R t
    rw [hzero, map_zero, map_zero, zero_add]
    exact nsInvLin_X t

variable {τ I}

/-- **The comparison map of normal sheaves of a refinement is injective.** -/
theorem nsProdMap_injective : Function.Injective (nsProdMap τ I) := by
  obtain ⟨ψ, hψ⟩ := nsProdMap_leftInverse τ I
  exact Function.LeftInverse.injective (g := ψ) fun w ↦ DFunLike.congr_fun hψ w

variable (τ I)

/-- **The product formula for the normal sheaf of a refinement.**  The normal sheaf of the
zero-section embedding `U ↪ M × 𝔸^τ` is the product `N_{U/M} × 𝔸^τ`: the normal-sheaf ring of
`I' = I·R[y_τ] + (y_τ)` is the polynomial ring `N_{U/M}[z_τ]`, the extra variables being the
degree-one classes of the new coordinates. -/
def nsProdEquiv : MvPolynomial τ (normalSheafRing R I) ≃+*
    normalSheafRing (MvPolynomial τ R) (polyExt τ I) :=
  RingEquiv.ofBijective (nsProdMap τ I) ⟨nsProdMap_injective, nsProdMap_surjective⟩

@[simp]
theorem nsProdEquiv_apply (w : MvPolynomial τ (normalSheafRing R I)) :
    nsProdEquiv τ I w = nsProdMap τ I w :=
  rfl

end NormalSheafProduct

/-! ### Transport of the normal-sheaf ring along an isomorphism -/

section Transport

variable {A B : Type u} [CommRing A] [CommRing B]

theorem nsMapOfEq_nsClass (J : Ideal A) (f : A →+* B) (K : Ideal B) (hK : J.map f = K) (x : J) :
    nsMapOfEq J f K hK (nsClass J x) =
      nsClass K ⟨f (x : A), hK ▸ Ideal.mem_map_of_mem f x.2⟩ := by
  rw [nsClass_eq_mk, nsMapOfEq_mk, symMapOfEq_ι, nsClass_eq_mk]

theorem nsMapOfEq_symm_comp (J : Ideal A) (K : Ideal B) (f : A ≃+* B)
    (h : J.map (f : A →+* B) = K) (h' : K.map (f.symm : B →+* A) = J) :
    (nsMapOfEq K (f.symm : B →+* A) J h').comp (nsMapOfEq J (f : A →+* B) K h) =
      RingHom.id (normalSheafRing A J) := by
  have hcomp := nsMapOfEq_comp J (f : A →+* B) K h (f.symm : B →+* A) J h'
  have he : ((f.symm : B →+* A).comp (f : A →+* B)) = RingHom.id A :=
    RingHom.ext fun a ↦ f.symm_apply_apply a
  rw [← hcomp, nsMapOfEq_congr J _ J _ he]
  exact nsMapOfEq_id J

/-- The normal-sheaf ring only depends on the pair `(ring, ideal)` up to isomorphism. -/
def nsEquivOfEquiv (J : Ideal A) (K : Ideal B) (f : A ≃+* B) (h : J.map (f : A →+* B) = K) :
    normalSheafRing A J ≃+* normalSheafRing B K where
  toFun := nsMapOfEq J (f : A →+* B) K h
  invFun := nsMapOfEq K (f.symm : B →+* A) J (map_symm_of_map J K f h)
  left_inv z := DFunLike.congr_fun (nsMapOfEq_symm_comp J K f h (map_symm_of_map J K f h)) z
  right_inv z := DFunLike.congr_fun
    (nsMapOfEq_symm_comp K J f.symm (map_symm_of_map J K f h) h) z
  map_mul' := map_mul _
  map_add' := map_add _

end Transport

/-! ### The product formula in the polynomial model -/

section GraphModel

open ConeTranslation EmbeddingIndependence

variable {A : Type u} [CommRing A] {σ τ : Type u} (I : Ideal (Amb A σ))

/-- **The normal sheaf of a refinement is a product.**  For the zero-section embedding
`U ↪ M' = 𝔸^{σ⊕τ}` refining `U ↪ M = 𝔸^σ`, the affine normal sheaf is
`N_{U/M'} = N_{U/M} × 𝔸^τ`: its coordinate ring is the polynomial ring `N_{U/M}[z_τ]`. -/
def nsRefinementEquiv : MvPolynomial τ (Ns I) ≃+* Ns (graphIdeal A σ τ I 0) :=
  (nsProdEquiv τ I).trans
    (nsEquivOfEquiv (graphIdeal A σ τ I 0) (polyExt τ I) (sumRingEquiv A σ τ)
      (map_sumRingEquiv_graphIdeal I)).symm

theorem nsRefinementEquiv_apply (w : MvPolynomial τ (Ns I)) :
    nsRefinementEquiv I w =
      nsMapOfEq (polyExt τ I) (((sumRingEquiv A σ τ).symm :
          MvPolynomial τ (Amb A σ) ≃+* Amb A (σ ⊕ τ)) :
          MvPolynomial τ (Amb A σ) →+* Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
        (map_symm_of_map _ _ _ (map_sumRingEquiv_graphIdeal I)) (nsProdMap τ I w) :=
  rfl

@[simp]
theorem nsRefinementEquiv_toRingHom_apply (w : MvPolynomial τ (Ns I)) :
    (nsRefinementEquiv I).toRingHom w = nsRefinementEquiv I w :=
  rfl

variable {I}

@[simp]
theorem nsRefinementEquiv_C_algebraMap (r : Amb A σ) :
    nsRefinementEquiv I (C (algebraMap (Amb A σ) (Ns I) r)) =
      algebraMap (Amb A (σ ⊕ τ)) (Ns (graphIdeal A σ τ I 0)) (incl A σ τ r) := by
  rw [nsRefinementEquiv_apply, nsProdMap_C, nsIncl_algebraMap, nsMapOfEq_algebraMap]
  change algebraMap _ _ ((sumRingEquiv A σ τ).symm (C r)) = _
  rw [sumRingEquiv_symm_C]

@[simp]
theorem nsRefinementEquiv_C_nsClass (x : I) :
    nsRefinementEquiv I (C (nsClass I x)) =
      nsClass (graphIdeal A σ τ I 0)
        ⟨incl A σ τ (x : Amb A σ), incl_mem_graphIdeal x.2⟩ := by
  rw [nsRefinementEquiv_apply, nsProdMap_C, nsIncl_nsClass, nsMapOfEq_nsClass]
  exact congrArg _ (Subtype.ext (sumRingEquiv_symm_C (x : Amb A σ)))

@[simp]
theorem nsRefinementEquiv_X (t : τ) :
    nsRefinementEquiv I (X t) =
      nsClass (graphIdeal A σ τ I 0) ⟨X (Sum.inr t), X_inr_mem_graphIdeal t⟩ := by
  rw [nsRefinementEquiv_apply, nsProdMap_X, nsZVar, nsMapOfEq_nsClass]
  exact congrArg _ (Subtype.ext (sumRingEquiv_symm_X t))

/-- The closed immersion `C ⊆ N` is compatible with the two product decompositions, on the
first factor. -/
theorem nsToGr_comp_nsRefinementEquiv_comp_C :
    ((nsToGr (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)).toRingHom.comp
        (nsRefinementEquiv I).toRingHom).comp (C : Ns I →+* MvPolynomial τ (Ns I)) =
      ((refinementEquiv I).toRingHom.comp
        (C : Gr I →+* MvPolynomial τ (Gr I))).comp (nsToGr (Amb A σ) I).toRingHom := by
  refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · change nsToGr (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
      (nsRefinementEquiv I (C (algebraMap (Amb A σ) (Ns I) r))) =
      refinementEquiv I (C (nsToGr (Amb A σ) I (algebraMap (Amb A σ) (Ns I) r)))
    rw [nsRefinementEquiv_C_algebraMap, AlgHom.commutes, AlgHom.commutes,
      refinementEquiv_C_algebraMap]
  · change nsToGr (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)
      (nsRefinementEquiv I (C (nsClass I x))) =
      refinementEquiv I (C (nsToGr (Amb A σ) I (nsClass I x)))
    rw [nsRefinementEquiv_C_nsClass, nsToGr_nsClass, nsToGr_nsClass,
      refinementEquiv_C_degreeOneRaw]

/-- **The closed immersion `C ⊆ N` is compatible with the two product decompositions.**  The
isomorphisms `C_{U/M'} = C_{U/M} × 𝔸^τ` and `N_{U/M'} = N_{U/M} × 𝔸^τ` fit in a commutative
square with the surjections `Sym(I/I²) ↠ gr_I`. -/
theorem nsToGr_comp_nsRefinementEquiv :
    (nsToGr (Amb A (σ ⊕ τ)) (graphIdeal A σ τ I 0)).toRingHom.comp
        (nsRefinementEquiv I).toRingHom =
      (refinementEquiv I).toRingHom.comp
        (MvPolynomial.map (nsToGr (Amb A σ) I).toRingHom) := by
  have key := nsToGr_comp_nsRefinementEquiv_comp_C (I := I) (τ := τ)
  refine MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C]
    exact DFunLike.congr_fun key w
  · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_X,
      nsRefinementEquiv_toRingHom_apply, nsRefinementEquiv_X, refinementEquiv_toRingHom_apply,
      refinementEquiv_X]
    exact nsToGr_nsClass _ _

/-! #### Equivariance of the product decomposition -/

set_option maxHeartbeats 1600000 in
-- As for `ConeRefinement.translatePoint_comp_refinementEquiv`, the unifier has to match the
-- composite isomorphism `nsRefinementEquiv` against the quotient presentation of the
-- symmetric algebra, which is expensive.
/-- **Equivariance.**  On `B`-points, the translation action of `T_{M'} = 𝔸^{σ⊕τ}` on
`N_{U/M'} = N_{U/M} × 𝔸^τ` is the product of the translation action of `𝔸^σ` on `N_{U/M}` and
of the translation action of `𝔸^τ` on itself. -/
theorem nsTranslatePoint_comp_nsRefinementEquiv {B : Type u} [CommRing B]
    (φ : Ns (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) :
    (nsTranslatePoint (graphIdeal A σ τ I 0) φ v).comp (nsRefinementEquiv I).toRingHom =
      eval₂Hom (nsTranslatePoint I
          (φ.comp ((nsRefinementEquiv I).toRingHom.comp (C : Ns I →+* MvPolynomial τ (Ns I))))
          (v ∘ Sum.inl))
        fun t ↦ φ (nsRefinementEquiv I (X t)) + v (Sum.inr t) := by
  have hcomp : (φ.comp (algebraMap (Amb A (σ ⊕ τ)) (Ns (graphIdeal A σ τ I 0)))).comp
        (incl A σ τ : Amb A σ →+* Amb A (σ ⊕ τ)) =
      (φ.comp ((nsRefinementEquiv I).toRingHom.comp
        (C : Ns I →+* MvPolynomial τ (Ns I)))).comp (algebraMap (Amb A σ) (Ns I)) :=
    RingHom.ext fun r ↦ by
      change φ (algebraMap (Amb A (σ ⊕ τ)) (Ns (graphIdeal A σ τ I 0)) (incl A σ τ r)) =
        φ (nsRefinementEquiv I (C (algebraMap (Amb A σ) (Ns I) r)))
      rw [nsRefinementEquiv_C_algebraMap]
  have key : (nsTranslatePoint (graphIdeal A σ τ I 0) φ v).comp
      ((nsRefinementEquiv I).toRingHom.comp (C : Ns I →+* MvPolynomial τ (Ns I))) =
      nsTranslatePoint I (φ.comp ((nsRefinementEquiv I).toRingHom.comp
        (C : Ns I →+* MvPolynomial τ (Ns I)))) (v ∘ Sum.inl) := by
    refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
    · change nsTranslatePoint (graphIdeal A σ τ I 0) φ v
        (nsRefinementEquiv I (C (algebraMap (Amb A σ) (Ns I) r))) =
        nsTranslatePoint I _ (v ∘ Sum.inl) (algebraMap (Amb A σ) (Ns I) r)
      rw [nsRefinementEquiv_C_algebraMap, nsTranslatePoint_algebraMap,
        nsTranslatePoint_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
        nsRefinementEquiv_toRingHom_apply, nsRefinementEquiv_C_algebraMap]
    · change nsTranslatePoint (graphIdeal A σ τ I 0) φ v
        (nsRefinementEquiv I (C (nsClass I x))) =
        nsTranslatePoint I _ (v ∘ Sum.inl) (nsClass I x)
      rw [nsRefinementEquiv_C_nsClass, nsTranslatePoint_nsClass, nsTranslatePoint_nsClass,
        eval₂_taylor_incl, hcomp, RingHom.comp_apply, RingHom.comp_apply,
        nsRefinementEquiv_toRingHom_apply, nsRefinementEquiv_C_nsClass]
  refine MvPolynomial.ringHom_ext (fun w ↦ ?_) fun t ↦ ?_
  · rw [RingHom.comp_apply, eval₂Hom_C]
    exact DFunLike.congr_fun key w
  · rw [RingHom.comp_apply, eval₂Hom_X', nsRefinementEquiv_toRingHom_apply,
      nsRefinementEquiv_X, nsTranslatePoint_nsClass]
    simp only [ConeTranslation.taylor_X, eval₂_X]

theorem nsTranslatePoint_comp_nsRefinementEquiv_comp_C {B : Type u} [CommRing B]
    (φ : Ns (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) :
    nsTranslatePoint I
        (φ.comp ((nsRefinementEquiv I).toRingHom.comp (C : Ns I →+* MvPolynomial τ (Ns I))))
        (v ∘ Sum.inl) =
      (nsTranslatePoint (graphIdeal A σ τ I 0) φ v).comp
        ((nsRefinementEquiv I).toRingHom.comp (C : Ns I →+* MvPolynomial τ (Ns I))) := by
  refine RingHom.ext fun w ↦ ?_
  have h := DFunLike.congr_fun (nsTranslatePoint_comp_nsRefinementEquiv (I := I) φ v) (C w)
  rw [RingHom.comp_apply, eval₂Hom_C] at h
  exact h.symm

theorem nsTranslatePoint_nsRefinementEquiv_X {B : Type u} [CommRing B]
    (φ : Ns (graphIdeal A σ τ I 0) →+* B) (v : σ ⊕ τ → B) (t : τ) :
    nsTranslatePoint (graphIdeal A σ τ I 0) φ v (nsRefinementEquiv I (X t)) =
      φ (nsRefinementEquiv I (X t)) + v (Sum.inr t) := by
  have h := DFunLike.congr_fun (nsTranslatePoint_comp_nsRefinementEquiv (I := I) φ v) (X t)
  rw [RingHom.comp_apply, eval₂Hom_X', nsRefinementEquiv_toRingHom_apply] at h
  exact h

end GraphModel

/-! ### The quotient groupoids of the normal sheaf -/

section NsQuotientGroupoid

open CategoryTheory ConeTranslation EmbeddingIndependence

variable {A : Type u} [CommRing A] {σ τ : Type u}

/-! #### The translation action on `B`-points -/

section Action

variable (I : Ideal (Amb A σ)) {B : Type u} [CommRing B]

/-- Translating a `B`-point of the normal sheaf by the zero section does nothing. -/
theorem nsTranslatePoint_zero (φ : Ns I →+* B) : nsTranslatePoint I φ 0 = φ := by
  refine ns_ringHom_ext I (fun r ↦ nsTranslatePoint_algebraMap φ 0 r) fun x ↦ ?_
  rw [nsTranslatePoint_nsClass, eval₂_taylor_zero, add_zero]

/-- Translating a `B`-point of the normal sheaf twice is translating by the sum. -/
theorem nsTranslatePoint_add (φ : Ns I →+* B) (v w : σ → B) :
    nsTranslatePoint I (nsTranslatePoint I φ v) w = nsTranslatePoint I φ (v + w) := by
  refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · rw [nsTranslatePoint_algebraMap, nsTranslatePoint_algebraMap, nsTranslatePoint_algebraMap]
  · have e : (nsTranslatePoint I φ v).comp (algebraMap (Amb A σ) (Ns I)) =
        φ.comp (algebraMap (Amb A σ) (Ns I)) :=
      RingHom.ext fun r ↦ nsTranslatePoint_algebraMap φ v r
    rw [nsTranslatePoint_nsClass, nsTranslatePoint_nsClass, nsTranslatePoint_nsClass, e,
      eval₂_taylor_add, add_assoc]

end Action

/-- The `B`-points of the quotient stack `[N_{U/M} / T_M|_U]` in the polynomial model: the
action groupoid of the translation action of the `B`-points `σ → B` of the tangent bundle on
the `B`-points of the affine normal sheaf. -/
@[ext]
structure NsGroupoid (I : Ideal (Amb A σ)) (B : Type u) [CommRing B] where
  /-- The underlying `B`-point of the affine normal sheaf. -/
  point : Ns I →+* B

namespace NsGroupoid

variable {I : Ideal (Amb A σ)} {B : Type u} [CommRing B]

/-- An arrow of the quotient groupoid: a `B`-point of the tangent bundle `T_M|_U = U × 𝔸^σ`
carrying the source to the target. -/
@[ext]
structure Hom (x y : NsGroupoid I B) where
  /-- The translating tangent vector. -/
  val : σ → B
  /-- It carries the source point to the target point. -/
  translate_eq : nsTranslatePoint I x.point val = y.point

/-- The action groupoid structure on the `B`-points of `[N_{U/M}/T_M|_U]`. -/
instance instCategory : Category (NsGroupoid I B) where
  Hom := Hom
  id x := ⟨0, nsTranslatePoint_zero I x.point⟩
  comp f g := ⟨f.val + g.val, by
    rw [← nsTranslatePoint_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

@[simp]
theorem id_val (x : NsGroupoid I B) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

@[simp]
theorem comp_val {x y z : NsGroupoid I B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Every arrow of the action groupoid is invertible. -/
instance instGroupoid : Groupoid (NsGroupoid I B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, nsTranslatePoint_add, add_neg_cancel, nsTranslatePoint_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

@[simp]
theorem eqToHom_val {x y : NsGroupoid I B} (h : x = y) : (eqToHom h).val = 0 := by
  subst h
  rfl

end NsGroupoid

/-- The functor `[N_{U/M'}/T_{M'}|_U](B) → [N_{U/M}/T_M|_U](B)` induced by the projection
`M' = 𝔸^{σ⊕τ} → M = 𝔸^σ`: on points it is the projection `N_{U/M} × 𝔸^τ → N_{U/M}` and on
arrows the projection `𝔸^{σ⊕τ} → 𝔸^σ` of tangent bundles. -/
def nsRefinementFunctor (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B] :
    NsGroupoid (graphIdeal A σ τ I 0) B ⥤ NsGroupoid I B where
  obj x := ⟨x.point.comp ((nsRefinementEquiv I).toRingHom.comp
    (C : Ns I →+* MvPolynomial τ (Ns I)))⟩
  map f := ⟨f.val ∘ Sum.inl, by
    rw [nsTranslatePoint_comp_nsRefinementEquiv_comp_C, f.translate_eq]⟩
  map_id x := NsGroupoid.Hom.ext rfl
  map_comp f g := NsGroupoid.Hom.ext rfl

@[simp]
theorem nsRefinementFunctor_obj_point (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u)
    [CommRing B] (x : NsGroupoid (graphIdeal A σ τ I 0) B) :
    ((nsRefinementFunctor I τ B).obj x).point =
      x.point.comp ((nsRefinementEquiv I).toRingHom.comp
        (C : Ns I →+* MvPolynomial τ (Ns I))) :=
  rfl

@[simp]
theorem nsRefinementFunctor_map_val (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B]
    {x y : NsGroupoid (graphIdeal A σ τ I 0) B} (f : x ⟶ y) :
    ((nsRefinementFunctor I τ B).map f).val = f.val ∘ Sum.inl :=
  rfl

set_option maxHeartbeats 1600000 in
-- As for `refinementQuotientEquivalence`, the unifier has to see through the composite
-- isomorphism `nsRefinementEquiv` and the quotient presentation of the symmetric algebra.
/-- **The refinement lemma for the normal sheaf in the polynomial model.**  For a refinement
`(U, M' = 𝔸^{σ⊕τ}) → (U, M = 𝔸^σ)` of local embeddings, given by the zero-section embedding,
the induced functor `[N_{U/M'}/T_{M'}|_U](B) → [N_{U/M}/T_M|_U](B)` is an equivalence of
groupoids for every test algebra `B`: the pair `N_{U/M} ⊆ T_M|_U` is the quotient of
`N_{U/M'} ⊆ T_{M'}|_U` by the relative tangent bundle `T_{M'/M}|_U = 𝔸^τ`. -/
theorem nsRefinementQuotientEquivalence (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u)
    [CommRing B] : (nsRefinementFunctor I τ B).IsEquivalence where
  faithful := ⟨fun {x y f g} hfg ↦ by
    have hval : f.val ∘ Sum.inl = g.val ∘ Sum.inl := congrArg NsGroupoid.Hom.val hfg
    refine NsGroupoid.Hom.ext (funext fun i ↦ ?_)
    cases i with
    | inl j => exact congrFun hval j
    | inr t =>
      have hf := congrArg (fun z ↦ z (nsRefinementEquiv I (X t))) f.translate_eq
      have hg := congrArg (fun z ↦ z (nsRefinementEquiv I (X t))) g.translate_eq
      simp only [nsTranslatePoint_nsRefinementEquiv_X] at hf hg
      exact add_left_cancel (hf.trans hg.symm)⟩
  full := ⟨fun {x y} k ↦ by
    refine ⟨⟨Sum.elim k.val fun t ↦ y.point (nsRefinementEquiv I (X t)) -
      x.point (nsRefinementEquiv I (X t)), ?_⟩, NsGroupoid.Hom.ext rfl⟩
    have hk := k.translate_eq
    refine RingHom.ext fun z ↦ ?_
    obtain ⟨w, rfl⟩ := (nsRefinementEquiv I).surjective z
    have hring : (nsTranslatePoint (graphIdeal A σ τ I 0) x.point
        (Sum.elim k.val fun t ↦ y.point (nsRefinementEquiv I (X t)) -
          x.point (nsRefinementEquiv I (X t)))).comp (nsRefinementEquiv I).toRingHom =
        y.point.comp (nsRefinementEquiv I).toRingHom := by
      rw [nsTranslatePoint_comp_nsRefinementEquiv]
      refine MvPolynomial.ringHom_ext (fun u ↦ ?_) fun t ↦ ?_
      · rw [eval₂Hom_C, RingHom.comp_apply, nsRefinementEquiv_toRingHom_apply]
        exact congrArg (fun z ↦ z u) hk
      · rw [eval₂Hom_X', RingHom.comp_apply, nsRefinementEquiv_toRingHom_apply, Sum.elim_inr]
        ring
    exact DFunLike.congr_fun hring w⟩
  essSurj := ⟨fun y ↦ by
    refine ⟨⟨(eval₂Hom y.point fun _ : τ ↦ (0 : B)).comp (nsRefinementEquiv I).symm.toRingHom⟩,
      ⟨eqToIso (NsGroupoid.ext ?_)⟩⟩
    rw [nsRefinementFunctor_obj_point, RingHom.comp_assoc]
    have hid : ((nsRefinementEquiv I).symm.toRingHom).comp
        ((nsRefinementEquiv I).toRingHom.comp (C : Ns I →+* MvPolynomial τ (Ns I))) =
        (C : Ns I →+* MvPolynomial τ (Ns I)) :=
      RingHom.ext fun w ↦ (nsRefinementEquiv I).symm_apply_apply (C w)
    rw [hid]
    exact RingHom.ext fun u ↦ eval₂Hom_C _ _ u⟩

/-! #### Compatibility with the closed immersion `C ⊆ N` -/

/-- The closed immersion `C_{U/M} ⊆ N_{U/M}` on the quotient groupoids of `B`-points: a
`B`-point of the normal cone is a `B`-point of the normal sheaf, equivariantly for the tangent
translation (`ConeTranslation.nsTranslatePoint_comp_nsToGr`, Vistoli's lemma). -/
def coneToNsFunctor (I : Ideal (Amb A σ)) (B : Type u) [CommRing B] :
    ConeGroupoid I B ⥤ NsGroupoid I B where
  obj x := ⟨x.point.comp (nsToGr (Amb A σ) I).toRingHom⟩
  map f := ⟨f.val, by rw [nsTranslatePoint_comp_nsToGr, f.translate_eq]⟩
  map_id x := NsGroupoid.Hom.ext rfl
  map_comp f g := NsGroupoid.Hom.ext rfl

/-- The two refinement functors, for the normal cone and for the normal sheaf, agree on the
`B`-points of the normal cone. -/
theorem nsRefinementFunctor_obj_coneToNs (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u)
    [CommRing B] (x : ConeGroupoid (graphIdeal A σ τ I 0) B) :
    (nsRefinementFunctor I τ B).obj ((coneToNsFunctor (graphIdeal A σ τ I 0) B).obj x) =
      (coneToNsFunctor I B).obj ((refinementFunctor I τ B).obj x) := by
  refine NsGroupoid.ext (RingHom.ext fun w ↦ ?_)
  exact congrArg x.point (DFunLike.congr_fun (nsToGr_comp_nsRefinementEquiv_comp_C (I := I)) w)

/-- **The refinement equivalences are compatible with the closed immersions `C ⊆ N`.**  The
square formed by the two refinement functors and the two closed immersions of quotient
groupoids commutes up to a canonical natural isomorphism. -/
def coneToNsRefinementIso (I : Ideal (Amb A σ)) (τ : Type u) (B : Type u) [CommRing B] :
    coneToNsFunctor (graphIdeal A σ τ I 0) B ⋙ nsRefinementFunctor I τ B ≅
      refinementFunctor I τ B ⋙ coneToNsFunctor I B :=
  NatIso.ofComponents (fun x ↦ eqToIso (nsRefinementFunctor_obj_coneToNs I τ B x))
    fun f ↦ NsGroupoid.Hom.ext (by
      simp only [NsGroupoid.comp_val, eqToIso.hom, NsGroupoid.eqToHom_val, add_zero, zero_add]
      rfl)

end NsQuotientGroupoid

/-! ### Independence of the presentation for the normal sheaf -/

section NsEmbeddingIndependence

open CategoryTheory ConeTranslation EmbeddingIndependence

variable {A : Type u} [CommRing A] {σ σ' σ'' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {I'' : Ideal (Amb A σ'')}
  {h : σ' → Amb A σ} {B : Type u} [CommRing B]

/-- The tangent vector of the second presentation induced by a tangent vector of the first at a
`B`-point of the normal sheaf: the transpose of the Jacobian of the lift. -/
def nsCompareVec (h : σ' → Amb A σ) (ψ : Ns I →+* B) (v : σ → B) : σ' → B :=
  fun t ↦ eval₂ (ψ.comp (algebraMap (Amb A σ) (Ns I))) v (taylor A σ (h t))

theorem nsCompareVec_zero (ψ : Ns I →+* B) : nsCompareVec h ψ (0 : σ → B) = 0 :=
  funext fun _ ↦ eval₂_taylor_zero _ _

theorem nsCompareVec_add (ψ : Ns I →+* B) (v w : σ → B) :
    nsCompareVec h ψ (v + w) = nsCompareVec h ψ v + nsCompareVec h ψ w :=
  funext fun _ ↦ eval₂_taylor_add _ _ _ _

theorem nsCompareVec_congr {ψ ψ' : Ns I →+* B}
    (hψ : ψ.comp (algebraMap (Amb A σ) (Ns I)) = ψ'.comp (algebraMap (Amb A σ) (Ns I)))
    (v : σ → B) : nsCompareVec h ψ v = nsCompareVec h ψ' v := by
  refine funext fun t ↦ ?_
  rw [nsCompareVec, nsCompareVec, hψ]

theorem nsCompareVec_id (ψ : Ns I →+* B) (v : σ → B) :
    nsCompareVec (X : σ → Amb A σ) ψ v = v :=
  funext fun i ↦ by rw [nsCompareVec, taylor_X, eval₂_X]

theorem nsCompareVec_comp (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (ψ : Ns I →+* B) (v : σ → B) :
    nsCompareVec (fun t ↦ liftHom h (k t)) ψ v =
      nsCompareVec k (ψ.comp (nsPresMap I I' h hmap)) (nsCompareVec h ψ v) := by
  have hcomp : (ψ.comp (nsPresMap I I' h hmap)).comp (algebraMap (Amb A σ') (Ns I')) =
      (ψ.comp (algebraMap (Amb A σ) (Ns I))).comp (liftHom h) :=
    RingHom.ext fun r ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, nsPresMap_algebraMap, RingHom.comp_apply,
        RingHom.comp_apply]
  refine funext fun t ↦ ?_
  rw [nsCompareVec, nsCompareVec, hcomp, eval₂_taylor_liftHom]
  rfl

/-- The equivariance of `nsPresMap`, in terms of `nsCompareVec`. -/
theorem nsTranslatePoint_comp_nsPresMap_eq (hmap : Ideal.map (liftHom h) I' ≤ I)
    (ψ : Ns I →+* B) (v : σ → B) :
    (nsTranslatePoint I ψ v).comp (nsPresMap I I' h hmap) =
      nsTranslatePoint I' (ψ.comp (nsPresMap I I' h hmap)) (nsCompareVec h ψ v) :=
  nsTranslatePoint_comp_nsPresMap hmap ψ v

variable (I I')

/-- **The comparison functor for normal sheaves.**  A lift `h` of the presentation
`A[x_{σ'}] ↠ S` into `A[x_σ] ↠ S` induces a functor
`[N_{U/M}/T_M|_U](B) ⥤ [N_{U/M'}/T_{M'}|_U](B)` between the quotient groupoids of the two
presentations. -/
def nsCompareFunctor (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] : NsGroupoid I B ⥤ NsGroupoid I' B where
  obj x := ⟨x.point.comp (nsPresMap I I' h hmap)⟩
  map {x _} f := ⟨nsCompareVec h x.point f.val, by
    rw [← nsTranslatePoint_comp_nsPresMap_eq hmap, f.translate_eq]⟩
  map_id x := NsGroupoid.Hom.ext (nsCompareVec_zero x.point)
  map_comp {x y _} f g := NsGroupoid.Hom.ext (by
    have hψ : y.point.comp (algebraMap (Amb A σ) (Ns I)) =
        x.point.comp (algebraMap (Amb A σ) (Ns I)) := by
      rw [← f.translate_eq]
      exact RingHom.ext fun r ↦ nsTranslatePoint_algebraMap x.point f.val r
    change nsCompareVec h x.point (f.val + g.val) =
      nsCompareVec h x.point f.val + nsCompareVec h y.point g.val
    rw [nsCompareVec_add, nsCompareVec_congr hψ])

@[simp]
theorem nsCompareFunctor_obj_point (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] (x : NsGroupoid I B) :
    ((nsCompareFunctor I I' h hmap B).obj x).point = x.point.comp (nsPresMap I I' h hmap) :=
  rfl

@[simp]
theorem nsCompareFunctor_map_val (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] {x y : NsGroupoid I B} (f : x ⟶ y) :
    ((nsCompareFunctor I I' h hmap B).map f).val = nsCompareVec h x.point f.val :=
  rfl

variable {I I'}

/-! #### Functoriality -/

theorem nsPresMap_id (hmap : Ideal.map (liftHom (X : σ → Amb A σ)) I ≤ I) :
    nsPresMap I I (X : σ → Amb A σ) hmap = RingHom.id (Ns I) := by
  refine ns_ringHom_ext I (fun r ↦ ?_) fun x ↦ ?_
  · rw [nsPresMap_algebraMap, liftHom_id]
    rfl
  · rw [nsPresMap_nsClass]
    refine congrArg _ (Subtype.ext ?_)
    change liftHom (X : σ → Amb A σ) (x : Amb A σ) = (x : Amb A σ)
    rw [liftHom_id]
    rfl

theorem nsPresMap_comp (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I'' ≤ I')
    (hmap'' : Ideal.map (liftHom fun t ↦ liftHom h (k t)) I'' ≤ I) :
    (nsPresMap I I' h hmap).comp (nsPresMap I' I'' k hmap') =
      nsPresMap I I'' (fun t ↦ liftHom h (k t)) hmap'' := by
  refine ns_ringHom_ext I'' (fun r ↦ ?_) fun x ↦ ?_
  · change nsPresMap I I' h hmap (nsPresMap I' I'' k hmap'
      (algebraMap (Amb A σ'') (Ns I'') r)) = _
    rw [nsPresMap_algebraMap, nsPresMap_algebraMap, nsPresMap_algebraMap, liftHom_comp]
    rfl
  · change nsPresMap I I' h hmap (nsPresMap I' I'' k hmap' (nsClass I'' x)) = _
    rw [nsPresMap_nsClass, nsPresMap_nsClass, nsPresMap_nsClass]
    refine congrArg _ (Subtype.ext ?_)
    change liftHom h (liftHom k (x : Amb A σ'')) =
      liftHom (fun t ↦ liftHom h (k t)) (x : Amb A σ'')
    rw [liftHom_comp]
    rfl

/-- The comparison functor of the identity lift is (canonically isomorphic to) the identity
functor. -/
def nsCompareFunctorIdIso (hmap : Ideal.map (liftHom (X : σ → Amb A σ)) I ≤ I)
    (B : Type u) [CommRing B] :
    nsCompareFunctor I I (X : σ → Amb A σ) hmap B ≅ 𝟭 (NsGroupoid I B) :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm ⟨0, by
      rw [nsTranslatePoint_zero]
      change x.point.comp (nsPresMap I I (X : σ → Amb A σ) hmap) = x.point
      rw [nsPresMap_id, RingHom.comp_id]⟩)
    fun {x _} f ↦ NsGroupoid.Hom.ext (by
      change nsCompareVec (X : σ → Amb A σ) x.point f.val + 0 = 0 + f.val
      rw [nsCompareVec_id, add_zero, zero_add])

/-- **The cocycle identity for normal sheaves.**  The composite of the comparison functors
attached to two lifts is canonically isomorphic to the comparison functor attached to the
composite lift. -/
def nsCompareFunctorCompIso (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I'' ≤ I')
    (hmap'' : Ideal.map (liftHom fun t ↦ liftHom h (k t)) I'' ≤ I)
    (B : Type u) [CommRing B] :
    nsCompareFunctor I I' h hmap B ⋙ nsCompareFunctor I' I'' k hmap' B ≅
      nsCompareFunctor I I'' (fun t ↦ liftHom h (k t)) hmap'' B :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm ⟨0, by
      rw [nsTranslatePoint_zero]
      change (x.point.comp (nsPresMap I I' h hmap)).comp (nsPresMap I' I'' k hmap') =
        x.point.comp (nsPresMap I I'' (fun t ↦ liftHom h (k t)) hmap'')
      rw [RingHom.comp_assoc, nsPresMap_comp h k hmap hmap' hmap'']⟩)
    fun {x _} f ↦ NsGroupoid.Hom.ext (by
      change nsCompareVec k (x.point.comp (nsPresMap I I' h hmap))
          (nsCompareVec h x.point f.val) + 0 =
        0 + nsCompareVec (fun t ↦ liftHom h (k t)) x.point f.val
      rw [nsCompareVec_comp h k hmap, add_zero, zero_add])

/-! #### Independence of the chosen lift -/

variable {h' : σ' → Amb A σ}

/-- **The difference of two lifts, in degree one, on the normal sheaf.**  The degree-one class
of `h'(f) - h(f)` at a `B`-point of the normal sheaf is computed by the Taylor derivation from
the degree-one classes of the differences `h' t - h t` of the lifts. -/
theorem point_nsClass_sub (hI : ∀ t, h' t - h t ∈ I) (ψ : Ns I →+* B) (f : Amb A σ')
    (hf : liftHom h' f - liftHom h f ∈ I) :
    ψ (nsClass I ⟨liftHom h' f - liftHom h f, hf⟩) =
      eval₂ ((ψ.comp (algebraMap (Amb A σ) (Ns I))).comp (liftHom h))
        (fun t ↦ ψ (nsClass I ⟨h' t - h t, hI t⟩)) (taylor A σ' f) := by
  revert hf
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro hf
    have hz : (⟨liftHom h' (C a) - liftHom h (C a), hf⟩ : I) = 0 := by
      apply Subtype.ext
      change liftHom h' (C a) - liftHom h (C a) = 0
      rw [liftHom_C, liftHom_C, sub_self]
    rw [hz, map_zero, map_zero, taylor_C, eval₂_zero]
  | add f g ihf ihg =>
    intro hfg
    have hf' : liftHom h' f - liftHom h f ∈ I := liftHom_sub_mem hI f
    have hg' : liftHom h' g - liftHom h g ∈ I := liftHom_sub_mem hI g
    have hsum : (⟨liftHom h' (f + g) - liftHom h (f + g), hfg⟩ : I) =
        (⟨liftHom h' f - liftHom h f, hf'⟩ : I) + ⟨liftHom h' g - liftHom h g, hg'⟩ := by
      apply Subtype.ext
      change liftHom h' (f + g) - liftHom h (f + g) =
        (liftHom h' f - liftHom h f) + (liftHom h' g - liftHom h g)
      rw [map_add, map_add]
      ring
    rw [hsum, map_add, map_add, ihf hf', ihg hg', map_add, eval₂_add]
  | mul_X f t ih =>
    intro hfX
    have hD : liftHom h' f - liftHom h f ∈ I := liftHom_sub_mem hI f
    have hkey : (⟨liftHom h' (f * X t) - liftHom h (f * X t), hfX⟩ : I) =
        liftHom h' f • (⟨h' t - h t, hI t⟩ : I) +
          h t • (⟨liftHom h' f - liftHom h f, hD⟩ : I) := by
      apply Subtype.ext
      change liftHom h' (f * X t) - liftHom h (f * X t) =
        liftHom h' f * (h' t - h t) + h t * (liftHom h' f - liftHom h f)
      rw [map_mul, map_mul, liftHom_X, liftHom_X]
      ring
    have hzero : ψ (algebraMap (Amb A σ) (Ns I) (liftHom h' f)) =
        ψ (algebraMap (Amb A σ) (Ns I) (liftHom h f)) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub, ConeRefinement.algebraMap_ns_eq_zero I hD,
        map_zero]
    rw [hkey, map_add, nsClass_smul, nsClass_smul, map_add, map_mul, map_mul, ih hD, hzero,
      taylor_mul, taylor_X, eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_X]
    simp only [RingHom.comp_apply, liftHom_X]

/-- The canonical tangent vector comparing two lifts at a `B`-point of the normal sheaf. -/
def nsLiftHomotopy (hI : ∀ t, h' t - h t ∈ I) (ψ : Ns I →+* B) : σ' → B :=
  fun t ↦ ψ (nsClass I ⟨h' t - h t, hI t⟩)

/-- The canonical tangent vector translates the point attached to one lift into the point
attached to the other. -/
theorem nsTranslatePoint_nsLiftHomotopy (hI : ∀ t, h' t - h t ∈ I)
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom h') I' ≤ I)
    (ψ : Ns I →+* B) :
    nsTranslatePoint I' (ψ.comp (nsPresMap I I' h hmap)) (nsLiftHomotopy hI ψ) =
      ψ.comp (nsPresMap I I' h' hmap') := by
  have hcomp : (ψ.comp (nsPresMap I I' h hmap)).comp (algebraMap (Amb A σ') (Ns I')) =
      (ψ.comp (algebraMap (Amb A σ) (Ns I))).comp (liftHom h) :=
    RingHom.ext fun r ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, nsPresMap_algebraMap, RingHom.comp_apply,
        RingHom.comp_apply]
  refine ns_ringHom_ext I' (fun r ↦ ?_) fun x ↦ ?_
  · have hmem : liftHom h r - liftHom h' r ∈ I := by
      have hneg := neg_mem (liftHom_sub_mem hI r)
      rwa [neg_sub] at hneg
    rw [nsTranslatePoint_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
      nsPresMap_algebraMap, nsPresMap_algebraMap, ← sub_eq_zero, ← map_sub, ← map_sub,
      ConeRefinement.algebraMap_ns_eq_zero I hmem, map_zero]
  · rw [nsTranslatePoint_nsClass, RingHom.comp_apply, nsPresMap_nsClass, RingHom.comp_apply,
      nsPresMap_nsClass, hcomp]
    have hlh : nsLiftHomotopy hI ψ = fun t ↦ ψ (nsClass I ⟨h' t - h t, hI t⟩) := rfl
    rw [hlh, ← point_nsClass_sub hI ψ (x : Amb A σ') (liftHom_sub_mem hI (x : Amb A σ')),
      ← map_add, ← map_add]
    refine congrArg _ (congrArg _ (Subtype.ext ?_))
    change liftHom h (x : Amb A σ') + (liftHom h' (x : Amb A σ') - liftHom h (x : Amb A σ')) =
      liftHom h' (x : Amb A σ')
    ring

/-- **Canonicity of the comparison on normal sheaves.**  Two lifts of the same presentation
induce canonically isomorphic comparison functors. -/
def nsLiftIso (hI : ∀ t, h' t - h t ∈ I) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (hmap' : Ideal.map (liftHom h') I' ≤ I) (B : Type u) [CommRing B] :
    nsCompareFunctor I I' h hmap B ≅ nsCompareFunctor I I' h' hmap' B :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm
      ⟨nsLiftHomotopy hI x.point, nsTranslatePoint_nsLiftHomotopy hI hmap hmap' x.point⟩)
    fun {x y} f ↦ NsGroupoid.Hom.ext (by
      change nsCompareVec h x.point f.val + nsLiftHomotopy hI y.point =
        nsLiftHomotopy hI x.point + nsCompareVec h' x.point f.val
      refine funext fun t ↦ ?_
      have hy : y.point = nsTranslatePoint I x.point f.val := f.translate_eq.symm
      have hstep : nsLiftHomotopy hI y.point t =
          nsLiftHomotopy hI x.point t +
            eval₂ (x.point.comp (algebraMap (Amb A σ) (Ns I))) f.val
              (taylor A σ (h' t - h t)) := by
        rw [nsLiftHomotopy, hy, nsTranslatePoint_nsClass]
        rfl
      change nsCompareVec h x.point f.val t + nsLiftHomotopy hI y.point t =
        nsLiftHomotopy hI x.point t + nsCompareVec h' x.point f.val t
      rw [hstep, nsCompareVec, nsCompareVec, map_sub, eval₂_sub]
      ring)

/-! #### The comparison is an equivalence of groupoids -/

/-- **Two presentations related by mutually inverse lifts have equivalent quotient groupoids of
normal sheaves.**  This is the normal-sheaf half of the affine Layer-5 gate statement. -/
def nsCompareEquivalence (h : σ' → Amb A σ) (k : σ → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I ≤ I')
    (hhk : ∀ i, liftHom h (k i) - X i ∈ I) (hkh : ∀ t, liftHom k (h t) - X t ∈ I')
    (B : Type u) [CommRing B] : NsGroupoid I B ≌ NsGroupoid I' B := by
  refine CategoryTheory.Equivalence.mk (nsCompareFunctor I I' h hmap B)
    (nsCompareFunctor I' I k hmap' B) ?_ ?_
  · refine (nsCompareFunctorIdIso (map_liftHom_X_le I) B).symm ≪≫ ?_
    refine nsLiftIso (h := (X : σ → Amb A σ)) (h' := fun i ↦ liftHom h (k i)) hhk
      (map_liftHom_X_le I) (map_liftHom_comp_le hmap hmap') B ≪≫ ?_
    exact (nsCompareFunctorCompIso h k hmap hmap' (map_liftHom_comp_le hmap hmap') B).symm
  · refine nsCompareFunctorCompIso k h hmap' hmap (map_liftHom_comp_le hmap' hmap) B ≪≫ ?_
    refine nsLiftIso (h := fun t ↦ liftHom k (h t)) (h' := (X : σ' → Amb A σ'))
      (fun t ↦ ?_) (map_liftHom_comp_le hmap' hmap) (map_liftHom_X_le I') B ≪≫
        nsCompareFunctorIdIso (map_liftHom_X_le I') B
    have hneg := neg_mem (hkh t)
    rwa [neg_sub] at hneg

end NsEmbeddingIndependence

/-! ### Two presentations of the same algebra -/

section NsPresentations

open CategoryTheory ConeTranslation EmbeddingIndependence

variable {A : Type u} [CommRing A] {σ σ' σ'' : Type u} {S : Type u} [CommRing S] [Algebra A S]
  {π : Amb A σ →ₐ[A] S} {π' : Amb A σ' →ₐ[A] S} {π'' : Amb A σ'' →ₐ[A] S}

/-- **Independence of the local embedding for the normal sheaf.**  Two presentations of the same
algebra have equivalent quotient groupoids `[N_{U/M}/T_M|_U](B)`, via any pair of lifts. -/
def nsPresentationEquivalence {h : σ' → Amb A σ} {k : σ → Amb A σ'}
    (hh : ∀ t, π (h t) = π' (X t)) (hk : ∀ i, π' (k i) = π (X i))
    (B : Type u) [CommRing B] :
    NsGroupoid (presIdeal π) B ≌ NsGroupoid (presIdeal π') B :=
  nsCompareEquivalence h k (map_liftHom_presIdeal_le hh) (map_liftHom_presIdeal_le hk)
    (liftHom_comp_sub_X_mem hh hk) (liftHom_comp_sub_X_mem hk hh) B

/-- **Canonicity.**  Two choices of lifts give canonically isomorphic comparison functors of
normal-sheaf groupoids. -/
def nsPresentationLiftIso {h h' : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t))
    (hh' : ∀ t, π (h' t) = π' (X t)) (B : Type u) [CommRing B] :
    nsCompareFunctor (presIdeal π) (presIdeal π') h (map_liftHom_presIdeal_le hh) B ≅
      nsCompareFunctor (presIdeal π) (presIdeal π') h' (map_liftHom_presIdeal_le hh') B :=
  nsLiftIso (lift_sub_mem_presIdeal hh hh') _ _ B

/-- **The cocycle condition for normal sheaves.**  For three presentations the comparison
functors compose, up to the canonical isomorphism of Behrend–Fantechi's gluing datum. -/
def nsCocycleIso {h : σ' → Amb A σ} {k : σ'' → Amb A σ'} {l : σ'' → Amb A σ}
    (hh : ∀ t, π (h t) = π' (X t)) (hk : ∀ t, π' (k t) = π'' (X t))
    (hl : ∀ t, π (l t) = π'' (X t)) (B : Type u) [CommRing B] :
    nsCompareFunctor (presIdeal π) (presIdeal π') h (map_liftHom_presIdeal_le hh) B ⋙
        nsCompareFunctor (presIdeal π') (presIdeal π'') k (map_liftHom_presIdeal_le hk) B ≅
      nsCompareFunctor (presIdeal π) (presIdeal π'') l (map_liftHom_presIdeal_le hl) B := by
  have hcomp : ∀ t, π (liftHom h (k t)) = π'' (X t) := fun t ↦ by
    rw [liftHom_apply_eq hh, hk]
  refine nsCompareFunctorCompIso h k (map_liftHom_presIdeal_le hh)
    (map_liftHom_presIdeal_le hk) (map_liftHom_presIdeal_le hcomp) B ≪≫ ?_
  exact nsLiftIso (lift_sub_mem_presIdeal hcomp hl) _ _ B

/-- The comparison functor of the identity presentation and the identity lift is the identity. -/
def nsPresentationIdIso (π : Amb A σ →ₐ[A] S) (B : Type u) [CommRing B] :
    nsCompareFunctor (presIdeal π) (presIdeal π) (X : σ → Amb A σ)
        (map_liftHom_presIdeal_le (π := π) (π' := π) fun _ ↦ rfl) B ≅
      𝟭 (NsGroupoid (presIdeal π) B) :=
  nsCompareFunctorIdIso _ B

end NsPresentations

end

end ConeRefinement

end GromovWitten.AlgebraicGeometry
