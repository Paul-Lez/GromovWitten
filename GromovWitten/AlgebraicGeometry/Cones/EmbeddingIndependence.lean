/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.RefinementQuotient

/-!
# Independence of the local embedding (polynomial model)

Behrend–Fantechi's intrinsic normal cone is glued from the local presentations
`[C_{U/M}/T_M|_U]` attached to closed embeddings of `U` into smooth schemes.  For that gluing to
make sense the presentation must not depend on the embedding, canonically and compatibly with
composition.  This file proves that in the affine polynomial model of
`Cones/ConeTranslation.lean` and `Cones/RefinementQuotient.lean`: for two presentations
`π : A[x_σ] ↠ S` and `π' : A[x_{σ'}] ↠ S` of the same `A`-algebra `S = Γ(U)`, with ideals
`I = ker π` and `I' = ker π'`, the quotient groupoids `ConeGroupoid I B` and `ConeGroupoid I' B`
are equivalent for every test algebra `B`, canonically and cocyclically.

## The comparison functor

Instead of going through the common refinement, the comparison is constructed directly from a
*lift* `h : σ' → A[x_σ]` of the generators of the second presentation (`π (h t) = π' (X t)`).
Such a lift induces `liftHom h : A[x_{σ'}] →+* A[x_σ]` carrying `I'` into `I`, hence a map
`presMap : gr_{I'} → gr_I` of the coordinate rings of the normal cones, and therefore a map of
`B`-points in the opposite direction.  On tangent vectors the comparison is the transpose of the
Jacobian of the lift, `compareVec h φ v t = Σ_i v_i ∂_i h_t` (`compareVec`), and the fact that
this is compatible with the tangent translation action of `Cones/ConeTranslation.lean`
(`translatePoint_comp_presMap`) is exactly the **chain rule** `taylor_liftHom` for the Taylor
derivation.  The resulting functor is `compareFunctor`.

## Canonicity, the cocycle condition and the equivalence

* `compareFunctorIdIso`: the identity lift induces the identity functor.
* `compareFunctorCompIso`: the comparison functors compose, the composite of the comparisons of
  two lifts being the comparison of the composite lift (`presMap_comp`, `compareVec_comp`).
* `liftIso`: **canonicity**.  Two lifts `h, h'` of the same presentation differ by elements of
  `I`, and the two comparison functors are canonically isomorphic; the isomorphism is the
  translation by the degree-one classes `[h' t - h t]`, which translates the point attached to
  one lift into the point attached to the other (`translatePoint_liftHomotopy`).  The
  computation behind it is `point_degreeOneRaw_sub`: the degree-one class of `h'(f) - h(f)` is
  obtained from those of `h' t - h t` by the Taylor derivation.
* `compareEquivalence` and `presentationEquivalence`: two presentations with lifts in both
  directions have equivalent quotient groupoids — the affine Layer-5 gate statement.
* `cocycleIso`: for three presentations, the composite of the comparisons of `π, π'` and of
  `π', π''` is canonically isomorphic to the comparison of `π, π''`, which is the cocycle
  condition for gluing the intrinsic normal cone.
* `ker_jointPres` records the link with `Cones/RefinementQuotient.lean`: the joint presentation
  `A[x_σ, x_{σ'}] ↠ S` is the graph embedding of the lift, so the common refinement of the two
  embeddings is the one whose quotient groupoid is computed there.

## The normal sheaf

`nsPresMap` is the corresponding map `N_{U/M'} → N_{U/M}` of normal-sheaf rings,
`nsToGr_comp_nsPresMap` and `point_comp_nsToGr` say that the comparison commutes with the closed
immersions `C ⊆ N`, and `nsTranslatePoint_comp_nsPresMap` that it is equivariant for the tangent
translation on the normal sheaf.  What is *not* proved here is the sheaf-level analogue of
`ConeRefinement.prodMap_injective` (the product formula for normal sheaves), which is still open
in `Cones/RefinementQuotient.lean`, and everything beyond the affine polynomial model: a general
smooth ambient space, non-affine bases, and the fppf stackification.
-/

namespace GromovWitten.AlgebraicGeometry

namespace EmbeddingIndependence

universe u

noncomputable section

open CategoryTheory AffineNormalCone MvPolynomial ConeTranslation ConeRefinement

/-! ### Lifts and the chain rule for the Taylor derivation -/

section ChainRule

variable {A : Type u} [CommRing A] {σ σ' : Type u}

/-- The `A`-algebra map `A[x_{σ'}] → A[x_σ]` determined by a family of lifts `h`. -/
def liftHom (h : σ' → Amb A σ) : Amb A σ' →+* Amb A σ :=
  (MvPolynomial.aeval h).toRingHom

@[simp]
theorem liftHom_X (h : σ' → Amb A σ) (t : σ') : liftHom h (X t) = h t :=
  aeval_X _ _

@[simp]
theorem liftHom_C (h : σ' → Amb A σ) (a : A) : liftHom h (C a) = C a := by
  change MvPolynomial.aeval h (C a) = C a
  rw [aeval_C, algebraMap_eq]

theorem liftHom_id : liftHom (X : σ → Amb A σ) = RingHom.id (Amb A σ) :=
  MvPolynomial.ringHom_ext (fun a ↦ by rw [liftHom_C, RingHom.id_apply])
    fun i ↦ by rw [liftHom_X, RingHom.id_apply]

theorem liftHom_comp {σ'' : Type u} (h : σ' → Amb A σ) (k : σ'' → Amb A σ') :
    liftHom (fun t ↦ liftHom h (k t)) = (liftHom h).comp (liftHom k) :=
  MvPolynomial.ringHom_ext (fun a ↦ by simp) fun t ↦ by simp

/-- **The chain rule** for the Taylor derivation: the derivative of a substitution is the
substitution of the derivatives. -/
theorem taylor_liftHom (h : σ' → Amb A σ) (f : Amb A σ') :
    taylor A σ (liftHom h f) =
      eval₂ ((MvPolynomial.C : Amb A σ →+* Ext A σ).comp (liftHom h))
        (fun t ↦ taylor A σ (h t)) (taylor A σ' f) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [liftHom_C, taylor_C, taylor_C, eval₂_zero]
  | add f g hf hg => rw [map_add, map_add, map_add, eval₂_add, hf, hg]
  | mul_X f t hf =>
    rw [map_mul, liftHom_X, taylor_mul, taylor_mul, taylor_X, eval₂_add, eval₂_mul,
      eval₂_mul, eval₂_C, eval₂_C, eval₂_X, hf, RingHom.comp_apply, RingHom.comp_apply,
      liftHom_X]

/-- The chain rule on `B`-points. -/
theorem eval₂_taylor_liftHom {B : Type u} [CommSemiring B] (ψ : Amb A σ →+* B) (v : σ → B)
    (h : σ' → Amb A σ) (f : Amb A σ') :
    eval₂ ψ v (taylor A σ (liftHom h f)) =
      eval₂ (ψ.comp (liftHom h)) (fun t ↦ eval₂ ψ v (taylor A σ (h t))) (taylor A σ' f) := by
  have hcomp : (eval₂Hom ψ v).comp ((MvPolynomial.C : Amb A σ →+* Ext A σ).comp (liftHom h)) =
      ψ.comp (liftHom h) := by
    rw [← RingHom.comp_assoc]
    congr 1
    exact RingHom.ext fun p ↦ eval₂Hom_C ψ v p
  rw [taylor_liftHom]
  change eval₂Hom ψ v (eval₂ _ _ _) = _
  rw [eval₂_comp_left (eval₂Hom ψ v), hcomp]
  rfl

/-- Two lifts of the same family differ by the ideal generated by their differences. -/
theorem liftHom_sub_mem_span (h h' : σ' → Amb A σ) (f : Amb A σ') :
    liftHom h' f - liftHom h f ∈ Ideal.span (Set.range fun t ↦ h' t - h t) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [liftHom_C, liftHom_C, sub_self]
    exact Ideal.zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, show liftHom h' f + liftHom h' g - (liftHom h f + liftHom h g) =
      (liftHom h' f - liftHom h f) + (liftHom h' g - liftHom h g) by ring]
    exact Ideal.add_mem _ hf hg
  | mul_X f t hf =>
    rw [map_mul, map_mul, liftHom_X, liftHom_X,
      show liftHom h' f * h' t - liftHom h f * h t =
        liftHom h' f * (h' t - h t) + (liftHom h' f - liftHom h f) * h t by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨t, rfl⟩))
      (Ideal.mul_mem_right _ _ hf)

theorem liftHom_sub_mem {I : Ideal (Amb A σ)} {h h' : σ' → Amb A σ}
    (hI : ∀ t, h' t - h t ∈ I) (f : Amb A σ') : liftHom h' f - liftHom h f ∈ I := by
  refine Ideal.span_le.mpr ?_ (liftHom_sub_mem_span h h' f)
  rintro _ ⟨t, rfl⟩
  exact hI t

end ChainRule

/-! ### The comparison functor attached to a lift -/

section Compare

variable {A : Type u} [CommRing A] {σ σ' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {h : σ' → Amb A σ}

/-- The map of associated graded rings `gr_{I'} → gr_I` induced by a lift `h` of the second
presentation into the first. -/
def presMap (I : Ideal (Amb A σ)) (I' : Ideal (Amb A σ')) (h : σ' → Amb A σ)
    (hmap : Ideal.map (liftHom h) I' ≤ I) : Gr I' →+* Gr I :=
  grMapOfLe I' I (liftHom h) hmap

theorem presMap_algebraMap (hmap : Ideal.map (liftHom h) I' ≤ I) (r : Amb A σ') :
    presMap I I' h hmap (algebraMap (Amb A σ') (Gr I') r) =
      algebraMap (Amb A σ) (Gr I) (liftHom h r) :=
  grMapOfLe_algebraMap I' I (liftHom h) hmap r

theorem presMap_degreeOneRaw (hmap : Ideal.map (liftHom h) I' ≤ I) (x : I') :
    presMap I I' h hmap (degreeOneRaw (Amb A σ') I' x) =
      degreeOneRaw (Amb A σ) I
        ⟨liftHom h (x : Amb A σ'), hmap (Ideal.mem_map_of_mem _ x.2)⟩ := by
  rw [degreeOneRaw_eq_mk, presMap, grMapOfLe_degreeOneRees, degreeOneRaw_eq_mk]

/-- The tangent vector of the second presentation induced by a tangent vector of the first at a
given point: the transpose of the Jacobian of the lift. -/
def compareVec (h : σ' → Amb A σ) {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B) :
    σ' → B :=
  fun t ↦ eval₂ (φ.comp (algebraMap (Amb A σ) (Gr I))) v (taylor A σ (h t))

variable {B : Type u} [CommRing B]

theorem compareVec_zero (φ : Gr I →+* B) : compareVec h φ (0 : σ → B) = 0 :=
  funext fun _ ↦ eval₂_taylor_zero _ _

theorem compareVec_add (φ : Gr I →+* B) (v w : σ → B) :
    compareVec h φ (v + w) = compareVec h φ v + compareVec h φ w :=
  funext fun _ ↦ eval₂_taylor_add _ _ _ _

theorem compareVec_congr {φ φ' : Gr I →+* B}
    (hψ : φ.comp (algebraMap (Amb A σ) (Gr I)) = φ'.comp (algebraMap (Amb A σ) (Gr I)))
    (v : σ → B) : compareVec h φ v = compareVec h φ' v := by
  refine funext fun t ↦ ?_
  rw [compareVec, compareVec, hψ]

/-- **Functoriality of the comparison on points.**  Translating a point of `C_{U/M}` and then
restricting it along the lift is the same as restricting it and translating by the Jacobian
image of the tangent vector. -/
theorem translatePoint_comp_presMap (hmap : Ideal.map (liftHom h) I' ≤ I)
    (φ : Gr I →+* B) (v : σ → B) :
    (translatePoint I φ v).comp (presMap I I' h hmap) =
      translatePoint I' (φ.comp (presMap I I' h hmap)) (compareVec h φ v) := by
  refine ConeTranslation.gr_ringHom_ext I' (fun r ↦ ?_) fun x ↦ ?_
  · rw [RingHom.comp_apply, presMap_algebraMap, translatePoint_algebraMap,
      translatePoint_algebraMap, RingHom.comp_apply, presMap_algebraMap]
  · have hcomp : (φ.comp (presMap I I' h hmap)).comp (algebraMap (Amb A σ') (Gr I')) =
        (φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h) :=
      RingHom.ext fun r ↦ by
        rw [RingHom.comp_apply, RingHom.comp_apply, presMap_algebraMap, RingHom.comp_apply,
          RingHom.comp_apply]
    rw [RingHom.comp_apply, ← degreeOneRaw_eq_mk, presMap_degreeOneRaw,
      translatePoint_degreeOneRaw, translatePoint_degreeOneRaw, eval₂_taylor_liftHom, hcomp,
      RingHom.comp_apply, presMap_degreeOneRaw]
    rfl

variable (I I')

/-- **The comparison functor.**  A lift `h` of the presentation `A[x_{σ'}] ↠ S` into
`A[x_σ] ↠ S` induces a functor `[C_{U/M}/T_M|_U](B) ⥤ [C_{U/M'}/T_{M'}|_U](B)` between the
quotient groupoids of the two presentations. -/
def compareFunctor (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] : ConeGroupoid I B ⥤ ConeGroupoid I' B where
  obj x := ⟨x.point.comp (presMap I I' h hmap)⟩
  map {x _} f := ⟨compareVec h x.point f.val, by
    rw [← translatePoint_comp_presMap hmap, f.translate_eq]⟩
  map_id x := ConeGroupoid.Hom.ext (compareVec_zero x.point)
  map_comp {x y _} f g := ConeGroupoid.Hom.ext (by
    have hψ : y.point.comp (algebraMap (Amb A σ) (Gr I)) =
        x.point.comp (algebraMap (Amb A σ) (Gr I)) := by
      rw [← f.translate_eq]
      exact RingHom.ext fun r ↦ translatePoint_algebraMap I x.point f.val r
    change compareVec h x.point (f.val + g.val) =
      compareVec h x.point f.val + compareVec h y.point g.val
    rw [compareVec_add, compareVec_congr hψ])

@[simp]
theorem compareFunctor_obj_point (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] (x : ConeGroupoid I B) :
    ((compareFunctor I I' h hmap B).obj x).point = x.point.comp (presMap I I' h hmap) :=
  rfl

@[simp]
theorem compareFunctor_map_val (h : σ' → Amb A σ) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (B : Type u) [CommRing B] {x y : ConeGroupoid I B} (f : x ⟶ y) :
    ((compareFunctor I I' h hmap B).map f).val = compareVec h x.point f.val :=
  rfl

end Compare

/-! ### Functoriality of the comparison -/

section Functoriality

variable {A : Type u} [CommRing A] {σ σ' σ'' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {I'' : Ideal (Amb A σ'')}

theorem grMapOfLe_id (J : Ideal (Amb A σ)) (hJ : Ideal.map (RingHom.id (Amb A σ)) J ≤ J) :
    grMapOfLe J J (RingHom.id (Amb A σ)) hJ = RingHom.id (Gr J) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  change Ideal.Quotient.mk _ (reesMapOfLe J J (RingHom.id (Amb A σ)) hJ p) =
    Ideal.Quotient.mk _ p
  refine congrArg _ (Subtype.ext ?_)
  rw [reesMapOfLe_coe, Polynomial.map_id]

theorem grMapOfLe_comp {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {J₃ : Ideal R₃} (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (h₁ : Ideal.map f J₁ ≤ J₂) (h₂ : Ideal.map g J₂ ≤ J₃)
    (h₃ : Ideal.map (g.comp f) J₁ ≤ J₃) :
    (grMapOfLe J₂ J₃ g h₂).comp (grMapOfLe J₁ J₂ f h₁) = grMapOfLe J₁ J₃ (g.comp f) h₃ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
  change Ideal.Quotient.mk _ (reesMapOfLe J₂ J₃ g h₂ (reesMapOfLe J₁ J₂ f h₁ p)) =
    Ideal.Quotient.mk _ (reesMapOfLe J₁ J₃ (g.comp f) h₃ p)
  refine congrArg _ (Subtype.ext ?_)
  rw [reesMapOfLe_coe, reesMapOfLe_coe, reesMapOfLe_coe, Polynomial.map_map]

theorem grMapOfLe_congr {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {J₁ : Ideal R₁}
    {J₂ : Ideal R₂} {f f' : R₁ →+* R₂} (e : f = f') (hf : Ideal.map f J₁ ≤ J₂) :
    grMapOfLe J₁ J₂ f hf = grMapOfLe J₁ J₂ f' (e ▸ hf) := by
  subst e
  rfl

theorem presMap_id (hmap : Ideal.map (liftHom (X : σ → Amb A σ)) I ≤ I) :
    presMap I I (X : σ → Amb A σ) hmap = RingHom.id (Gr I) := by
  rw [presMap, grMapOfLe_congr liftHom_id, grMapOfLe_id]

theorem presMap_comp (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I'' ≤ I')
    (hmap'' : Ideal.map (liftHom fun t ↦ liftHom h (k t)) I'' ≤ I) :
    (presMap I I' h hmap).comp (presMap I' I'' k hmap') =
      presMap I I'' (fun t ↦ liftHom h (k t)) hmap'' := by
  rw [presMap, presMap, presMap, grMapOfLe_comp (liftHom k) (liftHom h) hmap' hmap
    (by rwa [← liftHom_comp]), grMapOfLe_congr (liftHom_comp h k).symm]

theorem compareVec_id {B : Type u} [CommRing B] (φ : Gr I →+* B) (v : σ → B) :
    compareVec (X : σ → Amb A σ) φ v = v :=
  funext fun i ↦ by rw [compareVec, taylor_X, eval₂_X]

theorem compareVec_comp {B : Type u} [CommRing B] (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (φ : Gr I →+* B) (v : σ → B) :
    compareVec (fun t ↦ liftHom h (k t)) φ v =
      compareVec k (φ.comp (presMap I I' h hmap)) (compareVec h φ v) := by
  have hcomp : (φ.comp (presMap I I' h hmap)).comp (algebraMap (Amb A σ') (Gr I')) =
      (φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h) :=
    RingHom.ext fun r ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, presMap_algebraMap, RingHom.comp_apply,
        RingHom.comp_apply]
  refine funext fun t ↦ ?_
  rw [compareVec, compareVec, hcomp, eval₂_taylor_liftHom]
  rfl

theorem eqToHom_val {B : Type u} [CommRing B] {x y : ConeGroupoid I B} (e : x = y) :
    (eqToHom e : x ⟶ y).val = 0 := by
  subst e
  rfl

/-- The comparison functor of the identity lift is (canonically isomorphic to) the identity
functor. -/
def compareFunctorIdIso (hmap : Ideal.map (liftHom (X : σ → Amb A σ)) I ≤ I)
    (B : Type u) [CommRing B] :
    compareFunctor I I (X : σ → Amb A σ) hmap B ≅ 𝟭 (ConeGroupoid I B) :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm ⟨0, by
      rw [translatePoint_zero]
      change x.point.comp (presMap I I (X : σ → Amb A σ) hmap) = x.point
      rw [presMap_id, RingHom.comp_id]⟩)
    fun {x _} f ↦ ConeGroupoid.Hom.ext (by
      change compareVec (X : σ → Amb A σ) x.point f.val + 0 = 0 + f.val
      rw [compareVec_id, add_zero, zero_add])

/-- **The cocycle identity.**  The composite of the comparison functors attached to two lifts is
canonically isomorphic to the comparison functor attached to the composite lift. -/
def compareFunctorCompIso (h : σ' → Amb A σ) (k : σ'' → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I'' ≤ I')
    (hmap'' : Ideal.map (liftHom fun t ↦ liftHom h (k t)) I'' ≤ I)
    (B : Type u) [CommRing B] :
    compareFunctor I I' h hmap B ⋙ compareFunctor I' I'' k hmap' B ≅
      compareFunctor I I'' (fun t ↦ liftHom h (k t)) hmap'' B :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm ⟨0, by
      rw [translatePoint_zero]
      change (x.point.comp (presMap I I' h hmap)).comp (presMap I' I'' k hmap') =
        x.point.comp (presMap I I'' (fun t ↦ liftHom h (k t)) hmap'')
      rw [RingHom.comp_assoc, presMap_comp h k hmap hmap' hmap'']⟩)
    fun {x _} f ↦ ConeGroupoid.Hom.ext (by
      change compareVec k (x.point.comp (presMap I I' h hmap)) (compareVec h x.point f.val) + 0 =
        0 + compareVec (fun t ↦ liftHom h (k t)) x.point f.val
      rw [compareVec_comp h k hmap, add_zero, zero_add])

end Functoriality

/-! ### Independence of the chosen lift -/

section LiftIndependence

variable {A : Type u} [CommRing A] {σ σ' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {h h' : σ' → Amb A σ} {B : Type u} [CommRing B]

/-- **The difference of two lifts, in degree one.**  The degree-one class of `h'(f) - h(f)` at a
`B`-point is computed by the Taylor derivation from the degree-one classes of the differences
`h' t - h t` of the lifts; this is the first-order part of the comparison of two lifts. -/
theorem point_degreeOneRaw_sub (hI : ∀ t, h' t - h t ∈ I) (φ : Gr I →+* B) (f : Amb A σ')
    (hf : liftHom h' f - liftHom h f ∈ I) :
    φ (degreeOneRaw (Amb A σ) I ⟨liftHom h' f - liftHom h f, hf⟩) =
      eval₂ ((φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h))
        (fun t ↦ φ (degreeOneRaw (Amb A σ) I ⟨h' t - h t, hI t⟩)) (taylor A σ' f) := by
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
    have hzero : φ (algebraMap (Amb A σ) (Gr I) (liftHom h' f)) =
        φ (algebraMap (Amb A σ) (Gr I) (liftHom h f)) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub, algebraMap_gr_eq_zero I hD, map_zero]
    rw [hkey, map_add, degreeOneRaw_smul, degreeOneRaw_smul, map_add, map_mul, map_mul, ih hD,
      hzero, taylor_mul, taylor_X, eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_X]
    simp only [RingHom.comp_apply, liftHom_X]

/-- The canonical tangent vector comparing two lifts at a `B`-point. -/
def liftHomotopy (hI : ∀ t, h' t - h t ∈ I) (φ : Gr I →+* B) : σ' → B :=
  fun t ↦ φ (degreeOneRaw (Amb A σ) I ⟨h' t - h t, hI t⟩)

/-- The canonical tangent vector translates the point attached to one lift into the point
attached to the other. -/
theorem translatePoint_liftHomotopy (hI : ∀ t, h' t - h t ∈ I)
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom h') I' ≤ I)
    (φ : Gr I →+* B) :
    translatePoint I' (φ.comp (presMap I I' h hmap)) (liftHomotopy hI φ) =
      φ.comp (presMap I I' h' hmap') := by
  have hcomp : (φ.comp (presMap I I' h hmap)).comp (algebraMap (Amb A σ') (Gr I')) =
      (φ.comp (algebraMap (Amb A σ) (Gr I))).comp (liftHom h) :=
    RingHom.ext fun r ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, presMap_algebraMap, RingHom.comp_apply,
        RingHom.comp_apply]
  refine ConeTranslation.gr_ringHom_ext I' (fun r ↦ ?_) fun x ↦ ?_
  · have hmem : liftHom h r - liftHom h' r ∈ I := by
      have hneg := neg_mem (liftHom_sub_mem hI r)
      rwa [neg_sub] at hneg
    rw [translatePoint_algebraMap, RingHom.comp_apply, RingHom.comp_apply, presMap_algebraMap,
      presMap_algebraMap, ← sub_eq_zero, ← map_sub, ← map_sub,
      algebraMap_gr_eq_zero I hmem, map_zero]
  · rw [← degreeOneRaw_eq_mk, translatePoint_degreeOneRaw, RingHom.comp_apply,
      presMap_degreeOneRaw, RingHom.comp_apply, presMap_degreeOneRaw, hcomp]
    have hlh : liftHomotopy hI φ =
        fun t ↦ φ (degreeOneRaw (Amb A σ) I ⟨h' t - h t, hI t⟩) := rfl
    rw [hlh, ← point_degreeOneRaw_sub hI φ (x : Amb A σ') (liftHom_sub_mem hI (x : Amb A σ')),
      ← map_add, ← map_add]
    refine congrArg _ (congrArg _ (Subtype.ext ?_))
    change liftHom h (x : Amb A σ') + (liftHom h' (x : Amb A σ') - liftHom h (x : Amb A σ')) =
      liftHom h' (x : Amb A σ')
    ring

/-- **Canonicity of the comparison.**  Two lifts of the same presentation induce canonically
isomorphic comparison functors; the isomorphism is the translation by the degree-one class of
the difference of the lifts. -/
def liftIso (hI : ∀ t, h' t - h t ∈ I) (hmap : Ideal.map (liftHom h) I' ≤ I)
    (hmap' : Ideal.map (liftHom h') I' ≤ I) (B : Type u) [CommRing B] :
    compareFunctor I I' h hmap B ≅ compareFunctor I I' h' hmap' B :=
  NatIso.ofComponents
    (fun x ↦ (Groupoid.isoEquivHom _ _).symm
      ⟨liftHomotopy hI x.point, translatePoint_liftHomotopy hI hmap hmap' x.point⟩)
    fun {x y} f ↦ ConeGroupoid.Hom.ext (by
      change compareVec h x.point f.val + liftHomotopy hI y.point =
        liftHomotopy hI x.point + compareVec h' x.point f.val
      refine funext fun t ↦ ?_
      have hy : y.point = translatePoint I x.point f.val := f.translate_eq.symm
      have hstep : liftHomotopy hI y.point t =
          liftHomotopy hI x.point t +
            eval₂ (x.point.comp (algebraMap (Amb A σ) (Gr I))) f.val
              (taylor A σ (h' t - h t)) := by
        rw [liftHomotopy, hy, translatePoint_degreeOneRaw]
        rfl
      change compareVec h x.point f.val t + liftHomotopy hI y.point t =
        liftHomotopy hI x.point t + compareVec h' x.point f.val t
      rw [hstep, compareVec, compareVec, map_sub, eval₂_sub]
      ring)

end LiftIndependence

/-! ### The comparison is an equivalence of groupoids -/

section Equivalence

variable {A : Type u} [CommRing A] {σ σ' σ'' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {I'' : Ideal (Amb A σ'')}

theorem map_liftHom_X_le (I : Ideal (Amb A σ)) :
    Ideal.map (liftHom (X : σ → Amb A σ)) I ≤ I := by
  rw [liftHom_id, Ideal.map_id]

theorem map_liftHom_comp_le {h : σ' → Amb A σ} {k : σ'' → Amb A σ'}
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I'' ≤ I') :
    Ideal.map (liftHom fun t ↦ liftHom h (k t)) I'' ≤ I := by
  rw [liftHom_comp, ← Ideal.map_map]
  exact le_trans (Ideal.map_mono hmap') hmap

/-- **Two presentations related by mutually inverse lifts have equivalent quotient groupoids.**
This is the affine Layer-5 gate statement: the presentation `[C_{U/M}/T_M|_U]` of the intrinsic
normal cone does not depend on the chosen embedding. -/
def compareEquivalence (h : σ' → Amb A σ) (k : σ → Amb A σ')
    (hmap : Ideal.map (liftHom h) I' ≤ I) (hmap' : Ideal.map (liftHom k) I ≤ I')
    (hhk : ∀ i, liftHom h (k i) - X i ∈ I) (hkh : ∀ t, liftHom k (h t) - X t ∈ I')
    (B : Type u) [CommRing B] : ConeGroupoid I B ≌ ConeGroupoid I' B := by
  refine CategoryTheory.Equivalence.mk (compareFunctor I I' h hmap B)
    (compareFunctor I' I k hmap' B) ?_ ?_
  · refine (compareFunctorIdIso (map_liftHom_X_le I) B).symm ≪≫ ?_
    refine liftIso (h := (X : σ → Amb A σ)) (h' := fun i ↦ liftHom h (k i)) hhk
      (map_liftHom_X_le I) (map_liftHom_comp_le hmap hmap') B ≪≫ ?_
    exact (compareFunctorCompIso h k hmap hmap' (map_liftHom_comp_le hmap hmap') B).symm
  · refine compareFunctorCompIso k h hmap' hmap (map_liftHom_comp_le hmap' hmap) B ≪≫ ?_
    refine liftIso (h := fun t ↦ liftHom k (h t)) (h' := (X : σ' → Amb A σ'))
      (fun t ↦ ?_) (map_liftHom_comp_le hmap' hmap) (map_liftHom_X_le I') B ≪≫
        compareFunctorIdIso (map_liftHom_X_le I') B
    have hneg := neg_mem (hkh t)
    rwa [neg_sub] at hneg

end Equivalence

/-! ### Two presentations of the same algebra -/

section Presentations

variable {A : Type u} [CommRing A] {σ σ' σ'' : Type u} {S : Type u} [CommRing S] [Algebra A S]
  (π : Amb A σ →ₐ[A] S) (π' : Amb A σ' →ₐ[A] S) (π'' : Amb A σ'' →ₐ[A] S)

/-- The ideal of a presentation `A[x_σ] ↠ S` of `Γ(U)`. -/
abbrev presIdeal : Ideal (Amb A σ) := RingHom.ker π.toRingHom

variable {π π'}

theorem mem_presIdeal_iff {f : Amb A σ} : f ∈ presIdeal π ↔ π f = 0 :=
  RingHom.mem_ker

/-- A family of lifts of the generators of one presentation into the other induces a map of
presentations. -/
theorem comp_liftHom_eq {h : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t)) :
    π.toRingHom.comp (liftHom h) = π'.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun t ↦ ?_
  · rw [RingHom.comp_apply, liftHom_C]
    change π (C a) = π' (C a)
    rw [← algebraMap_eq, ← algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
  · rw [RingHom.comp_apply, liftHom_X]
    exact hh t

theorem liftHom_apply_eq {h : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t)) (f : Amb A σ') :
    π (liftHom h f) = π' f :=
  DFunLike.congr_fun (comp_liftHom_eq hh) f

theorem map_liftHom_presIdeal_le {h : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t)) :
    Ideal.map (liftHom h) (presIdeal π') ≤ presIdeal π := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_presIdeal_iff, liftHom_apply_eq hh]
  exact mem_presIdeal_iff.mp hx

theorem lift_sub_mem_presIdeal {h h' : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t))
    (hh' : ∀ t, π (h' t) = π' (X t)) (t : σ') : h' t - h t ∈ presIdeal π := by
  rw [mem_presIdeal_iff, map_sub, hh, hh', sub_self]

theorem exists_lift (hπ : Function.Surjective π) (π' : Amb A σ' →ₐ[A] S) :
    ∃ h : σ' → Amb A σ, ∀ t, π (h t) = π' (X t) :=
  ⟨fun t ↦ (hπ (π' (X t))).choose, fun t ↦ (hπ (π' (X t))).choose_spec⟩

/-- Lifts in both directions compose to the identity modulo the ideal of the presentation. -/
theorem liftHom_comp_sub_X_mem {h : σ' → Amb A σ} {k : σ → Amb A σ'}
    (hh : ∀ t, π (h t) = π' (X t)) (hk : ∀ i, π' (k i) = π (X i)) (i : σ) :
    liftHom h (k i) - X i ∈ presIdeal π := by
  rw [mem_presIdeal_iff, map_sub, liftHom_apply_eq hh, hk, sub_self]

/-- **Independence of the local embedding.**  Two presentations of the same algebra have
equivalent quotient groupoids `[C_{U/M}/T_M|_U](B)`, via any pair of lifts. -/
def presentationEquivalence {h : σ' → Amb A σ} {k : σ → Amb A σ'}
    (hh : ∀ t, π (h t) = π' (X t)) (hk : ∀ i, π' (k i) = π (X i))
    (B : Type u) [CommRing B] :
    ConeGroupoid (presIdeal π) B ≌ ConeGroupoid (presIdeal π') B :=
  compareEquivalence h k (map_liftHom_presIdeal_le hh) (map_liftHom_presIdeal_le hk)
    (liftHom_comp_sub_X_mem hh hk) (liftHom_comp_sub_X_mem hk hh) B

/-- **Canonicity.**  Two choices of lifts give canonically isomorphic comparison functors. -/
def presentationLiftIso {h h' : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t))
    (hh' : ∀ t, π (h' t) = π' (X t)) (B : Type u) [CommRing B] :
    compareFunctor (presIdeal π) (presIdeal π') h (map_liftHom_presIdeal_le hh) B ≅
      compareFunctor (presIdeal π) (presIdeal π') h' (map_liftHom_presIdeal_le hh') B :=
  liftIso (lift_sub_mem_presIdeal hh hh') _ _ B

variable {π''}

/-- **The cocycle condition.**  For three presentations the comparison functors compose, up to
the canonical isomorphism of Behrend–Fantechi's gluing datum. -/
def cocycleIso {h : σ' → Amb A σ} {k : σ'' → Amb A σ'} {l : σ'' → Amb A σ}
    (hh : ∀ t, π (h t) = π' (X t)) (hk : ∀ t, π' (k t) = π'' (X t))
    (hl : ∀ t, π (l t) = π'' (X t)) (B : Type u) [CommRing B] :
    compareFunctor (presIdeal π) (presIdeal π') h (map_liftHom_presIdeal_le hh) B ⋙
        compareFunctor (presIdeal π') (presIdeal π'') k (map_liftHom_presIdeal_le hk) B ≅
      compareFunctor (presIdeal π) (presIdeal π'') l (map_liftHom_presIdeal_le hl) B := by
  have hcomp : ∀ t, π (liftHom h (k t)) = π'' (X t) := fun t ↦ by
    rw [liftHom_apply_eq hh, hk]
  refine compareFunctorCompIso h k (map_liftHom_presIdeal_le hh) (map_liftHom_presIdeal_le hk)
    (map_liftHom_presIdeal_le hcomp) B ≪≫ ?_
  exact liftIso (lift_sub_mem_presIdeal hcomp hl) _ _ B

/-- The comparison functor of the identity presentation and the identity lift is the identity. -/
def presentationIdIso (B : Type u) [CommRing B] :
    compareFunctor (presIdeal π) (presIdeal π) (X : σ → Amb A σ)
        (map_liftHom_presIdeal_le (π := π) (π' := π) fun _ ↦ rfl) B ≅
      𝟭 (ConeGroupoid (presIdeal π) B) :=
  compareFunctorIdIso _ B

/-- The common refinement of the two embeddings is the graph embedding of
`Cones/RefinementQuotient.lean`: the joint presentation `A[x_σ, x_{σ'}] ↠ S` has as kernel the
graph ideal of the lift `h`. -/
theorem ker_jointPres {h : σ' → Amb A σ} (hh : ∀ t, π (h t) = π' (X t)) :
    RingHom.ker (MvPolynomial.aeval
        (Sum.elim (fun i ↦ π (X i)) fun t ↦ π' (X t)) : Amb A (σ ⊕ σ') →ₐ[A] S).toRingHom =
      graphIdeal A σ σ' (presIdeal π) h := by
  have hfac : (MvPolynomial.aeval (Sum.elim (fun i ↦ π (X i)) fun t ↦ π' (X t)) :
      Amb A (σ ⊕ σ') →ₐ[A] S) = π.comp (graphProj h) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    cases i with
    | inl i => rw [aeval_X, AlgHom.comp_apply, graphProj_X_inl]; rfl
    | inr t => rw [aeval_X, AlgHom.comp_apply, graphProj_X_inr, hh]; rfl
  rw [hfac]
  refine Ideal.ext fun f ↦ ?_
  rw [RingHom.mem_ker, mem_graphIdeal_iff, mem_presIdeal_iff]
  rfl

end Presentations

/-! ### Compatibility with the normal sheaf -/

section NormalSheaf

variable {A : Type u} [CommRing A] {σ σ' : Type u}
  {I : Ideal (Amb A σ)} {I' : Ideal (Amb A σ')} {h : σ' → Amb A σ}

/-- The map of normal-sheaf rings `N_{U/M'} → N_{U/M}` induced by a lift. -/
def nsPresMap (I : Ideal (Amb A σ)) (I' : Ideal (Amb A σ')) (h : σ' → Amb A σ)
    (hmap : Ideal.map (liftHom h) I' ≤ I) : Ns I' →+* Ns I :=
  (nsMapOfLe (Ideal.map (liftHom h) I') I hmap).comp
    (nsMapOfEq I' (liftHom h) (Ideal.map (liftHom h) I') rfl)

theorem nsPresMap_algebraMap (hmap : Ideal.map (liftHom h) I' ≤ I) (r : Amb A σ') :
    nsPresMap I I' h hmap (algebraMap (Amb A σ') (Ns I') r) =
      algebraMap (Amb A σ) (Ns I) (liftHom h r) := by
  rw [nsPresMap, RingHom.comp_apply]
  change nsMapOfLe _ _ _ (nsMapOfEq I' (liftHom h) _ rfl
    (Ideal.Quotient.mk _ (algebraMap (Amb A σ') (SymmetricAlgebra (Amb A σ') I') r))) = _
  rw [nsMapOfEq_mk, symMapOfEq_algebraMap, nsMapOfLe_mk]
  change Ideal.Quotient.mk _ (symMapOfLe _ _ _ (algebraMap _ _ (liftHom h r))) = _
  rw [AlgHom.commutes]
  rfl

theorem nsPresMap_nsClass (hmap : Ideal.map (liftHom h) I' ≤ I) (x : I') :
    nsPresMap I I' h hmap (nsClass I' x) =
      nsClass I ⟨liftHom h (x : Amb A σ'), hmap (Ideal.mem_map_of_mem _ x.2)⟩ := by
  rw [nsPresMap, RingHom.comp_apply, nsClass_eq_mk, nsMapOfEq_mk, symMapOfEq_ι, nsMapOfLe_mk,
    symMapOfLe_ι, nsClass_eq_mk]

/-- **The comparison is compatible with the closed immersion `C ⊆ N`.**  The square formed by
the two comparison maps and the two surjections `Sym(I/I²) ↠ gr_I` commutes. -/
theorem nsToGr_comp_nsPresMap (hmap : Ideal.map (liftHom h) I' ≤ I) :
    (nsToGr (Amb A σ) I).toRingHom.comp (nsPresMap I I' h hmap) =
      (presMap I I' h hmap).comp (nsToGr (Amb A σ') I').toRingHom := by
  refine ns_ringHom_ext I' (fun r ↦ ?_) fun x ↦ ?_
  · change nsToGr (Amb A σ) I (nsPresMap I I' h hmap
      (algebraMap (Amb A σ') (Ns I') r)) =
      presMap I I' h hmap (nsToGr (Amb A σ') I' (algebraMap (Amb A σ') (Ns I') r))
    rw [nsPresMap_algebraMap, AlgHom.commutes, AlgHom.commutes, presMap_algebraMap]
  · change nsToGr (Amb A σ) I (nsPresMap I I' h hmap (nsClass I' x)) =
      presMap I I' h hmap (nsToGr (Amb A σ') I' (nsClass I' x))
    rw [nsPresMap_nsClass, nsToGr_nsClass, nsToGr_nsClass, presMap_degreeOneRaw]

/-- On `B`-points: including a point of the normal cone into the normal sheaf commutes with the
comparison of the two presentations. -/
theorem point_comp_nsToGr (hmap : Ideal.map (liftHom h) I' ≤ I) {B : Type u} [CommRing B]
    (φ : Gr I →+* B) :
    (φ.comp (presMap I I' h hmap)).comp (nsToGr (Amb A σ') I').toRingHom =
      (φ.comp (nsToGr (Amb A σ) I).toRingHom).comp (nsPresMap I I' h hmap) := by
  rw [RingHom.comp_assoc, RingHom.comp_assoc, nsToGr_comp_nsPresMap]

/-! #### The tangent translation on the normal sheaf -/

variable {B : Type u} [CommRing B]

theorem nsTranslatePoint_algebraMap (φ : Ns I →+* B) (v : σ → B) (r : Amb A σ) :
    nsTranslatePoint I φ v (algebraMap (Amb A σ) (Ns I) r) =
      φ (algebraMap (Amb A σ) (Ns I) r) := by
  change eval₂Hom φ v (nsCoaction I (algebraMap (Amb A σ) (Ns I) r)) = _
  rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, eval₂Hom_C]

theorem nsTranslatePoint_nsClass (φ : Ns I →+* B) (v : σ → B) (x : I) :
    nsTranslatePoint I φ v (nsClass I x) =
      φ (nsClass I x) +
        eval₂ (φ.comp (algebraMap (Amb A σ) (Ns I))) v (taylor A σ (x : Amb A σ)) := by
  change eval₂Hom φ v (nsCoaction I (Ideal.Quotient.mk _ (SymmetricAlgebra.ι (Amb A σ) I x))) = _
  rw [nsCoaction_mk_ι, map_add, eval₂Hom_C, MvPolynomial.coe_eval₂Hom, eval₂_map]
  rfl

/-- **Equivariance of the comparison on the normal sheaf.**  The tangent translation on the
normal sheaf is compatible with the comparison of two presentations, by the same Jacobian
formula as for the normal cone. -/
theorem nsTranslatePoint_comp_nsPresMap (hmap : Ideal.map (liftHom h) I' ≤ I)
    (φ : Ns I →+* B) (v : σ → B) :
    (nsTranslatePoint I φ v).comp (nsPresMap I I' h hmap) =
      nsTranslatePoint I' (φ.comp (nsPresMap I I' h hmap))
        (fun t ↦ eval₂ (φ.comp (algebraMap (Amb A σ) (Ns I))) v (taylor A σ (h t))) := by
  have hcomp : (φ.comp (nsPresMap I I' h hmap)).comp (algebraMap (Amb A σ') (Ns I')) =
      (φ.comp (algebraMap (Amb A σ) (Ns I))).comp (liftHom h) :=
    RingHom.ext fun r ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, nsPresMap_algebraMap, RingHom.comp_apply,
        RingHom.comp_apply]
  refine ns_ringHom_ext I' (fun r ↦ ?_) fun x ↦ ?_
  · change nsTranslatePoint I φ v (nsPresMap I I' h hmap (algebraMap (Amb A σ') (Ns I') r)) =
      nsTranslatePoint I' (φ.comp (nsPresMap I I' h hmap)) _
        (algebraMap (Amb A σ') (Ns I') r)
    rw [nsPresMap_algebraMap, nsTranslatePoint_algebraMap, nsTranslatePoint_algebraMap,
      RingHom.comp_apply, nsPresMap_algebraMap]
  · change nsTranslatePoint I φ v (nsPresMap I I' h hmap (nsClass I' x)) =
      nsTranslatePoint I' (φ.comp (nsPresMap I I' h hmap)) _ (nsClass I' x)
    rw [nsPresMap_nsClass, nsTranslatePoint_nsClass, nsTranslatePoint_nsClass,
      eval₂_taylor_liftHom, hcomp, RingHom.comp_apply, nsPresMap_nsClass]

end NormalSheaf

end

end EmbeddingIndependence

end GromovWitten.AlgebraicGeometry
