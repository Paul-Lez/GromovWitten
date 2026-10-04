/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.EtalePullback
import GromovWitten.AlgebraicGeometry.IntersectionTheory.VistoliRelations
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClassGeneral
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Unramified.Field

/-!
# The Čech groupoid of an étale cover computes the Chow group

Let `k` be a field, `U` a scheme locally of finite type over `k` and `π : U' ⟶ U` an étale
morphism. The *Čech groupoid* of `π` is the étale presentation groupoid with atlas `U'`, arrows
`U' ×_U U'` and the two projections as source and target, graded by the canonical dimension
functions (transcendence degree of residue fields over `k`). This file proves the point-level
properties of the comparison map from the Čech groupoid to the identity groupoid of `U`
(surjectivity, fullness, the residue-field compatibility over the identity, and Galois descent in
the fibres of `π`), packages them into a Morita map, and deduces that the Vistoli rational Chow
group of the Čech groupoid is the rational Chow group of `U` (atlas independence for schemes).

## Main results

* `CechGroupoidChow.tensor_descent`: for a finite separable field extension `L / K`, an element
  `a : L` such that `a ⊗ 1 - 1 ⊗ a` lies in every prime of `L ⊗[K] L` lies in `K`.
* `CechGroupoidChow.finite_residueField_of_formallyUnramified`: residue field extensions of a
  formally unramified morphism locally of finite type are finite.
* `CechGroupoidChow.resTrdeg_comp_etale`, `CechGroupoidChow.dimensionFunction_comp_etale`: étale
  morphisms preserve the transcendence degree of residue fields over `k`, hence the canonical
  dimension functions.
* `CechGroupoidChow.tensorInl_sub_tensorInr_mem`: description of the points of a fibre product
  above a triplet through the primes of the tensor product of residue fields.
* `CechGroupoidChow.residue_descent_of_etale`: Galois descent in the fibres of an étale morphism.
* `CechGroupoidChow.residueFieldMap_fst_comp_eq`, `CechGroupoidChow.exists_cech_arrow`: the
  residue-field compatibility and the existence of arrows over the identity.
* `cechGroupoid`: the Čech groupoid as an `EtalePresentationGroupoid`, and `cechGroupoid_good`:
  it satisfies the standing hypotheses when `U'` and `π` are quasi-compact.
* `cechMorita`: for `π` étale surjective, the Morita map from the Čech groupoid to the identity
  groupoid of `U`, with all four conditions (F0)–(F3) proved.
* `cechVistoliChowEquiv`: the Vistoli rational Chow group of the Čech groupoid of a quasi-compact
  étale surjection `π : U' ⟶ U` (with `U'` quasi-compact) is the rational Chow group of `U`.
-/

open CategoryTheory AlgebraicGeometry Limits TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace CechGroupoidChow

/-! ## Galois descent for a finite separable extension -/

/-- **Galois descent for a finite separable field extension.** If `L / K` is finite separable and
`a : L` is such that `a ⊗ 1 - 1 ⊗ a` lies in every prime ideal of `L ⊗[K] L`, then `a ∈ K`.
The proof: the element is nilpotent, `L ⊗[K] L` is reduced (separability), so `a ⊗ 1 = 1 ⊗ a`,
and comparing coordinates in a tensor-product basis built from a basis of `L` containing `1`
forces `a ∈ K`. -/
theorem tensor_descent {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] [Module.Finite K L] (a : L)
    (h : ∀ P : Ideal (L ⊗[K] L), P.IsPrime → a ⊗ₜ[K] (1 : L) - (1 : L) ⊗ₜ[K] a ∈ P) :
    a ∈ (algebraMap K L).range := by
  classical
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  have hred : IsReduced (L ⊗[K] L) := Algebra.FormallyUnramified.isReduced_of_field L _
  have hnil : IsNilpotent (a ⊗ₜ[K] (1 : L) - (1 : L) ⊗ₜ[K] a) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    exact fun P hP ↦ h P hP
  have H : (a ⊗ₜ[K] (1 : L) : L ⊗[K] L) = 1 ⊗ₜ a := sub_eq_zero.mp hnil.eq_zero
  by_cases h' : LinearIndependent K ![1, a]
  · have h := h'.linearIndepOn_id
    let e : h.extend (Set.subset_univ _) := ⟨1, h.subset_extend _ (by simp)⟩
    have he : Module.Basis.extend h e = 1 := by simp [e]
    let b : h.extend (Set.subset_univ _) := ⟨a, h.subset_extend _ (by simp)⟩
    have hb : Module.Basis.extend h b = a := by simp [b]
    by_cases hne : e = b
    · obtain rfl : 1 = a := congr_arg Subtype.val hne
      exact ⟨1, map_one _⟩
    have := DFunLike.congr_fun
      (DFunLike.congr_arg ((Module.Basis.extend h).tensorProduct
        (Module.Basis.extend h)).repr H) (b, e)
    simp only [Module.Basis.tensorProduct_repr_tmul_apply, ← he, ← hb, Module.Basis.repr_self,
      smul_eq_mul, Finsupp.single_apply, hne, Ne.symm hne, ↓reduceIte, mul_one, mul_zero,
      one_ne_zero] at this
  · rw [LinearIndependent.pair_iff] at h'
    simp only [not_forall, not_and, exists_prop] at h'
    obtain ⟨c, d, hcd, hab⟩ := h'
    have : IsUnit d := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_smul, ← Algebra.algebraMap_eq_smul_one, add_zero,
        (injective_iff_map_eq_zero' _).mp (algebraMap K L).injective] at hcd
      cases hab hcd rfl
    refine ⟨-this.unit⁻¹ * c, ?_⟩
    rw [map_mul, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one,
      eq_neg_iff_add_eq_zero.mpr hcd, smul_neg, neg_smul, neg_neg, smul_smul, this.val_inv_mul,
      one_smul]

/-! ## Residue extensions of étale morphisms -/

section Residue

variable {X Y : Scheme.{u}}

/-- The residue field extensions of a formally unramified morphism locally of finite type are
finite (Stacks 00UW (2)), stated for the algebra structure given by `residueFieldMap`. -/
theorem finite_residueField_of_formallyUnramified (g : Y ⟶ X) [FormallyUnramified g]
    [LocallyOfFiniteType g] (y : Y) :
    letI : Algebra (X.residueField (g.base y)) (Y.residueField y) :=
      (g.residueFieldMap y).hom.toAlgebra
    Module.Finite (X.residueField (g.base y)) (Y.residueField y) := by
  algebraize [(g.stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap y).hom
  suffices h : Module.Finite
      (IsLocalRing.ResidueField <| X.presheaf.stalk (g.base y))
      (IsLocalRing.ResidueField <| Y.presheaf.stalk y) by
    change (g.residueFieldMap y).hom.Finite
    have e : (g.residueFieldMap y).hom = algebraMap
        (IsLocalRing.ResidueField <| X.presheaf.stalk (g.base y))
        (IsLocalRing.ResidueField <| Y.presheaf.stalk y) := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    have h' := RingHom.finite_algebraMap.mpr h
    rw [e]
    exact h'
  have : Algebra.EssFiniteType (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap g y
  have : Algebra.FormallyUnramified (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap g y
  infer_instance

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

open FiniteTypeDimension in
/-- An étale morphism preserves the transcendence degree of residue fields over the base field:
the residue extensions are separable, hence algebraic, and the transcendence degree is additive
in towers. -/
theorem resTrdeg_comp_etale (g : Y ⟶ X) [Etale g] (y : Y) :
    resTrdeg (g ≫ f) y = resTrdeg f (g.base y) := by
  let K := X.residueField (g.base y)
  let L := Y.residueField y
  let _ : Algebra k K := (residueMap f (g.base y)).toAlgebra
  let _ : Algebra K L := (g.residueFieldMap y).hom.toAlgebra
  let _ : Algebra k L := (residueMap (g ≫ f) y).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun c ↦
    (residueFieldMap_residueMap f g y c).symm
  have : Algebra.IsAlgebraic K L := Algebra.IsSeparable.isAlgebraic K L
  have h := trdeg_add_eq k K (A := L)
  rw [trdeg_eq_zero (R := K) (A := L), add_zero] at h
  change Cardinal.toENat (Algebra.trdeg k L) = Cardinal.toENat (Algebra.trdeg k K)
  rw [h]

open FiniteTypeDimension in
/-- The canonical dimension functions are compatible with étale morphisms. -/
theorem dimensionFunction_comp_etale [LocallyOfFiniteType f] (g : Y ⟶ X) [Etale g]
    [LocallyOfFiniteType (g ≫ f)] (y : Y) :
    dimensionFunction (g ≫ f) y = dimensionFunction f (g.base y) := by
  simp only [dimensionFunction_apply, resTrdeg_comp_etale]

end Residue

/-! ## Points of a fibre product and the tensor product of residue fields -/

section Carrier

open Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The canonical map `κ(x) ⊗[κ(s)] κ(y) → κ(t)` sends `inl a` to the image of `a` under the
residue map of the first projection, after transport along an equality of triplets. -/
theorem ofPointTensor_tensorCongr_inv_inl (t : ↑(pullback f g)) (T : Triplet f g)
    (e : Triplet.ofPoint t = T) (a : X.residueField T.x) :
    ofPointTensor t ((Triplet.tensorCongr e).inv (T.tensorInl a)) =
      (pullback.fst f g).residueFieldMap t
        ((X.residueFieldCongr (congrArg Triplet.x e)).inv a) := by
  subst e
  simp only [Triplet.tensorCongr_refl, Iso.refl_inv, Scheme.residueFieldCongr_refl]
  change ((Triplet.ofPoint t).tensorInl ≫ ofPointTensor t) a = _
  have h1 : (Triplet.ofPoint t).tensorInl ≫ ofPointTensor t =
      (pullback.fst f g).residueFieldMap t := pushout.inl_desc _ _ _
  rw [h1]
  rfl

/-- The canonical map `κ(x) ⊗[κ(s)] κ(y) → κ(t)` sends `inr b` to the image of `b` under the
residue map of the second projection, after transport along an equality of triplets. -/
theorem ofPointTensor_tensorCongr_inv_inr (t : ↑(pullback f g)) (T : Triplet f g)
    (e : Triplet.ofPoint t = T) (b : Y.residueField T.y) :
    ofPointTensor t ((Triplet.tensorCongr e).inv (T.tensorInr b)) =
      (pullback.snd f g).residueFieldMap t
        ((Y.residueFieldCongr (congrArg Triplet.y e)).inv b) := by
  subst e
  simp only [Triplet.tensorCongr_refl, Iso.refl_inv, Scheme.residueFieldCongr_refl]
  change ((Triplet.ofPoint t).tensorInr ≫ ofPointTensor t) b = _
  have h1 : (Triplet.ofPoint t).tensorInr ≫ ofPointTensor t =
      (pullback.snd f g).residueFieldMap t := pushout.inr_desc _ _ _
  rw [h1]
  rfl

/-- If, at every point `t` of `X ×_S Y` above a triplet `T`, the images of `a ∈ κ(x)` and
`b ∈ κ(y)` in `κ(t)` agree, then `inl a - inr b` lies in every prime of
`κ(x) ⊗[κ(s)] κ(y)`. -/
theorem tensorInl_sub_tensorInr_mem (T : Triplet f g) (a : X.residueField T.x)
    (b : Y.residueField T.y)
    (h : ∀ t : ↑(pullback f g), (hx : pullback.fst f g t = T.x) →
      (hy : pullback.snd f g t = T.y) →
      (pullback.fst f g).residueFieldMap t ((X.residueFieldCongr hx).inv a) =
        (pullback.snd f g).residueFieldMap t ((Y.residueFieldCongr hy).inv b))
    (Q : Spec T.tensor) : T.tensorInl a - T.tensorInr b ∈ Q.asIdeal := by
  obtain ⟨e, he⟩ : ∃ e : Triplet.ofPoint (T.SpecTensorTo Q) = T,
      Spec.map (Triplet.tensorCongr e).inv (SpecOfPoint (T.SpecTensorTo Q)) = Q :=
    carrierEquiv_eq_iff.mp (carrierEquiv.apply_symm_apply ⟨T, Q⟩)
  rw [← he]
  change ofPointTensor (T.SpecTensorTo Q) ((Triplet.tensorCongr e).inv
    (T.tensorInl a - T.tensorInr b)) ∈ (⊥ : Ideal _)
  rw [map_sub, map_sub, ofPointTensor_tensorCongr_inv_inl, ofPointTensor_tensorCongr_inv_inr,
    Ideal.mem_bot, sub_eq_zero]
  exact h _ _ _

end Carrier

/-! ## Point-level properties of the Čech groupoid -/

section PointLevel

open Scheme.Pullback

variable {U U' : Scheme.{u}} (π : U' ⟶ U)

/-- **Galois descent in the fibres of an étale morphism.** If `a ∈ κ(u')` has the same image
under the two residue maps `κ(u') → κ(r')` of the projections, at every point `r'` of
`U' ×_U U'` lying over `(u', u')`, then `a` comes from `κ(π u')`. -/
theorem residue_descent_of_etale [Etale π] (u' : U') (a : U'.residueField u')
    (h : ∀ r' : ↑(pullback π π), (hs : pullback.fst π π r' = u') →
      (ht : pullback.snd π π r' = u') →
      (pullback.fst π π).residueFieldMap r' ((U'.residueFieldCongr hs).inv a) =
        (pullback.snd π π).residueFieldMap r' ((U'.residueFieldCongr ht).inv a)) :
    ∃ b : U.residueField (π.base u'), π.residueFieldMap u' b = a := by
  let T : Triplet π π := Triplet.mk' u' u' rfl
  let K := U.residueField (π.base u')
  let L := U'.residueField u'
  let _ : Algebra K L := (π.residueFieldMap u').hom.toAlgebra
  have : Module.Finite K L := finite_residueField_of_formallyUnramified π u'
  have hsep : Algebra.IsSeparable K L := inferInstance
  let iL : L →+* L ⊗[K] L := Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := L)
  let iR : L →+* L ⊗[K] L := (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom
  let Ψ : T.tensor ⟶ CommRingCat.of (L ⊗[K] L) :=
    pushout.desc (CommRingCat.ofHom iL) (CommRingCat.ofHom iR) (by
      have key (c : K) : (algebraMap K L c) ⊗ₜ[K] (1 : L) = (1 : L) ⊗ₜ[K] (algebraMap K L c) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      ext c
      exact key c)
  have hΨl : T.tensorInl ≫ Ψ = CommRingCat.ofHom iL := pushout.inl_desc _ _ _
  have hΨr : T.tensorInr ≫ Ψ = CommRingCat.ofHom iR := pushout.inr_desc _ _ _
  have hmem := tensorInl_sub_tensorInr_mem T a a h
  obtain ⟨b, hb⟩ := tensor_descent (K := K) a fun P hP ↦ by
    have := hmem ⟨P.comap Ψ.hom, Ideal.comap_isPrime _ _⟩
    change Ψ (T.tensorInl a - T.tensorInr a) ∈ P at this
    rw [map_sub] at this
    change (T.tensorInl ≫ Ψ) a - (T.tensorInr ≫ Ψ) a ∈ P at this
    rw [hΨl, hΨr] at this
    exact this
  exact ⟨b, hb⟩


/-- The two composites `κ(π (fst r')) → κ(fst r') → κ(r')` and
`κ(π (snd r')) → κ(snd r') → κ(r')` agree (after identifying `π (fst r') = π (snd r')`): both
are the residue map of `fst ≫ π = snd ≫ π` at `r'`. -/
theorem residueFieldMap_fst_comp_eq (r' : ↑(pullback π π)) :
    π.residueFieldMap (pullback.fst π π r') ≫ (pullback.fst π π).residueFieldMap r' =
      (U.residueFieldCongr (by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])).hom ≫
        π.residueFieldMap (pullback.snd π π r') ≫ (pullback.snd π π).residueFieldMap r' := by
  rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
  exact Scheme.Hom.residueFieldMap_congr pullback.condition r'

/-- Two points of `U'` with the same image in `U` are the two projections of a point of
`U' ×_U U'`. -/
theorem exists_cech_arrow (u' v' : U') (h : π.base u' = π.base v') :
    ∃ r' : ↑(pullback π π), pullback.fst π π r' = u' ∧ pullback.snd π π r' = v' :=
  exists_preimage_pullback u' v' h

end PointLevel

end CechGroupoidChow

/-! ## The Čech groupoid -/

section Groupoid

variable {k : Type u} [Field k] {U U' : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType f] (π : U' ⟶ U) [Etale π]

open FiniteTypeDimension CechGroupoidChow

/-- **The Čech groupoid of an étale morphism** `π : U' ⟶ U` of schemes locally of finite type
over a field `k`: the atlas is `U'`, the arrows are `U' ×_U U'` with the two projections as source
and target, and both are graded by the canonical dimension functions
`FiniteTypeDimension.dimensionFunction` (transcendence degree of residue fields over `k`). The
relative-dimension-zero conditions `src_dim`, `tgt_dim` are proved: étale morphisms have algebraic
residue field extensions. -/
noncomputable abbrev cechGroupoid : EtalePresentationGroupoid.{u} where
  base := U'
  arrows := pullback π π
  baseDim := dimensionFunction (π ≫ f)
  arrowsDim := dimensionFunction (pullback.fst π π ≫ π ≫ f)
  src := pullback.fst π π
  tgt := pullback.snd π π
  src_etale := inferInstance
  tgt_etale := inferInstance
  src_dim r := dimensionFunction_comp_etale (π ≫ f) (pullback.fst π π) r
  tgt_dim r := by
    simp only [dimensionFunction_apply]
    rw [pullback.condition_assoc, resTrdeg_comp_etale]

/-- Under quasi-compactness of `U'` and of `π`, the Čech groupoid satisfies the standing
hypotheses `EtalePresentationGroupoid.Good`: both schemes are quasi-compact and locally
Noetherian (locally of finite type over a field), and the canonical dimension functions satisfy
`CovByDimension`. -/
theorem cechGroupoid_good [CompactSpace U'] [QuasiCompact π] : (cechGroupoid f π).Good where
  compactSpace_base := ‹_›
  compactSpace_arrows := inferInstanceAs (CompactSpace ↥(pullback π π))
  isLocallyNoetherian_base := LocallyOfFiniteType.isLocallyNoetherian (π ≫ f)
  isLocallyNoetherian_arrows :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst π π ≫ π ≫ f)
  covByDimension_base := covByDimension_finiteTypeDimension (π ≫ f)
  covByDimension_arrows := covByDimension_finiteTypeDimension (pullback.fst π π ≫ π ≫ f)

/-- **The Čech groupoid of an étale surjection is Morita equivalent to the identity groupoid.**
For `π : U' ⟶ U` étale and surjective, `π` and `fst ≫ π : U' ×_U U' ⟶ U` form a Morita map from
the Čech groupoid of `π` to the identity groupoid of `U` (with the canonical dimension
functions). All four conditions are proved: (F0) is the surjectivity of `π`, (F1) and (F3) come
from the existence of points of a fibre product over given points
(`exists_cech_arrow`, `residueFieldMap_congr`), and (F2) is Galois descent
(`residue_descent_of_etale`). -/
noncomputable def cechMorita [Surjective π] :
    MoritaMap (cechGroupoid f π) (identityGroupoid U (dimensionFunction f)) where
  onBase := π
  onArrows := pullback.fst π π ≫ π
  onBase_etale := inferInstance
  onBase_dim u := dimensionFunction_comp_etale f π u
  src_comm := Category.comp_id _
  tgt_comm := by
    change (pullback.fst π π ≫ π) ≫ 𝟙 U = pullback.snd π π ≫ π
    rw [Category.comp_id, pullback.condition]
  onBase_surjective := π.surjective
  exists_arrow_over_identity u' v' h := by
    obtain ⟨r', hs, ht⟩ := exists_cech_arrow π u' v' h
    exact ⟨r', _, hs, ht, Scheme.Hom.residueFieldMap_congr pullback.condition r'⟩
  residue_descent u' a h := residue_descent_of_etale π u' a h
  full r u' v' hu hv := by
    obtain ⟨r', hs, ht⟩ := exists_cech_arrow π u' v' (hu.trans hv.symm)
    refine ⟨r', hs, ht, ?_⟩
    change π.base (pullback.fst π π r') = r
    rw [hs]
    exact hu

/-- **The Vistoli Chow group of the Čech groupoid of an étale cover of a scheme is the Chow group
of the scheme.** Let `U` be locally of finite type over a field `k` and `π : U' ⟶ U` étale,
surjective and quasi-compact with `U'` quasi-compact. Then the Vistoli rational Chow group
computed on the atlas `U'` (cycles invariant under `U' ×_U U'` modulo divisors of invariant
rational functions) is the rational Chow group `A_i(U)` for the canonical dimension function.
This is atlas independence for schemes; the Morita conditions are proved (`cechMorita`), not
assumed. -/
noncomputable def cechVistoliChowEquiv [CompactSpace U'] [QuasiCompact π] [Surjective π]
    (i : ℤ) :
    (cechGroupoid f π).vistoliChow i ≃ₗ[ℚ]
      (RationalEquivalenceSystem.canonical (X := U) (dimension := dimensionFunction f)
        (i := i)).ChowGroup :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace U := π.surjective.compactSpace π.continuous
  ((cechMorita f π).vistoliChowEquiv i (cechGroupoid_good f π)
      (identityGroupoid_good U _ (covByDimension_finiteTypeDimension f))).symm.trans
    (vistoliChow_identity_equiv U _ i (covByDimension_finiteTypeDimension f))

end Groupoid


end GromovWitten.AlgebraicGeometry.IntersectionTheory
