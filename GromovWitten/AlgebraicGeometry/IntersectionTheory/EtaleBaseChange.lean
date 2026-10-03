/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.CechGroupoidChow
import GromovWitten.Algebra.TensorFieldDecomposition

/-!
# Étale base change of proper pushforward

Consider a cartesian square of schemes
```
U ×_V V' --fst--> U
   |              |
  snd             f
   v              v
   V' ----g-----> V
```
with `g` étale (more generally, for the point-level statements, formally unramified and locally
of finite type). For `u : U` and `v' : V'` with `f u = g v'`, the points of `U ×_V V'` lying over
`(u, v')` are the primes of `κ(u) ⊗[κ(f u)] κ(v')` (Mathlib's `Scheme.Pullback.carrierEquiv`),
and we show that their residue fields are the residue fields of these primes. Combined with the
algebra of `GromovWitten.Algebra.TensorFieldDecomposition` (`κ(v') / κ(g v')` is finite
separable), this gives the degree formula `∑ [κ(u') : κ(v')] = [κ(u) : κ(f u)]` and the
corresponding norm formula, and hence the étale base change of the proper pushforward of cycles
(Fulton, Proposition 1.7, étale case).

All degree and norm identities hold without finiteness hypotheses on `κ(u) / κ(f u)`, with
Mathlib's conventions `finrank = 0` and `norm = 1` for infinite extensions.

## Main results

* `residueFieldMap_specTensorTo_bijective`: for a triplet `T` and a point `p` of
  `Spec (κ(x) ⊗[κ(s)] κ(y))`, the residue field map of `T.SpecTensorTo : Spec T.tensor ⟶ X ×_S Y`
  at `p` is bijective; `specTensorToResidueFieldEquiv` is the resulting ring isomorphism
  `κ(T.SpecTensorTo p) ≃+* p.asIdeal.ResidueField`.
* `isPushout_tripletTensor`: `T.tensor` is an `Algebra.IsPushout` of `κ(x)` and `κ(y)` over
  `κ(s)`; `finite_primeSpectrum_triplet`, `sum_finrank_residueField_triplet`,
  `norm_eq_prod_triplet`: the algebraic finiteness, degree and norm formulas for `T.tensor`.
* `finite_fibre_pair`, `fibrePair`: the points of `U ×_V V'` over a pair `(u, v')` form a finite
  set when `g` is formally unramified and locally of finite type.
* `sum_residueDegree_fibre`: `∑ u' ∈ fibrePair f g u v', [κ(u') : κ(v')] = [κ(u) : κ(f u)]`.
* `norm_residueFieldMap_eq_prod`, `units_map_norm_residueFieldMap_eq_prod`: the image in `κ(v')`
  of `N_{κ(u)/κ(f u)} a` is `∏ u' ∈ fibrePair f g u v', N_{κ(u')/κ(v')} a`.
* `pullbackEtale_map` (**Theorem E1**): for `f` quasi-compact (e.g. proper) and `g` étale, and
  weight functions with `dimU' = dimU ∘ fst`, `dimV' = dimV ∘ g`,
  `pullbackEtale g (map f dimU dimV z) = map (pullback.snd f g) dimU' dimV' (pullbackEtale fst z)`.
* `flatPullbackEtale_properPushforward`: the dimension-graded form, for `f` proper;
  `flatPullbackEtale_properPushforward_of_locallyOfFiniteType`: the same with the compatibility
  of the dimension functions discharged (`dimensionFunction_apply_eq_of_etale`) when `U` and `V`
  are locally of finite type over a field.
-/

open CategoryTheory AlgebraicGeometry Limits TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

section Carrier

open Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- For a point `p` of `Spec (κ(x) ⊗[κ(s)] κ(y))` with image `t := T.SpecTensorTo p` in
`X ×_S Y`, the composite `κ(x) ⊗[κ(s)] κ(y) → κ(t) → κ(p)` (canonical map `ofPointTensor`, then
the residue map of `T.SpecTensorTo` at `p`) is the residue map `κ(x) ⊗[κ(s)] κ(y) → κ(p)` of the
prime `p`, read through `Spec.residueFieldIso`. -/
theorem specTensorTo_residueFieldMap_comm (T : Triplet f g) (p : Spec T.tensor) :
    (Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom ≫
        ofPointTensor (T.SpecTensorTo p) ≫ T.SpecTensorTo.residueFieldMap p =
      CommRingCat.ofHom (algebraMap T.tensor p.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso T.tensor p).inv := by
  rw [← Spec.map_inj]
  simp only [Spec.map_comp]
  rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    ← T.Spec_ofPointTensor_SpecTensorTo p, Category.assoc]

/-- Elementwise form of `specTensorTo_residueFieldMap_comm`. -/
theorem residueFieldMap_specTensorTo_apply (T : Triplet f g) (p : Spec T.tensor)
    (a : T.tensor) :
    (T.SpecTensorTo.residueFieldMap p) (ofPointTensor (T.SpecTensorTo p)
        ((Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom a)) =
      (Scheme.Spec.residueFieldIso T.tensor p).inv (algebraMap _ _ a) := by
  have h := congrArg (fun φ ↦ φ.hom a) (specTensorTo_residueFieldMap_comm T p)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

/-- The residue map of `X ×_S Y ⟶ X` at `T.SpecTensorTo p`, followed by the residue map of
`T.SpecTensorTo` at `p`, is the map `κ(x) → κ(x) ⊗[κ(s)] κ(y) → κ(p)`. -/
theorem residueFieldMap_specTensorTo_fst_apply (T : Triplet f g) (p : Spec T.tensor)
    (a : X.residueField T.x) :
    (T.SpecTensorTo.residueFieldMap p) ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p)
        ((X.residueFieldCongr (T.fst_SpecTensorTo_apply p)).inv a)) =
      (Scheme.Spec.residueFieldIso T.tensor p).inv (algebraMap _ _ (T.tensorInl a)) := by
  rw [← residueFieldMap_specTensorTo_apply]
  exact congrArg _ (CechGroupoidChow.ofPointTensor_tensorCongr_inv_inl _ T
    (T.ofPoint_SpecTensorTo p) a).symm

/-- The residue map of `X ×_S Y ⟶ Y` at `T.SpecTensorTo p`, followed by the residue map of
`T.SpecTensorTo` at `p`, is the map `κ(y) → κ(x) ⊗[κ(s)] κ(y) → κ(p)`. -/
theorem residueFieldMap_specTensorTo_snd_apply (T : Triplet f g) (p : Spec T.tensor)
    (b : Y.residueField T.y) :
    (T.SpecTensorTo.residueFieldMap p) ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)
        ((Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).inv b)) =
      (Scheme.Spec.residueFieldIso T.tensor p).inv (algebraMap _ _ (T.tensorInr b)) := by
  rw [← residueFieldMap_specTensorTo_apply]
  exact congrArg _ (CechGroupoidChow.ofPointTensor_tensorCongr_inv_inr _ T
    (T.ofPoint_SpecTensorTo p) b).symm

/-- **Residue fields of the points of a fibre product above a triplet.** For a point `p` of
`Spec (κ(x) ⊗[κ(s)] κ(y))`, the residue field map `κ(T.SpecTensorTo p) → κ(p)` of the canonical
morphism `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×_S Y` is bijective. -/
theorem residueFieldMap_specTensorTo_bijective (T : Triplet f g) (p : Spec T.tensor) :
    Function.Bijective (T.SpecTensorTo.residueFieldMap p).hom := by
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  let c := (Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom ≫
    ofPointTensor (T.SpecTensorTo p)
  have key (a : T.tensor) : (T.SpecTensorTo.residueFieldMap p) (c a) =
      (Scheme.Spec.residueFieldIso T.tensor p).inv (algebraMap _ _ a) :=
    residueFieldMap_specTensorTo_apply T p a
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := T.tensor ⧸ p.asIdeal)
    ((Scheme.Spec.residueFieldIso T.tensor p).hom y)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨c a / c b, ?_⟩
  rw [map_div₀, key, key, ← map_div₀, ← Ideal.algebraMap_quotient_residueField_mk,
    ← Ideal.algebraMap_quotient_residueField_mk, hab]
  exact (Scheme.Spec.residueFieldIso T.tensor p).hom_inv_id_apply y

end Carrier

section TripletAlgebra

open Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The tensor product `κ(x) ⊗[κ(s)] κ(y)` of a triplet, a pushout in `CommRingCat`, is an
algebraic pushout (`Algebra.IsPushout`) for any algebra structures given by the legs and the two
inclusions. -/
theorem isPushout_tripletTensor (T : Triplet f g)
    [Algebra (S.residueField T.s) (X.residueField T.x)]
    [Algebra (S.residueField T.s) (Y.residueField T.y)] [Algebra (S.residueField T.s) T.tensor]
    [Algebra (X.residueField T.x) T.tensor] [Algebra (Y.residueField T.y) T.tensor]
    [IsScalarTower (S.residueField T.s) (X.residueField T.x) T.tensor]
    [IsScalarTower (S.residueField T.s) (Y.residueField T.y) T.tensor]
    (hX : algebraMap (S.residueField T.s) (X.residueField T.x) =
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom)
    (hY : algebraMap (S.residueField T.s) (Y.residueField T.y) =
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom)
    (hK : algebraMap (X.residueField T.x) T.tensor = T.tensorInl.hom)
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom) :
    Algebra.IsPushout (S.residueField T.s) (X.residueField T.x) (Y.residueField T.y)
      T.tensor := by
  rw [← CommRingCat.isPushout_iff_isPushout, hX, hY, hK, hL]
  simp only [CommRingCat.ofHom_hom]
  exact IsPushout.of_hasPushout _ _

variable (T : Triplet f g)
    [Algebra (S.residueField T.s) (X.residueField T.x)]
    [Algebra (S.residueField T.s) (Y.residueField T.y)] [Algebra (Y.residueField T.y) T.tensor]

/-- Under the hypotheses of `isPushout_tripletTensor`, with the `κ(x)`- and `κ(s)`-algebra
structures on `κ(x) ⊗[κ(s)] κ(y)` built from the inclusion `tensorInl`: the scalar towers and the
pushout property hold. Internal helper. -/
private theorem tensor_setup
    (hX : algebraMap (S.residueField T.s) (X.residueField T.x) =
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom)
    (hY : algebraMap (S.residueField T.s) (Y.residueField T.y) =
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom)
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom) :
    let _ : Algebra (X.residueField T.x) T.tensor := T.tensorInl.hom.toAlgebra
    let _ : Algebra (S.residueField T.s) T.tensor :=
      (T.tensorInl.hom.comp (algebraMap (S.residueField T.s) (X.residueField T.x))).toAlgebra
    ∃ (_ : IsScalarTower (S.residueField T.s) (X.residueField T.x) T.tensor)
      (_ : IsScalarTower (S.residueField T.s) (Y.residueField T.y) T.tensor),
      Algebra.IsPushout (S.residueField T.s) (X.residueField T.x) (Y.residueField T.y)
        T.tensor := by
  intro _ _
  have h1 : IsScalarTower (S.residueField T.s) (X.residueField T.x) T.tensor :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h2 : IsScalarTower (S.residueField T.s) (Y.residueField T.y) T.tensor :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change T.tensorInl (algebraMap _ (X.residueField T.x) c) = _
      rw [hX, hY, hL]
      exact congrArg (fun φ ↦ φ.hom c) (pushout.condition (f :=
        (S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) (g :=
        (S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  exact ⟨h1, h2, isPushout_tripletTensor T hX hY rfl hL⟩

variable
    (hX : algebraMap (S.residueField T.s) (X.residueField T.x) =
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom)
    (hY : algebraMap (S.residueField T.s) (Y.residueField T.y) =
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom)
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom)

include hX hY hL in
/-- If `κ(y) / κ(s)` is finite, then `κ(x) ⊗[κ(s)] κ(y)` has finitely many primes. -/
theorem finite_primeSpectrum_triplet
    [Module.Finite (S.residueField T.s) (Y.residueField T.y)] :
    Finite (PrimeSpectrum T.tensor) := by
  let _ : Algebra (X.residueField T.x) T.tensor := T.tensorInl.hom.toAlgebra
  let _ : Algebra (S.residueField T.s) T.tensor :=
    (T.tensorInl.hom.comp (algebraMap (S.residueField T.s) (X.residueField T.x))).toAlgebra
  obtain ⟨_, _, _⟩ := tensor_setup T hX hY hL
  exact GromovWitten.Algebra.finite_primeSpectrum_tensor (S.residueField T.s) (X.residueField T.x)
    (Y.residueField T.y) T.tensor

include hX hY hL in
/-- **Degree formula for a triplet.** If `κ(y) / κ(s)` is finite separable, then
`∑ p, [κ(p) : κ(y)] = [κ(x) : κ(s)]`, the sum running over the primes of
`κ(x) ⊗[κ(s)] κ(y)` (with Mathlib's convention `finrank = 0` for infinite extensions). -/
theorem sum_finrank_residueField_triplet
    [Algebra.IsSeparable (S.residueField T.s) (Y.residueField T.y)]
    [Module.Finite (S.residueField T.s) (Y.residueField T.y)] [Fintype (PrimeSpectrum T.tensor)] :
    ∑ p : PrimeSpectrum T.tensor, Module.finrank (Y.residueField T.y) p.asIdeal.ResidueField =
      Module.finrank (S.residueField T.s) (X.residueField T.x) := by
  let _ : Algebra (X.residueField T.x) T.tensor := T.tensorInl.hom.toAlgebra
  let _ : Algebra (S.residueField T.s) T.tensor :=
    (T.tensorInl.hom.comp (algebraMap (S.residueField T.s) (X.residueField T.x))).toAlgebra
  obtain ⟨_, _, _⟩ := tensor_setup T hX hY hL
  exact GromovWitten.Algebra.finrank_sum_residueField' (S.residueField T.s) (X.residueField T.x)
    (Y.residueField T.y) T.tensor

include hX hY hL in
/-- **Norm formula for a triplet.** If `κ(y) / κ(s)` is finite separable, then for `a : κ(x)`,
the image in `κ(y)` of `N_{κ(x)/κ(s)} a` is the product over the primes `p` of
`κ(x) ⊗[κ(s)] κ(y)` of `N_{κ(p)/κ(y)}` of the image of `a` (with Mathlib's convention
`norm = 1` for infinite extensions). -/
theorem norm_eq_prod_triplet
    [Algebra.IsSeparable (S.residueField T.s) (Y.residueField T.y)]
    [Module.Finite (S.residueField T.s) (Y.residueField T.y)] [Fintype (PrimeSpectrum T.tensor)]
    (a : X.residueField T.x) :
    algebraMap (S.residueField T.s) (Y.residueField T.y)
        (Algebra.norm (S.residueField T.s) a) =
      ∏ p : PrimeSpectrum T.tensor, Algebra.norm (Y.residueField T.y)
        (algebraMap T.tensor p.asIdeal.ResidueField (T.tensorInl a)) := by
  let _ : Algebra (X.residueField T.x) T.tensor := T.tensorInl.hom.toAlgebra
  let _ : Algebra (S.residueField T.s) T.tensor :=
    (T.tensorInl.hom.comp (algebraMap (S.residueField T.s) (X.residueField T.x))).toAlgebra
  obtain ⟨_, _, _⟩ := tensor_setup T hX hY hL
  exact GromovWitten.Algebra.norm_tensor_eq_prod' (S.residueField T.s) (X.residueField T.x)
    (Y.residueField T.y) T.tensor a

end TripletAlgebra

section PointDegree

open Scheme.Pullback

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The ring isomorphism `κ(T.SpecTensorTo p) ≃+* κ(p)` between the residue field of the image
in `X ×_S Y` of a point `p` of `Spec (κ(x) ⊗[κ(s)] κ(y))` and the residue field
`p.asIdeal.ResidueField`. -/
noncomputable def specTensorToResidueFieldEquiv (T : Triplet f g) (p : Spec T.tensor) :
    (pullback f g).residueField (T.SpecTensorTo p) ≃+* p.asIdeal.ResidueField :=
  (RingEquiv.ofBijective _ (residueFieldMap_specTensorTo_bijective T p)).trans
    (Scheme.Spec.residueFieldIso T.tensor p).commRingCatIsoToRingEquiv

/-- `specTensorToResidueFieldEquiv` sends the image of `b : κ(y)` under the residue map of the
second projection to the image of `b` in `κ(p)` (through `tensorInr`). -/
theorem specTensorToResidueFieldEquiv_snd (T : Triplet f g) (p : Spec T.tensor)
    [Algebra (Y.residueField T.y) T.tensor]
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom)
    (b : Y.residueField T.y) :
    specTensorToResidueFieldEquiv T p ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)
        ((Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).inv b)) =
      algebraMap (Y.residueField T.y) p.asIdeal.ResidueField b := by
  change (Scheme.Spec.residueFieldIso T.tensor p).hom (T.SpecTensorTo.residueFieldMap p _) = _
  rw [residueFieldMap_specTensorTo_snd_apply]
  refine ((Scheme.Spec.residueFieldIso T.tensor p).inv_hom_id_apply _).trans ?_
  rw [IsScalarTower.algebraMap_apply (Y.residueField T.y) T.tensor p.asIdeal.ResidueField b, hL]

/-- `specTensorToResidueFieldEquiv` sends the image of `a : κ(x)` under the residue map of the
first projection to the image of `a ⊗ 1` in `κ(p)`. -/
theorem specTensorToResidueFieldEquiv_fst (T : Triplet f g) (p : Spec T.tensor)
    (a : X.residueField T.x) :
    specTensorToResidueFieldEquiv T p ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p)
        ((X.residueFieldCongr (T.fst_SpecTensorTo_apply p)).inv a)) =
      algebraMap T.tensor p.asIdeal.ResidueField (T.tensorInl a) := by
  change (Scheme.Spec.residueFieldIso T.tensor p).hom (T.SpecTensorTo.residueFieldMap p _) = _
  rw [residueFieldMap_specTensorTo_fst_apply]
  exact (Scheme.Spec.residueFieldIso T.tensor p).inv_hom_id_apply _

/-- Compatibility of `specTensorToResidueFieldEquiv` with the `κ(y)`-algebra structures on both
sides (through the residue map of the second projection, resp. through `tensorInr`). -/
theorem specTensorToResidueFieldEquiv_comp (T : Triplet f g) (p : Spec T.tensor)
    [Algebra (Y.residueField T.y) T.tensor]
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom) :
    let _ := ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom.toAlgebra
    (algebraMap (Y.residueField T.y) p.asIdeal.ResidueField).comp
        (Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).commRingCatIsoToRingEquiv.toRingHom =
      (specTensorToResidueFieldEquiv T p).toRingHom.comp
        (algebraMap _ ((pullback f g).residueField (T.SpecTensorTo p))) := by
  intro _
  ext b
  obtain ⟨b, rfl⟩ : ∃ b', b = (Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).inv b' :=
    ⟨_, ((Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).hom_inv_id_apply b).symm⟩
  change algebraMap (Y.residueField T.y) p.asIdeal.ResidueField
      ((Y.residueFieldCongr _).hom ((Y.residueFieldCongr _).inv b)) =
    specTensorToResidueFieldEquiv T p ((pullback.snd f g).residueFieldMap _ _)
  rw [specTensorToResidueFieldEquiv_snd T p hL, Iso.inv_hom_id_apply]

/-- The residue degree of `X ×_S Y ⟶ Y` at the point `T.SpecTensorTo p` is the degree of
`κ(p)` over `κ(y)`. -/
theorem residueDegree_snd_specTensorTo (T : Triplet f g) (p : Spec T.tensor)
    [Algebra (Y.residueField T.y) T.tensor]
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom) :
    (pullback.snd f g).residueDegree (T.SpecTensorTo p) =
      Module.finrank (Y.residueField T.y) p.asIdeal.ResidueField := by
  let _ := ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv _ _ (specTensorToResidueFieldEquiv_comp T p hL)

/-- The norm form of `residueDegree_snd_specTensorTo`: for `a : κ(x)`, the norm from
`κ(T.SpecTensorTo p)` down to `κ(y)` of the image of `a` is the norm from `κ(p)` down to `κ(y)`
of the image of `a ⊗ 1`. -/
theorem norm_snd_specTensorTo (T : Triplet f g) (p : Spec T.tensor)
    [Algebra (Y.residueField T.y) T.tensor]
    (hL : algebraMap (Y.residueField T.y) T.tensor = T.tensorInr.hom) (a : X.residueField T.x) :
    letI := ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom.toAlgebra
    (Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).hom
        (Algebra.norm (Y.residueField (pullback.snd f g (T.SpecTensorTo p)))
          ((pullback.fst f g).residueFieldMap (T.SpecTensorTo p)
            ((X.residueFieldCongr (T.fst_SpecTensorTo_apply p)).inv a))) =
      Algebra.norm (Y.residueField T.y)
        (algebraMap T.tensor p.asIdeal.ResidueField (T.tensorInl a)) := by
  let _ := ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p)).hom.toAlgebra
  have hc := specTensorToResidueFieldEquiv_comp T p hL
  simp only [RingEquiv.toRingHom_eq_coe] at hc
  rw [Algebra.norm_eq_of_equiv_equiv _ _ hc, specTensorToResidueFieldEquiv_fst]
  exact (Y.residueFieldCongr (T.snd_SpecTensorTo_apply p)).inv_hom_id_apply _

end PointDegree

section Fibre

open Scheme.Pullback

variable {U V V' : Scheme.{u}} (f : U ⟶ V) (g : V' ⟶ V)

/-- The points of `U ×_V V'` over a pair `(u, v')` with `f u = g v'` are exactly the images of
the points of `Spec (κ(u) ⊗[κ(v)] κ(v'))`. -/
theorem fibre_pair_iff_exists_specTensorTo {u : U} {v' : V'} (h : f.base u = g.base v')
    (u' : ↑(pullback f g)) :
    (pullback.fst f g u' = u ∧ pullback.snd f g u' = v') ↔
      ∃ p, (Triplet.mk' u v' h).SpecTensorTo p = u' := by
  constructor
  · rintro ⟨h1, h2⟩
    have e : Triplet.ofPoint u' = Triplet.mk' u v' h := Triplet.ext h1 h2
    refine ⟨Spec.map (Triplet.tensorCongr e.symm).hom (SpecOfPoint u'), ?_⟩
    rw [← Scheme.Hom.comp_apply, tensorCongr_SpecTensorTo, SpecTensorTo_SpecOfPoint]
  · rintro ⟨p, rfl⟩
    exact ⟨Triplet.fst_SpecTensorTo_apply _ p, Triplet.snd_SpecTensorTo_apply _ p⟩

/-- The canonical morphism `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×_S Y` is injective on points. -/
theorem specTensorTo_injective {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triplet f g) :
    Function.Injective T.SpecTensorTo := by
  intro p q hpq
  have h' : (carrierEquiv.symm ⟨T, p⟩ : ↑(pullback f g)) = carrierEquiv.symm ⟨T, q⟩ := hpq
  have h := carrierEquiv.symm.injective h'
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

variable [FormallyUnramified g] [LocallyOfFiniteType g]

/-- **Finiteness of the fibre over a pair.** If `g` is formally unramified and locally of finite
type (e.g. étale), then for `u : U` and `v' : V'` the set of points of `U ×_V V'` lying over `u`
and over `v'` is finite. -/
theorem finite_fibre_pair (u : U) (v' : V') :
    {u' : ↑(pullback f g) | pullback.fst f g u' = u ∧ pullback.snd f g u' = v'}.Finite := by
  by_cases h : f.base u = g.base v'
  · let T := Triplet.mk' u v' h
    let _ : Algebra (V.residueField T.s) (U.residueField T.x) :=
      ((V.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
    let _ : Algebra (V.residueField T.s) (V'.residueField T.y) :=
      (g.residueFieldMap v').hom.toAlgebra
    let _ : Algebra (V'.residueField T.y) T.tensor := T.tensorInr.hom.toAlgebra
    have : Module.Finite (V.residueField T.s) (V'.residueField T.y) :=
      CechGroupoidChow.finite_residueField_of_formallyUnramified g v'
    have : Finite (Spec T.tensor) := finite_primeSpectrum_triplet T rfl (by ext; rfl) rfl
    refine (Set.finite_range (fun p : Spec T.tensor ↦ T.SpecTensorTo p)).subset ?_
    intro u' hu'
    exact (fibre_pair_iff_exists_specTensorTo f g h u').1 hu'
  · refine Set.finite_empty.subset ?_
    rintro u' ⟨h1, h2⟩
    refine h ?_
    rw [← h1, ← h2, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- The finite set of points of `U ×_V V'` lying over `u : U` and over `v' : V'`. -/
noncomputable def fibrePair (u : U) (v' : V') : Finset ↑(pullback f g) :=
  (finite_fibre_pair f g u v').toFinset

/-- Membership in `fibrePair`. -/
@[simp]
theorem mem_fibrePair {u : U} {v' : V'} {u' : ↑(pullback f g)} :
    u' ∈ fibrePair f g u v' ↔ pullback.fst f g u' = u ∧ pullback.snd f g u' = v' :=
  Set.Finite.mem_toFinset _

/-- Reindexing the points of `U ×_V V'` over `(u, v')` by the primes of
`κ(u) ⊗[κ(v)] κ(v')`. -/
private theorem sum_fibrePair_eq {M : Type*} [AddCommMonoid M] {u : U} {v' : V'}
    (h : f.base u = g.base v') [Fintype (PrimeSpectrum (Triplet.mk' u v' h).tensor)]
    (φ : ↑(pullback f g) → M) :
    ∑ u' ∈ fibrePair f g u v', φ u' =
      ∑ p : PrimeSpectrum (Triplet.mk' u v' h).tensor,
        φ ((Triplet.mk' u v' h).SpecTensorTo p) := by
  symm
  refine Finset.sum_nbij (fun p ↦ (Triplet.mk' u v' h).SpecTensorTo p) ?_ ?_ ?_ ?_
  · intro p _
    exact (mem_fibrePair f g).2 ((fibre_pair_iff_exists_specTensorTo f g h _).2 ⟨p, rfl⟩)
  · intro p _ q _ hpq
    exact specTensorTo_injective _ hpq
  · intro u' hu'
    obtain ⟨p, hp⟩ := (fibre_pair_iff_exists_specTensorTo f g h u').1 ((mem_fibrePair f g).1 hu')
    exact ⟨p, Finset.mem_coe.2 (Finset.mem_univ _), hp⟩
  · intro p _
    rfl

/-- **The degree formula (★) for étale base change.** Let `g : V' ⟶ V` be formally unramified
and locally of finite type (e.g. étale), `u : U` and `v' : V'` with `f u = g v'`. Then the
residue degrees over `v'` of the points of `U ×_V V'` lying over `(u, v')` add up to the residue
degree of `u` over `f u`: `∑ [κ(u') : κ(v')] = [κ(u) : κ(f u)]`. This holds without finiteness
hypotheses, with Mathlib's convention that the degree of an infinite extension is `0` (in that
case all the terms vanish). -/
theorem sum_residueDegree_fibre {u : U} {v' : V'} (h : f.base u = g.base v') :
    ∑ u' ∈ fibrePair f g u v', (pullback.snd f g).residueDegree u' = f.residueDegree u := by
  let T := Triplet.mk' u v' h
  let _ : Algebra (V.residueField T.s) (U.residueField T.x) :=
    ((V.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let _ : Algebra (V.residueField T.s) (V'.residueField T.y) :=
    (g.residueFieldMap v').hom.toAlgebra
  let _ : Algebra (V'.residueField T.y) T.tensor := T.tensorInr.hom.toAlgebra
  have : Module.Finite (V.residueField T.s) (V'.residueField T.y) :=
    CechGroupoidChow.finite_residueField_of_formallyUnramified g v'
  have : Algebra.IsSeparable (V.residueField T.s) (V'.residueField T.y) :=
    (inferInstance : letI := (g.residueFieldMap v').hom.toAlgebra
      Algebra.IsSeparable (V.residueField (g.base v')) (V'.residueField v'))
  have hY : algebraMap (V.residueField T.s) (V'.residueField T.y) =
      ((V.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom := by
    ext; rfl
  have : Finite (PrimeSpectrum T.tensor) := finite_primeSpectrum_triplet T rfl hY rfl
  let _ : Fintype (PrimeSpectrum T.tensor) := Fintype.ofFinite _
  have hsum : ∑ p : PrimeSpectrum T.tensor, (pullback.snd f g).residueDegree (T.SpecTensorTo p) =
      ∑ p : PrimeSpectrum T.tensor, Module.finrank (V'.residueField T.y) p.asIdeal.ResidueField :=
    Finset.sum_congr rfl fun p _ ↦ residueDegree_snd_specTensorTo T p rfl
  rw [sum_fibrePair_eq f g h]
  refine hsum.trans ?_
  rw [sum_finrank_residueField_triplet T rfl hY rfl]
  let _ := (f.residueFieldMap u).hom.toAlgebra
  symm
  refine Algebra.finrank_eq_of_equiv_equiv (V.residueFieldCongr h).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  ext c
  change (f.residueFieldMap u) ((V.residueFieldCongr h).inv ((V.residueFieldCongr h).hom c)) =
    (f.residueFieldMap u) c
  rw [Iso.hom_inv_id_apply]

/-- **Norms under étale base change.** Let `g : V' ⟶ V` be formally unramified and locally of
finite type (e.g. étale), `u : U` and `v' : V'` with `f u = g v'`. For `a : κ(u)`, the image in
`κ(v')` of the norm `N_{κ(u)/κ(f u)} a` is the product, over the points `u'` of `U ×_V V'` lying
over `(u, v')`, of the norms `N_{κ(u')/κ(v')}` of the image of `a` in `κ(u')`. All residue fields
are compared along the canonical isomorphisms `residueFieldCongr`. This holds without finiteness
hypotheses, with Mathlib's convention that the norm of an infinite extension is `1` (in that
case all the factors are `1`). -/
theorem norm_residueFieldMap_eq_prod {u : U} {v' : V'} (h : f.base u = g.base v')
    (a : U.residueField u) :
    let _ := (f.residueFieldMap u).hom.toAlgebra
    g.residueFieldMap v'
        ((V.residueFieldCongr h).hom (Algebra.norm (V.residueField (f.base u)) a)) =
      ∏ u' ∈ (fibrePair f g u v').attach,
        let _ := ((pullback.snd f g).residueFieldMap u'.1).hom.toAlgebra
        (V'.residueFieldCongr ((mem_fibrePair f g).1 u'.2).2).hom
          (Algebra.norm (V'.residueField (pullback.snd f g u'.1))
            ((pullback.fst f g).residueFieldMap u'.1
              ((U.residueFieldCongr ((mem_fibrePair f g).1 u'.2).1).inv a))) := by
  intro _
  let T := Triplet.mk' u v' h
  let _ : Algebra (V.residueField T.s) (U.residueField T.x) :=
    ((V.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let _ : Algebra (V.residueField T.s) (V'.residueField T.y) :=
    (g.residueFieldMap v').hom.toAlgebra
  let _ : Algebra (V'.residueField T.y) T.tensor := T.tensorInr.hom.toAlgebra
  have : Module.Finite (V.residueField T.s) (V'.residueField T.y) :=
    CechGroupoidChow.finite_residueField_of_formallyUnramified g v'
  have : Algebra.IsSeparable (V.residueField T.s) (V'.residueField T.y) :=
    (inferInstance : letI := (g.residueFieldMap v').hom.toAlgebra
      Algebra.IsSeparable (V.residueField (g.base v')) (V'.residueField v'))
  have hY : algebraMap (V.residueField T.s) (V'.residueField T.y) =
      ((V.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom := by
    ext; rfl
  have : Finite (PrimeSpectrum T.tensor) := finite_primeSpectrum_triplet T rfl hY rfl
  let _ : Fintype (PrimeSpectrum T.tensor) := Fintype.ofFinite _
  have hc : (algebraMap (V.residueField T.s) (U.residueField T.x)).comp
      (V.residueFieldCongr h).commRingCatIsoToRingEquiv.toRingHom =
      (RingEquiv.refl (U.residueField u)).toRingHom.comp
        (algebraMap (V.residueField (f.base u)) (U.residueField u)) := by
    ext c
    change (f.residueFieldMap u) ((V.residueFieldCongr h).inv ((V.residueFieldCongr h).hom c)) =
      (f.residueFieldMap u) c
    rw [Iso.hom_inv_id_apply]
  simp only [RingEquiv.toRingHom_eq_coe] at hc
  have h1 : (V.residueFieldCongr h).hom (Algebra.norm (V.residueField (f.base u)) a) =
      Algebra.norm (S := U.residueField T.x) (V.residueField T.s) a := by
    rw [Algebra.norm_eq_of_equiv_equiv _ _ hc a]
    exact (V.residueFieldCongr h).inv_hom_id_apply _
  rw [h1]
  change algebraMap (V.residueField T.s) (V'.residueField T.y)
    (Algebra.norm (S := U.residueField T.x) (V.residueField T.s) a) = _
  rw [norm_eq_prod_triplet T rfl hY rfl a]
  refine Finset.prod_nbij (fun p ↦ ⟨T.SpecTensorTo p,
    (mem_fibrePair f g).2 ((fibre_pair_iff_exists_specTensorTo f g h _).2 ⟨p, rfl⟩)⟩)
    (fun _ _ ↦ Finset.mem_attach _ _) ?_ ?_ ?_
  · intro p _ q _ hpq
    exact specTensorTo_injective _ (congrArg Subtype.val hpq)
  · rintro ⟨u', hu'⟩ -
    obtain ⟨p, hp⟩ := (fibre_pair_iff_exists_specTensorTo f g h u').1 ((mem_fibrePair f g).1 hu')
    exact ⟨p, Finset.mem_coe.2 (Finset.mem_univ _), Subtype.ext hp⟩
  · intro p _
    exact (norm_snd_specTensorTo T p rfl a).symm

/-- The units form of `norm_residueFieldMap_eq_prod`: the same identity for `a : κ(u)ˣ`, with
norms and residue maps acting on units through `Units.map`. -/
theorem units_map_norm_residueFieldMap_eq_prod {u : U} {v' : V'} (h : f.base u = g.base v')
    (a : (U.residueField u)ˣ) :
    let _ := (f.residueFieldMap u).hom.toAlgebra
    Units.map ((g.residueFieldMap v').hom.comp (V.residueFieldCongr h).hom.hom).toMonoidHom
        (Units.map (Algebra.norm (V.residueField (f.base u))) a) =
      ∏ u' ∈ (fibrePair f g u v').attach,
        let _ := ((pullback.snd f g).residueFieldMap u'.1).hom.toAlgebra
        Units.map
          (((V'.residueFieldCongr ((mem_fibrePair f g).1 u'.2).2).hom.hom).toMonoidHom.comp
            (Algebra.norm (V'.residueField (pullback.snd f g u'.1))))
          (Units.map (((pullback.fst f g).residueFieldMap u'.1).hom.comp
              (U.residueFieldCongr ((mem_fibrePair f g).1 u'.2).1).inv.hom).toMonoidHom a) := by
  intro _
  ext
  simp only [Units.coe_prod, Units.coe_map]
  exact norm_residueFieldMap_eq_prod f g h (a : U.residueField u)

end Fibre

section BaseChange

variable {U V V' : Scheme.{u}}

/-- For a quasi-compact morphism `f : U ⟶ V`, the support of a cycle on `U` meets each fibre of
`f` in a finite set. -/
theorem finite_fibre_inter_support (f : U ⟶ V) [QuasiCompact f] (z : AlgebraicCycle U ℚ)
    (v : V) : (f.base ⁻¹' {v} ∩ Function.support z).Finite := by
  obtain ⟨W, hW⟩ := (PrespectralSpace.isTopologicalBasis (X := V)).exists_subset_of_mem_open
    (Set.mem_univ v) isOpen_univ
  refine (z.locallyFiniteSupport.finite_inter_support_of_isCompact
    (f.isSpectralMap.2 hW.1.1 hW.1.2)).subset ?_
  exact Set.inter_subset_inter_left _ (Set.preimage_mono (Set.singleton_subset_iff.2 hW.2.1))

variable (f : U ⟶ V) (g : V' ⟶ V)

/-- **Étale base change of proper pushforward of cycles (Theorem E1).** For a cartesian square
`U ×_V V' ⟶ U`, `U ×_V V' ⟶ V'` with `f : U ⟶ V` quasi-compact (e.g. proper) and `g : V' ⟶ V`
étale, and weight functions with `dimU' = dimU ∘ fst` and `dimV' = dimV ∘ g`, pulling back along
`g` the pushforward along `f` equals pushing forward along the second projection the pullback
along the first projection:
`g^* (f_* z) = (pullback.snd f g)_* ((pullback.fst f g)^* z)`. -/
theorem pullbackEtale_map [QuasiCompact f] [Etale g] (dimU : U → ℤ) (dimV : V → ℤ)
    (dimU' : ↑(pullback f g) → ℤ) (dimV' : V' → ℤ)
    (hU' : ∀ u', dimU' u' = dimU (pullback.fst f g u')) (hV' : ∀ v', dimV' v' = dimV (g.base v'))
    (z : AlgebraicCycle U ℚ) :
    AlgebraicCycle.pullbackEtale g (AlgebraicCycle.map f dimU dimV z) =
      AlgebraicCycle.map (pullback.snd f g) dimU' dimV'
        (AlgebraicCycle.pullbackEtale (pullback.fst f g) z) := by
  classical
  ext v'
  rw [AlgebraicCycle.pullbackEtale_apply]
  change (∑ᶠ u ∈ f.base ⁻¹' {g.base v'}, z u * (AlgebraicCycle.mapCoeff f dimU dimV u : ℚ)) =
    ∑ᶠ u' ∈ (pullback.snd f g).base ⁻¹' {v'},
      z (pullback.fst f g u') * (AlgebraicCycle.mapCoeff (pullback.snd f g) dimU' dimV' u' : ℚ)
  have hS := finite_fibre_inter_support f z (g.base v')
  have hfib (u' : ↑(pullback f g)) (hu' : pullback.snd f g u' = v') :
      f.base (pullback.fst f g u') = g.base v' := by
    rw [← hu', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [finsum_mem_eq_sum_of_subset _ (t := hS.toFinset) ?_ ?_,
    finsum_mem_eq_sum_of_subset _ (t := hS.toFinset.biUnion fun u ↦ fibrePair f g u v') ?_ ?_,
    Finset.sum_biUnion ?_]
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu : f.base u = g.base v' := ((Set.Finite.mem_toFinset _).1 hu).1
    have hterm : ∀ u' ∈ fibrePair f g u v',
        z (pullback.fst f g u') *
            (AlgebraicCycle.mapCoeff (pullback.snd f g) dimU' dimV' u' : ℚ) =
          z u * ((if dimU u = dimV (f.base u) then
            (pullback.snd f g).residueDegree u' else 0 : ℕ) : ℚ) := by
      intro u' hu'
      obtain ⟨h1, h2⟩ := (mem_fibrePair f g).1 hu'
      simp only [AlgebraicCycle.mapCoeff, hU', hV', h1, h2, hu]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum]
    congr 2
    simp only [AlgebraicCycle.mapCoeff]
    split_ifs
    · exact (sum_residueDegree_fibre f g hu).symm
    · simp
  · intro u _ w _ huw
    refine Finset.disjoint_left.2 fun u' h1 h2 ↦ huw ?_
    exact ((mem_fibrePair f g).1 h1).1.symm.trans ((mem_fibrePair f g).1 h2).1
  · rintro u' ⟨hu', hne⟩
    have hz : z (pullback.fst f g u') ≠ 0 := left_ne_zero_of_mul hne
    refine Finset.mem_biUnion.2 ⟨pullback.fst f g u', ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset _).2 ⟨hfib u' hu', hz⟩
    · exact (mem_fibrePair f g).2 ⟨rfl, hu'⟩
  · intro u' hu'
    obtain ⟨u, -, hu'⟩ := Finset.mem_biUnion.1 hu'
    exact ((mem_fibrePair f g).1 hu').2
  · rintro u ⟨hu, hne⟩
    exact (Set.Finite.mem_toFinset _).2 ⟨hu, left_ne_zero_of_mul hne⟩
  · intro u hu
    exact ((Set.Finite.mem_toFinset _).1 hu).1

/-- **Étale base change of the graded proper pushforward.** For `f` proper and `g` étale, with
dimension functions on `U ×_V V'` and `V'` pulled back from those of `U` and `V`,
`g^* ∘ f_* = (pullback.snd f g)_* ∘ (pullback.fst f g)^*` on `cyclesOfDimension U dimU i`. -/
theorem flatPullbackEtale_properPushforward [IsProper f] [Etale g]
    {dimU : DimensionFunction U} {dimV : DimensionFunction V}
    {dimU' : DimensionFunction (pullback f g)} {dimV' : DimensionFunction V'} {i : ℤ}
    (hU' : ∀ u', dimU' u' = dimU (pullback.fst f g u')) (hV' : ∀ v', dimV' v' = dimV (g.base v'))
    (c : cyclesOfDimension U dimU i) :
    cyclesOfDimension.flatPullbackEtale g hV'
        (cyclesOfDimension.properPushforward (dimensionY := dimV) f c) =
      cyclesOfDimension.properPushforward (dimensionY := dimV') (pullback.snd f g)
        (cyclesOfDimension.flatPullbackEtale (pullback.fst f g) hU' c) :=
  Subtype.ext (pullbackEtale_map f g dimU dimV dimU' dimV' hU' hV' c.1)

/-- Any two dimension functions on a scheme agree (both are the order-theoretic height). A local
copy of `dimensionFunction_eq` from `ProperPushforwardDivisor.lean`, to keep imports light. -/
private theorem dimensionFunction_eq_aux {X : Scheme.{u}} (d e : DimensionFunction X) :
    d = e := by
  refine DimensionFunction.ext fun x ↦ ?_
  have h : (Int.toNat (d x) : ℕ∞) = (Int.toNat (e x) : ℕ∞) := by
    rw [← d.height_eq, ← e.height_eq]
  have h' : Int.toNat (d x) = Int.toNat (e x) := by exact_mod_cast h
  have := d.nonnegative x
  have := e.nonnegative x
  omega

/-- Along an étale morphism `g : Y ⟶ X` with `X` locally of finite type over a field, any two
dimension functions on `Y` and `X` satisfy `dimY = dimX ∘ g` (both are the canonical
transcendence-degree dimension functions). -/
theorem dimensionFunction_apply_eq_of_etale {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] (g : Y ⟶ X) [Etale g]
    (dimY : DimensionFunction Y) (dimX : DimensionFunction X) (y : Y) :
    dimY y = dimX (g.base y) := by
  rw [dimensionFunction_eq_aux dimY (FiniteTypeDimension.dimensionFunction (g ≫ sX)),
    dimensionFunction_eq_aux dimX (FiniteTypeDimension.dimensionFunction sX)]
  exact CechGroupoidChow.dimensionFunction_comp_etale sX g y

/-- **Étale base change of the graded proper pushforward, canonical dimension functions.** If `U`
and `V` are locally of finite type over a field `k`, `f` is proper and `g` étale, then for any
dimension functions (necessarily the canonical ones) the compatibility hypotheses of
`flatPullbackEtale_properPushforward` hold automatically. -/
theorem flatPullbackEtale_properPushforward_of_locallyOfFiniteType {k : Type u} [Field k]
    (sU : U ⟶ Spec (CommRingCat.of k)) (sV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sU] [LocallyOfFiniteType sV] [IsProper f] [Etale g]
    (dimU : DimensionFunction U) (dimV : DimensionFunction V)
    (dimU' : DimensionFunction (pullback f g)) (dimV' : DimensionFunction V') {i : ℤ}
    (c : cyclesOfDimension U dimU i) :
    cyclesOfDimension.flatPullbackEtale g
        (dimensionFunction_apply_eq_of_etale sV g dimV' dimV)
        (cyclesOfDimension.properPushforward (dimensionY := dimV) f c) =
      cyclesOfDimension.properPushforward (dimensionY := dimV') (pullback.snd f g)
        (cyclesOfDimension.flatPullbackEtale (pullback.fst f g)
          (dimensionFunction_apply_eq_of_etale sU (pullback.fst f g) dimU' dimU) c) :=
  flatPullbackEtale_properPushforward f g _ _ c

end BaseChange

end GromovWitten.AlgebraicGeometry.IntersectionTheory
