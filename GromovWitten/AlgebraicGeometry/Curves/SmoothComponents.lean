/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.IrreducibleNeighborhoods
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Components at smooth points

A smooth scheme over a field has local étale charts over affine space. Combining those charts
with normalization gives integral open neighbourhoods. Thus a smooth point of a nodal curve
lies on a unique irreducible component, and every edge of its geometric graph is an actual
nonsmooth point.
-/

open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves

universe u
noncomputable section

variable {K : Type u} [Field K]

lemma exists_smooth_etale_affine_chart
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    ∃ (R : Type u) (_ : Field R) (n : ℕ)
      (Y : Scheme.{u}) (y : Y) (j : Y ⟶ X)
      (g : Y ⟶ Spec (.of (MvPolynomial (Fin n) R))),
      IsNoetherian Y ∧ IsOpenImmersion j ∧ j y = x ∧ Etale g := by
  let B : Scheme := Spec (.of K)
  let T : B.Opens := ⊤
  let hT : IsAffineOpen T := isAffineOpen_top B
  let R : Type u := Γ(B, T)
  let _ : CommRing R := inferInstance
  let _ : IsField R :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv).isField
      (Field.toIsField K)
  let _ : Field R := ‹IsField R›.toField
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq x
  let a := X.affineCover.f i
  let W : X.Opens := a.opensRange
  let hW : IsAffineOpen W := isAffineOpen_opensRange a
  let yW : W := ⟨x, ⟨z, hz⟩⟩
  let eW : W ≤ f ⁻¹ᵁ T := by simp [T]
  let φ : R →+* Γ(X, W) := (f.appLE T W eW).hom
  let _ : Algebra R Γ(X, W) := φ.toAlgebra
  have hφ : φ.Smooth := by
    exact f.smooth_appLE hT hW eW
  let _ : Algebra.Smooth R Γ(X, W) := by
    rw [← RingHom.smooth_algebraMap]
    exact hφ
  have hφfp : Algebra.FinitePresentation R Γ(X, W) := hφ.finitePresentation
  let S := Γ(X, W)
  let p : Ideal S := (hW.primeIdealOf yW).asIdeal
  let _ : p.IsPrime := (hW.primeIdealOf yW).isPrime
  obtain ⟨s, hs, n, _x, hst, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
      (R := R) (S := S) (p := p)
  let L := Localization.Away s
  let q : PrimeSpectrum S := hW.primeIdealOf yW
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S L)) := by
    rw [PrimeSpectrum.localization_away_comap_range L s]
    exact (PrimeSpectrum.mem_basicOpen s q).2 (by simpa [p] using hs)
  obtain ⟨y', hy'⟩ := hq
  let Y : Scheme := Spec (.of L)
  let m : Y ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S L))
  let j : Y ⟶ X := m ≫ hW.fromSpec
  let g : Y ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial (Fin n) R) L))
  let _ : IsNoetherianRing S := by
    let _ : Algebra.FinitePresentation R S := hφfp
    let _ : Algebra.FiniteType R S := inferInstance
    exact Algebra.FiniteType.isNoetherianRing R S
  let _ : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Submonoid.powers s) L inferInstance
  let _ : IsNoetherian Y := inferInstance
  let _ : IsOpenImmersion m := by infer_instance
  let _ : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  let _ : IsOpenImmersion j := by infer_instance
  let _ : Algebra.IsStandardEtale (MvPolynomial (Fin n) R) L := hstd
  let _ : Etale g := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)
      (Q := @RingHom.Etale)).2
    change (algebraMap (MvPolynomial (Fin n) R) L).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  have hj : j y' = x := by
    change hW.fromSpec (m y') = x
    have hm : m y' = q := by
      change PrimeSpectrum.comap (algebraMap S L) y' = q
      exact hy'
    rw [hm, hW.fromSpec_primeIdealOf]
  refine ⟨R, inferInstance, n, Y, y', j, g, ?_⟩
  exact ⟨inferInstance, inferInstance, hj, inferInstance⟩

end
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {K : Type u} [Field K]

lemma exists_integral_openImmersion_of_smooth
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsIntegral Z ∧ IsOpenImmersion j ∧
      ∃ z : Z, j z = x := by
  obtain ⟨R, hR, n, Y, y, j, g, hY, hj, hy, hg⟩ :=
    exists_smooth_etale_affine_chart f x
  let _ := hR
  let _ := hY
  let _ := hj
  let _ := hg
  obtain ⟨Z, k, hZ, hk, z, hz⟩ :=
    exists_integral_openImmersion_of_etale_affineSpace R n g y
  let _ := hk
  exact ⟨Z, k ≫ j, hZ, inferInstance, z, by simp [hz, hy]⟩

lemma components_eq_of_smoothChart {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {x : X} (c : SmoothChartAt f x)
    {C D : Component X} (hxC : x ∈ (C : Set X)) (hxD : x ∈ (D : Set X)) : C = D := by
  let _ : Smooth (c.toCurve ≫ f) := c.smooth_toBase
  let _ : Etale c.toCurve := c.etale_toCurve
  obtain ⟨Y, j, hY, hj, y, hy⟩ :=
    exists_integral_openImmersion_of_smooth (c.toCurve ≫ f) c.point
  let _ := hY
  let _ := hj
  let g := j ≫ c.toCurve
  have hg : g y = x := by simp [g, hy, c.mapsToPoint]
  exact components_eq_of_irreducible_open_map g g.isOpenMap y
    (hg.symm ▸ hxC) (hg.symm ▸ hxD)

lemma edgePoint_mem_nodeSet {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (e : Edge f) :
    edgePoint f e ∈ nodeSet f := by
  cases e with
  | inl e => exact e.property.1
  | inr e =>
    intro hsm
    obtain ⟨c⟩ := hsm
    have heq := components_eq_of_smoothChart c
      (e.property.2 _ (Sym2.out_fst_mem e.val.2))
      (e.property.2 _ (Sym2.out_snd_mem e.val.2))
    apply e.property.1
    rw [← Quot.out_eq e.val.2]
    exact Sym2.mk_isDiag_iff.mpr heq

end
end GromovWitten.AlgebraicGeometry.Curves
