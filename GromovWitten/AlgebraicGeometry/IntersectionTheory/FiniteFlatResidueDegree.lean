/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteFlatCycleOperations
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Residue degrees of affine finite maps

For the affine finite map induced by `R → S`, the residue degree occurring in
scheme-theoretic proper pushforward is the `Ideal.inertiaDeg` used by the
ramification formula.  The comparison is made from the actual residue-field
map of `Spec.map`, via `Scheme.Spec.residueFieldIso`; no residue-degree
hypothesis is supplied by a caller.

For a finite flat algebra over a domain, the ramification/inertia sum over
the actual scheme fibre then proves the dimension-graded push-pull formula:
proper pushforward after finite-flat pullback is multiplication by the rank.
This is a cycle-level theorem; descent to rational equivalence is separate.
-/

open CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry
open _root_.AlgebraicGeometry

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace AlgebraicCycle

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private lemma residue_square (q : Spec (CommRingCat.of S)) :
    letI : q.asIdeal.IsPrime := q.isPrime
    letI : (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.IsPrime :=
      (PrimeSpectrum.comap (algebraMap R S) q).isPrime
    CommRingCat.ofHom (algebraMap R
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of R)
        (PrimeSpectrum.comap (algebraMap R S) q)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom =
    CommRingCat.ofHom (algebraMap R S) ≫
      CommRingCat.ofHom (algebraMap S q.asIdeal.ResidueField) := by
  let : q.asIdeal.IsPrime := q.isPrime
  let : (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.IsPrime :=
    (PrimeSpectrum.comap (algebraMap R S) q).isPrime
  set_option backward.isDefEq.respectTransparency false in
  erw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc (CommRingCat.of R)
    (PrimeSpectrum.comap (algebraMap R S) q)]
  erw [Scheme.germ_residue_assoc]
  erw [Scheme.Γevaluation_naturality_assoc
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) q]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  have hs : (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
      (Spec (CommRingCat.of S)).Γevaluation q ≫
      (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom =
      CommRingCat.ofHom (algebraMap S q.asIdeal.ResidueField) := by
    simpa only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom)
        (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of S) q).symm
  rw [hs]

/-- The degree used by scheme pushforward is the actual residue-field inertia degree. -/
theorem specFiniteMap_residueDegree_eq_inertiaDeg
    [Module.Finite R S] (q : Spec (CommRingCat.of S)) :
    (specFiniteMap (R := R) (S := S)).residueDegree q =
      q.asIdeal.inertiaDeg R := by
  let f := specFiniteMap (R := R) (S := S)
  let p : Spec (CommRingCat.of R) :=
    PrimeSpectrum.comap (algebraMap R S) q
  let : q.asIdeal.IsPrime := q.isPrime
  let : p.asIdeal.IsPrime := p.isPrime
  have hp : p.asIdeal = q.asIdeal.comap (algebraMap R S) := by
    rfl
  have hLie : q.asIdeal.LiesOver p.asIdeal := by
    rw [hp]
    exact ⟨rfl⟩
  let : q.asIdeal.LiesOver p.asIdeal := hLie
  let : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  let : Algebra ((Spec (CommRingCat.of R)).residueField p)
      ((Spec (CommRingCat.of S)).residueField q) :=
    (f.residueFieldMap q).hom.toAlgebra
  let i := (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv
  let j := (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).commRingCatIsoToRingEquiv
  have hmap :
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField =
        (j.toRingHom.comp (algebraMap ((Spec (CommRingCat.of R)).residueField p)
          ((Spec (CommRingCat.of S)).residueField q))).comp i.symm.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ p.asIdeal)
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.algebraMap_quotient_residueField_mk]
    have hs := residue_square (R := R) (S := S) q
    have hs' := congrArg CommRingCat.Hom.hom hs
    have hsx := congrArg (fun h ↦ h x) hs'
    change
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField
          (algebraMap R p.asIdeal.ResidueField x) =
        (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom
          ((f.residueFieldMap q).hom
            ((Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv
              (algebraMap R p.asIdeal.ResidueField x)))
    rw [← IsScalarTower.algebraMap_apply R
      ((p : PrimeSpectrum R).asIdeal.ResidueField)
      ((q : PrimeSpectrum S).asIdeal.ResidueField) x]
    have hscalar :
        algebraMap R ((q : PrimeSpectrum S).asIdeal.ResidueField) x =
          algebraMap S ((q : PrimeSpectrum S).asIdeal.ResidueField)
            ((algebraMap R S) x) := by
      exact IsScalarTower.algebraMap_apply R S
        ((q : PrimeSpectrum S).asIdeal.ResidueField) x
    rw [hscalar]
    change
      algebraMap S ((q : PrimeSpectrum S).asIdeal.ResidueField) ((algebraMap R S) x) =
        (CommRingCat.Hom.hom
          ((f.residueFieldMap q) ≫
            (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom))
          ((CommRingCat.Hom.hom
            (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv)
            (algebraMap R p.asIdeal.ResidueField x))
    have hsx' := hsx.symm
    change
      algebraMap S ((q : PrimeSpectrum S).asIdeal.ResidueField)
          ((algebraMap R S) x) =
        ((CommRingCat.Hom.hom
            (Scheme.Spec.residueFieldIso (CommRingCat.of S) q).hom).comp
          (CommRingCat.Hom.hom (f.residueFieldMap q)))
          ((CommRingCat.Hom.hom
            (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv)
            (algebraMap R p.asIdeal.ResidueField x)) at hsx'
    exact hsx'
  have hc :
      (algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField).comp i.toRingHom =
        j.toRingHom.comp (algebraMap ((Spec (CommRingCat.of R)).residueField p)
          ((Spec (CommRingCat.of S)).residueField q)) := by
    apply RingHom.ext
    intro z
    have hz := congrArg
      (fun h : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField ↦ h (i z)) hmap
    simpa [Function.comp_apply] using hz
  unfold Scheme.Hom.residueDegree
  rw [Ideal.inertiaDeg_eq p.asIdeal q.asIdeal]
  change Module.finrank ((Spec (CommRingCat.of R)).residueField p)
      ((Spec (CommRingCat.of S)).residueField q) = _
  exact Algebra.finrank_eq_of_equiv_equiv i j hc

end AlgebraicCycle

namespace cyclesOfDimension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [Module.Finite R S] [Module.Flat R S]

private lemma affine_fibre_sum (p : PrimeSpectrum R) :
    (∑ᶠ q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p},
      (q.asIdeal.ramificationIdx R : ℚ) * (q.asIdeal.inertiaDeg R : ℚ)) =
      (Module.finrank R S : ℚ) := by
  classical
  let : p.asIdeal.IsPrime := p.isPrime
  let : Fintype (p.asIdeal.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver p.asIdeal).fintype
  let e : (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ≃
      p.asIdeal.primesOver S :=
    { toFun := fun q => ⟨q.1.asIdeal, q.1.isPrime,
        ⟨(congrArg PrimeSpectrum.asIdeal q.2).symm⟩⟩
      invFun := fun q => ⟨⟨q.1, q.2.1⟩, PrimeSpectrum.ext q.2.2.1.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← finsum_set_coe_eq_finsum_mem]
  change (∑ᶠ q, ((e q).1.ramificationIdx R : ℚ) *
    ((e q).1.inertiaDeg R : ℚ)) = _
  rw [finsum_comp_equiv e (f := fun q : p.asIdeal.primesOver S =>
    (q.1.ramificationIdx R : ℚ) * (q.1.inertiaDeg R : ℚ)),
    finsum_eq_sum_of_fintype]
  exact_mod_cast Ideal.sum_ramification_inertia_eq_finrank p.asIdeal S

set_option backward.isDefEq.respectTransparency false in
/-- Finite-flat pullback followed by proper pushforward multiplies a graded cycle by the rank. -/
theorem properPushforward_finiteFlatPullback
    (dimensionR : DimensionFunction (Spec (CommRingCat.of R)))
    (dimensionS : DimensionFunction (Spec (CommRingCat.of S))) (i : ℤ)
    (c : cyclesOfDimension (Spec (CommRingCat.of R)) dimensionR i) :
    properPushforward (dimension := dimensionS) (dimensionY := dimensionR)
        (i := i) (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
        (AlgebraicCycle.finiteFlatPullback dimensionR dimensionS i c) =
      (Module.finrank R S : ℚ) • c := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext p
  change PrimeSpectrum R at p
  change
    ((properPushforward (dimension := dimensionS) (dimensionY := dimensionR)
      (i := i) (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
      (AlgebraicCycle.finiteFlatPullback dimensionR dimensionS i c) :
        AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) p) =
      (((Module.finrank R S : ℚ) • c :
        cyclesOfDimension (Spec (CommRingCat.of R)) dimensionR i) :
        AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) p
  rw [properPushforward_apply]
  change (∑ᶠ q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {(p : PrimeSpectrum R)},
    (((AlgebraicCycle.finiteFlatPullback dimensionR dimensionS i c :
      cyclesOfDimension (Spec (CommRingCat.of S)) dimensionS i) :
        AlgebraicCycle (Spec (CommRingCat.of S)) ℚ) q) *
      (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff
        (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
        dimensionS dimensionR q : ℚ)) =
    ((Module.finrank R S : ℚ) • (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)) p
  have hdim (q : Spec (CommRingCat.of S)) :
      dimensionS q = dimensionR
        ((AlgebraicCycle.finiteFlatMap (R := R) (S := S)).base q) :=
    DimensionFunction.apply_eq_of_finiteFlatMap dimensionR dimensionS q
  have hcoeff (q : Spec (CommRingCat.of S)) :
      (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff
        (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
        dimensionS dimensionR q : ℚ) =
        (q.asIdeal.inertiaDeg R : ℚ) := by
    rw [_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff, if_pos (hdim q)]
    exact_mod_cast AlgebraicCycle.specFiniteMap_residueDegree_eq_inertiaDeg q
  have hpull (q : PrimeSpectrum S) :
      ((AlgebraicCycle.finiteFlatPullback dimensionR dimensionS i c :
        cyclesOfDimension (Spec (CommRingCat.of S)) dimensionS i) :
          AlgebraicCycle (Spec (CommRingCat.of S)) ℚ) q =
        c.1 (PrimeSpectrum.comap (algebraMap R S) q) *
          (q.asIdeal.ramificationIdx R : ℚ) := by
    exact AlgebraicCycle.finiteFlatPullback_apply dimensionR dimensionS i c q
  have hcoeff' (q : PrimeSpectrum S) :
      (_root_.AlgebraicGeometry.AlgebraicCycle.mapCoeff
        (AlgebraicCycle.finiteFlatMap (R := R) (S := S))
        dimensionS dimensionR q : ℚ) =
        (q.asIdeal.inertiaDeg R : ℚ) := hcoeff q
  simp_rw [hpull, hcoeff']
  calc
    (∑ᶠ q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p},
        c.1 (PrimeSpectrum.comap (algebraMap R S) q) *
          (q.asIdeal.ramificationIdx R : ℚ) *
          (q.asIdeal.inertiaDeg R : ℚ)) =
      ∑ᶠ q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p},
        c.1 p * ((q.asIdeal.ramificationIdx R : ℚ) *
          (q.asIdeal.inertiaDeg R : ℚ)) := by
      apply finsum_mem_congr rfl
      intro q hq
      have hqp : PrimeSpectrum.comap (algebraMap R S) q = p := by
        simpa using hq
      rw [hqp]
      ring
    _ = c.1 p *
        (∑ᶠ q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p},
          (q.asIdeal.ramificationIdx R : ℚ) *
            (q.asIdeal.inertiaDeg R : ℚ)) := by
      rw [mul_finsum_mem]
    _ = ((Module.finrank R S : ℚ) •
        (c : AlgebraicCycle (Spec (CommRingCat.of R)) ℚ)) p := by
      rw [affine_fibre_sum (R := R) (S := S) (p := p)]
      simp [smul_eq_mul]
      ring

end cyclesOfDimension

end GromovWitten.AlgebraicGeometry.IntersectionTheory
