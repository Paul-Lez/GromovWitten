/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.IntrinsicPullbackSequence
import GromovWitten.AlgebraicGeometry.Cones.NormalConeAction
import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDualInvariance

/-!
# Derived invariance of obstruction theories, and the smooth Jacobi–Zariski sequence

Two complementary items: obstruction theories only depend on the class of the source in the
derived category, and the hypotheses of the intrinsic pullback sequence are automatic in the
formally smooth case.

## Main results

### The Jacobi–Zariski sequence for a flat extension of a formally smooth algebra

* `PicardCriteria.injective_jzToComp_degreeZero_of_flat`: for a tower `R → S → T` with `S`
  formally smooth over `R` and `T` flat over `S`, the conormal map `T ⊗_S I/I² → J/J²` is
  injective.  This discharges the only hypothesis of
  `Cones/IntrinsicPullbackSequence.shortExact_jz`, giving `shortExact_jz_of_flat`: the map on
  ambient differentials is always injective, formal smoothness makes the cotangent differential
  of `S/R` injective (`Algebra.Extension.cotangentComplex_injective_iff`), flatness keeps it
  injective after base change, and the commuting square does the rest.
* `PicardCriteria.projective_cotangent_of_formallySmooth`: if `T` is formally smooth over `S`
  then the relative conormal module `K/K²` of any presentation is projective — it is the kernel
  of the surjection from the free module of ambient differentials onto `Ω[T⁄S]`, which splits
  because `Ω[T⁄S]` is projective.  This discharges the second hypothesis.
* `PicardCriteria.shortExact_dual_jz_of_smooth` and `shortExactPicard_dual_jz_of_smooth`: the
  **intrinsic pullback sequence is unconditional** for `R → S → T` with `S` formally smooth over
  `R`, `T` flat and formally smooth over `S`.

### Derived invariance of obstruction theories

* `PicardCriteria.nonempty_homotopy_of_Q_map_eq`: chain maps out of a K-projective complex are
  determined up to homotopy by their image in the derived category.
* `PicardCriteria.homotopyEquivalenceOfDerivedIso`: an isomorphism `Q(E) ≅ Q(E')` of the cochain
  realizations of two-term complexes of finite free modules comes from a chain homotopy
  equivalence `E ≃ E'` (`exists_homotopyEquiv_of_derivedIso` plus `ofHomotopyEquiv`), realizing
  the given isomorphism (`Q_map_homotopyEquivalenceOfDerivedIso`).
* `PicardCriteria.nonempty_chainHomotopy_of_derivedIso`: if the derived isomorphism is
  compatible with two maps `φ : E ⟶ L`, `φ' : E' ⟶ L`, then `φ' ∘ e` and `φ` are chain
  homotopic.
* `PicardCriteria.isObstructionTheory_iff_of_derivedIso`: **being an obstruction theory is
  invariant under isomorphism of the source in the derived category.**
* `PicardCriteria.nonempty_natIso_dualHom_quotientFunctor` and
  `nonempty_natIso_obstructionCone`: the induced functors on the dual Picard groupoids, and
  hence the obstruction cones, agree up to a natural isomorphism over every test algebra;
  together with `obstructionCone_comp_homotopyEquivalence` this says that the obstruction cone
  of `φ'` composed with the equivalence of fibres induced by `e` is the obstruction cone of `φ`.

## What is assumed

Nothing beyond the stated hypotheses.  Two remarks: plain flatness of `T` over `S` is *not*
enough for the Jacobi–Zariski sequence to be degreewise short exact (the obstruction is the
image of `H₂(L_{T/S})` in `T ⊗ H₁(L_{S/R})`, which is why the formal smoothness of `S` over `R`
appears), and Mathlib's `Algebra.Generators` files contain no injectivity statement for
`T ⊗_S I/I² → J/J²`; the proof here goes through the commuting square with the ambient
differentials.  The derived invariance is stated for the fixed target `L`; the case of a
simultaneous change of `L` is not treated.
-/

open CategoryTheory TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex CotangentComplex

/-! ## The Jacobi–Zariski sequence in the formally smooth case -/

section JacobiZariski

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι σ : Type u} (Q : Algebra.Generators.{u} S T ι) (P : Algebra.Generators.{u} R S σ)

/-- **The conormal map of the Jacobi–Zariski sequence is injective** when `T` is flat over `S`
and `S` has no `H¹` over `R` — for instance when `S` is formally smooth over `R`.  Indeed the
map on ambient differentials is always injective, and flatness plus the injectivity of the
cotangent differential of `S/R` make the base-changed differential injective, so the commuting
square forces injectivity. -/
theorem injective_jzToComp_degreeZero_of_flat [Module.Flat S T]
    [Algebra.FormallySmooth R S] : Function.Injective (jzToComp Q P).degreeZero := by
  have hring : Algebra.FormallySmooth R P.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial σ R))
  have hinjd : Function.Injective P.toExtension.cotangentComplex := by
    rw [Algebra.Extension.cotangentComplex_injective_iff]
    infer_instance
  have hbase : Function.Injective
      (LinearMap.baseChange T P.toExtension.cotangentComplex) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinjd
  intro x y hxy
  have hone : (jzToComp Q P).degreeOne ((jzLeftComplex T P).differential x) =
      (jzToComp Q P).degreeOne ((jzLeftComplex T P).differential y) := by
    rw [(jzToComp Q P).comm x, (jzToComp Q P).comm y, hxy]
  exact hbase (injective_jzToComp_degreeOne Q P hone)

/-- **The Jacobi–Zariski sequence of two-term complexes is short exact** for a flat extension of
a formally smooth algebra: hypothesis (i) of `shortExact_jz` is discharged. -/
theorem shortExact_jz_of_flat [Module.Flat S T] [Algebra.FormallySmooth R S] :
    ShortExact (jzToComp Q P) (jzOfComp Q P) :=
  shortExact_jz Q P (injective_jzToComp_degreeZero_of_flat Q P)

/-- **The relative conormal module of a formally smooth algebra is projective.**  The cotangent
differential of the presentation is injective with image the kernel of the surjection onto the
Kähler differentials, and that kernel is a direct summand of the free module of ambient
differentials because `Ω[T⁄S]` is projective. -/
theorem projective_cotangent_of_formallySmooth [Algebra.FormallySmooth S T] :
    Module.Projective T Q.toExtension.Cotangent := by
  have hring : Algebra.FormallySmooth S Q.toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth S (MvPolynomial ι S))
  have hinj : Function.Injective Q.toExtension.cotangentComplex := by
    rw [Algebra.Extension.cotangentComplex_injective_iff]
    infer_instance
  have hfree : Module.Free T Q.toExtension.CotangentSpace :=
    Module.Free.of_basis Q.cotangentSpaceBasis
  have hker : Module.Projective T (LinearMap.ker Q.toExtension.toKaehler) :=
    projective_ker_of_surjective _ Q.toExtension.toKaehler_surjective
  have hrange : LinearMap.range Q.toExtension.cotangentComplex =
      LinearMap.ker Q.toExtension.toKaehler :=
    (LinearMap.exact_iff.mp Q.toExtension.exact_cotangentComplex_toKaehler).symm
  exact Module.Projective.of_equiv'
    ((LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)).symm

/-- **The intrinsic pullback sequence is unconditional in the smooth case.**  If `S` is formally
smooth over `R`, `T` is flat over `S` and `T` is formally smooth over `S`, both hypotheses of
`shortExactPicard_dual_jz` hold, so the dual sequence of Picard groupoids is exact over every
test algebra. -/
theorem shortExactPicard_dual_jz_of_smooth [Module.Flat S T] [Algebra.FormallySmooth R S]
    [Algebra.FormallySmooth S T] (B : Type u) [CommRing B] [Algebra T B] :
    ShortExactPicard (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  shortExactPicard_dual_jz Q P B (injective_jzToComp_degreeZero_of_flat Q P)
    (projective_cotangent_of_formallySmooth Q)

/-- The same in the form of a short exact sequence of two-term complexes of `B`-points. -/
theorem shortExact_dual_jz_of_smooth [Module.Flat S T] [Algebra.FormallySmooth R S]
    [Algebra.FormallySmooth S T] (B : Type u) [CommRing B] [Algebra T B] :
    ShortExact (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  shortExact_dual_jz Q P B (injective_jzToComp_degreeZero_of_flat Q P)
    (projective_cotangent_of_formallySmooth Q)

end JacobiZariski

/-! ## Derived invariance of obstruction theories -/

section DerivedInvariance

open CotangentComplex.PerfectComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- **Chain maps out of a K-projective complex are determined up to homotopy by their image in
the derived category.** -/
theorem nonempty_homotopy_of_Q_map_eq {K M : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : K.IsKProjective) (φ ψ : K ⟶ M)
    (hQ : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ) : Nonempty (Homotopy φ ψ) := by
  have hKp := hK
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj M)).injective
    have h1 := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
    have h2 := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality ψ
    rw [Functor.comp_map] at h1 h2
    rw [hQ, ← h2] at h1
    exact (cancel_mono _).mp h1
  exact ⟨HomotopyCategory.homotopyOfEq _ _ hq⟩

variable {E E' L : LinearTwoTermComplex R}

/-- The cochain realization of chain maps of two-term complexes is functorial. -/
theorem toCochainComplexHom_comp (f : Hom E E') (g : Hom E' L) :
    toCochainComplexHom (g.comp f) = toCochainComplexHom f ≫ toCochainComplexHom g := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hneg : n = -1
  · subst hneg
    rfl
  · by_cases hzero : n = 0
    · subst hzero
      rfl
    · exact (toCochainComplex_X_isZero L n hneg hzero).eq_of_tgt _ _

/-- A morphism of the cochain realizations is the realization of its two-term restriction. -/
theorem toCochainComplexHom_ofCochainComplexHom (f : E.toCochainComplex ⟶ E'.toCochainComplex) :
    toCochainComplexHom (ofCochainComplexHom f) = f := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  by_cases hneg : n = -1
  · subst hneg
    rfl
  · by_cases hzero : n = 0
    · subst hzero
      rfl
    · exact (toCochainComplex_X_isZero E' n hneg hzero).eq_of_tgt _ _

/-- **A derived isomorphism of perfect two-term complexes is a chain homotopy equivalence.**
Two-term complexes of finite free modules are K-projective, so the isomorphism is the image of a
homotopy equivalence of cochain complexes, which restricts to the two-term complexes. -/
noncomputable def homotopyEquivalenceOfDerivedIso
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex) :
    HomotopyEquivalence E E' :=
  ofHomotopyEquiv (toCochainComplex_X_isZero E 1 (by norm_num) (by norm_num))
    (toCochainComplex_X_isZero E (-2) (by norm_num) (by norm_num))
    (toCochainComplex_X_isZero E' 1 (by norm_num) (by norm_num))
    (toCochainComplex_X_isZero E' (-2) (by norm_num) (by norm_num))
    (exists_homotopyEquiv_of_derivedIso hE hE' e).choose

/-- The homotopy equivalence realizes the given derived isomorphism. -/
theorem Q_map_homotopyEquivalenceOfDerivedIso
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex) :
    DerivedCategory.Q.map
        (toCochainComplexHom (homotopyEquivalenceOfDerivedIso hE hE' e).hom) = e.hom := by
  have h1 : toCochainComplexHom (homotopyEquivalenceOfDerivedIso hE hE' e).hom =
      (exists_homotopyEquiv_of_derivedIso hE hE' e).choose.hom :=
    toCochainComplexHom_ofCochainComplexHom _
  rw [h1]
  exact (exists_homotopyEquiv_of_derivedIso hE hE' e).choose_spec

/-- **Compatibility with the target is a chain homotopy.**  If the derived isomorphism commutes
with the two maps to `L`, then the transported chain map `φ' ∘ e` is chain homotopic to `φ`. -/
theorem nonempty_chainHomotopy_of_derivedIso
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex)
    (φ : Hom E L) (φ' : Hom E' L)
    (hcompat : e.hom ≫ DerivedCategory.Q.map (toCochainComplexHom φ') =
      DerivedCategory.Q.map (toCochainComplexHom φ)) :
    Nonempty (ChainHomotopy (φ'.comp (homotopyEquivalenceOfDerivedIso hE hE' e).hom) φ) := by
  have hQ : DerivedCategory.Q.map
      (toCochainComplexHom (φ'.comp (homotopyEquivalenceOfDerivedIso hE hE' e).hom)) =
      DerivedCategory.Q.map (toCochainComplexHom φ) := by
    rw [toCochainComplexHom_comp, Functor.map_comp,
      Q_map_homotopyEquivalenceOfDerivedIso hE hE' e]
    exact hcompat
  obtain ⟨H⟩ := nonempty_homotopy_of_Q_map_eq hE.isKProjective _ _ hQ
  exact ⟨(ofHomotopy (toCochainComplex_X_isZero E 1 (by norm_num) (by norm_num))
    (toCochainComplex_X_isZero L (-2) (by norm_num) (by norm_num)) H).symm⟩

/-- **Derived invariance of obstruction theories.**  Two chain maps to `L` whose sources are
isomorphic in the derived category, compatibly with the maps to `L`, are obstruction theories
simultaneously. -/
theorem isObstructionTheory_iff_of_derivedIso
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex)
    (φ : Hom E L) (φ' : Hom E' L)
    (hcompat : e.hom ≫ DerivedCategory.Q.map (toCochainComplexHom φ') =
      DerivedCategory.Q.map (toCochainComplexHom φ)) :
    IsObstructionTheory φ ↔ IsObstructionTheory φ' := by
  obtain ⟨H⟩ := nonempty_chainHomotopy_of_derivedIso hE hE' e φ φ' hcompat
  set u := homotopyEquivalenceOfDerivedIso hE hE' e with hu
  constructor
  · intro h
    have h1 : IsObstructionTheory (φ'.comp u.hom) := h.of_chainHomotopy H.symm
    have h2 : IsObstructionTheory ((φ'.comp u.hom).comp u.inv) :=
      h1.homotopyEquivalence_comp (homotopyEquivalenceSymm u)
    exact h2.of_chainHomotopy (u.counit.postcomp φ')
  · intro h
    exact (h.homotopyEquivalence_comp u).of_chainHomotopy H

/-- **The induced functors on the dual Picard groupoids agree up to a natural isomorphism**, for
every test algebra.  Composed with the comparison of a cone with `h¹/h⁰` of the dual, this says
that the obstruction cones of `φ` and of `φ'` agree up to the equivalence of dual Picard
groupoids induced by the derived isomorphism, naturally in the test algebra. -/
theorem nonempty_natIso_dualHom_quotientFunctor
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex)
    (φ : Hom E L) (φ' : Hom E' L)
    (hcompat : e.hom ≫ DerivedCategory.Q.map (toCochainComplexHom φ') =
      DerivedCategory.Q.map (toCochainComplexHom φ))
    (B : Type u) [CommRing B] [Algebra R B] :
    Nonempty ((dualHom (φ'.comp (homotopyEquivalenceOfDerivedIso hE hE' e).hom) B).quotientFunctor
      ≅ (dualHom φ B).quotientFunctor) := by
  obtain ⟨H⟩ := nonempty_chainHomotopy_of_derivedIso hE hE' e φ φ' hcompat
  exact ⟨(dualChainHomotopy B H).natIso⟩

end DerivedInvariance

/-! ## Invariance of the obstruction cone -/

section ObstructionCone

open ConeQuotient NormalSheafPicard CotangentComplex.PerfectComplex

attribute [local instance] HasDerivedCategory.standard

variable {A N F S : Type u} [CommRing A] [AddCommGroup N] [Module A N] [AddCommGroup F]
  [Module A F] [CommRing S] [Algebra A S] {d : N →ₗ[A] F} {Ac : ConeAction A S F}
  {ψ : SymmetricAlgebra A N →ₐ[A] S} {E E' : LinearTwoTermComplex A}

/-- **The obstruction cones of two derived-isomorphic obstruction theories agree.**  Composing
the natural isomorphism of the induced functors on the dual Picard groupoids with the comparison
of the cone with `h¹/h⁰` of the dual gives, over every test algebra `B`, a natural isomorphism
between the obstruction cone of `φ` and the obstruction cone of the transported map `φ' ∘ e`;
and `obstructionCone_comp_homotopyEquivalence` identifies the latter with the obstruction cone
of `φ'` followed by the equivalence `dualQuotientEquivalence` of the fibres induced by `e`. -/
theorem nonempty_natIso_obstructionCone
    (hE : IsStrictlyPerfect E.toCochainComplex) (hE' : IsStrictlyPerfect E'.toCochainComplex)
    (e : DerivedCategory.Q.obj E.toCochainComplex ≅ DerivedCategory.Q.obj E'.toCochainComplex)
    (φ : Hom E (dualComplexOf d)) (φ' : Hom E' (dualComplexOf d))
    (hcompat : e.hom ≫ DerivedCategory.Q.map (toCochainComplexHom φ') =
      DerivedCategory.Q.map (toCochainComplexHom φ))
    (h : IsEquivariant (bundleTranslationAction d) Ac ψ LinearMap.id)
    (B : Type u) [CommRing B] [Algebra A B] :
    Nonempty (obstructionCone (φ'.comp (homotopyEquivalenceOfDerivedIso hE hE' e).hom) h B ≅
      obstructionCone φ h B) := by
  obtain ⟨α⟩ := nonempty_natIso_dualHom_quotientFunctor hE hE' e φ φ' hcompat B
  exact ⟨CategoryTheory.Functor.isoWhiskerLeft (coneToDualPoints h B) α⟩

end ObstructionCone

end PicardCriteria

end GromovWitten.AlgebraicGeometry
