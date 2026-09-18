/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedTruncationRoof
import GromovWitten.AlgebraicGeometry.Cones.CriteriaBundle
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Perfect complexes of amplitude `[-1, 0]` and vector-bundle stacks

The Picard groupoid `h¹/h⁰(Eᵛ)` of a two-term complex is a vector-bundle stack exactly when the
two terms are finitely generated projective modules.  This file provides the two-term complex of
finitely generated projectives attached to a perfect complex of amplitude `[-1, 0]`, in the
affine model.

## Main results

* `PicardCriteria.projective_ker_of_surjective`, `finite_ker_of_surjective`: the kernel of a
  surjection of projective modules is a direct summand of the source, hence projective (and
  finitely generated if the source is).
* `PicardCriteria.projective_finite_cocycles`: **chopping the top.**  For a bounded complex of
  finitely generated projective modules which is exact above degree `n`, the cocycles
  `Z^i = ker d^i` are finitely generated projective for every `i ≥ n`.  This is the
  dimension-shifting argument, run downwards from the top of the support; it replaces the
  iterated construction of a homotopy equivalence chopping off the terms in positive degrees.
* `PicardCriteria.perfectTwoTerm K = [K⁻¹/im d⁻² → Z⁰(K)]`, the chain-level form of the
  two-sided truncation, with `projective_finite_perfectTwoTerm_degreeOne` (unconditional, from
  the previous item), `finitePresentation_perfectTwoTerm_degreeZero` and
  `projective_perfectTwoTerm_degreeZero_of_flat`: **chopping the bottom**, where flatness of
  `K⁻¹/im d⁻²` — which is what `HasTorAmplitudeIn K (-1) 0` provides — turns the finitely
  presented degree-zero term into a projective one.  When `K` vanishes in degree `-2` no
  flatness is needed (`projective_finite_perfectTwoTerm_degreeZero_of_isZero`).
* `PicardCriteria.IsVectorBundleComplex`: the property of a two-term complex that both terms are
  finitely generated projective.  `isVectorBundleComplex_perfectTwoTerm`,
  `isVectorBundleComplex_twoTermTrunc` and their unconditional `of_isZero` variants establish it,
  and `isVectorBundleComplex_dualPoints` shows it is inherited by the complexes of `B`-points of
  the dual — the fibrewise vector-bundle-stack statement, proved from
  `projective_finite_hom_of_projective_finite`.
* `PicardCriteria.perfectToTwoTermTrunc`, `isQuasiIsomorphism_perfectToTwoTermTrunc`,
  `perfectQuotientEquivalence`: for a complex with no differential out of degree `0`, the perfect
  two-term complex is quasi-isomorphic to the truncation of `Cones/DerivedTruncation.lean`, so
  its `h⁰` is `H⁻¹(K)` and its `h¹` is `H⁰(K)`; `isQuasiIsomorphism_of_bijective` is the general
  criterion used.
* `PicardCriteria.quasiIso_truncProjection` and `PicardCriteria.truncRepOfExact`: a complex
  exact outside `[-1, 0]` with no differential out of degree `0` is represented in the derived
  category by its two-term truncation, which therefore gives a `TruncRep` of `Q.obj K`; combined
  with `isVectorBundleComplex_dualPoints_truncRepOfExact` this is the statement that
  `h¹/h⁰(Eᵛ)` is a vector-bundle stack for a perfect object of amplitude `[-1, 0]`.
* `CotangentComplex.PerfectComplex.GlobalTwoTermResolution.isVectorBundleComplex` and
  `isVectorBundleComplex_dualPoints`: the unconditional special case of the repository's global
  two-term resolutions, whose terms are finite free.

## What is assumed

Flatness of the bottom cokernel `K⁻¹/im d⁻²` is an explicit hypothesis rather than a consequence
of `HasTorAmplitudeIn K (-1) 0`: deducing it requires identifying the higher Tor modules of that
cokernel with the vanishing cohomology of `K ⊗ M` through the finite projective resolution
`K^a → ⋯ → K⁻¹`, which is not formalized here.  Everything else is unconditional, and the case
of a complex supported in `[-1, 0]` — in particular a global two-term resolution — needs no
hypothesis at all.  The chopping is performed at the level of modules and of the resulting
two-term complex; the homotopy equivalence `K ≃ L` of cochain complexes is not constructed, the
quasi-isomorphism `truncProjection` being enough for every statement about `h¹/h⁰`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex

variable {R : Type u} [CommRing R]

/-! ## Kernels of surjections of projective modules -/

section Modules

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The retraction of the kernel of a split surjection: `x ↦ x - s (f x)` for a section `s`. -/
def kerRetraction (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (by
    intro x
    rw [LinearMap.mem_ker]
    change f (x - s (f x)) = 0
    rw [map_sub, hs, sub_self])

@[simp]
theorem kerRetraction_apply_coe (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y)
    (x : M) : ((kerRetraction f hs x : LinearMap.ker f) : M) = x - s (f x) :=
  rfl

/-- The retraction restricts to the identity on the kernel. -/
theorem kerRetraction_comp_subtype (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    (kerRetraction f hs).comp (LinearMap.ker f).subtype = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  change (x : M) - s (f (x : M)) = (x : M)
  have hx : f (x : M) = 0 := x.2
  rw [hx, map_zero, sub_zero]

/-- The retraction onto the kernel of a split surjection is surjective. -/
theorem kerRetraction_surjective (f : M →ₗ[R] N) {s : N →ₗ[R] M} (hs : ∀ y, f (s y) = y) :
    Function.Surjective (kerRetraction f hs) := by
  intro x
  refine ⟨(x : M), ?_⟩
  exact congrArg (fun m : LinearMap.ker f →ₗ[R] LinearMap.ker f => m x)
    (kerRetraction_comp_subtype f hs)

/-- **The kernel of a surjection of projective modules is projective**: the surjection splits, so
the kernel is a direct summand of the source. -/
theorem projective_ker_of_surjective [Module.Projective R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ y, f (s y) = y := fun y =>
    congrArg (fun m : N →ₗ[R] N => m y) hs
  exact Module.Projective.of_split (LinearMap.ker f).subtype (kerRetraction f hs')
    (kerRetraction_comp_subtype f hs')

/-- The kernel of a surjection onto a projective module, from a finitely generated module, is
finitely generated. -/
theorem finite_ker_of_surjective [Module.Finite R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R (LinearMap.ker f) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ y, f (s y) = y := fun y =>
    congrArg (fun m : N →ₗ[R] N => m y) hs
  exact Module.Finite.of_surjective (kerRetraction f hs') (kerRetraction_surjective f hs')

end Modules

/-! ## The cocycles of a bounded complex of projectives -/

section Cocycles

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The module of cocycles of a cochain complex of modules in degree `i`. -/
abbrev cocycles (i : ℤ) : Submodule R (K.X i) := LinearMap.ker (K.d i (i + 1)).hom

/-- The differential, corestricted to the cocycles of the next degree. -/
def dToCocycles (i : ℤ) : K.X i →ₗ[R] cocycles K (i + 1) :=
  ((K.d i (i + 1)).hom).codRestrict _ (by
    intro x
    rw [LinearMap.mem_ker]
    exact congrArg (fun m : K.X i ⟶ K.X (i + 1 + 1) => (ModuleCat.Hom.hom m) x)
      (K.d_comp_d i (i + 1) (i + 1 + 1)))

@[simp]
theorem dToCocycles_apply_coe (i : ℤ) (x : K.X i) :
    ((dToCocycles K i x : cocycles K (i + 1)) : K.X (i + 1)) = (K.d i (i + 1)).hom x :=
  rfl

theorem ker_dToCocycles (i : ℤ) : LinearMap.ker (dToCocycles K i) = cocycles K i :=
  LinearMap.ker_codRestrict _ _ _

/-- Exactness at `i + 1`, elementwise: the image of the differential is the cocycles. -/
theorem range_eq_cocycles_of_exactAt (i : ℤ) (h : K.ExactAt (i + 1)) :
    LinearMap.range (K.d i (i + 1)).hom = cocycles K (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' K i (i + 1) (i + 1 + 1)
    (by rw [CochainComplex.prev]; omega) (by rw [CochainComplex.next])] at h
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h

/-- The corestricted differential is surjective onto the cocycles when the complex is exact in
the target degree. -/
theorem dToCocycles_surjective (i : ℤ) (h : K.ExactAt (i + 1)) :
    Function.Surjective (dToCocycles K i) := by
  rintro ⟨y, hy⟩
  have hmem : y ∈ LinearMap.range (K.d i (i + 1)).hom := by
    rw [range_eq_cocycles_of_exactAt K i h]
    exact hy
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, Subtype.ext hx⟩

/-- Above the support the cocycles are everything, hence projective. -/
theorem projective_cocycles_of_isZero (i : ℤ) (h : IsZero (K.X (i + 1)))
    [Module.Projective R (K.X i)] : Module.Projective R (cocycles K i) := by
  have htop : cocycles K i = ⊤ := by
    refine le_antisymm le_top (fun x _ => ?_)
    rw [LinearMap.mem_ker]
    exact congrArg (fun m : K.X i ⟶ K.X (i + 1) => (ModuleCat.Hom.hom m) x) (h.eq_of_tgt _ 0)
  exact Module.Projective.of_equiv' ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv).symm

/-- Above the support the cocycles are everything, hence finitely generated. -/
theorem finite_cocycles_of_isZero (i : ℤ) (h : IsZero (K.X (i + 1)))
    [Module.Finite R (K.X i)] : Module.Finite R (cocycles K i) := by
  have htop : cocycles K i = ⊤ := by
    refine le_antisymm le_top (fun x _ => ?_)
    rw [LinearMap.mem_ker]
    exact congrArg (fun m : K.X i ⟶ K.X (i + 1) => (ModuleCat.Hom.hom m) x) (h.eq_of_tgt _ 0)
  exact Module.Finite.equiv ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv).symm

/-- **The cocycles of a bounded complex of finitely generated projective modules, exact above
degree `n`, are finitely generated projective in every degree `≥ n`.**  This is the
dimension-shifting argument: the short exact sequences `0 → Z^i → K^i → Z^{i+1} → 0` split from
the top of the support downwards. -/
theorem projective_finite_cocycles (n b : ℤ)
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hexact : ∀ i : ℤ, n < i → K.ExactAt i) :
    ∀ i : ℤ, n ≤ i → Module.Projective R (cocycles K i) ∧ Module.Finite R (cocycles K i) := by
  have key : ∀ k : ℕ, ∀ i : ℤ, n ≤ i → b ≤ i + k →
      Module.Projective R (cocycles K i) ∧ Module.Finite R (cocycles K i) := by
    intro k
    induction k with
    | zero =>
      intro i _ hik
      have hzero : IsZero (K.X (i + 1)) := hb (i + 1) (by omega)
      have h1 := hproj i
      have h2 := hfin i
      exact ⟨projective_cocycles_of_isZero K i hzero, finite_cocycles_of_isZero K i hzero⟩
    | succ k ih =>
      intro i hni hik
      by_cases hib : b ≤ i
      · have hzero : IsZero (K.X (i + 1)) := hb (i + 1) (by omega)
        have h1 := hproj i
        have h2 := hfin i
        exact ⟨projective_cocycles_of_isZero K i hzero, finite_cocycles_of_isZero K i hzero⟩
      · obtain ⟨hp, hf⟩ := ih (i + 1) (by omega) (by omega)
        have hsurj := dToCocycles_surjective K i (hexact (i + 1) (by omega))
        have h1 := hproj i
        have h2 := hfin i
        have hp' : Module.Projective R (LinearMap.ker (dToCocycles K i)) :=
          projective_ker_of_surjective _ hsurj
        have hf' : Module.Finite R (LinearMap.ker (dToCocycles K i)) :=
          finite_ker_of_surjective _ hsurj
        rw [ker_dToCocycles] at hp' hf'
        exact ⟨hp', hf'⟩
  intro i hi
  exact key (max 0 (b - i)).toNat i hi (by omega)

end Cocycles

/-! ## The two-term complex of a perfect complex of amplitude `[-1, 0]` -/

section PerfectTwoTerm

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The two-term complex `[K⁻¹/im d⁻² → Z⁰(K)]` attached to a cochain complex of modules: the
coboundaries are divided out at the bottom and the cocycles are cut out at the top, which is the
chain-level form of the two-sided truncation `τ≥-1 τ≤0 K`. -/
abbrev perfectTwoTerm : LinearTwoTermComplex R where
  degreeZero := K.X (-1) ⧸ (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1)))
  degreeOne := cocycles K 0
  differential := Submodule.liftQ _ (dToCocycles K (-1)) (by
    rw [ker_dToCocycles]
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun m : K.X (-2) ⟶ K.X 0 => (ModuleCat.Hom.hom m) x)
      (K.d_comp_d (-2) (-1) 0))

@[simp]
theorem perfectTwoTerm_differential_mk (x : K.X (-1)) :
    (((perfectTwoTerm K).differential (Submodule.Quotient.mk x) : cocycles K 0) : K.X 0) =
      (K.d (-1) 0).hom x :=
  rfl

/-- **The degree-one term of the perfect two-term complex is finitely generated projective**, by
dimension shifting from the top of the support. -/
theorem projective_finite_perfectTwoTerm_degreeOne (b : ℤ)
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hexact : ∀ i : ℤ, 0 < i → K.ExactAt i) :
    Module.Projective R (perfectTwoTerm K).degreeOne ∧
      Module.Finite R (perfectTwoTerm K).degreeOne :=
  projective_finite_cocycles K 0 b hproj hfin hb hexact 0 le_rfl

/-- The degree-zero term of the perfect two-term complex is finitely presented: it is a quotient
of a finitely presented module by a finitely generated submodule. -/
theorem finitePresentation_perfectTwoTerm_degreeZero
    (hproj : Module.Projective R (K.X (-1))) (hfin : Module.Finite R (K.X (-1)))
    (hfin' : Module.Finite R (K.X (-2))) :
    Module.FinitePresentation R (perfectTwoTerm K).degreeZero := by
  have h1 := hproj
  have h2 := hfin
  have h3 := hfin'
  have hfp : Module.FinitePresentation R (K.X (-1)) :=
    Module.finitePresentation_of_projective R (K.X (-1))
  have hfg : (LinearMap.ker
      (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1))).mkQ).FG := by
    rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
    exact (Module.finite_def.1 h3).map _
  exact Module.finitePresentation_of_surjective _ (Submodule.mkQ_surjective _) hfg

/-- **The degree-zero term is projective as soon as it is flat.**  Flatness of
`K⁻¹/im d⁻²` is exactly what the Tor-amplitude hypothesis `HasTorAmplitudeIn K (-1) 0` provides
(the truncated complex `K^a → ⋯ → K⁻¹` is a finite projective resolution of it, and all its
higher Tor modules are the vanishing cohomology of `K ⊗ M`); the flatness itself is taken here
as an explicit hypothesis. -/
theorem projective_perfectTwoTerm_degreeZero_of_flat
    (hproj : Module.Projective R (K.X (-1))) (hfin : Module.Finite R (K.X (-1)))
    (hfin' : Module.Finite R (K.X (-2)))
    (hflat : Module.Flat R (perfectTwoTerm K).degreeZero) :
    Module.Projective R (perfectTwoTerm K).degreeZero := by
  have hfp := finitePresentation_perfectTwoTerm_degreeZero K hproj hfin hfin'
  have h := hflat
  exact Module.Flat.projective_of_finitePresentation

/-- When the complex vanishes in degree `-2` there is nothing to divide out and the degree-zero
term of the perfect two-term complex is the term of `K` in degree `-1`. -/
noncomputable def perfectTwoTermDegreeZeroEquiv (h : IsZero (K.X (-2))) :
    (perfectTwoTerm K).degreeZero ≃ₗ[R] K.X (-1) := by
  have hbot : (LinearMap.range (K.d (-2) (-1)).hom : Submodule R (K.X (-1))) = ⊥ := by
    rw [show (K.d (-2) (-1)) = 0 from h.eq_of_src _ _]
    exact LinearMap.range_eq_bot.2 rfl
  exact Submodule.quotEquivOfEqBot _ hbot

/-- If the complex vanishes in degree `-2`, the degree-zero term is finitely generated
projective with no flatness hypothesis. -/
theorem projective_finite_perfectTwoTerm_degreeZero_of_isZero (h : IsZero (K.X (-2)))
    (hproj : Module.Projective R (K.X (-1))) (hfin : Module.Finite R (K.X (-1))) :
    Module.Projective R (perfectTwoTerm K).degreeZero ∧
      Module.Finite R (perfectTwoTerm K).degreeZero := by
  have h1 := hproj
  have h2 := hfin
  exact ⟨Module.Projective.of_equiv' (perfectTwoTermDegreeZeroEquiv K h).symm,
    Module.Finite.equiv (perfectTwoTermDegreeZeroEquiv K h).symm⟩

end PerfectTwoTerm

/-! ## Vector-bundle two-term complexes and their fibres -/

/-- A two-term complex of `R`-modules has *vector-bundle terms* when both terms are finitely
generated projective; this is exactly the condition making `h¹/h⁰(Eᵛ)` a vector-bundle stack. -/
structure IsVectorBundleComplex (E : LinearTwoTermComplex R) : Prop where
  /-- The degree-zero term is projective. -/
  projective_degreeZero : Module.Projective R E.degreeZero
  /-- The degree-zero term is finitely generated. -/
  finite_degreeZero : Module.Finite R E.degreeZero
  /-- The degree-one term is projective. -/
  projective_degreeOne : Module.Projective R E.degreeOne
  /-- The degree-one term is finitely generated. -/
  finite_degreeOne : Module.Finite R E.degreeOne

/-- **The `B`-points of the dual of a finitely generated projective module form a finitely
generated projective `B`-module.**  The module is a retract of a finite free module, and
`Hom_R(-, B)` turns that retract into a retract of `Bⁿ`. -/
theorem projective_finite_hom_of_projective_finite (P : Type u) [AddCommGroup P] [Module R P]
    (hproj : Module.Projective R P) (hfin : Module.Finite R P)
    (B : Type u) [CommRing B] [Algebra R B] :
    Module.Projective B (P →ₗ[R] B) ∧ Module.Finite B (P →ₗ[R] B) := by
  have h1 := hproj
  have h2 := hfin
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ x, f (s x) = x := fun x => congrArg (fun m : P →ₗ[R] P => m x) hs
  have hcomp : (precomp s B).comp (precomp f B) = LinearMap.id := by
    refine LinearMap.ext fun l => ?_
    refine LinearMap.ext fun x => ?_
    change l (f (s x)) = l x
    rw [hs']
  have e : (Fin n → B) ≃ₗ[B] ((Fin n → R) →ₗ[R] B) := (Pi.basisFun R (Fin n)).constr B
  have hprojFree : Module.Projective B ((Fin n → R) →ₗ[R] B) := Module.Projective.of_equiv' e
  have hfinFree : Module.Finite B ((Fin n → R) →ₗ[R] B) := Module.Finite.equiv e
  have hsurj : Function.Surjective (precomp s B) := fun l =>
    ⟨precomp f B l, congrArg (fun m : (P →ₗ[R] B) →ₗ[B] (P →ₗ[R] B) => m l) hcomp⟩
  exact ⟨Module.Projective.of_split (precomp f B) (precomp s B) hcomp,
    Module.Finite.of_surjective (precomp s B) hsurj⟩

/-- **The fibres of `h¹/h⁰(Eᵛ)` are vector-bundle stacks.**  If `E` is a two-term complex with
finitely generated projective terms then, for every `R`-algebra `B`, the complex of `B`-points of
its dual is a two-term complex of finitely generated projective `B`-modules. -/
theorem isVectorBundleComplex_dualPoints {E : LinearTwoTermComplex R}
    (h : IsVectorBundleComplex E) (B : Type u) [CommRing B] [Algebra R B] :
    IsVectorBundleComplex (dualPoints E B) := by
  obtain ⟨p0, f0⟩ := projective_finite_hom_of_projective_finite E.degreeOne
    h.projective_degreeOne h.finite_degreeOne B
  obtain ⟨p1, f1⟩ := projective_finite_hom_of_projective_finite E.degreeZero
    h.projective_degreeZero h.finite_degreeZero B
  exact ⟨p0, f0, p1, f1⟩

/-! ## Comparison with the truncation of `Cones/DerivedTruncation.lean` -/

section Bridge

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- A chain map of two-term complexes which is bijective in both degrees is a
quasi-isomorphism. -/
theorem isQuasiIsomorphism_of_bijective {E F : LinearTwoTermComplex R} (f : Hom E F)
    (hzero : Function.Bijective f.degreeZero) (hone : Function.Bijective f.degreeOne) :
    f.IsQuasiIsomorphism := by
  refine ⟨⟨fun a b hab => Subtype.ext (hzero.1 (congrArg Subtype.val hab)), ?_⟩, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hzero.2 y
    have hx : E.differential x = 0 := by
      apply hone.1
      rw [f.comm]
      rw [map_zero]
      exact hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro q q' hqq'
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    obtain ⟨x', rfl⟩ := h1mk_surjective q'
    rw [cokernelMap_h1mk, cokernelMap_h1mk, h1mk_eq_iff] at hqq'
    obtain ⟨a, ha⟩ := hqq'
    obtain ⟨b, rfl⟩ := hzero.2 a
    rw [h1mk_eq_iff]
    refine ⟨b, hone.1 ?_⟩
    rw [map_sub, f.comm, ← ha]
  · intro q
    obtain ⟨y, rfl⟩ := h1mk_surjective q
    obtain ⟨x, rfl⟩ := hone.2 y
    exact ⟨h1mk E x, cokernelMap_h1mk f x⟩

/-- With no differential out of degree `0` every element of `K⁰` is a cocycle. -/
theorem cocycles_zero_eq_top (h : K.d 0 1 = 0) : cocycles K 0 = ⊤ := by
  refine le_antisymm le_top (fun x _ => ?_)
  rw [LinearMap.mem_ker]
  exact congrArg (fun m : K.X 0 ⟶ K.X (0 + 1) => (ModuleCat.Hom.hom m) x) h

/-- The comparison from the perfect two-term complex to the two-term truncation: the identity on
the quotient in degree `-1` and the inclusion of the cocycles in degree `0`. -/
def perfectToTwoTermTrunc : Hom (perfectTwoTerm K) (twoTermTrunc K) where
  degreeZero := LinearMap.id
  degreeOne := (cocycles K 0).subtype
  comm x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- **The comparison is a quasi-isomorphism when `K` has no differential out of degree `0`.**
So the Picard groupoid of the perfect two-term complex is the `h¹/h⁰` of
`Cones/DerivedTruncation.lean`, with `h⁰ = H⁻¹(K)` and `h¹ = H⁰(K)`. -/
theorem isQuasiIsomorphism_perfectToTwoTermTrunc (h : K.d 0 1 = 0) :
    (perfectToTwoTermTrunc K).IsQuasiIsomorphism := by
  refine isQuasiIsomorphism_of_bijective _ Function.bijective_id ⟨Subtype.val_injective, ?_⟩
  intro y
  have hy : y ∈ cocycles K 0 := by
    rw [cocycles_zero_eq_top K h]
    trivial
  exact ⟨⟨y, hy⟩, rfl⟩

/-- The Picard groupoid of the perfect two-term complex is the one of the truncation. -/
noncomputable def perfectQuotientEquivalence (h : K.d 0 1 = 0) :
    (perfectTwoTerm K).quotient ≌ (twoTermTrunc K).quotient :=
  (isQuasiIsomorphism_perfectToTwoTermTrunc K h).quotientEquivalence

end Bridge

/-! ## The main statements -/

section Main

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **A bounded complex of finitely generated projective modules with cohomology in `[-1, 0]`
and flat bottom cokernel has vector-bundle two-term model.**  The flatness hypothesis on
`K⁻¹/im d⁻²` is what the Tor-amplitude condition `HasTorAmplitudeIn K (-1) 0` provides. -/
theorem isVectorBundleComplex_perfectTwoTerm (b : ℤ)
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hexact : ∀ i : ℤ, 0 < i → K.ExactAt i)
    (hflat : Module.Flat R (perfectTwoTerm K).degreeZero) :
    IsVectorBundleComplex (perfectTwoTerm K) := by
  obtain ⟨p1, f1⟩ := projective_finite_perfectTwoTerm_degreeOne K b hproj hfin hb hexact
  exact { projective_degreeZero :=
            projective_perfectTwoTerm_degreeZero_of_flat K (hproj (-1)) (hfin (-1))
              (hfin (-2)) hflat
          finite_degreeZero := by
            have h1 := hproj (-1)
            have h2 := hfin (-1)
            have h3 := hfin (-2)
            have : Module.FinitePresentation R (perfectTwoTerm K).degreeZero :=
              finitePresentation_perfectTwoTerm_degreeZero K h1 h2 h3
            infer_instance
          projective_degreeOne := p1
          finite_degreeOne := f1 }

/-- **The unconditional case.**  If the complex already vanishes in degree `-2` there is no
flatness hypothesis: the two-term model has finitely generated projective terms as soon as the
terms of `K` do and `K` is exact above degree `0`. -/
theorem isVectorBundleComplex_perfectTwoTerm_of_isZero (b : ℤ)
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hexact : ∀ i : ℤ, 0 < i → K.ExactAt i)
    (hbot : IsZero (K.X (-2))) :
    IsVectorBundleComplex (perfectTwoTerm K) := by
  obtain ⟨p1, f1⟩ := projective_finite_perfectTwoTerm_degreeOne K b hproj hfin hb hexact
  obtain ⟨p0, f0⟩ := projective_finite_perfectTwoTerm_degreeZero_of_isZero K hbot
    (hproj (-1)) (hfin (-1))
  exact ⟨p0, f0, p1, f1⟩

/-- **The fibrewise vector-bundle-stack statement.**  For a perfect complex of amplitude
`[-1, 0]` the fibre of `h¹/h⁰(Eᵛ)` over every affine test scheme `Spec B` is the translation
groupoid of a two-term complex of finitely generated projective `B`-modules. -/
theorem isVectorBundleComplex_dualPoints_perfectTwoTerm (b : ℤ)
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i)) (hexact : ∀ i : ℤ, 0 < i → K.ExactAt i)
    (hflat : Module.Flat R (perfectTwoTerm K).degreeZero)
    (B : Type u) [CommRing B] [Algebra R B] :
    IsVectorBundleComplex (dualPoints (perfectTwoTerm K) B) :=
  isVectorBundleComplex_dualPoints
    (isVectorBundleComplex_perfectTwoTerm K b hproj hfin hb hexact hflat) B

/-- **The two-term truncation of a complex of finitely generated projectives has vector-bundle
terms**, given flatness of the bottom cokernel.  Here no exactness hypothesis is needed in
positive degrees, because the degree-one term of the truncation is `K⁰` itself. -/
theorem isVectorBundleComplex_twoTermTrunc
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hflat : Module.Flat R (twoTermTrunc K).degreeZero) :
    IsVectorBundleComplex (twoTermTrunc K) := by
  have h1 := hproj (-1)
  have h2 := hfin (-1)
  have h3 := hfin (-2)
  have hfp : Module.FinitePresentation R (twoTermTrunc K).degreeZero :=
    finitePresentation_perfectTwoTerm_degreeZero K h1 h2 h3
  have hfl := hflat
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance, hproj 0, hfin 0⟩

/-- The unconditional version: if the complex vanishes in degree `-2` there is no flatness
hypothesis. -/
theorem isVectorBundleComplex_twoTermTrunc_of_isZero
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hbot : IsZero (K.X (-2))) :
    IsVectorBundleComplex (twoTermTrunc K) := by
  obtain ⟨p0, f0⟩ := projective_finite_perfectTwoTerm_degreeZero_of_isZero K hbot
    (hproj (-1)) (hfin (-1))
  exact ⟨p0, f0, hproj 0, hfin 0⟩

end Main

/-! ## The derived-category statement -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **The projection onto the two-term truncation is a quasi-isomorphism** for a complex with no
differential out of degree `0` which is exact outside degrees `-1` and `0`. -/
theorem quasiIso_truncProjection (hK : K.d 0 1 = 0)
    (hexact : ∀ i : ℤ, i < -1 ∨ 0 < i → K.ExactAt i) : QuasiIso (truncProjection K) := by
  rw [quasiIso_iff]
  intro n
  by_cases hneg : n = -1
  · subst hneg
    exact quasiIsoAt_truncProjection_negOne K
  · by_cases hzero : n = 0
    · subst hzero
      exact quasiIsoAt_truncProjection_zero K hK
    · rw [quasiIsoAt_iff_exactAt _ n (hexact n (by omega))]
      exact HomologicalComplex.ExactAt.of_isZero
        (toCochainComplex_X_isZero (twoTermTrunc K) n hneg hzero)

/-- **A complex exact outside `[-1, 0]` is represented by its two-term truncation.**  This is the
`TruncRep` of `Cones/DerivedTruncationRoof.lean` attached to `Q.obj K`, so its Picard groupoid is
`h¹/h⁰` of the derived object, independently of every choice. -/
noncomputable def truncRepOfExact (hK : K.d 0 1 = 0)
    (hexact : ∀ i : ℤ, i < -1 ∨ 0 < i → K.ExactAt i) :
    TruncRep (DerivedCategory.Q.obj K) where
  complex := (twoTermTrunc K).toCochainComplex
  d_zero_one :=
    (toCochainComplex_X_isZero (twoTermTrunc K) 1 (by norm_num) (by norm_num)).eq_of_tgt _ _
  iso :=
    have hq : QuasiIso (truncProjection K) := quasiIso_truncProjection K hK hexact
    have hiso : IsIso (DerivedCategory.Q.map (truncProjection K)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hq
    (asIso (DerivedCategory.Q.map (truncProjection K))).symm

@[simp]
theorem truncRepOfExact_complex (hK : K.d 0 1 = 0)
    (hexact : ∀ i : ℤ, i < -1 ∨ 0 < i → K.ExactAt i) :
    (truncRepOfExact K hK hexact).complex = (twoTermTrunc K).toCochainComplex :=
  rfl

/-- **`h¹/h⁰(Eᵛ)` is a vector-bundle stack for a perfect object of amplitude `[-1, 0]`.**  For a
bounded complex `K` of finitely generated projective modules with no differential out of degree
`0`, exact outside `[-1, 0]` and with flat bottom cokernel, the derived object `Q.obj K` is
represented by the two-term complex `twoTermTrunc K` of finitely generated projective modules,
and the fibre of the dual over every affine test scheme `Spec B` is the translation groupoid of a
two-term complex of finitely generated projective `B`-modules. -/
theorem isVectorBundleComplex_dualPoints_truncRepOfExact
    (hproj : ∀ i : ℤ, Module.Projective R (K.X i)) (hfin : ∀ i : ℤ, Module.Finite R (K.X i))
    (hflat : Module.Flat R (twoTermTrunc K).degreeZero)
    (B : Type u) [CommRing B] [Algebra R B] :
    IsVectorBundleComplex (dualPoints (twoTermTrunc K) B) :=
  isVectorBundleComplex_dualPoints (isVectorBundleComplex_twoTermTrunc K hproj hfin hflat) B

end Derived

end PicardCriteria

namespace CotangentComplex.PerfectComplex

open PicardCriteria LinearTwoTermComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {E : DerivedCategory (ModuleCat.{u} R)}

/-- **The two-term complex of a global two-term resolution has vector-bundle terms.**  Its terms
are finite free, so `h¹/h⁰(Eᵛ)` is a vector-bundle stack with no further hypothesis. -/
theorem GlobalTwoTermResolution.isVectorBundleComplex (F : GlobalTwoTermResolution E) :
    IsVectorBundleComplex F.linearComplex where
  projective_degreeZero := by
    change Module.Projective R (F.complex.X (-1))
    have h := (F.finiteFree (-1)).free
    infer_instance
  finite_degreeZero := by
    change Module.Finite R (F.complex.X (-1))
    exact (F.finiteFree (-1)).finite
  projective_degreeOne := by
    change Module.Projective R (F.complex.X 0)
    have h := (F.finiteFree 0).free
    infer_instance
  finite_degreeOne := by
    change Module.Finite R (F.complex.X 0)
    exact (F.finiteFree 0).finite

/-- **The fibres of `h¹/h⁰(Eᵛ)` over affine test schemes are vector-bundle stacks**, for every
object with a global two-term resolution. -/
theorem GlobalTwoTermResolution.isVectorBundleComplex_dualPoints (F : GlobalTwoTermResolution E)
    (B : Type u) [CommRing B] [Algebra R B] :
    IsVectorBundleComplex (dualPoints F.linearComplex B) :=
  PicardCriteria.isVectorBundleComplex_dualPoints F.isVectorBundleComplex B

end CotangentComplex.PerfectComplex

end GromovWitten.AlgebraicGeometry
