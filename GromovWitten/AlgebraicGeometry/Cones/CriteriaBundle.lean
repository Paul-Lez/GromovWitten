/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.Criteria
import GromovWitten.AlgebraicGeometry.Cones.DerivedPicard
import GromovWitten.AlgebraicGeometry.Cones.Stack
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Vector-bundle stacks and the big-site `h¹/h⁰` of a dual two-term complex

This file continues `Cones/Criteria.lean` with the two parts of the `h¹/h⁰` story that involve
finiteness and base change.

## Virtual ranks

For a two-term complex `E = [E⁰ → E¹]` of finite free modules the *virtual rank* is
`rank E¹ - rank E⁰`.  The main theorem `PicardCriteria.virtualRank_eq_of_isQuasiIsomorphism`
proves that it is invariant under quasi-isomorphism, by splitting the three-term exact sequence

`0 → E⁰ → F⁰ × E¹ → F¹ → 0`

underlying the mapping cone of a quasi-isomorphism `f : E → F`, which is exact precisely because
`f` induces bijections on `h⁰` and `h¹`.  Consequences: the virtual rank of a global two-term
resolution of a derived object does not depend on the resolution
(`PicardCriteria.virtualRank_resolution_eq`), it agrees with the rank of the resolving complex
computed in `CotangentComplex/PerfectComplex.lean`, and the displayed rank of a vector-bundle
stack of `Cones/Stack.lean` is the virtual rank of the two-term complex of its local
presentation.

## The big-site `h¹/h⁰` of a dual

`PicardCriteria.dualPoints E B` is the two-term complex of `B`-modules

`[Hom_R(E¹, B) → Hom_R(E⁰, B)]`,

the complex of `B`-points of the dual `Eᵛ`; its Picard groupoid is the fibre over `Spec B` of
`h¹/h⁰(Eᵛ)`.  Because the points functor is a `Hom` and not a tensor product, reindexing along a
map of test algebras is strictly functorial, so the fibres assemble into an honest prestack
`PicardCriteria.dualPrestack E : CommAlgCat R ⥤ Cat` on the affine objects of the big fppf site,
with no coherence data left unproved.  A chain map induces a morphism of prestacks
(`PicardCriteria.dualPrestackMap`), a chain homotopy induces an invertible `2`-cell fibrewise
(`PicardCriteria.dualHomotopy`), and a chain homotopy equivalence induces an equivalence on every
fibre (`PicardCriteria.dualHomotopyEquivalence`, `PicardCriteria.dualQuotientEquivalence`),
without any flatness hypothesis.  For a general quasi-isomorphism only the fibrewise criterion
`PicardCriteria.dualIsEquivalence_iff` is available: cohomology of `Hom_R(-, B)` does not commute
with base change unless `B` is flat, so the hypothesis has to be imposed for every `B`
separately, which is exactly what `PicardCriteria.dualEquivalenceOfForallQuasiIso` records.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u

open LinearTwoTermComplex CotangentComplex.PerfectComplex

variable {R : Type u} [CommRing R]

/-! ## Two-term complexes of finite free modules -/

/-- A two-term complex both of whose terms are finite free modules. -/
structure IsFiniteFreeComplex (E : LinearTwoTermComplex R) : Prop where
  /-- The degree-zero term is free. -/
  free_degreeZero : Module.Free R E.degreeZero
  /-- The degree-zero term is of finite type. -/
  finite_degreeZero : Module.Finite R E.degreeZero
  /-- The degree-one term is free. -/
  free_degreeOne : Module.Free R E.degreeOne
  /-- The degree-one term is of finite type. -/
  finite_degreeOne : Module.Finite R E.degreeOne

/-- The virtual rank of a two-term complex: `rank E¹ - rank E⁰`, the Euler characteristic of the
complex in the cohomological convention of `Cones/Picard.lean`. -/
noncomputable def virtualRank (E : LinearTwoTermComplex R) : ℤ :=
  (Module.finrank R E.degreeOne : ℤ) - (Module.finrank R E.degreeZero : ℤ)

@[simp]
theorem virtualRank_eq (E : LinearTwoTermComplex R) :
    virtualRank E = (Module.finrank R E.degreeOne : ℤ) - (Module.finrank R E.degreeZero : ℤ) :=
  rfl

/-! ### The mapping cone of a chain map as a three-term sequence -/

section Cone

variable {E F : LinearTwoTermComplex R} (f : Hom E F)

/-- The first map `E⁰ → F⁰ × E¹` of the three-term sequence underlying the mapping cone of a
chain map of two-term complexes. -/
def coneAlpha : E.degreeZero →ₗ[R] F.degreeZero × E.degreeOne :=
  LinearMap.prod f.degreeZero (-E.differential)

/-- The second map `F⁰ × E¹ → F¹` of the three-term sequence underlying the mapping cone of a
chain map of two-term complexes. -/
def coneBeta : F.degreeZero × E.degreeOne →ₗ[R] F.degreeOne :=
  LinearMap.coprod F.differential f.degreeOne

@[simp]
theorem coneAlpha_apply (x : E.degreeZero) :
    coneAlpha f x = (f.degreeZero x, -E.differential x) :=
  rfl

@[simp]
theorem coneBeta_apply (m : F.degreeZero × E.degreeOne) :
    coneBeta f m = F.differential m.1 + f.degreeOne m.2 :=
  rfl

/-- The mapping cone sequence is a complex. -/
theorem coneBeta_coneAlpha (x : E.degreeZero) : coneBeta f (coneAlpha f x) = 0 := by
  simp only [coneAlpha_apply, coneBeta_apply, map_neg, f.comm]
  abel

/-- If `f` is injective on `h⁰` then the first map of the cone sequence is injective. -/
theorem coneAlpha_injective (hf : Function.Injective f.kernelMap) :
    Function.Injective (coneAlpha f) := by
  intro x y hxy
  have h1 : f.degreeZero x = f.degreeZero y := congrArg Prod.fst hxy
  have h2 : E.differential x = E.differential y := by
    have := congrArg Prod.snd hxy
    simpa [neg_inj] using this
  have hker : x - y ∈ LinearMap.ker E.differential := by
    rw [LinearMap.mem_ker, map_sub, h2, sub_self]
  have hzero : f.kernelMap ⟨x - y, hker⟩ = 0 := by
    apply Subtype.ext
    change f.degreeZero (x - y) = 0
    rw [map_sub, h1, sub_self]
  have hzero' : f.kernelMap ⟨x - y, hker⟩ = f.kernelMap 0 := by
    rw [hzero, map_zero]
  have hval := congrArg Subtype.val (hf hzero')
  change x - y = 0 at hval
  exact sub_eq_zero.mp hval

/-- If `f` is surjective on `h¹` then the second map of the cone sequence is surjective. -/
theorem coneBeta_surjective (hf : Function.Surjective f.cokernelMap) :
    Function.Surjective (coneBeta f) := by
  intro z
  obtain ⟨q, hq⟩ := hf (h1mk F z)
  obtain ⟨y, rfl⟩ := h1mk_surjective q
  have hq' : h1mk F (f.degreeOne y) = h1mk F z := hq
  have hmem : z - f.degreeOne y ∈ LinearMap.range F.differential := by
    rw [← h1mk_eq_zero_iff, h1mk_sub, hq', sub_self]
  obtain ⟨a, ha⟩ := hmem
  refine ⟨(a, y), ?_⟩
  rw [coneBeta_apply, ha]
  abel

/-- Exactness of the cone sequence in the middle, from injectivity of `h¹(f)` and surjectivity of
`h⁰(f)`. -/
theorem ker_coneBeta (hker : Function.Surjective f.kernelMap)
    (hcok : Function.Injective f.cokernelMap) :
    LinearMap.ker (coneBeta f) = LinearMap.range (coneAlpha f) := by
  apply le_antisymm
  · rintro ⟨a, y⟩ hay
    have hay' : F.differential a + f.degreeOne y = 0 := hay
    have hy : h1mk E y = 0 := by
      apply hcok
      rw [cokernelMap_h1mk, map_zero, h1mk_eq_zero_iff]
      exact ⟨-a, by rw [map_neg]; exact neg_eq_of_add_eq_zero_right hay'⟩
    obtain ⟨x, hx⟩ := (h1mk_eq_zero_iff (E := E) y).1 hy
    have hmem : a + f.degreeZero x ∈ LinearMap.ker F.differential := by
      rw [LinearMap.mem_ker, map_add, ← f.comm, hx]
      exact hay'
    obtain ⟨c, hc⟩ := hker ⟨a + f.degreeZero x, hmem⟩
    have hc' : f.degreeZero (c : E.degreeZero) = a + f.degreeZero x := congrArg Subtype.val hc
    refine ⟨(c : E.degreeZero) - x, ?_⟩
    rw [coneAlpha_apply]
    refine Prod.ext ?_ ?_
    · change f.degreeZero ((c : E.degreeZero) - x) = a
      rw [map_sub, hc']
      abel
    · change -E.differential ((c : E.degreeZero) - x) = y
      rw [map_sub, LinearMap.mem_ker.mp c.2, hx]
      abel
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact coneBeta_coneAlpha f x

end Cone

/-! ### Invariance of the virtual rank -/

/-- **The virtual rank is a quasi-isomorphism invariant.**  If a chain map between two-term
complexes of finite free modules induces bijections on `h⁰` and on `h¹` then the two complexes
have the same virtual rank.  The proof splits the exact cone sequence
`0 → E⁰ → F⁰ × E¹ → F¹ → 0`, which is possible because `F¹` is free, hence projective. -/
theorem virtualRank_eq_of_isQuasiIsomorphism [Nontrivial R] {E F : LinearTwoTermComplex R}
    (hE : IsFiniteFreeComplex E) (hF : IsFiniteFreeComplex F) {f : Hom E F}
    (hf : f.IsQuasiIsomorphism) : virtualRank E = virtualRank F := by
  have _ := hE.free_degreeZero
  have _ := hE.finite_degreeZero
  have _ := hE.free_degreeOne
  have _ := hE.finite_degreeOne
  have _ := hF.free_degreeZero
  have _ := hF.finite_degreeZero
  have _ := hF.free_degreeOne
  have _ := hF.finite_degreeOne
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property (coneBeta f) LinearMap.id (coneBeta_surjective f hf.2.2)
  have hsβ : ∀ z : F.degreeOne, coneBeta f (s z) = z := by
    intro z
    exact congrArg (fun m : F.degreeOne →ₗ[R] F.degreeOne => m z) hs
  have hbij : Function.Bijective (LinearMap.coprod (coneAlpha f) s) := by
    constructor
    · intro m m' hmm'
      have hkey : LinearMap.coprod (coneAlpha f) s (m - m') = 0 := by
        rw [map_sub, hmm', sub_self]
      have hsnd : (m - m').2 = 0 := by
        have hb := congrArg (coneBeta f) hkey
        rw [map_zero] at hb
        change coneBeta f (coneAlpha f (m - m').1 + s (m - m').2) = 0 at hb
        rw [map_add, coneBeta_coneAlpha, hsβ, zero_add] at hb
        exact hb
      have hfst : (m - m').1 = 0 := by
        have hz : coneAlpha f (m - m').1 = 0 := by
          change coneAlpha f (m - m').1 + s (m - m').2 = 0 at hkey
          rw [hsnd, map_zero, add_zero] at hkey
          exact hkey
        exact coneAlpha_injective f hf.1.1 (by rw [hz, map_zero])
      have : m - m' = 0 := Prod.ext hfst hsnd
      exact sub_eq_zero.mp this
    · intro m
      have hmem : m - s (coneBeta f m) ∈ LinearMap.ker (coneBeta f) := by
        rw [LinearMap.mem_ker, map_sub, hsβ, sub_self]
      rw [ker_coneBeta f hf.1.2 hf.2.1] at hmem
      obtain ⟨x, hx⟩ := hmem
      refine ⟨(x, coneBeta f m), ?_⟩
      change coneAlpha f x + s (coneBeta f m) = m
      rw [hx]
      abel
  have hfr := (LinearEquiv.ofBijective _ hbij).finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod] at hfr
  simp only [virtualRank_eq]
  omega

/-- The virtual rank is invariant under chain homotopy equivalence. -/
theorem virtualRank_eq_of_homotopyEquivalence [Nontrivial R] {E F : LinearTwoTermComplex R}
    (hE : IsFiniteFreeComplex E) (hF : IsFiniteFreeComplex F) (e : HomotopyEquivalence E F) :
    virtualRank E = virtualRank F :=
  virtualRank_eq_of_isQuasiIsomorphism hE hF e.isQuasiIsomorphism

/-! ### Comparison with the rank of a cochain complex -/

/-- For a cochain complex supported in degrees `-1` and `0`, the alternating-sum rank of
`CotangentComplex/PerfectComplex.lean` is the virtual rank of the underlying two-term complex. -/
theorem rank_eq_virtualRank [Nontrivial R] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : IsSupportedIn K (-1) 0) : rank K = virtualRank (ofCochainComplex K) := by
  rw [rank_eq_of_isSupportedIn_negOne_zero h]
  rfl

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {D : DerivedCategory (ModuleCat.{u} R)}

/-- The two-term complex underlying a global two-term resolution has finite free terms. -/
theorem isFiniteFreeComplex_linearComplex (P : GlobalTwoTermResolution D) :
    IsFiniteFreeComplex P.linearComplex where
  free_degreeZero := (P.finiteFree (-1)).free
  finite_degreeZero := (P.finiteFree (-1)).finite
  free_degreeOne := (P.finiteFree 0).free
  finite_degreeOne := (P.finiteFree 0).finite

/-- The virtual rank of a global two-term resolution is the virtual rank of its underlying
two-term complex, that is, the derived rank is the naive Euler characteristic. -/
theorem virtualRank_resolution [Nontrivial R] (P : GlobalTwoTermResolution D) :
    P.virtualRank = virtualRank P.linearComplex :=
  rank_eq_virtualRank P.supported

/-- **The derived virtual rank is independent of the resolution.**  Any two global two-term
resolutions of the same derived object have the same virtual rank, because the chain-level
comparison of `Cones/DerivedPicard.lean` is a quasi-isomorphism of complexes of finite free
modules. -/
theorem virtualRank_resolution_eq [Nontrivial R] (P P' : GlobalTwoTermResolution D) :
    P.virtualRank = P'.virtualRank := by
  obtain ⟨c⟩ := GlobalTwoTermResolution.hasChainComparison P P'
  rw [virtualRank_resolution, virtualRank_resolution]
  exact virtualRank_eq_of_isQuasiIsomorphism (isFiniteFreeComplex_linearComplex P)
    (isFiniteFreeComplex_linearComplex P') c.isQuasiIso

end Derived

/-! ### Comparison with the displayed rank of a vector-bundle stack -/

/-- The two-term complex presented by a matrix has finite free terms. -/
theorem isFiniteFreeComplex_freeTwoTermComplex {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R) : IsFiniteFreeComplex (freeTwoTermComplex d) where
  free_degreeZero := inferInstanceAs (Module.Free R (Fin r₀ → R))
  finite_degreeZero := inferInstanceAs (Module.Finite R (Fin r₀ → R))
  free_degreeOne := inferInstanceAs (Module.Free R (Fin r₁ → R))
  finite_degreeOne := inferInstanceAs (Module.Finite R (Fin r₁ → R))

/-- The virtual rank of the two-term complex of a matrix is the difference of the two sizes. -/
@[simp]
theorem virtualRank_freeTwoTermComplex [Nontrivial R] {r₀ r₁ : ℕ}
    (d : Matrix (Fin r₁) (Fin r₀) R) :
    virtualRank (freeTwoTermComplex d) = (r₁ : ℤ) - (r₀ : ℤ) := by
  rw [virtualRank_eq]
  change ((Module.finrank R (Fin r₁ → R) : ℤ)) - ((Module.finrank R (Fin r₀ → R) : ℤ)) = _
  rw [Module.finrank_fin_fun, Module.finrank_fin_fun]

/-- The displayed rank of a vector-bundle stack is the virtual rank of the two-term complex of
its local quotient presentation. -/
theorem stackRank_eq_virtualRank {base : FppfStack.{u}} {O : FppfScalarRings.{u}}
    (E : VectorBundleStack base O)
    [Nontrivial (O.ring E.presentation.chart.scheme)] :
    E.stackRank = virtualRank (freeTwoTermComplex E.presentation.differential) := by
  rw [VectorBundleStack.stackRank_eq, virtualRank_freeTwoTermComplex]

/-! ## The `h¹/h⁰` prestack of the dual on the big fppf site -/

section DualPoints

/-- Precomposition with an `R`-linear map, as a `B`-linear map between modules of `B`-points.
This is the coordinate description of the pullback of a map of vector bundles to a test
algebra. -/
def precomp {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (B : Type u) [CommRing B] [Algebra R B] :
    (N →ₗ[R] B) →ₗ[B] (M →ₗ[R] B) where
  toFun l := l.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem precomp_apply {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (B : Type u) [CommRing B] [Algebra R B] (l : N →ₗ[R] B) (x : M) :
    precomp g B l x = l (g x) :=
  rfl

/-- The two-term complex of `B`-points of the dual `Eᵛ` of a two-term complex `E`:

`[Hom_R(E¹, B) → Hom_R(E⁰, B)]`,

a two-term complex of `B`-modules whose Picard groupoid is the fibre of `h¹/h⁰(Eᵛ)` over the
affine test scheme `Spec B`. -/
def dualPoints (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R B] :
    LinearTwoTermComplex B where
  degreeZero := E.degreeOne →ₗ[R] B
  degreeOne := E.degreeZero →ₗ[R] B
  differential := precomp E.differential B

@[simp]
theorem dualPoints_differential (E : LinearTwoTermComplex R) (B : Type u) [CommRing B]
    [Algebra R B] : (dualPoints E B).differential = precomp E.differential B :=
  rfl

variable (E : LinearTwoTermComplex R) (B B' B'' : Type u) [CommRing B] [Algebra R B]
  [CommRing B'] [Algebra R B'] [CommRing B''] [Algebra R B'']

/-- An object of the fibre over `Spec B`, read as a linear functional on `E⁰`. -/
abbrev dualBack (x : (dualPoints E B).quotient) : E.degreeZero →ₗ[R] B :=
  x.back

/-- An arrow of the fibre over `Spec B`, read as a linear functional on `E¹`. -/
abbrev dualVal {x y : (dualPoints E B).quotient} (a : x ⟶ y) : E.degreeOne →ₗ[R] B :=
  a.val

/-- A degree-zero element of the fibre complex, read as a linear functional on `E¹`. -/
abbrev dualDegreeZero (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R B]
    (l : (dualPoints E B).degreeZero) : E.degreeOne →ₗ[R] B :=
  l

/-- A degree-one element of the fibre complex, read as a linear functional on `E⁰`. -/
abbrev dualDegreeOne (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R B]
    (l : (dualPoints E B).degreeOne) : E.degreeZero →ₗ[R] B :=
  l

/-- A linear functional on `E¹`, read as a degree-zero element of the fibre complex. -/
abbrev ofDualDegreeZero (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R B]
    (l : E.degreeOne →ₗ[R] B) : (dualPoints E B).degreeZero :=
  l

/-- The translation law of an arrow of the fibre, evaluated at an element of `E⁰`. -/
theorem dualPoints_translate {x y : (dualPoints E B).quotient} (a : x ⟶ y) (z : E.degreeZero) :
    dualBack E B x z + dualVal E B a (E.differential z) = dualBack E B y z :=
  congrArg (fun m : E.degreeZero →ₗ[R] B => m z) a.translate

/-- Reindexing the fibre of `h¹/h⁰(Eᵛ)` along a map of test algebras, by postcomposition. -/
def dualPointsMap (φ : B →ₐ[R] B') :
    (dualPoints E B).quotient ⥤ (dualPoints E B').quotient where
  obj x := ⟨φ.toLinearMap.comp (dualBack E B x)⟩
  map {x y} a :=
    { val := φ.toLinearMap.comp (dualVal E B a)
      translate := by
        refine LinearMap.ext fun z => ?_
        change φ (dualBack E B x z) + φ (dualVal E B a (E.differential z))
          = φ (dualBack E B y z)
        rw [← map_add, dualPoints_translate] }
  map_id x := by
    apply TwoTermQuotient.Hom.ext
    exact LinearMap.comp_zero _
  map_comp a b := by
    apply TwoTermQuotient.Hom.ext
    exact LinearMap.comp_add _ _ _

@[simp]
theorem dualPointsMap_obj_back (φ : B →ₐ[R] B') (x : (dualPoints E B).quotient) :
    dualBack E B' ((dualPointsMap E B B' φ).obj x) = φ.toLinearMap.comp (dualBack E B x) :=
  rfl

@[simp]
theorem dualPointsMap_map_val (φ : B →ₐ[R] B') {x y : (dualPoints E B).quotient} (a : x ⟶ y) :
    dualVal E B' ((dualPointsMap E B B' φ).map a) = φ.toLinearMap.comp (dualVal E B a) :=
  rfl

/-- Reindexing along the identity is the identity: the prestack is strictly unital. -/
theorem dualPointsMap_id : dualPointsMap E B B (AlgHom.id R B) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => quotient_ext rfl) fun x y a => ?_
  apply TwoTermQuotient.Hom.ext
  simp only [TwoTermQuotient.comp_val, eqToHom_val, Functor.id_map, zero_add, add_zero]
  exact LinearMap.id_comp _

/-- Reindexing is strictly functorial in the test algebra. -/
theorem dualPointsMap_comp (φ : B →ₐ[R] B') (ψ : B' →ₐ[R] B'') :
    dualPointsMap E B B'' (ψ.comp φ) = dualPointsMap E B B' φ ⋙ dualPointsMap E B' B'' ψ := by
  refine CategoryTheory.Functor.ext (fun x => quotient_ext rfl) fun x y a => ?_
  apply TwoTermQuotient.Hom.ext
  simp only [TwoTermQuotient.comp_val, eqToHom_val, Functor.comp_map, zero_add, add_zero]
  rfl

/-- **The `h¹/h⁰` prestack of a dual two-term complex on the affine objects of the big fppf
site.**  Its value on a test algebra `B` is the translation groupoid of the complex of
`B`-points of `Eᵛ`, and functoriality is strict: no coherence datum is left unproved, because
the points of a dual are a `Hom` and reindexing is postcomposition. -/
def dualPrestack (E : LinearTwoTermComplex R) : CommAlgCat.{u} R ⥤ Cat.{u, u} where
  obj B := Cat.of (dualPoints E B).quotient
  map φ := Functor.toCatHom (dualPointsMap E _ _ φ.hom)
  map_id B := Cat.ext (dualPointsMap_id E B)
  map_comp φ ψ := Cat.ext (dualPointsMap_comp E _ _ _ φ.hom ψ.hom)

@[simp]
theorem dualPrestack_obj (C : CommAlgCat.{u} R) :
    (dualPrestack E).obj C = Cat.of (dualPoints E C).quotient :=
  rfl

/-! ### Morphisms, homotopies and equivalences of the fibres -/

/-- A chain map `f : E ⟶ F` induces, contravariantly, a chain map of the complexes of `B`-points
of the duals. -/
def dualHom {E F : LinearTwoTermComplex R} (f : Hom E F) (B : Type u) [CommRing B]
    [Algebra R B] : Hom (dualPoints F B) (dualPoints E B) where
  degreeZero := precomp f.degreeOne B
  degreeOne := precomp f.degreeZero B
  comm l := by
    refine LinearMap.ext fun z => ?_
    change dualDegreeZero F B l (F.differential (f.degreeZero z))
      = dualDegreeZero F B l (f.degreeOne (E.differential z))
    exact congrArg (fun w => dualDegreeZero F B l w) (f.comm z).symm

@[simp]
theorem dualHom_degreeZero {E F : LinearTwoTermComplex R} (f : Hom E F) :
    (dualHom f B).degreeZero = precomp f.degreeOne B :=
  rfl

@[simp]
theorem dualHom_degreeOne {E F : LinearTwoTermComplex R} (f : Hom E F) :
    (dualHom f B).degreeOne = precomp f.degreeZero B :=
  rfl

/-- Dualising the identity chain map gives the identity. -/
theorem dualHom_id : dualHom (Hom.id E) B = Hom.id (dualPoints E B) :=
  rfl

/-- Dualising reverses composition. -/
theorem dualHom_comp {E F G : LinearTwoTermComplex R} (f : Hom E F) (g : Hom F G) :
    dualHom (g.comp f) B = (dualHom f B).comp (dualHom g B) :=
  rfl

/-- The fibrewise morphism induced by a chain map commutes strictly with reindexing along a map
of test algebras: `h¹/h⁰(fᵛ)` is a morphism of prestacks. -/
theorem dualHom_quotientFunctor_naturality {E F : LinearTwoTermComplex R} (f : Hom E F)
    (φ : B →ₐ[R] B') :
    (dualHom f B).quotientFunctor ⋙ dualPointsMap E B B' φ =
      dualPointsMap F B B' φ ⋙ (dualHom f B').quotientFunctor :=
  rfl

/-- A chain homotopy dualises to a chain homotopy of the complexes of `B`-points, for every test
algebra `B`. -/
def dualChainHomotopy {E F : LinearTwoTermComplex R} {f g : Hom E F} (H : ChainHomotopy f g) :
    ChainHomotopy (dualHom f B) (dualHom g B) where
  homotopy := precomp H.homotopy B
  degreeZero l := by
    refine LinearMap.ext fun z => ?_
    change dualDegreeZero F B l (g.degreeOne z)
      = dualDegreeZero F B l (f.degreeOne z)
        + dualDegreeZero F B l (F.differential (H.homotopy z))
    rw [← map_add]
    exact congrArg (fun w => dualDegreeZero F B l w) (H.degreeOne z)
  degreeOne l := by
    refine LinearMap.ext fun z => ?_
    change dualDegreeOne F B l (g.degreeZero z)
      = dualDegreeOne F B l (f.degreeZero z)
        + dualDegreeOne F B l (H.homotopy (E.differential z))
    rw [← map_add]
    exact congrArg (fun w => dualDegreeOne F B l w) (H.degreeZero z)

/-- A chain homotopy equivalence dualises to a chain homotopy equivalence of the complexes of
`B`-points, for every test algebra `B`; no flatness is needed, because homotopies are preserved
by dualisation. -/
def dualHomotopyEquivalence {E F : LinearTwoTermComplex R} (e : HomotopyEquivalence E F) :
    HomotopyEquivalence (dualPoints F B) (dualPoints E B) where
  hom := dualHom e.hom B
  inv := dualHom e.inv B
  unit := (dualChainHomotopy B e.counit).symm
  counit := (dualChainHomotopy B e.unit).symm

/-- **Fibrewise equivalence from a chain homotopy equivalence.**  A homotopy equivalence of
two-term complexes induces an equivalence of the fibres of the two `h¹/h⁰` prestacks of the duals
over every affine test scheme. -/
noncomputable def dualQuotientEquivalence {E F : LinearTwoTermComplex R}
    (e : HomotopyEquivalence E F) :
    (dualPoints F B).quotient ≌ (dualPoints E B).quotient :=
  (dualHomotopyEquivalence B e).quotientEquivalence

/-- **The fibrewise equivalence criterion on the big site.**  Over a fixed test algebra `B`, the
morphism of fibres induced by a chain map is an equivalence exactly when the dualised chain map
induces bijections on `h⁰` and `h¹` over `B`. -/
theorem dualIsEquivalence_iff {E F : LinearTwoTermComplex R} (f : Hom E F) :
    (dualHom f B).quotientFunctor.IsEquivalence ↔ (dualHom f B).IsQuasiIsomorphism :=
  isEquivalence_iff (dualHom f B)

/-- A chain map whose dual is a quasi-isomorphism after every base change induces an equivalence
of fibres over every test algebra.  The hypothesis has to be imposed base change by base change:
the cohomology of `Hom_R(-, B)` is not computed by base change from the cohomology over `R`
unless `B` is flat over `R`, so no single condition over `R` implies it. -/
theorem dualEquivalence_of_forall_quasiIso {E F : LinearTwoTermComplex R} (f : Hom E F)
    (h : ∀ (C : Type u) [CommRing C] [Algebra R C], (dualHom f C).IsQuasiIsomorphism) :
    (dualHom f B).quotientFunctor.IsEquivalence :=
  (dualIsEquivalence_iff B f).2 (h B)

/-! ### The fibrewise cohomology of the dual -/

/-- **Automorphisms in the fibre are the `B`-points of the dual of `h¹`.**  The degree-zero
cohomology of the complex of `B`-points of `Eᵛ` is `Hom_R(h¹(E), B)`; by
`PicardCriteria.autEquivKernel` this is the automorphism group of every object of the fibre of
`h¹/h⁰(Eᵛ)` over `Spec B`.  In particular this cohomology *is* computed from `h¹(E)` for every
test algebra, being a `Hom` out of it; it is `h¹` of the dual that fails to base change. -/
def dualH0Equiv : h0 (dualPoints E B) ≃ₗ[B] (h1 E →ₗ[R] B) where
  toFun l :=
    Submodule.liftQ (LinearMap.range E.differential) (dualDegreeZero E B l.1) (by
      rintro _ ⟨x, rfl⟩
      have hl : precomp E.differential B (dualDegreeZero E B l.1) = 0 := l.2
      exact congrArg (fun m : E.degreeZero →ₗ[R] B => m x) hl)
  invFun m := ⟨ofDualDegreeZero E B (m.comp (Submodule.mkQ (LinearMap.range E.differential))), by
    change precomp E.differential B
        (ofDualDegreeZero E B (m.comp (Submodule.mkQ (LinearMap.range E.differential)))) = 0
    refine LinearMap.ext fun x => ?_
    change m (h1mk E (E.differential x)) = 0
    rw [(h1mk_eq_zero_iff (E := E) (E.differential x)).2 ⟨x, rfl⟩, map_zero]⟩
  left_inv l := by
    apply Subtype.ext
    rfl
  right_inv m := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl
  map_add' l l' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl
  map_smul' b l := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := h1mk_surjective q
    rfl

@[simp]
theorem dualH0Equiv_apply (l : h0 (dualPoints E B)) (x : E.degreeOne) :
    dualH0Equiv E B l (h1mk E x) = dualDegreeZero E B l.1 x :=
  rfl

end DualPoints

end PicardCriteria

end GromovWitten.AlgebraicGeometry
