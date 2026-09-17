/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/

import GromovWitten.AlgebraicGeometry.Cones.CriteriaBundle
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# The affine Behrend–Fantechi criterion for obstruction theories

Behrend–Fantechi, Theorem 4.5, says that a morphism `φ : E ⟶ L` of objects of `D^{[-1,0]}` is an
obstruction theory — `H⁰(φ)` an isomorphism and `H⁻¹(φ)` an epimorphism — if and only if the
induced morphism of cone stacks `h¹/h⁰(Lᵛ) → h¹/h⁰(Eᵛ)` is a closed immersion.  This file proves
that equivalence in the affine, fibrewise two-term model of `Cones/Picard.lean`,
`Cones/Criteria.lean` and `Cones/CriteriaBundle.lean`, where "closed immersion" is the
cohomological monomorphism criterion `PicardCriteria.IsCohomologicalMono`.

## Conventions

A `LinearTwoTermComplex R` is displayed as `[E.degreeZero → E.degreeOne]` and realised as a
cochain complex with `E.degreeZero` in cohomological degree `-1` and `E.degreeOne` in degree `0`
(`LinearTwoTermComplex.toCochainComplex`).  Therefore

* `H⁻¹` is `PicardCriteria.h0`, the kernel of the differential, and the map it induces is
  `LinearTwoTermComplex.Hom.kernelMap`;
* `H⁰` is `PicardCriteria.h1`, the cokernel of the differential, and the map it induces is
  `LinearTwoTermComplex.Hom.cokernelMap`.

So `PicardCriteria.IsObstructionTheory φ` asks for `φ.cokernelMap` bijective and
`φ.kernelMap` surjective.

## Main results

* `PicardCriteria.IsObstructionTheory`: the definition, together with `IsObstructionTheory.id`,
  invariance under composition with quasi-isomorphisms
  (`IsObstructionTheory.comp_quasiIso`, `IsObstructionTheory.quasiIso_comp`), under chain
  homotopy (`IsObstructionTheory.of_chainHomotopy`) and under chain homotopy equivalences of
  either argument (`IsObstructionTheory.comp_homotopyEquivalence`,
  `IsObstructionTheory.homotopyEquivalence_comp`).
* `PicardCriteria.IsObstructionTheory.isCohomologicalMono_dualHom`: the forward direction of
  Behrend–Fantechi 4.5.  If `φ` is an obstruction theory then for **every** `R`-algebra `B`, with
  no projectivity or finiteness hypothesis whatsoever, the dualised chain map `dualHom φ B` is a
  cohomological monomorphism, hence `h¹/h⁰(Lᵛ)(B) → h¹/h⁰(Eᵛ)(B)` is fully faithful
  (`IsObstructionTheory.dualFullyFaithful`) and injective on isomorphism classes
  (`IsObstructionTheory.dual_injective_isoClass`), naturally in `B`
  (`IsObstructionTheory.dual_naturality`).
* `PicardCriteria.isObstructionTheory_of_trivSqZeroExt` and
  `PicardCriteria.isObstructionTheory_of_forall_isCohomologicalMono`: the converse.  Only the
  trivial square-zero extensions `B = TrivSqZeroExt R M` are used as test algebras: they turn
  `Hom_R(-, B)` into `Hom_R(-, R) × Hom_R(-, M)`, so that arbitrary module coefficients `M` are
  available.  Taking `M = h¹(E)` and `M = coker H⁰(φ)` gives `H⁰(φ)` bijective, and taking
  `M = coker(E⁻¹ → L⁻¹ ⊕ E⁰)` gives exactness of the mapping cone sequence in the middle, hence
  `H⁻¹(φ)` surjective.  `PicardCriteria.isObstructionTheory_iff_forall_isCohomologicalMono`
  packages both directions.
* `PicardCriteria.obstructionConeFunctor`: the obstruction cone attached to a cone `ι` inside
  `h¹/h⁰(Lᵛ)(B)`, namely its image in `h¹/h⁰(Eᵛ)(B)`; it is fully faithful
  (`obstructionConeFunctorFullyFaithful`), reflects isomorphism classes
  (`obstructionConeFunctor_injective_isoClass`), commutes with reindexing along a map of test
  algebras (`obstructionConeFunctor_dualPointsMap`), and changes by the equivalence
  `PicardCriteria.dualQuotientEquivalence` when `E` is replaced by a homotopy equivalent complex
  (`obstructionConeFunctor_comp_homotopyEquivalence`).

Nothing is stored as a structure field except the two cohomological hypotheses; every geometric
conclusion is derived.
-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

universe u v

open LinearTwoTermComplex

variable {R : Type u} [CommRing R] {E L : LinearTwoTermComplex R}

/-! ## Obstruction theories in the two-term model -/

/-- **An obstruction theory in the affine two-term model.**

With the cohomological convention of `Cones/Picard.lean` (the source of the differential sits in
degree `-1`), this says that `H⁰(φ)` is an isomorphism and `H⁻¹(φ)` is an epimorphism, which is
the Behrend–Fantechi condition on a morphism to the cotangent complex `[I/I² → Ω]`. -/
structure IsObstructionTheory (φ : Hom E L) : Prop where
  /-- `H⁰(φ)`, the map induced on the cokernel of the differential, is bijective. -/
  bijective_cokernelMap : Function.Bijective φ.cokernelMap
  /-- `H⁻¹(φ)`, the map induced on the kernel of the differential, is surjective. -/
  surjective_kernelMap : Function.Surjective φ.kernelMap

namespace IsObstructionTheory

/-- The identity chain map is the tautological obstruction theory. -/
theorem id (L : LinearTwoTermComplex R) : IsObstructionTheory (Hom.id L) where
  bijective_cokernelMap := by
    rw [Hom.cokernelMap_id, LinearMap.id_coe]
    exact Function.bijective_id
  surjective_kernelMap := by
    rw [Hom.kernelMap_id, LinearMap.id_coe]
    exact Function.surjective_id

/-- Postcomposing an obstruction theory with a quasi-isomorphism gives an obstruction theory. -/
theorem comp_quasiIso {L' : LinearTwoTermComplex R} {φ : Hom E L} (h : IsObstructionTheory φ)
    {q : Hom L L'} (hq : q.IsQuasiIsomorphism) : IsObstructionTheory (q.comp φ) where
  bijective_cokernelMap := by
    rw [Hom.cokernelMap_comp, LinearMap.coe_comp]
    exact hq.2.comp h.bijective_cokernelMap
  surjective_kernelMap := by
    rw [Hom.kernelMap_comp, LinearMap.coe_comp]
    exact hq.1.2.comp h.surjective_kernelMap

/-- Precomposing an obstruction theory with a quasi-isomorphism gives an obstruction theory. -/
theorem quasiIso_comp {E' : LinearTwoTermComplex R} {φ : Hom E L} (h : IsObstructionTheory φ)
    {q : Hom E' E} (hq : q.IsQuasiIsomorphism) : IsObstructionTheory (φ.comp q) where
  bijective_cokernelMap := by
    rw [Hom.cokernelMap_comp, LinearMap.coe_comp]
    exact h.bijective_cokernelMap.comp hq.2
  surjective_kernelMap := by
    rw [Hom.kernelMap_comp, LinearMap.coe_comp]
    exact h.surjective_kernelMap.comp hq.1.2

/-- Being an obstruction theory only depends on the chain homotopy class: chain homotopic maps
induce the same maps on `H⁻¹` and `H⁰`. -/
theorem of_chainHomotopy {φ φ' : Hom E L} (h : IsObstructionTheory φ)
    (H : ChainHomotopy φ φ') : IsObstructionTheory φ' where
  bijective_cokernelMap := H.cokernelMap_eq ▸ h.bijective_cokernelMap
  surjective_kernelMap := H.kernelMap_eq ▸ h.surjective_kernelMap

/-- Transport an obstruction theory along a chain homotopy equivalence of the target. -/
theorem comp_homotopyEquivalence {L' : LinearTwoTermComplex R} {φ : Hom E L}
    (h : IsObstructionTheory φ) (e : HomotopyEquivalence L L') :
    IsObstructionTheory (e.hom.comp φ) :=
  h.comp_quasiIso e.isQuasiIsomorphism

/-- Transport an obstruction theory along a chain homotopy equivalence of the source. -/
theorem homotopyEquivalence_comp {E' : LinearTwoTermComplex R} {φ : Hom E L}
    (h : IsObstructionTheory φ) (e : HomotopyEquivalence E' E) :
    IsObstructionTheory (φ.comp e.hom) :=
  h.quasiIso_comp e.isQuasiIsomorphism

end IsObstructionTheory

/-! ## The degree `-1` part of the dual: precomposition with `H⁰(φ)` -/

/-- Precomposition with a bijective linear map is a bijection on linear functionals with values
in any module. -/
theorem bijective_precomp_of_bijective {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : M →ₗ[R] N} (hg : Function.Bijective g)
    (B : Type u) [AddCommGroup B] [Module R B] :
    Function.Bijective (fun m : N →ₗ[R] B => m.comp g) := by
  constructor
  · intro m m' hmm'
    refine LinearMap.ext fun n => ?_
    obtain ⟨x, rfl⟩ := hg.2 n
    exact congrArg (fun k : M →ₗ[R] B => k x) hmm'
  · intro n
    refine ⟨n.comp (LinearEquiv.ofBijective g hg).symm.toLinearMap, ?_⟩
    refine LinearMap.ext fun x => ?_
    exact congrArg n ((LinearEquiv.ofBijective g hg).symm_apply_apply x)

/-- Under the identification `h⁰(Eᵛ(B)) = Hom_R(h¹(E), B)` of `PicardCriteria.dualH0Equiv`, the
map induced by `dualHom φ B` on `h⁰` is precomposition with `H⁰(φ) = φ.cokernelMap`. -/
theorem dualH0Equiv_kernelMap (φ : Hom E L) (B : Type u) [CommRing B] [Algebra R B]
    (l : h0 (dualPoints L B)) :
    dualH0Equiv E B ((dualHom φ B).kernelMap l)
      = (dualH0Equiv L B l).comp φ.cokernelMap := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := h1mk_surjective q
  rfl

/-- The map induced by `dualHom φ B` on `h⁰` is bijective exactly when precomposition with
`H⁰(φ)` is bijective on `B`-valued functionals. -/
theorem bijective_kernelMap_dualHom_iff (φ : Hom E L) (B : Type u) [CommRing B] [Algebra R B] :
    Function.Bijective (dualHom φ B).kernelMap ↔
      Function.Bijective (fun m : h1 L →ₗ[R] B => m.comp φ.cokernelMap) := by
  have key : ⇑(dualH0Equiv E B) ∘ ⇑(dualHom φ B).kernelMap
      = (fun m : h1 L →ₗ[R] B => m.comp φ.cokernelMap) ∘ ⇑(dualH0Equiv L B) :=
    funext fun l => dualH0Equiv_kernelMap φ B l
  rw [← Function.Bijective.of_comp_iff' (dualH0Equiv E B).bijective, key,
    Function.Bijective.of_comp_iff _ (dualH0Equiv L B).bijective]

/-! ## The forward direction of Behrend–Fantechi 4.5 -/

/-- A linear functional on `E⁻¹`, read as a degree-one element of the fibre complex of the dual.
This is the counterpart of `PicardCriteria.ofDualDegreeZero`; it is an `abbrev` so that the
identification stays reducible. -/
abbrev ofDualDegreeOne (E : LinearTwoTermComplex R) (B : Type u) [CommRing B] [Algebra R B]
    (l : E.degreeZero →ₗ[R] B) : (dualPoints E B).degreeOne :=
  l

/-- **Descent of a pair of functionals along the mapping cone, for an obstruction theory.**

If `φ` is an obstruction theory, the mapping cone sequence `E⁻¹ → L⁻¹ ⊕ E⁰ → L⁰ → 0` is exact,
so a functional `(a, y) ↦ λ a + μ y` on `L⁻¹ ⊕ E⁰` killing the image of `E⁻¹` — which is what
`λ ∘ φ⁻¹ = μ ∘ d_E` says — descends along the surjection to a functional `ν` on `L⁰` with
`ν ∘ d_L = λ`. -/
theorem exists_lift_of_isObstructionTheory {φ : Hom E L} (h : IsObstructionTheory φ)
    {B : Type u} [CommRing B] [Algebra R B]
    (lam : L.degreeZero →ₗ[R] B) (mu : E.degreeOne →ₗ[R] B)
    (hcomm : ∀ x : E.degreeZero, lam (φ.degreeZero x) = mu (E.differential x)) :
    ∃ nu : L.degreeOne →ₗ[R] B, ∀ a : L.degreeZero, nu (L.differential a) = lam a := by
  have hbeta : Function.Surjective (coneBeta φ) :=
    coneBeta_surjective φ h.bijective_cokernelMap.2
  have hexact : LinearMap.ker (coneBeta φ) = LinearMap.range (coneAlpha φ) :=
    ker_coneBeta φ h.surjective_kernelMap h.bijective_cokernelMap.1
  have hle : LinearMap.ker (coneBeta φ) ≤ LinearMap.ker (LinearMap.coprod lam mu) := by
    rw [hexact]
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, coneAlpha_apply, LinearMap.coprod_apply, map_neg, ← hcomm x,
      add_neg_cancel]
  refine ⟨(Submodule.liftQ _ (LinearMap.coprod lam mu) hle).comp
    ((LinearMap.quotKerEquivOfSurjective (coneBeta φ) hbeta).symm.toLinearMap), fun a => ?_⟩
  have hmk : (LinearMap.quotKerEquivOfSurjective (coneBeta φ) hbeta).symm (L.differential a)
      = Submodule.Quotient.mk ((a, 0) : L.degreeZero × E.degreeOne) := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, coneBeta_apply,
      map_zero, add_zero]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hmk,
    Submodule.liftQ_apply, LinearMap.coprod_apply, map_zero, add_zero]

/-- **Injectivity on `h¹` of the dual.**  This is the heart of the forward direction: a
`B`-valued functional on `L⁻¹` whose restriction along `φ⁻¹` is a coboundary is itself a
coboundary. -/
theorem injective_cokernelMap_dualHom {φ : Hom E L} (h : IsObstructionTheory φ) (B : Type u)
    [CommRing B] [Algebra R B] : Function.Injective (dualHom φ B).cokernelMap := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  obtain ⟨lam, rfl⟩ := h1mk_surjective p
  rw [cokernelMap_h1mk, h1mk_eq_zero_iff] at hp
  obtain ⟨mu, hmu⟩ := hp
  obtain ⟨nu, hnu⟩ := exists_lift_of_isObstructionTheory h (dualDegreeOne L B lam)
    (dualDegreeZero E B mu)
    (fun x => (congrArg (fun m : E.degreeZero →ₗ[R] B => m x) hmu).symm)
  rw [h1mk_eq_zero_iff]
  refine ⟨ofDualDegreeZero L B nu, ?_⟩
  change nu.comp L.differential = dualDegreeOne L B lam
  exact LinearMap.ext hnu

/-- **Behrend–Fantechi 4.5, forward direction, fibrewise.**

If `φ : E ⟶ L` is an obstruction theory in the two-term model, then for every `R`-algebra `B` the
dualised chain map is a cohomological monomorphism: `h⁰` is bijective and `h¹` is injective.  No
projectivity, flatness or finiteness hypothesis is needed. -/
theorem IsObstructionTheory.isCohomologicalMono_dualHom {φ : Hom E L}
    (h : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra R B] :
    IsCohomologicalMono (dualHom φ B) :=
  ⟨(bijective_kernelMap_dualHom_iff φ B).2
      (bijective_precomp_of_bijective h.bijective_cokernelMap B),
    injective_cokernelMap_dualHom h B⟩

/-- The fibre morphism `h¹/h⁰(Lᵛ)(B) → h¹/h⁰(Eᵛ)(B)` of an obstruction theory is fully
faithful. -/
noncomputable def IsObstructionTheory.dualFullyFaithful {φ : Hom E L}
    (h : IsObstructionTheory φ) (B : Type u) [CommRing B] [Algebra R B] :
    (dualHom φ B).quotientFunctor.FullyFaithful :=
  (h.isCohomologicalMono_dualHom B).fullyFaithful

/-- The fibre morphism of an obstruction theory is injective on isomorphism classes. -/
theorem IsObstructionTheory.dual_injective_isoClass {φ : Hom E L} (h : IsObstructionTheory φ)
    (B : Type u) [CommRing B] [Algebra R B] {x y : (dualPoints L B).quotient}
    (hxy : Nonempty ((dualHom φ B).quotientFunctor.obj x
      ≅ (dualHom φ B).quotientFunctor.obj y)) :
    Nonempty (x ≅ y) :=
  (h.isCohomologicalMono_dualHom B).injective_isoClass hxy

/-- The fibrewise closed immersions of an obstruction theory are natural in the test algebra:
they form a morphism of the prestacks of `Cones/CriteriaBundle.lean`. -/
theorem IsObstructionTheory.dual_naturality (φ : Hom E L) (B B' : Type u) [CommRing B]
    [Algebra R B] [CommRing B'] [Algebra R B'] (ψ : B →ₐ[R] B') :
    (dualHom φ B).quotientFunctor ⋙ dualPointsMap E B B' ψ =
      dualPointsMap L B B' ψ ⋙ (dualHom φ B').quotientFunctor :=
  dualHom_quotientFunctor_naturality B B' φ ψ

/-! ## Test algebras: trivial square-zero extensions -/

section SquareZero

variable (R)

/-- For a commutative ring `R`, every `R`-module is a module over `Rᵐᵒᵖ` through the canonical
isomorphism `Rᵐᵒᵖ ≃ R`.  This is only used to produce the trivial square-zero extension
`TrivSqZeroExt R M`, which Mathlib builds from a two-sided module structure. -/
@[instance_reducible]
def opModule (M : Type u) [AddCommGroup M] [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite fun x y => mul_comm x y)

attribute [local instance] opModule

/-- The left and right actions of a commutative ring on a module agree. -/
theorem isCentralScalar_of_commRing (M : Type u) [AddCommGroup M] [Module R M] :
    IsCentralScalar R M :=
  ⟨fun _ _ => rfl⟩

attribute [local instance] isCentralScalar_of_commRing

variable {R}

/-! ## The converse of Behrend–Fantechi 4.5 -/

/-- From bijectivity of `h⁰` of the dual over a test algebra containing an `R`-module `h¹(E)`
faithfully, `H⁰(φ)` is injective.  This is Yoneda for the module `h¹(E)`. -/
theorem injective_cokernelMap_of_bijective_kernelMap {φ : Hom E L} {B : Type u} [CommRing B]
    [Algebra R B] (j : h1 E →ₗ[R] B) (hj : Function.Injective j)
    (hb : Function.Bijective (dualHom φ B).kernelMap) :
    Function.Injective φ.cokernelMap := by
  obtain ⟨m, hm⟩ := ((bijective_kernelMap_dualHom_iff φ B).1 hb).2 j
  intro x y hxy
  apply hj
  have hx : m (φ.cokernelMap x) = j x := congrArg (fun k : h1 E →ₗ[R] B => k x) hm
  have hy : m (φ.cokernelMap y) = j y := congrArg (fun k : h1 E →ₗ[R] B => k y) hm
  rw [← hx, ← hy, hxy]

/-- From bijectivity of `h⁰` of the dual over a test algebra containing the cokernel of `H⁰(φ)`
faithfully, `H⁰(φ)` is surjective. -/
theorem surjective_cokernelMap_of_bijective_kernelMap {φ : Hom E L} {B : Type u} [CommRing B]
    [Algebra R B] (j : (h1 L ⧸ LinearMap.range φ.cokernelMap) →ₗ[R] B)
    (hj : Function.Injective j)
    (hb : Function.Bijective (dualHom φ B).kernelMap) :
    Function.Surjective φ.cokernelMap := by
  have hP := (bijective_kernelMap_dualHom_iff φ B).1 hb
  have hm : (j.comp (Submodule.mkQ (LinearMap.range φ.cokernelMap))).comp φ.cokernelMap
      = (0 : h1 L →ₗ[R] B).comp φ.cokernelMap := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ x), map_zero,
      LinearMap.zero_comp, LinearMap.zero_apply]
  have hzero := hP.1 hm
  intro y
  have hy : j (Submodule.Quotient.mk y) = 0 := by
    have := congrArg (fun k : h1 L →ₗ[R] B => k y) hzero
    simpa using this
  have : (Submodule.Quotient.mk y : h1 L ⧸ LinearMap.range φ.cokernelMap) = 0 :=
    hj (by rw [hy, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).1 this

/-- **Lifting a functional along `d_L` from injectivity on `h¹` of the dual.**

If `λ ∘ φ⁻¹ = μ ∘ d_E` then the class of `λ` in `h¹` of the dual complex of `B`-points dies in
`h¹` of the dual complex of `E`, so injectivity produces `ν` with `ν ∘ d_L = λ`. -/
theorem exists_lift_of_injective_cokernelMap {φ : Hom E L} {B : Type u} [CommRing B]
    [Algebra R B] (hinj : Function.Injective (dualHom φ B).cokernelMap)
    (lam : L.degreeZero →ₗ[R] B) (mu : E.degreeOne →ₗ[R] B)
    (hcomm : ∀ x : E.degreeZero, lam (φ.degreeZero x) = mu (E.differential x)) :
    ∃ nu : L.degreeOne →ₗ[R] B, ∀ a : L.degreeZero, nu (L.differential a) = lam a := by
  have hlam : h1mk (dualPoints L B) (ofDualDegreeOne L B lam) = 0 := by
    apply hinj
    rw [map_zero, cokernelMap_h1mk, h1mk_eq_zero_iff]
    refine ⟨ofDualDegreeZero E B mu, ?_⟩
    change mu.comp E.differential = lam.comp φ.degreeZero
    exact LinearMap.ext fun x => (hcomm x).symm
  obtain ⟨nu, hnu⟩ :=
    (h1mk_eq_zero_iff (E := dualPoints L B) (ofDualDegreeOne L B lam)).1 hlam
  exact ⟨dualDegreeZero L B nu,
    fun a => congrArg (fun m : L.degreeZero →ₗ[R] B => m a) hnu⟩

/-- **Descent of a pair of functionals along the mapping cone.**

Given `λ : L⁻¹ → B` and `μ : E⁰ → B` with `λ ∘ φ⁻¹ = μ ∘ d_E`, injectivity of `h¹` of the dual
produces `ν : L⁰ → B` with `ν ∘ d_L = λ`; correcting `ν` by a functional that kills `d_L` and
reproduces `μ - ν ∘ φ⁰` — which exists because `H⁰(φ)` is bijective — gives a single `ν` with
both `ν ∘ d_L = λ` and `ν ∘ φ⁰ = μ`. -/
theorem exists_descent {φ : Hom E L} {B : Type u} [CommRing B] [Algebra R B]
    (hck : Function.Bijective φ.cokernelMap)
    (hinj : Function.Injective (dualHom φ B).cokernelMap)
    (lam : L.degreeZero →ₗ[R] B) (mu : E.degreeOne →ₗ[R] B)
    (hcomm : ∀ x : E.degreeZero, lam (φ.degreeZero x) = mu (E.differential x)) :
    ∃ nu : L.degreeOne →ₗ[R] B,
      (∀ a : L.degreeZero, nu (L.differential a) = lam a) ∧
      (∀ y : E.degreeOne, nu (φ.degreeOne y) = mu y) := by
  obtain ⟨nu, hnud⟩ := exists_lift_of_injective_cokernelMap hinj lam mu hcomm
  have hker : (LinearMap.range E.differential : Submodule R E.degreeOne)
      ≤ LinearMap.ker (mu - nu.comp φ.degreeOne) := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, φ.comm x, hnud,
      hcomm x, sub_self]
  obtain ⟨kappa, hkappa⟩ : ∃ k : h1 E →ₗ[R] B, ∀ y : E.degreeOne,
      k (h1mk E y) = mu y - nu (φ.degreeOne y) :=
    ⟨Submodule.liftQ _ (mu - nu.comp φ.degreeOne) hker, fun _ => rfl⟩
  obtain ⟨nu2, hnu2d, hnu2f⟩ : ∃ n : L.degreeOne →ₗ[R] B,
      (∀ a : L.degreeZero, n (L.differential a) = 0) ∧
      (∀ y : E.degreeOne, n (φ.degreeOne y) = mu y - nu (φ.degreeOne y)) := by
    refine ⟨(kappa.comp (LinearEquiv.ofBijective φ.cokernelMap hck).symm.toLinearMap).comp
      (Submodule.mkQ (LinearMap.range L.differential)), fun a => ?_, fun y => ?_⟩
    · change kappa ((LinearEquiv.ofBijective φ.cokernelMap hck).symm
        (h1mk L (L.differential a))) = 0
      rw [(h1mk_eq_zero_iff (E := L) (L.differential a)).2 ⟨a, rfl⟩, map_zero, map_zero]
    · change kappa ((LinearEquiv.ofBijective φ.cokernelMap hck).symm
        (h1mk L (φ.degreeOne y))) = mu y - nu (φ.degreeOne y)
      rw [show h1mk L (φ.degreeOne y)
          = LinearEquiv.ofBijective φ.cokernelMap hck (h1mk E y) from rfl,
        LinearEquiv.symm_apply_apply, hkappa]
  refine ⟨nu + nu2, fun a => ?_, fun y => ?_⟩
  · rw [LinearMap.add_apply, hnud a, hnu2d a, add_zero]
  · rw [LinearMap.add_apply, hnu2f y]
    abel

/-- **Exactness in the middle of the mapping cone sequence** from injectivity of `h¹` of the
dual.  Testing against the cokernel of `E⁻¹ → L⁻¹ ⊕ E⁰` shows that the kernel of
`L⁻¹ ⊕ E⁰ → L⁰` is contained in the image of `E⁻¹`. -/
theorem ker_coneBeta_le_range_coneAlpha {φ : Hom E L} {B : Type u} [CommRing B] [Algebra R B]
    (hck : Function.Bijective φ.cokernelMap)
    (hinj : Function.Injective (dualHom φ B).cokernelMap)
    (j : ((L.degreeZero × E.degreeOne) ⧸ LinearMap.range (coneAlpha φ)) →ₗ[R] B)
    (hj : Function.Injective j) :
    LinearMap.ker (coneBeta φ) ≤ LinearMap.range (coneAlpha φ) := by
  have hcomm : ∀ x : E.degreeZero,
      (j.comp ((Submodule.mkQ (LinearMap.range (coneAlpha φ))).comp
        (LinearMap.inl R L.degreeZero E.degreeOne))) (φ.degreeZero x)
      = (j.comp ((Submodule.mkQ (LinearMap.range (coneAlpha φ))).comp
        (LinearMap.inr R L.degreeZero E.degreeOne))) (E.differential x) := by
    intro x
    have hq : (Submodule.Quotient.mk ((φ.degreeZero x, (0 : E.degreeOne)) :
          L.degreeZero × E.degreeOne) :
          (L.degreeZero × E.degreeOne) ⧸ LinearMap.range (coneAlpha φ))
        = Submodule.Quotient.mk ((0, E.differential x) : L.degreeZero × E.degreeOne) := by
      rw [Submodule.Quotient.eq]
      refine ⟨x, ?_⟩
      rw [coneAlpha_apply]
      exact Prod.ext (by simp) (by simp)
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      Submodule.mkQ_apply, hq]
  obtain ⟨nu, hnud, hnuf⟩ := exists_descent hck hinj _ _ hcomm
  intro m hm
  have hsum : ((m.1, (0 : E.degreeOne)) + (0, m.2) : L.degreeZero × E.degreeOne) = m :=
    Prod.ext (by simp) (by simp)
  have hval : nu (coneBeta φ m) = j (Submodule.Quotient.mk m) := by
    rw [coneBeta_apply, map_add, hnud, hnuf]
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      Submodule.mkQ_apply, ← map_add]
    congr 1
    rw [← Submodule.Quotient.mk_add, hsum]
  have hzero : j (Submodule.Quotient.mk m) = 0 := by
    rw [← hval, LinearMap.mem_ker.mp hm, map_zero]
  have : (Submodule.Quotient.mk m : (L.degreeZero × E.degreeOne) ⧸
      LinearMap.range (coneAlpha φ)) = 0 := hj (by rw [hzero, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).1 this

/-- Exactness in the middle of the mapping cone sequence gives surjectivity of `H⁻¹(φ)`. -/
theorem surjective_kernelMap_of_ker_coneBeta {φ : Hom E L}
    (h : LinearMap.ker (coneBeta φ) ≤ LinearMap.range (coneAlpha φ)) :
    Function.Surjective φ.kernelMap := by
  intro c
  have hmem : (((c : L.degreeZero), (0 : E.degreeOne)) : L.degreeZero × E.degreeOne)
      ∈ LinearMap.ker (coneBeta φ) := by
    rw [LinearMap.mem_ker, coneBeta_apply, LinearMap.mem_ker.mp c.2, map_zero, add_zero]
  obtain ⟨x, hx⟩ := h hmem
  have hfst : φ.degreeZero x = (c : L.degreeZero) := congrArg Prod.fst hx
  have hsnd : E.differential x = 0 := by
    have hs := congrArg Prod.snd hx
    rw [coneAlpha_apply] at hs
    simpa using hs
  exact ⟨⟨x, LinearMap.mem_ker.mpr hsnd⟩, Subtype.ext hfst⟩

/-- **Behrend–Fantechi 4.5, converse direction, from square-zero test algebras.**

If for every `R`-module `M` the dualised chain map over the trivial square-zero extension
`TrivSqZeroExt R M` is a cohomological monomorphism, then `φ` is an obstruction theory.  Only
these test algebras are used, which is the sharpest form of the converse: they are exactly what
is needed to test with arbitrary module coefficients. -/
theorem isObstructionTheory_of_trivSqZeroExt (φ : Hom E L)
    (hmono : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      IsCohomologicalMono (dualHom φ (TrivSqZeroExt R M))) :
    IsObstructionTheory φ := by
  have hinj : Function.Injective φ.cokernelMap :=
    injective_cokernelMap_of_bijective_kernelMap (TrivSqZeroExt.inrHom R (h1 E))
      TrivSqZeroExt.inr_injective (hmono (h1 E)).1
  have hsurj : Function.Surjective φ.cokernelMap :=
    surjective_cokernelMap_of_bijective_kernelMap
      (TrivSqZeroExt.inrHom R (h1 L ⧸ LinearMap.range φ.cokernelMap))
      TrivSqZeroExt.inr_injective (hmono _).1
  refine ⟨⟨hinj, hsurj⟩, surjective_kernelMap_of_ker_coneBeta
    (ker_coneBeta_le_range_coneAlpha ⟨hinj, hsurj⟩ (hmono _).2
      (TrivSqZeroExt.inrHom R _) TrivSqZeroExt.inr_injective)⟩

/-- **Behrend–Fantechi 4.5, converse direction.**  If `h¹/h⁰(Lᵛ) → h¹/h⁰(Eᵛ)` is a closed
immersion fibrewise over every affine test scheme, then `φ` is an obstruction theory. -/
theorem isObstructionTheory_of_forall_isCohomologicalMono (φ : Hom E L)
    (hmono : ∀ (B : Type u) [CommRing B] [Algebra R B], IsCohomologicalMono (dualHom φ B)) :
    IsObstructionTheory φ :=
  isObstructionTheory_of_trivSqZeroExt φ fun _ => hmono _

/-- **Behrend–Fantechi 4.5 in the affine two-term model.**  A chain map `φ : E ⟶ L` is an
obstruction theory exactly when the induced morphism of `h¹/h⁰` groupoids of the duals is a
cohomological monomorphism — the algebraic form of a closed immersion of cone stacks — over every
affine test scheme. -/
theorem isObstructionTheory_iff_forall_isCohomologicalMono (φ : Hom E L) :
    IsObstructionTheory φ ↔
      ∀ (B : Type u) [CommRing B] [Algebra R B], IsCohomologicalMono (dualHom φ B) :=
  ⟨fun h B _ _ => h.isCohomologicalMono_dualHom B,
    isObstructionTheory_of_forall_isCohomologicalMono φ⟩

end SquareZero

/-! ## The obstruction cone -/

section ObstructionCone

variable {C : Type u} [Groupoid.{v} C]

/-- **The obstruction cone of a cone inside the normal sheaf.**

Given a groupoid `C` mapping to the fibre `h¹/h⁰(Lᵛ)(B)` — in the intended application `C` is the
affine intrinsic normal cone of `Cones/Quotient.lean` sitting inside the intrinsic normal sheaf —
its obstruction cone is its image in `h¹/h⁰(Eᵛ)(B)` under the closed immersion attached to an
obstruction theory `φ`. -/
def obstructionConeFunctor (φ : Hom E L) (B : Type u) [CommRing B] [Algebra R B]
    (ι : C ⥤ (dualPoints L B).quotient) : C ⥤ (dualPoints E B).quotient :=
  ι ⋙ (dualHom φ B).quotientFunctor

/-- The obstruction cone of a fully faithful cone is fully faithful: the closed immersion does
not change the automorphisms or the arrows of the cone. -/
noncomputable def obstructionConeFunctorFullyFaithful {φ : Hom E L} (h : IsObstructionTheory φ)
    (B : Type u) [CommRing B] [Algebra R B] {ι : C ⥤ (dualPoints L B).quotient}
    (hι : ι.FullyFaithful) : (obstructionConeFunctor φ B ι).FullyFaithful :=
  hι.comp (h.dualFullyFaithful B)

/-- The obstruction cone determines the cone on isomorphism classes: two objects of `C` whose
images in `h¹/h⁰(Eᵛ)(B)` are isomorphic are already isomorphic. -/
theorem obstructionConeFunctor_injective_isoClass {φ : Hom E L} (h : IsObstructionTheory φ)
    (B : Type u) [CommRing B] [Algebra R B] {ι : C ⥤ (dualPoints L B).quotient}
    (hι : ι.FullyFaithful) {c c' : C}
    (hiso : Nonempty ((obstructionConeFunctor φ B ι).obj c
      ≅ (obstructionConeFunctor φ B ι).obj c')) :
    Nonempty (c ≅ c') := by
  obtain ⟨e⟩ := h.dual_injective_isoClass B hiso
  exact ⟨hι.preimageIso e⟩

/-- The obstruction cone commutes with reindexing along a map of test algebras, given the
corresponding compatibility of the cone itself. -/
theorem obstructionConeFunctor_dualPointsMap (φ : Hom E L) (B B' : Type u) [CommRing B]
    [Algebra R B] [CommRing B'] [Algebra R B'] (ψ : B →ₐ[R] B')
    (ι : C ⥤ (dualPoints L B).quotient) (ι' : C ⥤ (dualPoints L B').quotient)
    (hι : ι ⋙ dualPointsMap L B B' ψ = ι') :
    obstructionConeFunctor φ B ι ⋙ dualPointsMap E B B' ψ
      = obstructionConeFunctor φ B' ι' := by
  subst hι
  rfl

/-- Replacing `E` by a chain homotopy equivalent complex changes the obstruction cone by the
equivalence `PicardCriteria.dualQuotientEquivalence` of the fibres. -/
theorem obstructionConeFunctor_comp_homotopyEquivalence {E' : LinearTwoTermComplex R}
    (φ : Hom E L) (e : HomotopyEquivalence E' E) (B : Type u) [CommRing B] [Algebra R B]
    (ι : C ⥤ (dualPoints L B).quotient) :
    obstructionConeFunctor (φ.comp e.hom) B ι
      = obstructionConeFunctor φ B ι ⋙ (dualQuotientEquivalence B e).functor :=
  rfl

/-- The tautological obstruction theory has the tautological obstruction cone. -/
theorem obstructionConeFunctor_id (B : Type u) [CommRing B] [Algebra R B]
    (ι : C ⥤ (dualPoints L B).quotient) :
    obstructionConeFunctor (Hom.id L) B ι = ι :=
  rfl

end ObstructionCone

/-! ## The point case -/

/-- The identity is an obstruction theory, and its dual fibre morphism is the identity: the
obstruction cone of the tautological obstruction theory is the intrinsic normal cone itself. -/
theorem isCohomologicalMono_dualHom_id (L : LinearTwoTermComplex R) (B : Type u) [CommRing B]
    [Algebra R B] : IsCohomologicalMono (dualHom (Hom.id L) B) :=
  (IsObstructionTheory.id L).isCohomologicalMono_dualHom B

/-- Dualising the identity chain map induces the identity functor on the fibre. -/
theorem quotientFunctor_dualHom_id (L : LinearTwoTermComplex R) (B : Type u) [CommRing B]
    [Algebra R B] : (dualHom (Hom.id L) B).quotientFunctor = 𝟭 (dualPoints L B).quotient :=
  rfl

end PicardCriteria

end GromovWitten.AlgebraicGeometry
