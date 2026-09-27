/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ObstructionBundleFormula
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FirstChernClass
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysin

/-!
# The top Chern class of a trivialised line bundle is its first Chern class

`VirtualFundamentalClass/ObstructionBundleFormula.lean` defines the top Chern class operator of a
finite free module as the composite `0^! ∘ s_*` of the zero-section pushforward with the
zero-section Gysin isomorphism of `IntersectionTheory/BundleHomotopyKey.lean`, and proves the
no-obstruction formula `[X]^vir = c_top(E₁) ∩ [X]`.  This file compares that operator, in rank
one, with the first Chern class of `IntersectionTheory/FirstChernClass.lean`.

## The alleged obstruction is not one

`ObstructionBundleFormula.lean` records as an obstruction that `FirstChernClass.c1` is pinned to
the canonical system `chowSystem dim i` while `topChern` is parametrised by an arbitrary
`RationalEquivalenceSystem`, and that a lemma making `zeroSectionGysin'` independent of the
witnessing system is missing.  No such lemma is needed:
`RationalEquivalenceSystem X dim i` is an inductive type with the single constructor `.canonical`
and carries a `Subsingleton` instance, and `chowSystem dim i` *is* `.canonical`
(`eq_chowSystem` below).  Every system is therefore equal to `chowSystem dim i`, and the two
operators already act on the same Chow groups.

## The actual content in rank one

Both operators are defined over an *affine* base and for a *trivialised* bundle, so the line
bundle involved is the trivial one, and the comparison is the vanishing of both sides.  For
`c₁` this is `FirstChernClass.c1_trivial`.  For the top Chern class it is the geometric statement
that the zero section of the trivial line bundle is a principal divisor: on the fibre
`V × 𝔸¹` over a subvariety `V` of the base, the coordinate `T` has divisor exactly `V × {0}`.
This is proved here as `divisor_elementGenerator_eq_map_singlePoint` and
`zeroSectionPushforward_eq_zero` for the trivial line bundle `Spec R[T] → Spec R`.  It is then
transported to `ObstructionBundleFormula.topChern` itself: the
zero section of `Spec (Sym M)` factors through the zero section of `Spec S[T]` along the closed
immersion cut out by a surjective functional `φ : M →ₗ[S] S`
(`zeroSection_moduleAugmentation_eq_comp`), so `topChern` vanishes in every positive rank
(`topChern_eq_zero_of_nonempty`), and in rank one it equals `c₁` of the trivial line bundle
(`topChern_eq_c1_trivial`).

## Main declarations

* `eq_chowSystem`, `chowGradeEquiv` — every rational-equivalence system is the canonical one, and
  systems in equal grades have the same Chow group.
* `quotientMap_eq_zero_of_eq_divisor` — a graded cycle which *is* a generator divisor has zero
  class.
* `evalAlgHom c` — evaluation `T ↦ c` as an augmentation of `R[T]`, whose `Spec` is
  `VectorBundle.sectionMap c` by definition (`zeroSection_evalAlgHom`).
* `divisor_elementGenerator_eq_map_singlePoint` — the divisor of `T - c` on the fibre over a
  point `x` of the base is the pushforward along the section of the single-point cycle at `x`.
* `zeroSectionPushforward_eq_zero` — the zero-section pushforward vanishes on rational Chow
  groups: the section class is a principal divisor.
* `chowPullbackBundle_topChern`, `eq_topChern_of_chowPullbackBundle_eq` — the defining property
  of `ObstructionBundleFormula.topChern` in any rank: it is the unique operator whose flat pullback
  is the zero-section pushforward.
* `symToPoly`, `symToPoly_surjective`, `evalAlgHom_comp_symToPoly`, `polyToSym`,
  `zeroSection_moduleAugmentation_eq_comp` — the presentation of the trivial line bundle as a
  closed subscheme of `Spec (Sym M)` cut out by the kernel of a functional `φ : M →ₗ[S] S`, and
  the resulting factorisation of the zero section of `Spec (Sym M)`.
* `zeroSectionPushforward_moduleAugmentation_eq_zero`, `topChern_eq_zero_of_surjective`,
  `topChern_eq_zero_of_nonempty` — `ObstructionBundleFormula.topChern` itself vanishes whenever
  `M` has a surjective functional, in particular whenever the free module `M` has nonempty basis
  index (positive rank).
* `virtualClass_eq_zero_of_ideal_eq_zeroSection` — the resulting degeneracy of the affine
  no-obstruction formula: in positive rank the virtual fundamental class it computes is `0`.
* `topChern_apply_eq_c1_apply`, `topChern_eq_c1_trivial` — the rank-one comparison: for
  `φ : M ≃ₗ[S] S`, `ObstructionBundleFormula.topChern` equals the first Chern class of the trivial
  line bundle, the domains being identified by `chowGradeEquiv` through
  `grade_eq_of_linearEquiv`.

## What is not done

* Multiplicativity `topChern (M ⊕ N) = topChern M ∘ topChern N` is not proved.  Over an affine
  base with a free module it is implied by `topChern_eq_zero_of_nonempty` on both sides as soon as
  both summands are of positive rank, but the general statement needs the comparison of
  `Sym (M ⊕ N)` with `Sym M ⊗ Sym N`, which does not exist at this operator's level.
* Nothing here says anything about a *nontrivial* bundle: `ObstructionBundleFormula.topChern` is
  by construction the operator of a bundle with a trivialised coordinate algebra over an affine
  base, so its bundle is always trivial and, in positive rank, its top Chern class vanishes.  A
  formula for a nontrivial obstruction bundle needs the global (non-affine) Chern class theory of
  `IntersectionTheory/FirstChernClassDescent.lean` and beyond.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.TopChernRankOne

open GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Uniqueness of the rational-equivalence system -/

section Uniqueness

variable {X : Scheme.{u}} {dim : DimensionFunction X} {i : ℤ}

/-- Every rational-equivalence system is the canonical one, `chowSystem dim i`: the type has a
single constructor.  This is why no "independence of the witnessing system" lemma is needed to
compare the zero-section Gysin map with the first Chern class. -/
theorem eq_chowSystem (R : RationalEquivalenceSystem X dim i) : R = chowSystem dim i :=
  Subsingleton.elim _ _

/-- The Chow group of an arbitrary rational-equivalence system is the Chow group of the canonical
one. -/
theorem chowGroup_eq (R : RationalEquivalenceSystem X dim i) :
    R.ChowGroup = (chowSystem dim i).ChowGroup := by
  rw [eq_chowSystem R]

/-- Two rational-equivalence systems on the same scheme, in grades which are equal, have
canonically isomorphic Chow groups: the grades are equal and both systems are the canonical one,
so the two Chow groups are the same module. -/
noncomputable def chowGradeEquiv {g g' : ℤ} (h : g = g')
    (R : RationalEquivalenceSystem X dim g) (R' : RationalEquivalenceSystem X dim g') :
    R.ChowGroup ≃ₗ[ℚ] R'.ChowGroup := by
  subst h
  cases R
  cases R'
  exact LinearEquiv.refl ℚ _

end Uniqueness

/-! ## Classes of principal divisors -/

/-- A graded cycle whose underlying cycle is the divisor of a rational-function generator has
zero class in the Chow group. -/
theorem quotientMap_eq_zero_of_eq_divisor {X : Scheme.{u}} {dim : DimensionFunction X} {i : ℤ}
    (R : RationalEquivalenceSystem X dim i) (z : cyclesOfDimension X dim i)
    (g : RationalFunctionGenerator X)
    (h : (z : _root_.AlgebraicGeometry.AlgebraicCycle X ℚ) = g.divisor dim) :
    R.quotientMap z = 0 := by
  cases R
  have hmem : g.divisor dim ∈ cyclesOfDimension X dim i := h ▸ z.2
  have hz : (⟨g.divisor dim, hmem⟩ : cyclesOfDimension X dim i) = z := Subtype.ext h.symm
  rw [← hz]
  exact RationalEquivalenceSystem.quotientMap_divisor _ g hmem

/-! ## The trivial line bundle and its zero section -/

section Trivial

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (c : R)

/-- Evaluation at `c`, as an augmentation of the coordinate algebra of the trivial line bundle
`Spec R[T] → Spec R`.  Its `Spec` is the section `VectorBundle.sectionMap c`. -/
noncomputable def evalAlgHom : Polynomial R →ₐ[R] R :=
  { Polynomial.evalRingHom c with commutes' := fun r => by simp }

omit [IsNoetherianRing R] in
/-- The zero section attached to `evalAlgHom c` is the constant section with value `c`: both are
the `Spec` of evaluation at `c`. -/
theorem zeroSection_evalAlgHom :
    VectorBundle.zeroSection (evalAlgHom c) = VectorBundle.sectionMap c := rfl

omit [IsNoetherianRing R] in
/-- The defining equation of the section does not lie in the prime of the generic point of the
fibre over a point of the base. -/
theorem sectionPoly_notMem_fibre (x : ↥(Spec (CommRingCat.of R))) :
    VectorBundle.sectionPoly c ∉
      Ideal.map (algebraMap R (Polynomial R)) (x : PrimeSpectrum R).asIdeal :=
  VectorBundle.sectionPoly_notMem_map c _ (x : PrimeSpectrum R).isPrime.ne_top

/-- **The zero section of the trivial line bundle is a principal divisor.**  The divisor of
`T - c` on the fibre `V(P) = π⁻¹(closure x)` over a point `x` of the base is exactly the
pushforward along the section of the single-point cycle at `x`: the section meets the fibre
transversally in the single point `σ_c(x)`, and the divisor has no other component because a
prime containing `T - c` lies in the image of the section. -/
theorem divisor_elementGenerator_eq_map_singlePoint
    (dimX : DimensionFunction (Spec (CommRingCat.of R)))
    (dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R))))
    (x : ↥(Spec (CommRingCat.of R))) (P : Ideal (Polynomial R)) [P.IsPrime]
    (hPeq : P = Ideal.map (algebraMap R (Polynomial R)) (x : PrimeSpectrum R).asIdeal)
    (hs : VectorBundle.sectionPoly c ∉ P) :
    (VectorBundle.elementGenerator P (VectorBundle.sectionPoly c) hs).divisor dimE =
      _root_.AlgebraicGeometry.AlgebraicCycle.map (VectorBundle.sectionMap c) dimX dimE
        (AlgebraicCycle.singlePoint x) := by
  classical
  have hdim : dimX.toFun = fun a => dimE.toFun ((VectorBundle.sectionMap c).base a) := by
    funext a
    exact DimensionFunction.apply_eq_of_isClosedImmersion dimX dimE
      (VectorBundle.sectionMap c) a
  rw [hdim]
  apply Function.locallyFinsuppWithin.coe_injective
  funext Q
  by_cases hmem : VectorBundle.sectionPoly c ∈ (Q : PrimeSpectrum (Polynomial R)).asIdeal
  · obtain ⟨y, rfl⟩ := (VectorBundle.mem_range_sectionPoint_iff c Q).2 hmem
    have hL : ((VectorBundle.elementGenerator P (VectorBundle.sectionPoly c) hs).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) (VectorBundle.sectionPoint c y) =
        (AlgebraicCycle.singlePoint x : ↥(Spec (CommRingCat.of R)) → ℚ) y := by
      rw [← VectorBundle.sectionRestrict_apply c _ y,
        VectorBundle.sectionRestrict_divisor_sectionPoly c dimE x P hPeq hs]
    exact hL.trans (AlgebraicCycle.map_closedImmersion_apply_image (VectorBundle.sectionMap c)
      dimE.toFun (AlgebraicCycle.singlePoint x) y).symm
  · have hrange : Q ∉ Set.range (VectorBundle.sectionMap c).base := by
      intro hQ
      exact hmem ((VectorBundle.mem_range_sectionPoint_iff c Q).1 hQ)
    have hzero : ((VectorBundle.elementGenerator P (VectorBundle.sectionPoly c) hs).divisor dimE :
        ↥(Spec (CommRingCat.of (Polynomial R))) → ℚ) Q = 0 := by
      by_cases hle : P ≤ (Q : PrimeSpectrum (Polynomial R)).asIdeal
      · rw [VectorBundle.elementGenerator_divisor_apply_of_le P (VectorBundle.sectionPoly c) hs
          dimE Q hle]
        have hnot : Ideal.Quotient.mk P (VectorBundle.sectionPoly c) ∉
            (VectorBundle.quotientPoint P (Q : PrimeSpectrum (Polynomial R)).asIdeal
              (Q : PrimeSpectrum (Polynomial R)).isPrime hle :
                PrimeSpectrum (Polynomial R ⧸ P)).asIdeal := by
          intro hcon
          refine hmem ?_
          have hcm := VectorBundle.comap_map_quotientMk P
            (Q : PrimeSpectrum (Polynomial R)).asIdeal hle
          rw [← hcm]
          exact hcon
        have hord := VectorBundle.ord_algebraMap_eq_zero_of_notMem
          (CommRingCat.of (Polynomial R ⧸ P))
          (VectorBundle.quotientPoint P (Q : PrimeSpectrum (Polynomial R)).asIdeal
            (Q : PrimeSpectrum (Polynomial R)).isPrime hle)
          (Ideal.Quotient.mk P (VectorBundle.sectionPoly c)) hnot
        have hord' : ((Spec (CommRingCat.of (Polynomial R ⧸ P))).ord
            (VectorBundle.elementFunction P (VectorBundle.sectionPoly c) hs :
              (Spec (CommRingCat.of (Polynomial R ⧸ P))).functionField)
            (VectorBundle.quotientPoint P (Q : PrimeSpectrum (Polynomial R)).asIdeal
              (Q : PrimeSpectrum (Polynomial R)).isPrime hle) : ℤ) = 0 := hord
        rw [hord']
        norm_num
      · exact VectorBundle.elementGenerator_divisor_apply_of_not_le P
          (VectorBundle.sectionPoly c) hs dimE Q hle
    exact hzero.trans (AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      (VectorBundle.sectionMap c) dimE.toFun (AlgebraicCycle.singlePoint x) Q hrange).symm

variable {dimX : DimensionFunction (Spec (CommRingCat.of R))}
  {dimE : DimensionFunction (Spec (CommRingCat.of (Polynomial R)))} {i : ℤ}

omit [IsNoetherianRing R] in
/-- The underlying cycle of `cyclesOfDimension.pointProj` at a point of the right dimension is
the single-point cycle. -/
theorem coe_pointProj_eq_singlePoint {x : ↥(Spec (CommRingCat.of R))} (hx : dimX x = i) :
    (cyclesOfDimension.pointProj dimX i x :
        _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) =
      AlgebraicCycle.singlePoint x := by
  classical
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  simp only [cyclesOfDimension.pointProj_apply, AlgebraicCycle.singlePoint_apply]
  by_cases h : y = x
  · subst h
    rw [if_pos ⟨rfl, hx⟩, if_pos rfl]
  · rw [if_neg (fun hh => h hh.1.symm), if_neg h]

/-- **The zero-section class vanishes.**  The pushforward of any rational Chow class along the
section with constant value `c` of the trivial line bundle is zero, because the pushforward of a
point class is the divisor of `T - c` on the fibre over that point
(`divisor_elementGenerator_eq_map_singlePoint`) and every graded cycle is a finite sum of point
classes. -/
theorem zeroSectionPushforward_eq_zero
    (RX : RationalEquivalenceSystem (Spec (CommRingCat.of R)) dimX i)
    (RE : RationalEquivalenceSystem (Spec (CommRingCat.of (Polynomial R))) dimE i) :
    VectorBundle.zeroSectionPushforward (evalAlgHom c) RX RE = 0 := by
  classical
  have key : ∀ x : ↥(Spec (CommRingCat.of R)),
      RE.quotientMap (cyclesOfDimension.properPushforward (dimension := dimX)
        (dimensionY := dimE) (i := i) (VectorBundle.zeroSection (evalAlgHom c))
        (cyclesOfDimension.pointProj dimX i x)) = 0 := by
    intro x
    by_cases hx : dimX x = i
    · have hP : (Ideal.map (algebraMap R (Polynomial R))
          (x : PrimeSpectrum R).asIdeal).IsPrime :=
        VectorBundle.isPrime_map_algebraMap (VectorBundle.polyTrivialization R) x
      refine quotientMap_eq_zero_of_eq_divisor RE _
        (VectorBundle.elementGenerator _ (VectorBundle.sectionPoly c)
          (sectionPoly_notMem_fibre c x)) ?_
      change _root_.AlgebraicGeometry.AlgebraicCycle.map (VectorBundle.sectionMap c) dimX dimE
        (cyclesOfDimension.pointProj dimX i x :
          _root_.AlgebraicGeometry.AlgebraicCycle (Spec (CommRingCat.of R)) ℚ) = _
      rw [coe_pointProj_eq_singlePoint hx,
        divisor_elementGenerator_eq_map_singlePoint c dimX dimE x _ rfl
          (sectionPoly_notMem_fibre c x)]
    · rw [cyclesOfDimension.pointProj_eq_zero_of_ne hx, map_zero, map_zero]
  refine LinearMap.ext fun α => Submodule.Quotient.induction_on _ α (fun z => ?_)
  change VectorBundle.zeroSectionPushforward (evalAlgHom c) RX RE (RX.quotientMap z) = 0
  rw [VectorBundle.zeroSectionPushforward_quotientMap, cyclesOfDimension.eq_sum_pointProj z,
    map_sum, map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [map_smul, map_smul, key x, smul_zero]

end Trivial

/-! ## The rank-one case of `ObstructionBundleFormula.topChern` -/

section RankOne

open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ObstructionBundleFormula

variable {S : Type u} [CommRing S] [IsNoetherianRing S] {M : Type u} [AddCommGroup M]
  [Module S M] [Module.Free S M] [Module.Finite S M]

/-- The `S`-algebra map `Sym M → S[T]` attached to a linear functional `φ : M →ₗ[S] S`, sending a
vector `m` to the linear polynomial `φ(m) · T`.  Geometrically it presents the trivial line bundle
as the quotient of `Spec (Sym M)` cut out by the kernel of `φ`.  Only its surjectivity for
surjective `φ` (`symToPoly_surjective`) and its compatibility with the augmentations
(`evalAlgHom_comp_symToPoly`) are used. -/
noncomputable def symToPoly (φ : M →ₗ[S] S) : SymmetricAlgebra S M →ₐ[S] Polynomial S :=
  SymmetricAlgebra.lift ((Polynomial.monomial 1).comp φ)

omit [IsNoetherianRing S] [Module.Free S M] [Module.Finite S M] in
/-- `symToPoly` sends a vector to a linear polynomial. -/
theorem symToPoly_ι (φ : M →ₗ[S] S) (m : M) :
    symToPoly φ (SymmetricAlgebra.ι S M m) = Polynomial.monomial 1 (φ m) :=
  SymmetricAlgebra.lift_ι_apply _ m

omit [IsNoetherianRing S] [Module.Free S M] [Module.Finite S M] in
/-- `symToPoly` is surjective whenever `φ` is: its range is a subalgebra containing `T`. -/
theorem symToPoly_surjective (φ : M →ₗ[S] S) (hφ : Function.Surjective φ) :
    Function.Surjective (symToPoly φ) := by
  obtain ⟨m₀, hm₀⟩ := hφ 1
  have hXval : symToPoly φ (SymmetricAlgebra.ι S M m₀) = Polynomial.X := by
    rw [symToPoly_ι, hm₀, Polynomial.monomial_one_one_eq_X]
  have hX : Polynomial.X ∈ (symToPoly φ).range :=
    (AlgHom.mem_range (symToPoly φ)).2 ⟨SymmetricAlgebra.ι S M m₀, hXval⟩
  have htop : (⊤ : Subalgebra S (Polynomial S)) ≤ (symToPoly φ).range := by
    rw [← Polynomial.adjoin_X]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hX)
  intro p
  exact (AlgHom.mem_range (symToPoly φ)).1 (htop (Algebra.mem_top))

omit [IsNoetherianRing S] [Module.Free S M] [Module.Finite S M] in
/-- The augmentation of `Sym M` cutting out the zero section corresponds, under `symToPoly`, to
evaluation at `0`: a vector goes to a polynomial with zero constant term. -/
theorem evalAlgHom_comp_symToPoly (φ : M →ₗ[S] S) :
    (evalAlgHom (0 : S)).comp (symToPoly φ) = moduleAugmentation S M := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  have h1 : ((evalAlgHom (0 : S)).comp (symToPoly φ)) (SymmetricAlgebra.ι S M m) = 0 := by
    rw [AlgHom.comp_apply, symToPoly_ι]
    change Polynomial.eval 0 (Polynomial.monomial 1 (φ m)) = 0
    simp
  have h2 : (moduleAugmentation S M) (SymmetricAlgebra.ι S M m) = 0 := by
    rw [moduleAugmentation, SymmetricAlgebra.lift_ι_apply]
    exact LinearMap.zero_apply m
  exact h1.trans h2.symm

/-- The morphism `Spec S[T] ⟶ Spec (Sym M)` attached to a linear functional `φ : M →ₗ[S] S`; it
is a closed immersion whenever `φ` is surjective (`isClosedImmersion_polyToSym`), and an
isomorphism when `φ` is bijective. -/
noncomputable abbrev polyToSym (φ : M →ₗ[S] S) :
    Spec (CommRingCat.of (Polynomial S)) ⟶ Spec (CommRingCat.of (SymmetricAlgebra S M)) :=
  Spec.map (CommRingCat.ofHom (symToPoly φ).toRingHom)

omit [IsNoetherianRing S] [Module.Free S M] [Module.Finite S M] in
/-- `polyToSym φ` is a closed immersion for surjective `φ`. -/
theorem isClosedImmersion_polyToSym (φ : M →ₗ[S] S) (hφ : Function.Surjective φ) :
    _root_.AlgebraicGeometry.IsClosedImmersion (polyToSym φ) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ (symToPoly_surjective φ hφ)

omit [IsNoetherianRing S] [Module.Free S M] [Module.Finite S M] in
/-- The zero section of the bundle `Spec (Sym M)` factors through the zero section of the trivial
line bundle `Spec S[T]`, along `polyToSym φ`. -/
theorem zeroSection_moduleAugmentation_eq_comp (φ : M →ₗ[S] S) :
    VectorBundle.zeroSection (moduleAugmentation S M) =
      VectorBundle.zeroSection (evalAlgHom (0 : S)) ≫ polyToSym φ := by
  have h2 : CommRingCat.ofHom (symToPoly φ).toRingHom ≫
      CommRingCat.ofHom (evalAlgHom (0 : S)).toRingHom =
      CommRingCat.ofHom (moduleAugmentation S M).toRingHom := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    exact congrArg AlgHom.toRingHom (evalAlgHom_comp_symToPoly φ)
  change Spec.map (CommRingCat.ofHom (moduleAugmentation S M).toRingHom) =
    Spec.map (CommRingCat.ofHom (evalAlgHom (0 : S)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (symToPoly φ).toRingHom)
  rw [← Spec.map_comp, h2]

variable {dimS : DimensionFunction (Spec (CommRingCat.of S))}
  {dimM : DimensionFunction (Spec (CommRingCat.of (SymmetricAlgebra S M)))} {j : ℤ}

omit [Module.Free S M] [Module.Finite S M] in
/-- **The zero-section class of a bundle with a surjective coordinate vanishes.**  The zero
section of `Spec (Sym M) → Spec S` factors through the zero section of the trivial line bundle
`Spec S[T]` (`zeroSection_moduleAugmentation_eq_comp`), whose class already vanishes
(`zeroSectionPushforward_eq_zero`), and a closed-immersion pushforward is linear.  A surjective
functional `φ : M →ₗ[S] S` exists as soon as `M` is free of positive rank. -/
theorem zeroSectionPushforward_moduleAugmentation_eq_zero (φ : M →ₗ[S] S)
    (hφ : Function.Surjective φ)
    (RStop : RationalEquivalenceSystem (Spec (CommRingCat.of S)) dimS j)
    (RM : RationalEquivalenceSystem (Spec (CommRingCat.of (SymmetricAlgebra S M))) dimM j) :
    VectorBundle.zeroSectionPushforward (moduleAugmentation S M) RStop RM = 0 := by
  have hci := isClosedImmersion_polyToSym φ hφ
  refine LinearMap.ext fun α => Submodule.Quotient.induction_on _ α (fun z => ?_)
  change VectorBundle.zeroSectionPushforward (moduleAugmentation S M) RStop RM
    (RStop.quotientMap z) = 0
  rw [VectorBundle.zeroSectionPushforward_quotientMap,
    properPushforward_congr_of_isClosedImmersion (zeroSection_moduleAugmentation_eq_comp φ),
    cyclesOfDimension.properPushforward_comp_closedImmersion
      (dimensionY := DimensionFunction.comapClosedImmersion (polyToSym φ) dimM),
    LinearMap.comp_apply]
  have hz : (RationalEquivalenceSystem.canonical
      (X := Spec (CommRingCat.of (Polynomial S)))
      (dimension := DimensionFunction.comapClosedImmersion (polyToSym φ) dimM) (i := j)).quotientMap
      (cyclesOfDimension.properPushforward
        (VectorBundle.zeroSection (evalAlgHom (0 : S))) z) = 0 := by
    have h2 : VectorBundle.zeroSectionPushforward (evalAlgHom (0 : S)) RStop
        (RationalEquivalenceSystem.canonical
          (X := Spec (CommRingCat.of (Polynomial S)))
          (dimension := DimensionFunction.comapClosedImmersion (polyToSym φ) dimM) (i := j))
        (RStop.quotientMap z) = 0 := by
      rw [zeroSectionPushforward_eq_zero (0 : S) RStop RationalEquivalenceSystem.canonical]
      exact LinearMap.zero_apply _
    rwa [VectorBundle.zeroSectionPushforward_quotientMap] at h2
  have h3 : RationalEquivalenceSystem.DescendingMap.closedImmersionPushforward
      (RationalEquivalenceSystem.canonical
        (X := Spec (CommRingCat.of (Polynomial S)))
        (dimension := DimensionFunction.comapClosedImmersion (polyToSym φ) dimM) (i := j))
      (polyToSym φ) RM
      ((RationalEquivalenceSystem.canonical
        (X := Spec (CommRingCat.of (Polynomial S)))
        (dimension := DimensionFunction.comapClosedImmersion (polyToSym φ) dimM)
        (i := j)).quotientMap
        (cyclesOfDimension.properPushforward
          (VectorBundle.zeroSection (evalAlgHom (0 : S))) z)) = 0 := by
    rw [hz, map_zero]
  exact h3

variable {i : ℤ}
  (RStop : RationalEquivalenceSystem (Spec (CommRingCat.of S)) dimS
    (i + (Nat.card (Module.Free.ChooseBasisIndex S M) : ℤ)))
  (RS : RationalEquivalenceSystem (Spec (CommRingCat.of S)) dimS i)
  (RM : RationalEquivalenceSystem (Spec (CommRingCat.of (SymmetricAlgebra S M))) dimM
    (i + (Nat.card (Module.Free.ChooseBasisIndex S M) : ℤ)))
  (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of (SymmetricAlgebra S M))) dimM)
  (hinj : Function.Injective
    (VectorBundle.chowPullbackBundle (VectorBundle.symTrivialization S M) dimS dimM i RS RM))

/-- **The defining property of the top Chern class operator**, in any rank: the flat pullback of
`topChern … α` along the bundle projection is the zero-section pushforward of `α`.  This is what
makes the operator computable, and is all that is used below. -/
theorem chowPullbackBundle_topChern (α : RStop.ChowGroup) :
    VectorBundle.chowPullbackBundle (VectorBundle.symTrivialization S M) dimS dimM i RS RM
        (topChern RStop RS RM hhom hinj α) =
      VectorBundle.zeroSectionPushforward (moduleAugmentation S M) RStop RM α := by
  rw [topChern, LinearMap.comp_apply, LinearEquiv.coe_coe,
    VectorBundle.pullback_zeroSectionGysin']

/-- `topChern … α` is the *unique* class whose flat pullback is the zero-section class of `α`;
this is where injectivity of the flat pullback (`hinj`) is used. -/
theorem eq_topChern_of_chowPullbackBundle_eq (α : RStop.ChowGroup) (β : RS.ChowGroup)
    (hβ : VectorBundle.chowPullbackBundle (VectorBundle.symTrivialization S M) dimS dimM i RS RM β
      = VectorBundle.zeroSectionPushforward (moduleAugmentation S M) RStop RM α) :
    β = topChern RStop RS RM hhom hinj α :=
  hinj (hβ.trans (chowPullbackBundle_topChern RStop RS RM hhom hinj α).symm)

/-- **The top Chern class of a trivialised obstruction bundle of positive rank vanishes.**  This
is `ObstructionBundleFormula.topChern` itself: whenever `M` carries a surjective functional
`φ : M →ₗ[S] S` (equivalently, whenever the free module `M` has positive rank), the zero section
of `Spec (Sym M)` factors through the zero section of a trivial line bundle, whose class is a
principal divisor. -/
theorem topChern_eq_zero_of_surjective (φ : M →ₗ[S] S) (hφ : Function.Surjective φ) :
    topChern RStop RS RM hhom hinj = 0 := by
  rw [topChern, zeroSectionPushforward_moduleAugmentation_eq_zero φ hφ RStop RM,
    LinearMap.comp_zero]

omit [IsNoetherianRing S] [Module.Finite S M] in
/-- A free module whose basis index is nonempty carries a surjective functional: any coordinate of
a chosen basis. -/
theorem exists_surjective_of_nonempty [Nonempty (Module.Free.ChooseBasisIndex S M)] :
    ∃ φ : M →ₗ[S] S, Function.Surjective φ := by
  classical
  obtain ⟨j⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex S M)›
  refine ⟨(Module.Free.chooseBasis S M).coord j,
    fun a => ⟨a • (Module.Free.chooseBasis S M) j, ?_⟩⟩
  simp

/-- **The top Chern class of a trivialised obstruction bundle of positive rank vanishes.**  The
positive-rank hypothesis is that the chosen basis index of the free module `M` is nonempty; the
bundle `Spec (Sym M) → Spec S` is then a trivial bundle of positive rank over an affine base, and
its top Chern class operator is `0`. -/
theorem topChern_eq_zero_of_nonempty [Nonempty (Module.Free.ChooseBasisIndex S M)] :
    topChern RStop RS RM hhom hinj = 0 := by
  obtain ⟨φ, hφ⟩ := exists_surjective_of_nonempty (S := S) (M := M)
  exact topChern_eq_zero_of_surjective RStop RS RM hhom hinj φ hφ

/-- **The top Chern class in rank one is the first Chern class.**  For a rank-one obstruction
bundle over an affine base, `ObstructionBundleFormula.topChern` and the first Chern class of the
(necessarily trivial) line bundle both vanish, the first by
`topChern_eq_zero_of_surjective` and the second by `FirstChernClass.c1_trivial`.  The two
operators have the same target `(chowSystem dimS i).ChowGroup`; their domains are the two
descriptions `i + Nat.card (ChooseBasisIndex S M)` and `i + 1` of the rank-one grade, which are
equal but not syntactically so, whence the two arguments. -/
theorem topChern_apply_eq_c1_apply (φ : M ≃ₗ[S] S)
    (hcov : HomogeneityLocal.CovByDimension dimS)
    (hinj' : Function.Injective (VectorBundle.chowPullbackBundle
      (VectorBundle.symTrivialization S M) dimS dimM i (chowSystem dimS i) RM))
    (α : RStop.ChowGroup) (β : (chowSystem dimS (i + 1)).ChowGroup) :
    topChern RStop (chowSystem dimS i) RM hhom hinj' α =
      c1 (killsRelations_trivial dimS hcov i) β := by
  rw [topChern_eq_zero_of_surjective RStop (chowSystem dimS i) RM hhom hinj'
      (φ : M →ₗ[S] S) φ.surjective, c1_trivial dimS hcov i, LinearMap.zero_apply,
    LinearMap.zero_apply]

omit [IsNoetherianRing S] in
/-- A module carrying a trivialisation `φ : M ≃ₗ[S] S` has rank one, so the grade shift of its
bundle `Spec (Sym M)` is `1`. -/
theorem grade_eq_of_linearEquiv [StrongRankCondition S] (φ : M ≃ₗ[S] S) :
    i + (Nat.card (Module.Free.ChooseBasisIndex S M) : ℤ) = i + 1 := by
  have hrank : Nat.card (Module.Free.ChooseBasisIndex S M) = 1 := by
    rw [VectorBundle.card_chooseBasisIndex S M, φ.finrank_eq, Module.finrank_self]
  rw [hrank, Nat.cast_one]

/-- **The top Chern class in rank one is the first Chern class**, as an identity of operators.
For a rank-one obstruction bundle over an affine base the bundle is the trivial line bundle, and
both operators vanish: the left-hand side by `topChern_eq_zero_of_surjective` (the zero-section
class is the principal divisor of the fibre coordinate) and the right-hand side by
`FirstChernClass.c1_trivial`.  The domains are identified by `chowGradeEquiv`, which reindexes the
rank-one grade `i + Nat.card (ChooseBasisIndex S M)` as `i + 1`. -/
theorem topChern_eq_c1_trivial [StrongRankCondition S] (φ : M ≃ₗ[S] S)
    (hcov : HomogeneityLocal.CovByDimension dimS)
    (hinj' : Function.Injective (VectorBundle.chowPullbackBundle
      (VectorBundle.symTrivialization S M) dimS dimM i (chowSystem dimS i) RM)) :
    topChern RStop (chowSystem dimS i) RM hhom hinj' =
      (c1 (killsRelations_trivial dimS hcov i)).comp
        (chowGradeEquiv (grade_eq_of_linearEquiv φ) RStop
          (chowSystem dimS (i + 1))).toLinearMap := by
  rw [topChern_eq_zero_of_surjective RStop (chowSystem dimS i) RM hhom hinj'
      (φ : M →ₗ[S] S) φ.surjective, c1_trivial dimS hcov i, LinearMap.zero_comp]

end RankOne

/-! ## The affine no-obstruction formula is degenerate in positive rank -/

section Degenerate

open GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ObstructionBundleFormula
open VirtualClass ResolvedCone
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
  {E : LinearTwoTermComplex (R ⧸ I)} [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero]
  {φ : LinearTwoTermComplex.Hom E (conormalComplex k R I)}
  (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))
  (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))
  (RXtop : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (coneDegree φ))

include RXtop in
/-- **The affine no-obstruction formula is degenerate in positive rank.**  Under exactly the
hypotheses of `ObstructionBundleFormula.virtualClass_eq_topChern_cap` — the ideal of the resolved
cone is the ideal of the zero section of `E₁ = Spec Sym(E⁻¹)`, and `X` is pure of the excess
dimension `coneDegree φ` — the virtual fundamental class is `0` as soon as `E⁻¹` has positive rank
(nonempty chosen basis index).  The reason is not a defect of the formula but of the affine model:
`E⁻¹` is a *free* module over an affine base, so `E₁` is a trivial bundle, and the top Chern class
of a trivial bundle of positive rank vanishes (`topChern_eq_zero_of_nonempty`).  A nonzero virtual
class with a genuine obstruction bundle therefore requires the global theory. -/
theorem virtualClass_eq_zero_of_ideal_eq_zeroSection
    [Nonempty (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero)]
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ)
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj = 0 := by
  rw [virtualClass_eq_topChern_cap dimX dimE RX RE RXtop hzero hpureXtop hhom hinj,
    topChern_eq_zero_of_nonempty RXtop RX RE hhom hinj, LinearMap.zero_apply]

end Degenerate

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.TopChernRankOne
