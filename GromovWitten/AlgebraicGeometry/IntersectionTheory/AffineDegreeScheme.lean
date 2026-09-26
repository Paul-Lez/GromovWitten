/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroCycleDegree
import GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeFormula
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleSectionGysinIdentity
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackDescent
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyRankOne
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The scheme translation of the affine length formula

For `k` a field and `A` a finitely generated `k`-algebra that is an integral domain of Krull
dimension `1`, this file translates `AffineDegreeFormula.affineLengthFormula` (the algebraic
statement) into the scheme-theoretic language of `ZeroCycleDegree.lean`: for `X = Spec A` with its
structure morphism `f : X ⟶ Spec k` and `a : A` nonzero, the degree of the principal cycle of `a`
on `X` (w.r.t. `f`) equals the `k`-dimension of `A ⧸ (a)`.

## Main declarations

* `GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme.structureMorphism`: the
  structure morphism `Spec A ⟶ Spec k` attached to the `k`-algebra structure on `A`.
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme.
  degreeCycle_principalCycle_eq_finrank`: the main theorem, `degreeCycle f (X.principalCycle r) =
  finrank k (A ⧸ (a))` for `r` the function-field unit attached to `a`.
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme.
  instIsIso_residueFieldMap_of_isClosedImmersion`: a closed immersion induces an isomorphism of
  residue fields at every point of its source (a general fact, not yet in Mathlib, proved here
  from the surjectivity of stalk maps).
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme.
  degreeCycle_map_eq_of_isClosedImmersion`: for a closed immersion `i : Z ⟶ X` over `Spec k`,
  `degreeCycle f (i_* α) = degreeCycle (i ≫ f) α`.

## Proof outline

The residue-degree-weighted sum defining `degreeCycle` over the points of `X = Spec A` is first
reindexed, via `finsum_eq_finsum_comp_of_support_subset_range`, to a `finsum` over
`MaximalSpectrum A`: every point outside the range of `MaximalSpectrum.toPrimeSpectrum` has ideal
`⊥` (`isMaximal_of_ne_bot`, using `A` a domain of Krull dimension `≤ 1`), hence contributes `0`
to `degreeCycle` (its `Scheme.ord` vanishes, since its specialisation-order coheight is `0`, not
`1`, by `coheight_ne_one_of_eq_bot`). At each maximal ideal `m` the two termwise identifications
`ord_eq_localization_ord` (`Scheme.ord = Ring.ord` on the localisation, via
`VectorBundle.scheme_ord_eq_localization`, using `coheight_eq_one_of_ne_bot` to supply its
`Order.coheight = 1` hypothesis) and `residueDegree_eq_finrank_quotient` (`[κ(m):k] = finrank k
(A ⧸ m)`, via the residue field isomorphism `Scheme.Spec.residueFieldIso` composed with
`AffineDegreeFormula.length_residueField_localization_eq`) turn the reindexed sum into exactly
`AffineDegreeFormula.affineLengthFormula`'s left-hand side.

The closed-immersion compatibility `degreeCycle_map_eq_of_isClosedImmersion` rests on a fact not
otherwise recorded in Mathlib: a closed immersion `i` induces an isomorphism on residue fields at
every point (`instIsIso_residueFieldMap_of_isClosedImmersion`), proved directly from the
surjectivity of its stalk maps (`IsClosedImmersion`/`SurjectiveOnStalks`) via a general fact about
surjective local ring homomorphisms (`residueField_map_bijective_of_surjective`). This upgrades
`ZeroCycleDegree.residueDegree`'s absolute `k`-degree at a point of `Z` to the same degree at its
image in `X` (`residueDegree_closedImmersion`); combined with the repo's own
`ChowGroup.lean` facts about closed-immersion pushforward of algebraic cycles
(`AlgebraicCycle.map_closedImmersion_apply_image`,
`AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range`,
`DimensionFunction.apply_eq_of_isClosedImmersion`) and the same finsum reindexing lemma, this gives
the compatibility of `degreeCycle` with pushforward along a closed immersion.
-/

open CategoryTheory AlgebraicGeometry GromovWitten.AlgebraicGeometry.IntersectionTheory

universe u

/-! ## A finsum reindexing lemma -/

/-- A finite sum over `α` reindexes along an injective map `g : β → α`, provided the summand's
support lies in the range of `g`: this is `finsum_mem_range` combined with the observation that
restricting a finsum to a set containing its support doesn't change its value. -/
theorem finsum_eq_finsum_comp_of_support_subset_range {β α M : Type*} [AddCommMonoid M]
    {g : β → α} (hg : Function.Injective g) (f : α → M)
    (hsub : Function.support f ⊆ Set.range g) :
    ∑ᶠ a, f a = ∑ᶠ b, f (g b) := by
  rw [← finsum_mem_univ f,
    ← finsum_mem_inter_support_eq' f (Set.range g) Set.univ
      (fun x hx => ⟨fun _ => trivial, fun _ => hsub hx⟩)]
  exact finsum_mem_range hg

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsDomain A]
  [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A] [IsNoetherianRing A]

/-! ## The structure morphism of `Spec A` over `Spec k` -/

/-- The structure morphism `Spec A ⟶ Spec k` induced by the `k`-algebra structure on `A`. -/
noncomputable def structureMorphism : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

omit [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- The ring homomorphism `k →+* A` recovered from `structureMorphism` via
`FiniteTypeDimension.specAlgebraMap` is the original `algebraMap k A`, up to the naturality of
`Scheme.ΓSpecIso`. -/
theorem specAlgebraMap_structureMorphism :
    FiniteTypeDimension.specAlgebraMap (structureMorphism (k := k) (A := A)) = algebraMap k A := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (structureMorphism (k := k) (A := A)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom = algebraMap k A
  rw [structureMorphism, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]

/-- `structureMorphism` is locally of finite type, since `A` is a finite-type `k`-algebra. -/
instance instLocallyOfFiniteType_structureMorphism :
    LocallyOfFiniteType (structureMorphism (k := k) (A := A)) := by
  rw [structureMorphism, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
    CommRingCat.hom_ofHom]
  exact (RingHom.finiteType_algebraMap).mpr inferInstance

/-- `Spec A` is quasi-compact, as needed for `ZeroCycleDegree.degreeCycle`. -/
instance instCompactSpace_spec : CompactSpace (↥(Spec (CommRingCat.of A))) :=
  inferInstance

/-! ## The point of `Spec A` attached to a maximal ideal -/

/-- The point of `Spec A` attached to a maximal ideal of `A`. -/
noncomputable def toSpecPoint (m : MaximalSpectrum A) : ↥(Spec (CommRingCat.of A)) :=
  m.toPrimeSpectrum

omit [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- `toSpecPoint` is injective. -/
theorem toSpecPoint_injective : Function.Injective (toSpecPoint (A := A)) :=
  fun _ _ h => MaximalSpectrum.toPrimeSpectrum_injective h

/-! ## Transport of `finrank` along a compatible ring isomorphism -/

/-- `Module.finrank` transports along a ring isomorphism compatible with `k`-algebra maps, when
the source ring's `k`-algebra structure is a `letI`-supplied one (as in `residueDegree`) and the
target's is the ambient instance: mirrors `ZeroCycleDegree.finite_congr`, for `finrank` instead of
`Module.Finite`. -/
theorem finrank_congr' {K : CommRingCat.{u}} (φ : k →+* K) {L : CommRingCat.{u}} [Algebra k L]
    (e : K ≃+* L) (he : ∀ c, e (φ c) = algebraMap k L c) :
    (letI := φ.toAlgebra; Module.finrank k K) = Module.finrank k L := by
  let _ : Algebra k K := φ.toAlgebra
  let e' : K ≃ₐ[k] L := { e with commutes' := he }
  exact e'.toLinearEquiv.finrank_eq

omit [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- **The residue degree at a maximal ideal is the `k`-dimension of the residue field.**
`[κ(m):k] = finrank k (A ⧸ m)` for `m` a maximal ideal of `A`, via the residue field isomorphism
`Scheme.Spec.residueFieldIso` and `AffineDegreeFormula.length_residueField_localization_eq`. -/
theorem residueDegree_eq_finrank_quotient (m : MaximalSpectrum A) :
    ZeroCycleDegree.residueDegree (structureMorphism (k := k) (A := A)) (toSpecPoint m) =
      Module.finrank k (A ⧸ m.asIdeal) := by
  have hspec := specAlgebraMap_structureMorphism (k := k) (A := A)
  have hmm : m.asIdeal.IsMaximal := m.isMaximal
  have step1 : (letI := (FiniteTypeDimension.residueMap
        (structureMorphism (k := k) (A := A)) (toSpecPoint m)).toAlgebra;
      Module.finrank k ((Spec (CommRingCat.of A)).residueField (toSpecPoint m))) =
      Module.finrank k (toSpecPoint m).asIdeal.ResidueField := by
    apply finrank_congr'
      (FiniteTypeDimension.residueMap (structureMorphism (k := k) (A := A)) (toSpecPoint m))
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) (toSpecPoint m)).commRingCatIsoToRingEquiv
    intro c
    change (Scheme.Spec.residueFieldIso (CommRingCat.of A) (toSpecPoint m)).hom.hom
        (FiniteTypeDimension.residueMap (structureMorphism (k := k) (A := A)) (toSpecPoint m) c) =
        algebraMap k (toSpecPoint m).asIdeal.ResidueField c
    rw [FiniteTypeDimension.residueFieldIso_residueMap, hspec,
      ← IsScalarTower.algebraMap_apply k A (toSpecPoint m).asIdeal.ResidueField]
  have hlen := AffineDegreeFormula.length_residueField_localization_eq (k := k) m.asIdeal
    (Am := Localization.AtPrime m.asIdeal)
  have step2 : Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) =
      Module.finrank k (A ⧸ m.asIdeal) := by
    have hcast := congrArg ENat.toNat hlen
    rwa [AffineDegreeFormula.length_toNat_eq_finrank,
      AffineDegreeFormula.length_toNat_eq_finrank] at hcast
  change (letI := (FiniteTypeDimension.residueMap
      (structureMorphism (k := k) (A := A)) (toSpecPoint m)).toAlgebra;
    Module.finrank k ((Spec (CommRingCat.of A)).residueField (toSpecPoint m))) =
    Module.finrank k (A ⧸ m.asIdeal)
  exact step1.trans step2

/-! ## Dimension-`0` points of `Spec A` are the maximal ideals -/

omit [Algebra k A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- **A nonzero prime of a domain of Krull dimension `≤ 1` is maximal.** If it weren't, a maximal
ideal strictly above it would force a chain of length `2`, contradicting `Ring.KrullDimLE 1 A`. -/
theorem isMaximal_of_ne_bot (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) : p.IsMaximal := by
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal (Ideal.IsPrime.ne_top ‹p.IsPrime›)
  rcases eq_or_lt_of_le hpm with heq | hlt
  · rw [heq]; exact hm
  · exfalso
    have h1 : p.height + 1 ≤ m.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : m.height ≤ (1 : ℕ∞) := by
      have hb := Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
      have hk : ringKrullDim A ≤ (1 : ℕ) := Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›
      exact_mod_cast hb.trans hk
    have h3 : p.height ≠ 0 := by rw [ne_eq, Ideal.height_eq_zero_iff_eq_bot]; exact hp
    have h4 : (1 : ℕ∞) ≤ p.height := Order.one_le_iff_ne_zero.mpr h3
    have h5 : (2 : ℕ∞) ≤ p.height + 1 := by
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := by gcongr
    have h6 : (2 : ℕ∞) ≤ (1 : ℕ∞) := h5.trans (h1.trans h2)
    norm_num at h6

omit [Algebra k A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- A point of `Spec A` with nonzero ideal has specialisation-order coheight `1`: this is the
hypothesis `Scheme.ord` needs to be non-junk, translated from the classical ideal height via
`VectorBundle.coheight_eq_ideal_height`. -/
theorem coheight_eq_one_of_ne_bot (x : ↥(Spec (CommRingCat.of A))) (hx : x.asIdeal ≠ ⊥) :
    Order.coheight x = 1 := by
  have hco_eq : Order.coheight x = x.asIdeal.height := VectorBundle.coheight_eq_ideal_height A x
  rw [hco_eq]
  have h1 : x.asIdeal.height ≤ (1 : ℕ∞) := by
    have hb := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top x.isPrime)
    have hk : ringKrullDim A ≤ (1 : ℕ) := Ring.krullDimLE_iff.mp ‹Ring.KrullDimLE 1 A›
    exact_mod_cast hb.trans hk
  have h2 : x.asIdeal.height ≠ 0 := by
    rw [ne_eq, Ideal.height_eq_zero_iff_eq_bot]; exact hx
  exact le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)

omit [Ring.KrullDimLE 1 A] [Algebra k A] [Algebra.FiniteType k A] [IsNoetherianRing A] in
/-- The generic point of `Spec A` (ideal `⊥`) has specialisation-order coheight `≠ 1`. -/
theorem coheight_ne_one_of_eq_bot (x : ↥(Spec (CommRingCat.of A))) (hx : x.asIdeal = ⊥) :
    Order.coheight x ≠ 1 := by
  have hco_eq : Order.coheight x = x.asIdeal.height := VectorBundle.coheight_eq_ideal_height A x
  rw [hco_eq, hx, Ideal.height_bot]
  exact zero_ne_one

/-! ## The scheme-theoretic order of vanishing at a maximal ideal -/

/-- **`Scheme.ord` at a maximal ideal is `Ring.ord` on the localisation.** For `a ≠ 0` and `m` a
maximal ideal of `A`, the order of vanishing of `a` at the corresponding point of `Spec A` is the
length-theoretic order of vanishing of `a` in `Localization.AtPrime m`: this is
`VectorBundle.scheme_ord_eq_localization` when `a ∈ m` (using `coheight_eq_one_of_ne_bot`), and
both sides vanish (`Scheme.ord_algebraMap_eq_zero_of_notMem` / `Ring.ord_of_isUnit`) when
`a ∉ m`. -/
theorem ord_eq_localization_ord (a : A) (ha : a ≠ 0) (m : MaximalSpectrum A) :
    (Spec (CommRingCat.of A)).ord
        (VectorBundle.functionFieldUnit (CommRingCat.of A) a ha :
          (Spec (CommRingCat.of A)).functionField)
        (toSpecPoint m) =
      ((Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat : ℤ) := by
  rw [VectorBundle.functionFieldUnit_val]
  by_cases hmem : a ∈ m.asIdeal
  · have hne : (toSpecPoint m).asIdeal ≠ ⊥ := fun h => ha (Ideal.mem_bot.mp (h ▸ hmem))
    have hco := coheight_eq_one_of_ne_bot (toSpecPoint m) hne
    exact VectorBundle.scheme_ord_eq_localization (CommRingCat.of A) (toSpecPoint m) a ha hco
  · have hunit : IsUnit (algebraMap A (Localization.AtPrime m.asIdeal) a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m.asIdeal) m.asIdeal a).mpr
        hmem
    rw [VectorBundle.ord_algebraMap_eq_zero_of_notMem (CommRingCat.of A) (toSpecPoint m) a hmem,
      Ring.ord_of_isUnit hunit]
    rfl

/-! ## The main theorem -/

/-- **The scheme translation of the affine length formula.** For `k` a field, `A` a finitely
generated `k`-algebra that is an integral domain of Krull dimension `1`, `X = Spec A` with
structure morphism `structureMorphism`, and `a : A` nonzero, the degree of the principal cycle
attached to `a` (viewed as a unit `r` of the function field of `X` via
`VectorBundle.functionFieldUnit`) equals the `k`-dimension of `A ⧸ (a)`: Fulton's Example 1.2.3 /
Appendix A.3, restated on `Spec A` rather than algebraically. -/
theorem degreeCycle_principalCycle_eq_finrank (a : A) (ha : a ≠ 0) :
    ZeroCycleDegree.degreeCycle (structureMorphism (k := k) (A := A))
      ((Spec (CommRingCat.of A)).principalCycle
        (VectorBundle.functionFieldUnit (CommRingCat.of A) a ha :
          (Spec (CommRingCat.of A)).functionField)) =
      (Module.finrank k (A ⧸ Ideal.span {a}) : ℚ) := by
  rw [ZeroCycleDegree.degreeCycle_apply]
  simp_rw [AlgebraicGeometry.Scheme.principalCycle_apply]
  have hsub : Function.support (fun x : ↥(Spec (CommRingCat.of A)) =>
      ((Spec (CommRingCat.of A)).ord
          (VectorBundle.functionFieldUnit (CommRingCat.of A) a ha :
            (Spec (CommRingCat.of A)).functionField) x : ℚ) *
        (ZeroCycleDegree.residueDegree (structureMorphism (k := k) (A := A)) x : ℚ))
      ⊆ Set.range (toSpecPoint (A := A)) := by
    intro x hx
    by_contra hcon
    apply hx
    have hxnotmax : ¬ x.asIdeal.IsMaximal := by
      intro hxmax
      exact hcon ⟨⟨x.asIdeal, hxmax⟩, PrimeSpectrum.ext rfl⟩
    have hxbot : x.asIdeal = ⊥ := by
      by_contra hxne
      exact hxnotmax (isMaximal_of_ne_bot x.asIdeal hxne)
    have hco := coheight_ne_one_of_eq_bot x hxbot
    change ((Spec (CommRingCat.of A)).ord _ x : ℚ) * _ = 0
    rw [_root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco]
    simp
  rw [finsum_eq_finsum_comp_of_support_subset_range toSpecPoint_injective _ hsub]
  have hterm : ∀ m : MaximalSpectrum A,
      ((Spec (CommRingCat.of A)).ord
          (VectorBundle.functionFieldUnit (CommRingCat.of A) a ha :
            (Spec (CommRingCat.of A)).functionField) (toSpecPoint m) : ℚ) *
        (ZeroCycleDegree.residueDegree (structureMorphism (k := k) (A := A))
          (toSpecPoint m) : ℚ) =
      ((Module.finrank k (A ⧸ m.asIdeal) *
        (Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat : ℕ) : ℚ) := by
    intro m
    rw [ord_eq_localization_ord a ha m, residueDegree_eq_finrank_quotient m]
    push_cast
    ring
  simp_rw [hterm]
  have hcast : (∑ᶠ m : MaximalSpectrum A, ((Module.finrank k (A ⧸ m.asIdeal) *
        (Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat : ℕ) : ℚ)) =
      ((∑ᶠ m : MaximalSpectrum A, Module.finrank k (A ⧸ m.asIdeal) *
        (Ring.ord (Localization.AtPrime m.asIdeal)
          (algebraMap A (Localization.AtPrime m.asIdeal) a)).toNat : ℕ) : ℚ) :=
    ((Nat.castRingHom ℚ).toAddMonoidHom.map_finsum_of_injective Nat.cast_injective _).symm
  rw [hcast]
  exact_mod_cast AffineDegreeFormula.affineLengthFormula a ha

/-! ## Compatibility of `degreeCycle` with pushforward along a closed immersion -/

omit [CommRing A] [Algebra k A] [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
  [IsNoetherianRing A] in
/-- A surjective local ring homomorphism between local rings induces a bijection on residue
fields: injectivity is because the kernel of the residue map is always contained in the maximal
ideal (ring homomorphisms preserve units), which combined with the local-homomorphism inclusion
gives equality; surjectivity is because the composite with the (surjective) residue map of the
target is again surjective. -/
theorem residueField_map_bijective_of_surjective {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Function.Bijective (IsLocalRing.ResidueField.map φ) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    rw [IsLocalRing.ResidueField.map_residue] at ha
    rw [IsLocalRing.residue_eq_zero_iff] at ha ⊢
    intro hcon
    exact ha (hcon.map φ)
  · intro b
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective b
    obtain ⟨r, rfl⟩ := hφ s
    exact ⟨IsLocalRing.residue R r, by rw [IsLocalRing.ResidueField.map_residue]⟩

omit [CommRing A] [Algebra k A] [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
  [IsNoetherianRing A] in
/-- **A closed immersion induces an isomorphism of residue fields at every point of its source.**
This general scheme-theoretic fact is not otherwise recorded in Mathlib: it follows from
`residueField_map_bijective_of_surjective` applied to the (surjective, by `IsClosedImmersion`)
stalk map. -/
instance instIsIso_residueFieldMap_of_isClosedImmersion
    {X Y : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  have hsurj : Function.Surjective (f.stalkMap x).hom := f.stalkMap_surjective x
  have hbij := residueField_map_bijective_of_surjective (f.stalkMap x).hom hsurj
  exact (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom

omit [CommRing A] [Algebra k A] [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
  [IsNoetherianRing A] in
/-- `Module.finrank` transports along a ring isomorphism compatible with `k`-algebra maps, when
BOTH sides' `k`-algebra structures are `letI`-supplied ones (as in `residueDegree`): a variant of
`finrank_congr'` for when neither side has an ambient `Algebra k` instance to fall back on. -/
theorem finrank_congr'' {K L : CommRingCat.{u}} (φ : k →+* K) (ψ : k →+* L)
    (e : K ≃+* L) (he : ∀ c, e (φ c) = ψ c) :
    (letI := φ.toAlgebra; Module.finrank k K) = (letI := ψ.toAlgebra; Module.finrank k L) := by
  let _ : Algebra k K := φ.toAlgebra
  let _ : Algebra k L := ψ.toAlgebra
  let e' : K ≃ₐ[k] L := { e with commutes' := he }
  exact e'.toLinearEquiv.finrank_eq

omit [CommRing A] [Algebra k A] [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
  [IsNoetherianRing A] in
/-- **The residue degree at a point is unchanged by pulling back along a closed immersion.**
`residueDegree (i ≫ f) z = residueDegree f (i.base z)`, via the residue field isomorphism of
`instIsIso_residueFieldMap_of_isClosedImmersion` and the naturality
`FiniteTypeDimension.residueFieldMap_residueMap`. -/
theorem residueDegree_closedImmersion {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) {Z : _root_.AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) :
    ZeroCycleDegree.residueDegree (i ≫ f) z = ZeroCycleDegree.residueDegree f (i.base z) := by
  apply (finrank_congr'' (FiniteTypeDimension.residueMap f (i.base z))
    (FiniteTypeDimension.residueMap (i ≫ f) z)
    (asIso (i.residueFieldMap z)).commRingCatIsoToRingEquiv _).symm
  intro c
  change (asIso (i.residueFieldMap z)).hom.hom
      (FiniteTypeDimension.residueMap f (i.base z) c) = FiniteTypeDimension.residueMap (i ≫ f) z c
  exact FiniteTypeDimension.residueFieldMap_residueMap f i z c

omit [CommRing A] [Algebra k A] [IsDomain A] [Ring.KrullDimLE 1 A] [Algebra.FiniteType k A]
  [IsNoetherianRing A] in
/-- **`degreeCycle` is compatible with pushforward along a closed immersion.** For `i : Z ⟶ X` a
closed immersion, `f : X ⟶ Spec k` locally of finite type, and `α` a rational algebraic cycle on
`Z`, the degree (w.r.t. `f`) of the pushforward `i_*α` (`AlgebraicCycle.map`, weighted by the
canonical dimension functions of `X` and `Z`) equals the degree of `α` w.r.t. the structure
morphism `i ≫ f` of `Z`. Uses the repo's `ChowGroup.lean` facts about closed-immersion pushforward
(`AlgebraicCycle.map_closedImmersion_apply_image`,
`AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range`, which already account for the
residue-degree-`1` factor of `Scheme.Hom.residueDegree` at a closed immersion) together with
`DimensionFunction.apply_eq_of_isClosedImmersion` and `residueDegree_closedImmersion` above. -/
theorem degreeCycle_map_eq_of_isClosedImmersion
    {X : _root_.AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [CompactSpace X]
    {Z : _root_.AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ f)] [CompactSpace Z]
    (α : _root_.AlgebraicGeometry.AlgebraicCycle Z ℚ) :
    ZeroCycleDegree.degreeCycle f
      (_root_.AlgebraicGeometry.AlgebraicCycle.map i
        (FiniteTypeDimension.dimensionFunction (i ≫ f))
        (FiniteTypeDimension.dimensionFunction f) α) =
      ZeroCycleDegree.degreeCycle (i ≫ f) α := by
  have hwx : (FiniteTypeDimension.dimensionFunction (i ≫ f) : Z → ℤ) =
      fun z ↦ (FiniteTypeDimension.dimensionFunction f : X → ℤ) (i.base z) :=
    funext (DimensionFunction.apply_eq_of_isClosedImmersion
      (FiniteTypeDimension.dimensionFunction (i ≫ f)) (FiniteTypeDimension.dimensionFunction f) i)
  rw [ZeroCycleDegree.degreeCycle_apply, ZeroCycleDegree.degreeCycle_apply, hwx]
  have hsub : Function.support (fun x : X =>
      (_root_.AlgebraicGeometry.AlgebraicCycle.map i
        (fun z ↦ (FiniteTypeDimension.dimensionFunction f : X → ℤ) (i.base z))
        (FiniteTypeDimension.dimensionFunction f) α x) *
      (ZeroCycleDegree.residueDegree f x : ℚ)) ⊆ Set.range i.base := by
    intro x hx
    by_contra hcon
    apply hx
    dsimp only
    rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range i
      (FiniteTypeDimension.dimensionFunction f : X → ℤ) α x hcon, zero_mul]
  rw [finsum_eq_finsum_comp_of_support_subset_range i.isClosedEmbedding.injective _ hsub]
  refine finsum_congr fun z ↦ ?_
  rw [AlgebraicCycle.map_closedImmersion_apply_image i
    (FiniteTypeDimension.dimensionFunction f : X → ℤ) α z, residueDegree_closedImmersion f i z]

end GromovWitten.AlgebraicGeometry.IntersectionTheory.AffineDegreeScheme
