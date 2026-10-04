/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Filtration
import GromovWitten.AlgebraicGeometry.IntersectionTheory.PointOrder
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ZeroSectionCartier
import GromovWitten.AlgebraicGeometry.IntersectionTheory.LineBundleRestrict

/-!
# Orders of coordinate functions in affine charts

This file computes the order function `pointOrd` (`PointOrder.lean`) in affine charts.

* Point stalks are invariant under morphisms that are surjective on stalks, in particular under
  open and closed immersions (preimmersions): for `f : Z ⟶ Y` and `w ⤳ v` in `Z`, the point
  stalk of `f w ⤳ f v` is the point stalk of `w ⤳ v`, compatibly with `residueFieldMap`, so
  `pointOrd (f w ⤳ f v) u = pointOrd (w ⤳ v) (residueFieldMap u)`.
* In an affine chart `ψ : Spec R ⟶ Y` (an open immersion), the point stalk of `ψ x ⤳ ψ y` is the
  localisation `(R ⧸ x)_{y / x}`, and `pointOrd` of the residue class of `c : R` is the order of
  the class of `c` in that ring when it has Krull dimension one (and `0` otherwise).
* For `B` a Noetherian domain, `T` finite and `S ⊆ T`, the coordinate prime
  `coordPrime S = (X s : s ∈ S)` of `B[X_t : t ∈ T]` is prime with quotient
  `B[X_t : t ∉ S]`, and for `t ∉ S` no prime lies strictly between `coordPrime S` and
  `coordPrime (insert t S)` (Krull's intersection theorem).  Hence, for a preimmersion
  (e.g. an affine chart) `ψ : Spec B[X_t] ⟶ Y`, the order of `X t` along
  `ψ (coordPrime S) ⤳ ψ q` is `1` if `q = coordPrime (insert t S)` and `0` otherwise,
  and the two coordinate points differ by one in any dimension function satisfying
  `CovByDimension`.

## Main results

* `pointStalkEquivOfSurjective`, `pointOrd_of_stalkMap_surjective`, `pointOrd_preimmersion`,
  `pointOrd_openImmersion` (blueprint B4), `pointStalk_closedImmersion`,
  `pointOrd_closedImmersion`.
* `coordPrime`, `coordPrime_isPrime`, `quotientCoordPrimeEquiv`, `height_coordPrime_single`,
  `coordPrime_eq_or_eq_of_le` (blueprint B2).
* `specGerm` (germs of elements of `R` on `Spec R`), `coordPrimePt`, `coordPrimePt_covBy`.
* `pointOrd_coordPrime_spec`, `pointOrd_coordPrime` (blueprint B3; `pointOrd_coordPrime'` with
  the packaged unit `coordPrimeResidueUnit`), `dim_coordPrime_insert`
  (blueprint B5).
* `chartQuotPrime`, `specPointStalkEquiv`, `pointStalkChartEquiv` (blueprint B1),
  `pointOrd_chart`, `pointOrd_chart_of_ne_one` (blueprint B1'), and
  `residueFieldMap_residue_germ` (the residue of a section pulled back to a chart).
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace IsLocalRing

open scoped WithZero

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

/-! ## Point stalks and preimmersions -/

section Preimmersion

variable {Z Y : Scheme.{u}} (f : Z ⟶ Y) {w v : Z}

/-- The point-stalk maps of `w ⤳ v` and of its image `f w ⤳ f v` are intertwined by the stalk
map at `v` and the residue field map at `w`. -/
theorem pointStalkMap_stalkMap (h : w ⤳ v) (h' : f w ⤳ f v) (t : Y.presheaf.stalk (f v)) :
    pointStalkMap h (f.stalkMap v t) = f.residueFieldMap w (pointStalkMap h' t) := by
  rw [pointStalkMap_apply, pointStalkMap_apply,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply f w v h, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Y.residue _) (f.residueFieldMap w), Scheme.residue_residueFieldMap]

/-- The kernel of the point-stalk map of `f w ⤳ f v` is the preimage under the stalk map at `v`
of the kernel of the point-stalk map of `w ⤳ v`. -/
theorem ker_pointStalkMap_eq_comap (h : w ⤳ v) (h' : f w ⤳ f v) :
    RingHom.ker (pointStalkMap h') =
      (RingHom.ker (pointStalkMap h)).comap (f.stalkMap v).hom := by
  ext t
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, pointStalkMap_stalkMap f h h',
    map_eq_zero_iff _ (f.residueFieldMap w).hom.injective]

/-- For a morphism that is surjective on stalks (e.g. a preimmersion: an open or a closed
immersion), the point stalk of `f w ⤳ f v` is isomorphic to the point stalk of `w ⤳ v`,
through the stalk map at `v`. -/
noncomputable def pointStalkEquivOfSurjective (h : w ⤳ v) (h' : f w ⤳ f v)
    (hs : Function.Surjective (f.stalkMap v)) : pointStalk h' ≃+* pointStalk h :=
  (Ideal.quotEquivOfEq (by
      rw [ker_pointStalkMap_eq_comap f h h', ← RingHom.comap_ker, Ideal.mk_ker])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))).comp (f.stalkMap v).hom)
      (Ideal.Quotient.mk_surjective.comp hs))

/-- `pointStalkEquivOfSurjective` on classes is the stalk map. -/
theorem pointStalkEquivOfSurjective_mk (h : w ⤳ v) (h' : f w ⤳ f v)
    (hs : Function.Surjective (f.stalkMap v)) (t : Y.presheaf.stalk (f v)) :
    pointStalkEquivOfSurjective f h h' hs (Ideal.Quotient.mk _ t) =
      Ideal.Quotient.mk _ (f.stalkMap v t) := rfl

/-- `pointStalkEquivOfSurjective` is compatible with the embeddings into the residue fields,
identified by `residueFieldMap`. -/
theorem algebraMap_pointStalkEquivOfSurjective (h : w ⤳ v) (h' : f w ⤳ f v)
    (hs : Function.Surjective (f.stalkMap v)) (a : pointStalk h') :
    algebraMap (pointStalk h) (Z.residueField w) (pointStalkEquivOfSurjective f h h' hs a) =
      f.residueFieldMap w (algebraMap (pointStalk h') (Y.residueField (f w)) a) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [pointStalkEquivOfSurjective_mk, pointStalk_algebraMap_mk, pointStalk_algebraMap_mk,
    pointStalkMap_stalkMap f h h']

/-- If the stalk map at `w` is surjective, the residue field map at `w` is bijective. -/
theorem residueFieldMap_bijective (hs : Function.Surjective (f.stalkMap w)) :
    Function.Bijective (f.residueFieldMap w) := by
  refine ⟨(f.residueFieldMap w).hom.injective, fun z ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Z.residue_surjective w z
  obtain ⟨t, rfl⟩ := hs y
  exact ⟨Y.residue _ t, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

/-- The residue field map of a morphism surjective on the stalk at `w`, as a ring
isomorphism `κ(f w) ≃+* κ(w)`. -/
noncomputable def residueFieldEquivOfSurjective (hs : Function.Surjective (f.stalkMap w)) :
    Y.residueField (f w) ≃+* Z.residueField w :=
  RingEquiv.ofBijective (f.residueFieldMap w).hom (residueFieldMap_bijective f hs)

/-- The value of `residueFieldEquivOfSurjective`. -/
theorem residueFieldEquivOfSurjective_apply (hs : Function.Surjective (f.stalkMap w))
    (z : Y.residueField (f w)) :
    residueFieldEquivOfSurjective f hs z = f.residueFieldMap w z := rfl

/-- **`pointOrd` along a morphism surjective on stalks.**  If `f : Z ⟶ Y` is surjective on the
stalks at `w` and at `v` (with `w ⤳ v`), then for every unit `u` of `κ(f w)`, the order of `u`
along `f w ⤳ f v` equals the order along `w ⤳ v` of its image under `residueFieldMap`. -/
theorem pointOrd_of_stalkMap_surjective [IsLocallyNoetherian Z] [IsLocallyNoetherian Y]
    (h : w ⤳ v) (h' : f w ⤳ f v) (hsv : Function.Surjective (f.stalkMap v))
    (hsw : Function.Surjective (f.stalkMap w)) (u : (Y.residueField (f w))ˣ) :
    pointOrd h' u = pointOrd h (Units.map (f.residueFieldMap w).hom.toMonoidHom u) := by
  let e := pointStalkEquivOfSurjective f h h' hsv
  have hdim : ringKrullDim (pointStalk h') = ringKrullDim (pointStalk h) :=
    ringKrullDim_eq_of_ringEquiv e
  by_cases hd : ringKrullDim (pointStalk h) = 1
  · have hd' : ringKrullDim (pointStalk h') = 1 := hdim.trans hd
    have := krullDimLE_one_pointStalk_of_eq_one hd
    have := krullDimLE_one_pointStalk_of_eq_one hd'
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective (α := Multiplicative ℤ)
    rw [pointOrd_of_eq_one hd, pointOrd_of_eq_one hd', Units.coe_map,
      ← ordFrac_ringEquiv e (residueFieldEquivOfSurjective f hsw)
        (fun r ↦ (algebraMap_pointStalkEquivOfSurjective f h h' hsv r).symm) (u : _)]
    rfl
  · rw [pointOrd_of_ne_one hd, pointOrd_of_ne_one (hdim.trans_ne hd)]

/-- **`pointOrd` along a preimmersion** (in particular along an open or a closed immersion):
for `f : Z ⟶ Y` a preimmersion, `w ⤳ v` in `Z` and `u` a unit of `κ(f w)`,
`pointOrd (f w ⤳ f v) u = pointOrd (w ⤳ v) (residueFieldMap u)`. -/
theorem pointOrd_preimmersion [IsLocallyNoetherian Z] [IsLocallyNoetherian Y] [IsPreimmersion f]
    (h : w ⤳ v) (h' : f w ⤳ f v) (u : (Y.residueField (f w))ˣ) :
    pointOrd h' u = pointOrd h (Units.map (f.residueFieldMap w).hom.toMonoidHom u) :=
  pointOrd_of_stalkMap_surjective f h h' (f.stalkMap_surjective v) (f.stalkMap_surjective w) u

/-- **Locality of `pointOrd` under open immersions** (blueprint B4): for an open immersion
`f : Z ⟶ Y`, `w ⤳ v` in `Z` and `u` a unit of `κ(f w)`,
`pointOrd (f w ⤳ f v) u = pointOrd (w ⤳ v) (residueFieldMap u)`. -/
theorem pointOrd_openImmersion [IsLocallyNoetherian Z] [IsLocallyNoetherian Y]
    [IsOpenImmersion f] (h : w ⤳ v) (h' : f w ⤳ f v) (u : (Y.residueField (f w))ˣ) :
    pointOrd h' u = pointOrd h (Units.map (f.residueFieldMap w).hom.toMonoidHom u) :=
  pointOrd_preimmersion f h h' u

/-- The point stalk along a closed immersion: for a closed immersion `f : Z ⟶ Y` and `w ⤳ v`
in `Z`, the point stalk of `f w ⤳ f v` is isomorphic to that of `w ⤳ v`.  This is
`pointStalkClosedEquiv` (`LineBundleRestrict.lean`), stated for an arbitrary proof `h'`. -/
noncomputable def pointStalk_closedImmersion [IsClosedImmersion f] (h : w ⤳ v)
    (h' : f w ⤳ f v) : pointStalk h' ≃+* pointStalk h :=
  pointStalkClosedEquiv f h

/-- The point stalk along an open immersion: for an open immersion `f : Z ⟶ Y` and `w ⤳ v` in
`Z`, the point stalk of `f w ⤳ f v` is isomorphic to that of `w ⤳ v` (through the stalk map at
`v`; compatible with `residueFieldMap`, see `algebraMap_pointStalkEquivOfSurjective`). -/
noncomputable def pointStalk_openImmersion [IsOpenImmersion f] (h : w ⤳ v)
    (h' : f w ⤳ f v) : pointStalk h' ≃+* pointStalk h :=
  pointStalkEquivOfSurjective f h h' (f.stalkMap_surjective v)

/-- **`pointOrd` along a closed immersion**: for a closed immersion `f : Z ⟶ Y`, `w ⤳ v` in `Z`
and `u` a unit of `κ(f w)`, `pointOrd (f w ⤳ f v) u = pointOrd (w ⤳ v) (residueFieldMap u)`
(a restatement of `pointOrd_closedResidueFieldEquiv` from `LineBundleRestrict.lean`). -/
theorem pointOrd_closedImmersion [IsLocallyNoetherian Z] [IsLocallyNoetherian Y]
    [IsClosedImmersion f] (h : w ⤳ v) (h' : f w ⤳ f v) (u : (Y.residueField (f w))ˣ) :
    pointOrd h' u = pointOrd h (Units.map (f.residueFieldMap w).hom.toMonoidHom u) :=
  (pointOrd_closedResidueFieldEquiv f h u).symm

end Preimmersion

/-! ## Coordinate primes of a polynomial ring -/

section CoordPrime

open MvPolynomial

variable {T B : Type*} [CommRing B]

/-- The coordinate prime of `S ⊆ T` in `B[X_t : t ∈ T]`: the ideal generated by the variables
`X s`, `s ∈ S`. -/
noncomputable def coordPrime (S : Set T) : Ideal (MvPolynomial T B) :=
  Ideal.span (X '' S)

/-- The `B`-algebra map `B[X_t : t ∈ T] → B[X_t : t ∉ S]` killing the variables in `S`. -/
noncomputable def coordKill (S : Set T) :
    MvPolynomial T B →ₐ[B] MvPolynomial {s // s ∉ S} B :=
  killCompl Subtype.val_injective

/-- `coordKill S` kills the variables in `S`. -/
theorem coordKill_X_of_mem {S : Set T} {s : T} (hs : s ∈ S) :
    coordKill (B := B) S (X s) = 0 := by
  classical
  have : s ∉ Set.range (Subtype.val : {s // s ∉ S} → T) := by
    rintro ⟨⟨s', hs'⟩, rfl⟩
    exact hs' hs
  rw [coordKill, killCompl, aeval_X, dif_neg this]

/-- `coordKill S` keeps the variables outside `S`. -/
theorem coordKill_X_of_notMem {S : Set T} {s : T} (hs : s ∉ S) :
    coordKill (B := B) S (X s) = X ⟨s, hs⟩ := by
  have := killCompl_rename_app (R := B) (Subtype.val_injective (p := fun s ↦ s ∉ S))
    (X ⟨s, hs⟩)
  rwa [rename_X] at this

/-- `coordKill S` is surjective (a section is `rename Subtype.val`). -/
theorem coordKill_surjective (S : Set T) : Function.Surjective (coordKill (B := B) S) :=
  fun p ↦ ⟨rename Subtype.val p, killCompl_rename_app _ p⟩

/-- The kernel of `coordKill S` is the coordinate prime of `S`. -/
theorem ker_coordKill (S : Set T) : RingHom.ker (coordKill (B := B) S) = coordPrime S := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    rw [coordPrime, mem_ideal_span_X_image]
    intro m hm
    by_contra! hcon
    have hsub : ↑m.support ⊆ Set.range (Subtype.val : {s // s ∉ S} → T) := by
      intro i hi
      refine ⟨⟨i, fun hiS ↦ ?_⟩, rfl⟩
      exact (Finsupp.mem_support_iff.1 hi) (hcon i hiS)
    have hc := coeff_killCompl (R := B) (Subtype.val_injective (p := fun s ↦ s ∉ S))
      (p := p) (s := m.comapDomain Subtype.val Subtype.val_injective.injOn)
    rw [Finsupp.mapDomain_comapDomain _ Subtype.val_injective _ hsub] at hc
    change (coordKill S p).coeff _ = _ at hc
    rw [hp, coeff_zero] at hc
    exact (mem_support_iff.1 hm) hc.symm
  · rw [coordPrime, Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    exact coordKill_X_of_mem hs

/-- **The coordinate prime is prime** (over a domain). -/
theorem coordPrime_isPrime [IsDomain B] (S : Set T) : (coordPrime (B := B) S).IsPrime := by
  rw [← ker_coordKill]
  exact RingHom.ker_isPrime _

/-- **The quotient by a coordinate prime**: `B[X_t : t ∈ T] ⧸ coordPrime S ≃+*
B[X_t : t ∉ S]`, induced by `coordKill S`. -/
noncomputable def quotientCoordPrimeEquiv (S : Set T) :
    MvPolynomial T B ⧸ coordPrime (B := B) S ≃+* MvPolynomial {s // s ∉ S} B :=
  (Ideal.quotEquivOfEq (ker_coordKill S).symm).trans
    (RingHom.quotientKerEquivOfSurjective (coordKill_surjective S))

/-- `quotientCoordPrimeEquiv` on classes is `coordKill`. -/
theorem quotientCoordPrimeEquiv_mk (S : Set T) (p : MvPolynomial T B) :
    quotientCoordPrimeEquiv S (Ideal.Quotient.mk _ p) = coordKill S p := rfl

/-- The variables indexed by `S` lie in `coordPrime S`. -/
theorem X_mem_coordPrime {S : Set T} {s : T} (hs : s ∈ S) :
    (X s : MvPolynomial T B) ∈ coordPrime S :=
  Ideal.subset_span ⟨s, hs, rfl⟩

/-- The variables not indexed by `S` do not lie in `coordPrime S`. -/
theorem X_notMem_coordPrime [Nontrivial B] {S : Set T} {t : T} (ht : t ∉ S) :
    (X t : MvPolynomial T B) ∉ coordPrime S := by
  rw [← ker_coordKill, RingHom.mem_ker, coordKill_X_of_notMem ht]
  exact X_ne_zero _

/-- `coordPrime` is monotone. -/
theorem coordPrime_mono {S S' : Set T} (h : S ⊆ S') :
    coordPrime (B := B) S ≤ coordPrime S' :=
  Ideal.span_mono (Set.image_mono h)

/-- `coordPrime (insert t S) = (X t) + coordPrime S`. -/
theorem coordPrime_insert (S : Set T) (t : T) :
    coordPrime (B := B) (insert t S) = Ideal.span {X t} ⊔ coordPrime S := by
  rw [coordPrime, Set.image_insert_eq, Ideal.span_insert, coordPrime]

/-- For `t ∉ S`, `coordPrime S < coordPrime (insert t S)`. -/
theorem coordPrime_lt_insert [Nontrivial B] {S : Set T} {t : T} (ht : t ∉ S) :
    coordPrime (B := B) S < coordPrime (insert t S) :=
  lt_of_le_of_ne (coordPrime_mono (Set.subset_insert t S)) fun he ↦
    X_notMem_coordPrime (B := B) ht (he ▸ X_mem_coordPrime (Set.mem_insert t S))

/-- **The coordinate prime of one variable has height one** (`B` a Noetherian domain, `T`
finite): it is the principal ideal generated by the nonzero non-unit `X t` (Krull's principal
ideal theorem). -/
theorem height_coordPrime_single [IsDomain B] [IsNoetherianRing B] [Finite T] (t : T) :
    (coordPrime (B := B) {t}).height = 1 := by
  rw [coordPrime, Set.image_singleton]
  refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero t)) fun hu ↦ ?_
  have := hu.map (MvPolynomial.constantCoeff (R := B) (σ := T))
  simp at this

/-- **No prime lies strictly between `coordPrime S` and `coordPrime (insert t S)`** (`B` a
Noetherian domain, `T` finite, `t ∉ S`).  Proof: if `X t ∉ 𝔯`, every element of `𝔯` is, modulo
`coordPrime S`, divisible by every power of `X t`, hence lies in `coordPrime S` by Krull's
intersection theorem in `B[X_t : t ∉ S]`. -/
theorem coordPrime_eq_or_eq_of_le [IsDomain B] [IsNoetherianRing B] [Finite T]
    {S : Set T} {t : T} (ht : t ∉ S) (𝔯 : Ideal (MvPolynomial T B)) [𝔯.IsPrime]
    (h1 : coordPrime S ≤ 𝔯) (h2 : 𝔯 ≤ coordPrime (insert t S)) :
    𝔯 = coordPrime S ∨ 𝔯 = coordPrime (insert t S) := by
  by_cases hX : (X t : MvPolynomial T B) ∈ 𝔯
  · right
    refine le_antisymm h2 ?_
    rw [coordPrime_insert, sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    exact ⟨hX, h1⟩
  · left
    refine le_antisymm (fun g hg ↦ ?_) h1
    have key : ∀ n : ℕ, ∀ g ∈ 𝔯, ∃ a ∈ 𝔯, g - X t ^ n * a ∈ coordPrime (B := B) S := by
      intro n
      induction n with
      | zero => exact fun g hg ↦ ⟨g, hg, by simp⟩
      | succ n ih =>
        intro g hg
        obtain ⟨a, ha, hga⟩ := ih g hg
        have ha' := h2 ha
        rw [coordPrime_insert, Submodule.mem_sup] at ha'
        obtain ⟨y, hy, p, hp, hyp⟩ := ha'
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        have hb : b * X t ∈ 𝔯 := by
          have : b * X t = a - p := by rw [← hyp]; ring
          rw [this]
          exact 𝔯.sub_mem ha (h1 hp)
        refine ⟨b, (Ideal.IsPrime.mem_or_mem ‹_› hb).resolve_right hX, ?_⟩
        have : g - X t ^ (n + 1) * b = (g - X t ^ n * a) + X t ^ n * p := by
          rw [← hyp]; ring
        rw [this]
        exact (coordPrime S).add_mem hga (Ideal.mul_mem_left _ _ hp)
    rw [← ker_coordKill, RingHom.mem_ker]
    have hne : Ideal.span {(X ⟨t, ht⟩ : MvPolynomial {s // s ∉ S} B)} ≠ ⊤ := by
      intro htop
      have hu := Ideal.span_singleton_eq_top.1 htop
      have := hu.map (MvPolynomial.constantCoeff (R := B) (σ := {s // s ∉ S}))
      simp at this
    rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Submodule.mem_iInf]
    intro n
    obtain ⟨a, -, hga⟩ := key n g hg
    rw [← ker_coordKill, RingHom.mem_ker, map_sub, map_mul, map_pow,
      coordKill_X_of_notMem ht, sub_eq_zero] at hga
    rw [hga, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

end CoordPrime

/-! ## Germs of ring elements on `Spec R` -/

section SpecGerm

variable {R : CommRingCat.{u}}

/-- The germ at `x` of `c : R`, viewed as a global section of `Spec R`. -/
noncomputable def specGerm (x : ↥(Spec R)) : R →+* (Spec R).presheaf.stalk x :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial).hom

set_option backward.isDefEq.respectTransparency false in
/-- `specGerm` through the isomorphism of the stalk with the localisation. -/
theorem specGerm_eq_stalkIso (x : ↥(Spec R)) (c : R) :
    specGerm x c = (Spec.stalkIso R x).inv (algebraMap R (Localization.AtPrime x.asIdeal) c) :=
  (ConcreteCategory.congr_hom (Spec.algebraMap_stalkIso_inv x) c).symm

/-- The stalk of `Spec R` at `x` as the localisation, as a ring isomorphism. -/
noncomputable def specStalkEquiv (x : ↥(Spec R)) :
    Localization.AtPrime x.asIdeal ≃+* (Spec R).presheaf.stalk x :=
  (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- `specGerm` is the localisation map followed by `specStalkEquiv`. -/
theorem specGerm_eq_comp (x : ↥(Spec R)) :
    specGerm x = (specStalkEquiv x).toRingHom.comp
      (algebraMap R (Localization.AtPrime x.asIdeal)) := by
  ext c
  exact specGerm_eq_stalkIso x c

set_option backward.isDefEq.respectTransparency false in
/-- The germ of `c` at `x` is a unit iff `c ∉ x`. -/
theorem isUnit_specGerm_iff (x : ↥(Spec R)) (c : R) :
    IsUnit (specGerm x c) ↔ c ∉ x.asIdeal := by
  rw [specGerm_eq_comp, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    isUnit_map_iff (specStalkEquiv x), IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime x.asIdeal) x.asIdeal, Ideal.mem_primeCompl_iff]

/-- The germ of `c` at `x` lies in the maximal ideal iff `c ∈ x`. -/
theorem specGerm_mem_maximalIdeal_iff (x : ↥(Spec R)) (c : R) :
    specGerm x c ∈ maximalIdeal _ ↔ c ∈ x.asIdeal := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_specGerm_iff, not_not]

/-- The residue of the germ of `c` at `x` vanishes iff `c ∈ x`. -/
theorem residue_specGerm_eq_zero_iff (x : ↥(Spec R)) (c : R) :
    (Spec R).residue x (specGerm x c) = 0 ↔ c ∈ x.asIdeal := by
  change IsLocalRing.residue _ (specGerm x c) = 0 ↔ _
  rw [residue_eq_zero_iff, specGerm_mem_maximalIdeal_iff]

set_option backward.isDefEq.respectTransparency false in
/-- The residue class at `x` of an element `c ∉ x` of `R`, as a unit of `κ(x)`. -/
noncomputable def specGermResidueUnit (x : ↥(Spec R)) (c : R) (hc : c ∉ x.asIdeal) :
    ((Spec R).residueField x)ˣ :=
  (isUnit_iff_ne_zero.2 fun h0 ↦ hc ((residue_specGerm_eq_zero_iff x c).1 h0)).unit

/-- The value of `specGermResidueUnit`. -/
theorem specGermResidueUnit_val (x : ↥(Spec R)) (c : R) (hc : c ∉ x.asIdeal) :
    (specGermResidueUnit x c hc : (Spec R).residueField x) = (Spec R).residue x (specGerm x c) :=
  IsUnit.unit_spec _

/-- `specGerm` is compatible with specialisation maps of stalks. -/
theorem stalkSpecializes_specGerm {x y : ↥(Spec R)} (h : x ⤳ y) (c : R) :
    (Spec R).presheaf.stalkSpecializes h (specGerm y c) = specGerm x c :=
  TopCat.Presheaf.germ_stalkSpecializes_apply _ _ h _

set_option backward.isDefEq.respectTransparency false in
/-- The maximal ideal of the stalk of `Spec R` at `x` is generated by the germs of `x`. -/
theorem maximalIdeal_stalk_eq_map_specGerm (x : ↥(Spec R)) :
    maximalIdeal ((Spec R).presheaf.stalk x) = x.asIdeal.map (specGerm x) := by
  rw [← map_ringEquiv_maximalIdeal (specStalkEquiv x),
    ← IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal (Localization.AtPrime x.asIdeal),
    specGerm_eq_comp, ← Ideal.map_map]
  rfl

end SpecGerm

/-! ## Orders of coordinate functions -/

section CoordPrimeSpec

open MvPolynomial HomogeneityLocal

set_option backward.isDefEq.respectTransparency false in
/-- Specialisation of points of `Spec R` is inclusion of primes. -/
theorem specializes_iff_asIdeal_le {R : CommRingCat.{u}} {x y : ↥(Spec R)} :
    x ⤳ y ↔ x.asIdeal ≤ y.asIdeal :=
  (PrimeSpectrum.le_iff_specializes x y).symm

variable {T B : Type u} [CommRing B] [IsDomain B]

/-- The point of `Spec B[X_t : t ∈ T]` given by the coordinate prime `coordPrime S`. -/
noncomputable def coordPrimePt (S : Set T) : ↥(Spec (CommRingCat.of (MvPolynomial T B))) :=
  ⟨coordPrime S, coordPrime_isPrime S⟩

/-- The prime of `coordPrimePt S` is `coordPrime S`. -/
@[simp]
theorem coordPrimePt_asIdeal (S : Set T) :
    (coordPrimePt (B := B) S).asIdeal = coordPrime S := rfl

/-- `coordPrimePt S` specialises to `q` iff `coordPrime S ⊆ q`. -/
theorem coordPrimePt_specializes_iff (S : Set T)
    (q : ↥(Spec (CommRingCat.of (MvPolynomial T B)))) :
    coordPrimePt S ⤳ q ↔ coordPrime S ≤ q.asIdeal :=
  specializes_iff_asIdeal_le

/-- **`coordPrimePt (insert t S)` is covered by `coordPrimePt S`** in the specialisation order
of `Spec B[X_t]` (`B` a Noetherian domain, `T` finite, `t ∉ S`). -/
theorem coordPrimePt_covBy [IsNoetherianRing B] [Finite T] {S : Set T} {t : T} (ht : t ∉ S) :
    coordPrimePt (B := B) (insert t S) ⋖ coordPrimePt S := by
  have hle : coordPrimePt (B := B) (insert t S) ≤ coordPrimePt S :=
    le_iff_specializes.2 ((coordPrimePt_specializes_iff _ _).2
      (coordPrime_mono (Set.subset_insert t S)))
  have hne : coordPrimePt (B := B) (insert t S) ≠ coordPrimePt S := fun he ↦
    (coordPrime_lt_insert (B := B) ht).ne (congrArg PrimeSpectrum.asIdeal he).symm
  refine ⟨lt_of_le_not_ge hle fun hge ↦ hne ?_, fun z hz1 hz2 ↦ ?_⟩
  · exact PrimeSpectrum.ext (le_antisymm (specializes_iff_asIdeal_le.1 (le_iff_specializes.1 hge))
      (specializes_iff_asIdeal_le.1 (le_iff_specializes.1 hle)))
  have h1 : coordPrime S ≤ z.asIdeal :=
    (coordPrimePt_specializes_iff _ _).1 (le_iff_specializes.1 hz2.le)
  have h2 : z.asIdeal ≤ coordPrime (insert t S) :=
    specializes_iff_asIdeal_le.1 (le_iff_specializes.1 hz1.le)
  rcases coordPrime_eq_or_eq_of_le ht z.asIdeal h1 h2 with e | e
  · exact hz2.ne (PrimeSpectrum.ext e)
  · exact hz1.ne' (PrimeSpectrum.ext e)

open scoped Classical in
/-- **Orders of a coordinate function on `Spec B[X_t]`.**  Let `B` be a Noetherian domain, `T`
finite, `t ∉ S`, and `q` a specialisation of `coordPrimePt S`.  The order along
`coordPrimePt S ⤳ q` of the residue class of `X t` at `coordPrimePt S` is `1` if
`q = coordPrimePt (insert t S)` and `0` otherwise. -/
theorem pointOrd_coordPrime_spec [IsNoetherianRing B] [Finite T] {S : Set T} {t : T}
    (ht : t ∉ S) (q : ↥(Spec (CommRingCat.of (MvPolynomial T B))))
    (h : coordPrimePt S ⤳ q)
    (u : ((Spec (CommRingCat.of (MvPolynomial T B))).residueField (coordPrimePt S))ˣ)
    (hu : (u : (Spec (CommRingCat.of (MvPolynomial T B))).residueField (coordPrimePt S)) =
      (Spec (CommRingCat.of (MvPolynomial T B))).residue _
        (specGerm (coordPrimePt S) (X t))) :
    pointOrd h u = if q = coordPrimePt (insert t S) then 1 else 0 := by
  have hu' : (u : (Spec (CommRingCat.of (MvPolynomial T B))).residueField (coordPrimePt S)) =
      pointStalkMap h (specGerm q (X t)) := by
    rw [hu, pointStalkMap_apply, stalkSpecializes_specGerm]
  have hker : ∀ c : MvPolynomial T B, c ∈ coordPrime S →
      specGerm q c ∈ RingHom.ker (pointStalkMap h) := by
    intro c hc
    rw [RingHom.mem_ker, pointStalkMap_apply, stalkSpecializes_specGerm,
      residue_specGerm_eq_zero_iff]
    exact hc
  have hPq : coordPrime S ≤ q.asIdeal := (coordPrimePt_specializes_iff S q).1 h
  split_ifs with hq
  · subst hq
    have hd : ringKrullDim (pointStalk h) = 1 :=
      (ringKrullDim_pointStalk_eq_one_iff_covBy h).2 (coordPrimePt_covBy ht)
    refine ZeroSectionCartier.pointOrd_eq_one_of_maximalIdeal_eq_span h hd _ ?_ u hu'
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
      maximalIdeal_stalk_eq_map_specGerm, Ideal.map_map]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, coordPrimePt_asIdeal, coordPrime, Ideal.span_le]
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      rcases hs with rfl | hs
      · exact Ideal.subset_span rfl
      · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (hker _ (X_mem_coordPrime hs))]
        exact zero_mem _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (X_mem_coordPrime (Set.mem_insert t S))
  · by_cases hd : ringKrullDim (pointStalk h) = 1
    · have hXq : (X t : MvPolynomial T B) ∉ q.asIdeal := by
        intro hX
        have hcov := (ringKrullDim_pointStalk_eq_one_iff_covBy h).1 hd
        have hQq : coordPrime (insert t S) ≤ q.asIdeal := by
          rw [coordPrime_insert, sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
          exact ⟨hX, hPq⟩
        refine hcov.2 (c := coordPrimePt (insert t S))
          (lt_of_le_not_ge (le_iff_specializes.2 ((coordPrimePt_specializes_iff _ _).2 hQq))
            fun hge ↦ hq (PrimeSpectrum.ext (le_antisymm
              (specializes_iff_asIdeal_le.1 (le_iff_specializes.1 hge)) hQq)))
          (coordPrimePt_covBy ht).1
      have hunit : IsUnit (Ideal.Quotient.mk (RingHom.ker (pointStalkMap h))
          (specGerm q (X t))) :=
        ((isUnit_specGerm_iff q _).2 hXq).map _
      have := krullDimLE_one_pointStalk_of_eq_one hd
      have h1 := pointOrd_of_eq_one hd u
      rw [hu', ← pointStalk_algebraMap_mk, Ring.ordFrac_of_isUnit hunit] at h1
      have h2 : Multiplicative.ofAdd (pointOrd h u) = 1 :=
        WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
      simpa using h2
    · exact pointOrd_of_ne_one hd u

open scoped Classical in
/-- **Orders of coordinate functions in an affine chart** (blueprint B3).  Let
`ψ : Spec B[X_t : t ∈ T] ⟶ Y` be a preimmersion, e.g. an open immersion, or a closed immersion
followed by an open immersion (`B` a Noetherian domain, `T` finite), `t ∉ S`,
and `q` a point of the chart with `ψ (coordPrimePt S) ⤳ ψ q`.  If `u` is a unit of
`κ(ψ (coordPrimePt S))` whose image under `residueFieldMap` is the residue class of `X t`, then
`pointOrd (ψ (coordPrimePt S) ⤳ ψ q) u` is `1` if `q = coordPrimePt (insert t S)` and `0`
otherwise. -/
theorem pointOrd_coordPrime {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNoetherianRing B]
    [Finite T] (ψ : Spec (CommRingCat.of (MvPolynomial T B)) ⟶ Y) [IsPreimmersion ψ]
    {S : Set T} {t : T} (ht : t ∉ S) (q : ↥(Spec (CommRingCat.of (MvPolynomial T B))))
    (h : ψ (coordPrimePt S) ⤳ ψ q) (u : (Y.residueField (ψ (coordPrimePt S)))ˣ)
    (hu : ψ.residueFieldMap (coordPrimePt S) u =
      (Spec (CommRingCat.of (MvPolynomial T B))).residue _
        (specGerm (coordPrimePt S) (X t))) :
    pointOrd h u = if q = coordPrimePt (insert t S) then 1 else 0 := by
  have h' : coordPrimePt S ⤳ q := ψ.isEmbedding.isInducing.specializes_iff.1 h
  rw [pointOrd_preimmersion ψ h' h u]
  exact pointOrd_coordPrime_spec ht q h' _ hu

/-- The residue unit of `X t` at `ψ (coordPrimePt S)` (`t ∉ S`), for a preimmersion
`ψ : Spec B[X_t] ⟶ Y`: the preimage under the residue field isomorphism
`κ(ψ (coordPrimePt S)) ≃ κ(coordPrimePt S)` of the residue class of `X t`. -/
noncomputable def coordPrimeResidueUnit {Y : Scheme.{u}}
    (ψ : Spec (CommRingCat.of (MvPolynomial T B)) ⟶ Y) [IsPreimmersion ψ] (S : Set T) (t : T)
    (ht : t ∉ S) : (Y.residueField (ψ (coordPrimePt S)))ˣ :=
  Units.map (residueFieldEquivOfSurjective ψ (ψ.stalkMap_surjective _)).symm.toMonoidHom
    (specGermResidueUnit (coordPrimePt S) (X t) (X_notMem_coordPrime ht))

/-- `coordPrimeResidueUnit` satisfies the hypothesis `hu` of `pointOrd_coordPrime`. -/
theorem residueFieldMap_coordPrimeResidueUnit {Y : Scheme.{u}}
    (ψ : Spec (CommRingCat.of (MvPolynomial T B)) ⟶ Y) [IsPreimmersion ψ] (S : Set T) (t : T)
    (ht : t ∉ S) :
    ψ.residueFieldMap (coordPrimePt S) (coordPrimeResidueUnit ψ S t ht) =
      (Spec (CommRingCat.of (MvPolynomial T B))).residue _
        (specGerm (coordPrimePt S) (X t)) := by
  rw [← specGermResidueUnit_val (coordPrimePt S) (X t) (X_notMem_coordPrime ht),
    ← residueFieldEquivOfSurjective_apply ψ (ψ.stalkMap_surjective _)]
  exact RingEquiv.apply_symm_apply _ _

open scoped Classical in
/-- **Orders of coordinate functions in an affine chart**, with the residue unit packaged:
`pointOrd (ψ (coordPrimePt S) ⤳ ψ q) (coordPrimeResidueUnit ψ S t ht)` is `1` if
`q = coordPrimePt (insert t S)` and `0` otherwise (`ψ` a preimmersion, `B` a Noetherian domain,
`T` finite, `t ∉ S`). -/
theorem pointOrd_coordPrime' {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNoetherianRing B]
    [Finite T] (ψ : Spec (CommRingCat.of (MvPolynomial T B)) ⟶ Y) [IsPreimmersion ψ]
    {S : Set T} {t : T} (ht : t ∉ S) (q : ↥(Spec (CommRingCat.of (MvPolynomial T B))))
    (h : ψ (coordPrimePt S) ⤳ ψ q) :
    pointOrd h (coordPrimeResidueUnit ψ S t ht) =
      if q = coordPrimePt (insert t S) then 1 else 0 :=
  pointOrd_coordPrime ψ ht q h _ (residueFieldMap_coordPrimeResidueUnit ψ S t ht)

/-- **Covering pairs of coordinate points** (blueprint B5).  For a preimmersion (e.g. an open
immersion, or a closed immersion followed by an open immersion) `ψ : Spec B[X_t : t ∈ T] ⟶ Y`
(`B` a Noetherian domain, `T` finite), `t ∉ S`, and a dimension function `dim` on `Y` satisfying
`CovByDimension`,
`dim (ψ (coordPrimePt (insert t S))) = dim (ψ (coordPrimePt S)) - 1`. -/
theorem dim_coordPrime_insert {Y : Scheme.{u}} [IsNoetherianRing B] [Finite T]
    (ψ : Spec (CommRingCat.of (MvPolynomial T B)) ⟶ Y) [IsPreimmersion ψ]
    (dim : DimensionFunction Y) (hcov : CovByDimension dim) {S : Set T} {t : T}
    (ht : t ∉ S) :
    dim (ψ (coordPrimePt (insert t S))) = dim (ψ (coordPrimePt S)) - 1 := by
  have h' : coordPrimePt (B := B) S ⤳ coordPrimePt (insert t S) :=
    (coordPrimePt_specializes_iff _ _).2 (coordPrime_mono (Set.subset_insert t S))
  have h : ψ (coordPrimePt S) ⤳ ψ (coordPrimePt (insert t S)) := h'.map ψ.continuous
  have hd' : ringKrullDim (pointStalk h') = 1 :=
    (ringKrullDim_pointStalk_eq_one_iff_covBy h').2 (coordPrimePt_covBy ht)
  have hd : ringKrullDim (pointStalk h) = 1 :=
    (ringKrullDim_eq_of_ringEquiv
      (pointStalkEquivOfSurjective ψ h' h (ψ.stalkMap_surjective _))).trans hd'
  rw [ringKrullDim_pointStalk dim hcov h] at hd
  have hle := dimensionFunction_le_of_specializes dim h
  have : (dim (ψ (coordPrimePt S)) - dim (ψ (coordPrimePt (insert t S)))).toNat = 1 := by
    exact_mod_cast hd
  omega

end CoordPrimeSpec

/-! ## Point stalks in an affine chart -/

section Chart

variable {R : CommRingCat.{u}} {x y : ↥(Spec R)}

set_option backward.isDefEq.respectTransparency false in
/-- For `x ⤳ y` in `Spec R`, the prime `y / x` of the domain `R ⧸ x`. -/
noncomputable def chartQuotPrime (hxy : x ⤳ y) : PrimeSpectrum (R ⧸ x.asIdeal) :=
  ⟨y.asIdeal.map (Ideal.Quotient.mk x.asIdeal),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact specializes_iff_asIdeal_le.1 hxy)⟩

set_option backward.isDefEq.respectTransparency false in
/-- An element of `R` lies in `y` iff its class lies in `chartQuotPrime hxy`. -/
theorem mk_mem_chartQuotPrime_iff (hxy : x ⤳ y) (c : R) :
    Ideal.Quotient.mk x.asIdeal c ∈ (chartQuotPrime hxy).asIdeal ↔ c ∈ y.asIdeal := by
  refine ⟨fun hc ↦ ?_, fun hc ↦ Ideal.mem_map_of_mem _ hc⟩
  change _ ∈ y.asIdeal.map (Ideal.Quotient.mk x.asIdeal) at hc
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hc
  obtain ⟨d, hd, hdc⟩ := hc
  rw [Ideal.Quotient.eq] at hdc
  have := y.asIdeal.sub_mem hd (specializes_iff_asIdeal_le.1 hxy hdc)
  simpa using this

set_option backward.isDefEq.respectTransparency false in
/-- The germ map `R → 𝒪_{Spec R, y}` kills `x` modulo the kernel of `pointStalkMap`. -/
theorem specGerm_mem_ker_pointStalkMap_iff (hxy : x ⤳ y) (c : R) :
    specGerm y c ∈ RingHom.ker (pointStalkMap hxy) ↔ c ∈ x.asIdeal := by
  rw [RingHom.mem_ker, pointStalkMap_apply, stalkSpecializes_specGerm,
    residue_specGerm_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
/-- The ring map `R ⧸ x → pointStalk (x ⤳ y)` induced by the germs at `y`. -/
noncomputable def chartQuotToPointStalk (hxy : x ⤳ y) : R ⧸ x.asIdeal →+* pointStalk hxy :=
  Ideal.Quotient.lift x.asIdeal ((Ideal.Quotient.mk _).comp (specGerm y)) fun c hc ↦
    Ideal.Quotient.eq_zero_iff_mem.2 ((specGerm_mem_ker_pointStalkMap_iff hxy c).2 hc)

/-- `chartQuotToPointStalk` on classes. -/
theorem chartQuotToPointStalk_mk (hxy : x ⤳ y) (c : R) :
    chartQuotToPointStalk hxy (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (specGerm y c) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The point stalk of `x ⤳ y` in `Spec R` is the localisation of `R ⧸ x` at `y / x`.** -/
theorem isLocalization_chartQuotToPointStalk (hxy : x ⤳ y) :
    letI := (chartQuotToPointStalk hxy).toAlgebra
    IsLocalization.AtPrime (pointStalk hxy) (chartQuotPrime hxy).asIdeal := by
  let _ := (chartQuotToPointStalk hxy).toAlgebra
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨m, hm⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hc : c ∉ y.asIdeal := fun hc ↦ hm ((mk_mem_chartQuotPrime_iff hxy c).2 hc)
    exact ((isUnit_specGerm_iff y c).2 hc).map (Ideal.Quotient.mk _)
  · intro z
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨l, rfl⟩ := (specStalkEquiv y).surjective s
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj y.asIdeal.primeCompl l
    have hb : Ideal.Quotient.mk x.asIdeal b ∉ (chartQuotPrime hxy).asIdeal :=
      fun h ↦ b.2 ((mk_mem_chartQuotPrime_iff hxy b).1 h)
    refine ⟨⟨Ideal.Quotient.mk _ a, ⟨_, hb⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ (specGerm y b) =
      Ideal.Quotient.mk _ (specGerm y a)
    rw [← map_mul]
    refine congrArg (Ideal.Quotient.mk _) ?_
    rw [specGerm_eq_stalkIso, specGerm_eq_stalkIso]
    exact (map_mul (specStalkEquiv y) _ _).symm.trans (congrArg (specStalkEquiv y) hab)
  · intro a b hab
    refine ⟨1, ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change Ideal.Quotient.mk _ (specGerm y a) = Ideal.Quotient.mk _ (specGerm y b) at hab
    rw [Ideal.Quotient.eq, ← map_sub, specGerm_mem_ker_pointStalkMap_iff] at hab
    exact congrArg (_ * ·) (Ideal.Quotient.eq.2 hab)

/-- The point stalk of `x ⤳ y` in `Spec R` as the localisation `(R ⧸ x)_{y / x}`. -/
noncomputable def specPointStalkEquiv (hxy : x ⤳ y) :
    pointStalk hxy ≃+* Localization.AtPrime (chartQuotPrime hxy).asIdeal :=
  letI := (chartQuotToPointStalk hxy).toAlgebra
  haveI := isLocalization_chartQuotToPointStalk hxy
  (IsLocalization.algEquiv (chartQuotPrime hxy).asIdeal.primeCompl (pointStalk hxy)
    (Localization.AtPrime (chartQuotPrime hxy).asIdeal)).toRingEquiv

/-- `specPointStalkEquiv` on germs: the germ of `c` goes to the class of `c`. -/
theorem specPointStalkEquiv_mk_specGerm (hxy : x ⤳ y) (c : R) :
    specPointStalkEquiv hxy (Ideal.Quotient.mk _ (specGerm y c)) =
      algebraMap (R ⧸ x.asIdeal) _ (Ideal.Quotient.mk _ c) := by
  let _ := (chartQuotToPointStalk hxy).toAlgebra
  have := isLocalization_chartQuotToPointStalk hxy
  exact (IsLocalization.algEquiv (chartQuotPrime hxy).asIdeal.primeCompl (pointStalk hxy)
    (Localization.AtPrime (chartQuotPrime hxy).asIdeal)).commutes (Ideal.Quotient.mk _ c)

set_option backward.isDefEq.respectTransparency false in
/-- Residues of sections pulled back to an affine chart: if `ψ : Spec R ⟶ Y`, `V` is an open of
`Y` containing `ψ x`, and the pullback of `g ∈ Γ(Y, V)` along `ψ` is the restriction of the
global function `c ∈ R`, then `residueFieldMap` sends the residue of `g` at `ψ x` to the residue
of `c` at `x`.  (This is the form of the hypothesis `hu` of `pointOrd_chart` and
`pointOrd_coordPrime`.) -/
theorem residueFieldMap_residue_germ {Y : Scheme.{u}} (ψ : Spec R ⟶ Y) (V : Y.Opens)
    (hx : ψ x ∈ V) (g : Γ(Y, V)) (c : R)
    (hg : ψ.app V g = (Spec R).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso R).inv c)) :
    ψ.residueFieldMap x (Y.residue (ψ x) (Y.presheaf.germ V (ψ x) hx g)) =
      (Spec R).residue x (specGerm x c) := by
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply,
    Scheme.Hom.germ_stalkMap_apply, hg, TopCat.Presheaf.germ_res_apply]
  rfl

variable {Y : Scheme.{u}} (ψ : Spec R ⟶ Y) [IsOpenImmersion ψ]

/-- **`pointStalk` in an affine chart** (blueprint B1).  For an open immersion
`ψ : Spec R ⟶ Y` and `x ⤳ y` in `Spec R`, the point stalk of `ψ x ⤳ ψ y` is the localisation
of the domain `R ⧸ x` at the prime `y / x`; it sends the class of the germ of `c` at `ψ y`
(pulled back along `ψ`) to the class of `c` (`pointStalkChartEquiv_mk`). -/
noncomputable def pointStalkChartEquiv (hxy : x ⤳ y) (h : ψ x ⤳ ψ y) :
    pointStalk h ≃+* Localization.AtPrime (chartQuotPrime hxy).asIdeal :=
  (pointStalkEquivOfSurjective ψ hxy h (ψ.stalkMap_surjective y)).trans
    (specPointStalkEquiv hxy)

/-- `pointStalkChartEquiv` on classes whose stalk image is a germ. -/
theorem pointStalkChartEquiv_mk (hxy : x ⤳ y) (h : ψ x ⤳ ψ y)
    (t : Y.presheaf.stalk (ψ y)) (c : R) (ht : ψ.stalkMap y t = specGerm y c) :
    pointStalkChartEquiv ψ hxy h (Ideal.Quotient.mk _ t) =
      algebraMap (R ⧸ x.asIdeal) _ (Ideal.Quotient.mk _ c) := by
  rw [pointStalkChartEquiv, RingEquiv.trans_apply, pointStalkEquivOfSurjective_mk, ht,
    specPointStalkEquiv_mk_specGerm]

set_option backward.isDefEq.respectTransparency false in
/-- **Orders of residue units in an affine chart, Krull dimension one** (blueprint B1').  For
an open immersion `ψ : Spec R ⟶ Y` (`R` Noetherian, `Y` locally Noetherian), `x ⤳ y` in
`Spec R`, `c : R` and a unit `u` of `κ(ψ x)` whose image under `residueFieldMap` is the residue
class of `c`: if the localisation `(R ⧸ x)_{y / x}` has Krull dimension one, then
`pointOrd (ψ x ⤳ ψ y) u` is the order of the class of `c` in that ring. -/
theorem pointOrd_chart [IsLocallyNoetherian Y] [IsNoetherianRing R] (hxy : x ⤳ y)
    (h : ψ x ⤳ ψ y) (c : R) (u : (Y.residueField (ψ x))ˣ)
    (hu : ψ.residueFieldMap x u = (Spec R).residue x (specGerm x c))
    (hd : ringKrullDim (Localization.AtPrime (chartQuotPrime hxy).asIdeal) = 1)
    [Ring.KrullDimLE 1 (Localization.AtPrime (chartQuotPrime hxy).asIdeal)] :
    ((Multiplicative.ofAdd (pointOrd h u) : Multiplicative ℤ) : ℤᵐ⁰) =
      Ring.ordMonoidWithZeroHom (Localization.AtPrime (chartQuotPrime hxy).asIdeal)
        (algebraMap (R ⧸ x.asIdeal) _ (Ideal.Quotient.mk _ c)) := by
  rw [pointOrd_openImmersion ψ hxy h u]
  set u' := Units.map (ψ.residueFieldMap x).hom.toMonoidHom u
  have hu' : (u' : (Spec R).residueField x) =
      algebraMap (pointStalk hxy) _ (Ideal.Quotient.mk _ (specGerm y c)) := by
    rw [pointStalk_algebraMap_mk, pointStalkMap_apply, stalkSpecializes_specGerm, ← hu]
    rfl
  have hd' : ringKrullDim (pointStalk hxy) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (specPointStalkEquiv hxy)).trans hd
  have := krullDimLE_one_pointStalk_of_eq_one hd'
  have hne : (Ideal.Quotient.mk (RingHom.ker (pointStalkMap hxy)) (specGerm y c)) ≠ 0 := by
    intro h0
    apply u'.ne_zero
    rw [hu', h0, map_zero]
  rw [pointOrd_of_eq_one hd', hu', Ring.ordFrac_eq_ord _ hne,
    ← ordMonoidWithZeroHom_ringEquiv (specPointStalkEquiv hxy),
    specPointStalkEquiv_mk_specGerm]

/-- **Orders of residue units in an affine chart, junk case** (blueprint B1').  If the
localisation `(R ⧸ x)_{y / x}` does not have Krull dimension one, then `pointOrd (ψ x ⤳ ψ y)`
vanishes identically. -/
theorem pointOrd_chart_of_ne_one [IsLocallyNoetherian Y] (hxy : x ⤳ y) (h : ψ x ⤳ ψ y)
    (hd : ringKrullDim (Localization.AtPrime (chartQuotPrime hxy).asIdeal) ≠ 1)
    (u : (Y.residueField (ψ x))ˣ) : pointOrd h u = 0 :=
  pointOrd_of_ne_one (fun h1 ↦ hd ((ringKrullDim_eq_of_ringEquiv
    (pointStalkChartEquiv ψ hxy h)).symm.trans h1)) u

end Chart

end GromovWitten.AlgebraicGeometry.IntersectionTheory
