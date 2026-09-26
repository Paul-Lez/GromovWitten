/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChowGroup
import GromovWitten.AlgebraicGeometry.IntersectionTheory.HomogeneityLocal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundleHomotopyRankOne
import GromovWitten.AlgebraicGeometry.IntersectionTheory.GeneratorInvariance
import GromovWitten.AlgebraicGeometry.Curves.CartierDivisors

/-!
# The cycle-level Gysin operation of a principal Cartier divisor

For `X = Spec R` and an equation `f : R`, this file constructs the cycle operation associated to
the closed immersion `Spec (R ⧸ (f)) → Spec R`.  A component whose generic point contains `f`
contributes zero; otherwise its contribution is the divisor of `f` on that component, read on the
closed subscheme `f = 0`.  The construction is pointwise and therefore does not hide a carrier or
a divisor map in a structure field.

For a regular equation, `effectiveCartierDivisor` constructs the associated effective Cartier
divisor. The cycle formula itself is defined for every equation.

The support theorem is unconditional: a nonzero coefficient lies at a prime minimal above the
component and the equation, with an explicit height-one quotient statement.  A pure dimension
shift requires the usual dimension formula; it is therefore exposed as an explicit hypothesis,
and discharged below for finite-type algebras over a field.  The remaining passage from a principal
divisor on `Spec R` to rational equivalence on `Spec (R ⧸ (f))` requires the local order identity;
when the two functions have a common codimension-one component, this is the usual tame-symbol
correction and is not claimed here.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace PrincipalGysin

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

open VectorBundle

noncomputable section

abbrev affineScheme (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

/-! ## The principal closed immersion and restriction of cycles -/

noncomputable def immersion (f : R) :
    Spec (CommRingCat.of (R ⧸ Ideal.span {f})) ⟶ affineScheme R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

/-- A regular affine equation is packaged as an actual effective Cartier divisor. -/
noncomputable def effectiveCartierDivisor (f : R) (hf : IsRegular f) :
    Curves.EffectiveCartierDivisor (affineScheme R) :=
  Curves.EffectiveCartierDivisor.ofGlobalEquation (affineScheme R)
    ((Scheme.ΓSpecIso (.of R)).inv f) (by
      apply Curves.isRegular_map_of_flat (Scheme.ΓSpecIso (.of R)).inv.hom
      · exact RingHom.Flat.of_bijective
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)
      · exact hf)

omit [IsNoetherianRing R] in
@[simp]
theorem effectiveCartierDivisor_ideal_top (f : R) (hf : IsRegular f) :
    (effectiveCartierDivisor f hf).idealSheaf.ideal
        ⟨⊤, isAffineOpen_top (affineScheme R)⟩ =
      Ideal.span {((Scheme.ΓSpecIso (.of R)).inv f)} := by
  exact Curves.EffectiveCartierDivisor.ofGlobalEquation_ideal_top _ _ _

instance immersion_isClosedImmersion (f : R) :
    _root_.AlgebraicGeometry.IsClosedImmersion (immersion f) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.mk_surjective :
      Function.Surjective (Ideal.Quotient.mk (Ideal.span {f})))

omit [IsNoetherianRing R] in
theorem immersion_base_injective (f : R) :
    Function.Injective (immersion f).base :=
  (immersion f).isClosedEmbedding.injective

/-- Pull a cycle on `Spec R` back to the points of the principal closed subscheme. -/
noncomputable def restrictCycle (f : R) :
    AlgebraicCycle (affineScheme R) ℚ →ₗ[ℚ]
      AlgebraicCycle (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ := by
  let F : AlgebraicCycle (affineScheme R) ℚ → AlgebraicCycle
      (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ := fun z =>
    { toFun := fun x => z ((immersion f).base x)
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro x _
        obtain ⟨t, ht, hfin⟩ := z.supportLocallyFiniteWithinDomain
          ((immersion f).base x) (by trivial)
        refine ⟨(immersion f).base ⁻¹' t,
          (immersion f).continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
        refine Set.Finite.of_finite_image (f := (immersion f).base)
          (hfin.subset ?_) ((immersion_base_injective f).injOn)
        rintro y ⟨w, hw, rfl⟩
        exact ⟨hw.1, hw.2⟩ }
  exact {
    toFun := F
    map_add' := by
      intro z w
      apply Function.locallyFinsuppWithin.coe_injective
      funext x
      rfl
    map_smul' := by
      intro q z
      apply Function.locallyFinsuppWithin.coe_injective
      funext x
      simp [F, Function.locallyFinsuppWithin.coe_rational_smul] }

omit [IsNoetherianRing R] in
@[simp]
theorem restrictCycle_apply (f : R)
    (z : AlgebraicCycle (affineScheme R) ℚ)
    (x : Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) :
    (restrictCycle f z : _ → ℚ) x = z ((immersion f).base x) :=
  rfl

/-! ## Principal-divisor generators on affine integral components -/

noncomputable def quotientSubscheme (P : Ideal R) [P.IsPrime] :
    IntegralClosedSubscheme (affineScheme R) where
  scheme := Spec (CommRingCat.of (R ⧸ P))
  inclusion := quotImmersion P

omit [IsNoetherianRing R] in
theorem quotientMk_ne_zero (P : Ideal R) (a : R) (ha : a ∉ P) :
    (Ideal.Quotient.mk P a : R ⧸ P) ≠ 0 :=
  fun h => ha (Ideal.Quotient.eq_zero_iff_mem.1 h)

noncomputable def elementFunction (P : Ideal R) [P.IsPrime]
    (a : R) (ha : a ∉ P) :
    (Spec (CommRingCat.of (R ⧸ P))).functionFieldˣ :=
  functionFieldUnit (CommRingCat.of (R ⧸ P)) (Ideal.Quotient.mk P a)
    (quotientMk_ne_zero P a ha)

noncomputable def elementGenerator (P : Ideal R) [P.IsPrime]
    (a : R) (ha : a ∉ P) : RationalFunctionGenerator (affineScheme R) where
  subspace := quotientSubscheme P
  function := elementFunction P a ha

noncomputable def quotientPoint (P Q : Ideal R) (hQ : Q.IsPrime) (hPQ : P ≤ Q) :
    Spec (CommRingCat.of (R ⧸ P)) :=
  ⟨Q.map (Ideal.Quotient.mk P),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)⟩

omit [IsNoetherianRing R] in
theorem quotImmersion_base_quotientPoint (P Q : Ideal R) (hQ : Q.IsPrime)
    (hPQ : P ≤ Q) :
    ((quotImmersion P).base (quotientPoint P Q hQ hPQ) : PrimeSpectrum R).asIdeal = Q := by
  change (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr hPQ

omit [IsNoetherianRing R] in
theorem mem_range_quotImmersion_iff (P : Ideal R)
    (Q : affineScheme R) :
    Q ∈ Set.range (quotImmersion P).base ↔ P ≤ (Q : PrimeSpectrum R).asIdeal := by
  constructor
  · rintro ⟨y, rfl⟩
    intro a ha
    change Ideal.Quotient.mk P a ∈ (y : PrimeSpectrum (R ⧸ P)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Ideal.zero_mem _
  · intro hPQ
    exact ⟨quotientPoint P _ (Q : PrimeSpectrum R).isPrime hPQ,
      PrimeSpectrum.ext (quotImmersion_base_quotientPoint P _ _ hPQ)⟩

theorem elementGenerator_apply_image (P : Ideal R) [P.IsPrime]
    (a : R) (ha : a ∉ P) (dimX : DimensionFunction (affineScheme R))
    (Q : Spec (CommRingCat.of (R ⧸ P))) :
    (elementGenerator P a ha).divisor dimX ((quotImmersion P).base Q) =
      (((Spec (CommRingCat.of (R ⧸ P))).ord
        (elementFunction P a ha :
          (Spec (CommRingCat.of (R ⧸ P))).functionField) Q : ℤ) : ℚ) :=
  AlgebraicCycle.map_closedImmersion_apply_image (quotImmersion P)
    (dimX : _ → ℤ) _ Q

theorem elementGenerator_apply_of_le (P : Ideal R) [P.IsPrime]
    (a : R) (ha : a ∉ P) (dimX : DimensionFunction (affineScheme R))
    (Q : affineScheme R) (hPQ : P ≤ (Q : PrimeSpectrum R).asIdeal) :
    (elementGenerator P a ha).divisor dimX Q =
      (((Spec (CommRingCat.of (R ⧸ P))).ord
        (elementFunction P a ha :
          (Spec (CommRingCat.of (R ⧸ P))).functionField)
        (quotientPoint P (Q : PrimeSpectrum R).asIdeal
          (Q : PrimeSpectrum R).isPrime hPQ) : ℤ) : ℚ) := by
  have himg : (quotImmersion P).base
      (quotientPoint P (Q : PrimeSpectrum R).asIdeal
        (Q : PrimeSpectrum R).isPrime hPQ) = Q :=
    PrimeSpectrum.ext (quotImmersion_base_quotientPoint P _ _ hPQ)
  have h := elementGenerator_apply_image P a ha dimX
    (quotientPoint P (Q : PrimeSpectrum R).asIdeal
      (Q : PrimeSpectrum R).isPrime hPQ)
  rwa [himg] at h

theorem elementGenerator_apply_of_not_le (P : Ideal R) [P.IsPrime]
    (a : R) (ha : a ∉ P) (dimX : DimensionFunction (affineScheme R))
    (Q : affineScheme R) (hQ : ¬ P ≤ (Q : PrimeSpectrum R).asIdeal) :
    (elementGenerator P a ha).divisor dimX Q = 0 :=
  AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range (quotImmersion P)
    (dimX : _ → ℤ) _ Q (fun h => hQ ((mem_range_quotImmersion_iff P Q).1 h))

/-! ## The cycle operation and its support -/

open Classical in
noncomputable def term (f : R) (dimX : DimensionFunction (affineScheme R))
    (V : affineScheme R) :
    AlgebraicCycle (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ :=
  if h : f ∉ (V : PrimeSpectrum R).asIdeal then
    restrictCycle f
      ((@elementGenerator R _ _ (V : PrimeSpectrum R).asIdeal
        (V : PrimeSpectrum R).isPrime f h).divisor dimX)
  else 0

theorem finite_support_summand (f : R) (dimX : DimensionFunction (affineScheme R))
    (z : AlgebraicCycle (affineScheme R) ℚ) :
    (Function.support fun V ↦ (z : affineScheme R → ℚ) V • term f dimX V).Finite :=
  (AlgebraicCycle.finite_support z).subset fun V hV hz => hV (by
    change (z : affineScheme R → ℚ) V = 0 at hz
    change (z : affineScheme R → ℚ) V • term f dimX V = 0
    rw [hz, zero_smul])

noncomputable def map (f : R) (dimX : DimensionFunction (affineScheme R)) :
    AlgebraicCycle (affineScheme R) ℚ →ₗ[ℚ]
      AlgebraicCycle (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ where
  toFun z := ∑ᶠ V, (z : affineScheme R → ℚ) V • term f dimX V
  map_add' z w := by
    have h : ∀ V, ((z + w : AlgebraicCycle (affineScheme R) ℚ) : affineScheme R → ℚ) V •
          term f dimX V =
        (z : affineScheme R → ℚ) V • term f dimX V +
          (w : affineScheme R → ℚ) V • term f dimX V := by
      intro V
      have hzw : ((z + w : AlgebraicCycle (affineScheme R) ℚ) : affineScheme R → ℚ) V =
          (z : affineScheme R → ℚ) V + (w : affineScheme R → ℚ) V := by simp
      rw [hzw, add_smul]
    simp only [h]
    exact finsum_add_distrib (finite_support_summand f dimX z)
      (finite_support_summand f dimX w)
  map_smul' q z := by
    have h : ∀ V, ((q • z : AlgebraicCycle (affineScheme R) ℚ) : affineScheme R → ℚ) V •
          term f dimX V = q • ((z : affineScheme R → ℚ) V • term f dimX V) := by
      intro V
      rw [Function.locallyFinsuppWithin.coe_rational_smul]
      simp [smul_smul]
    simp only [RingHom.id_apply, h]
    exact (smul_finsum' q (finite_support_summand f dimX z)).symm

@[simp]
theorem map_apply (f : R) (dimX : DimensionFunction (affineScheme R))
    (z : AlgebraicCycle (affineScheme R) ℚ) :
    map f dimX z = ∑ᶠ V, (z : affineScheme R → ℚ) V • term f dimX V :=
  rfl

@[simp]
theorem term_of_mem (f : R) (dimX : DimensionFunction (affineScheme R))
    (V : affineScheme R) (h : f ∈ (V : PrimeSpectrum R).asIdeal) :
    term f dimX V = 0 := by
  classical
  rw [term, dif_neg (not_not_intro h)]

@[simp]
theorem term_of_not_mem (f : R) (dimX : DimensionFunction (affineScheme R))
    (V : affineScheme R) (h : f ∉ (V : PrimeSpectrum R).asIdeal) :
    term f dimX V = restrictCycle f
      ((@elementGenerator R _ _ (V : PrimeSpectrum R).asIdeal
        (V : PrimeSpectrum R).isPrime f h).divisor dimX) := by
  classical
  rw [term, dif_pos h]

/-! ## Exact support of a principal Cartier summand -/

theorem term_support (f : R) (dimX : DimensionFunction (affineScheme R))
    (P : Ideal R) (hP' : P.IsPrime) (hP : f ∉ P)
    (Q : Spec (CommRingCat.of (R ⧸ Ideal.span {f})))
    (hQ : (restrictCycle f
      ((@elementGenerator R _ _ P hP' f hP).divisor dimX) : _ → ℚ) Q ≠ 0) :
    P < ((immersion f).base Q : PrimeSpectrum R).asIdeal ∧
      f ∈ ((immersion f).base Q : PrimeSpectrum R).asIdeal ∧
      (Ideal.map (Ideal.Quotient.mk P)
        ((immersion f).base Q : PrimeSpectrum R).asIdeal).height = 1 ∧
      ∀ Q' : Ideal R, Q'.IsPrime → P ≤ Q' →
        Q' < ((immersion f).base Q : PrimeSpectrum R).asIdeal → f ∉ Q' := by
  have hPQ : P ≤ ((immersion f).base Q : PrimeSpectrum R).asIdeal := by
    by_contra h
    exact hQ (by
      simp only [restrictCycle_apply]
      exact elementGenerator_apply_of_not_le P f hP dimX _ h)
  have hord : (Spec (CommRingCat.of (R ⧸ P))).ord
      (elementFunction P f hP : (Spec (CommRingCat.of (R ⧸ P))).functionField)
      (quotientPoint P ((immersion f).base Q).asIdeal
        ((immersion f).base Q : PrimeSpectrum R).isPrime hPQ) ≠ 0 := by
    intro hz
    apply hQ
    simp only [restrictCycle_apply, elementGenerator_apply_of_le P f hP dimX _ hPQ,
      hz]
    norm_num
  have hco : Order.coheight (quotientPoint P ((immersion f).base Q).asIdeal
      ((immersion f).base Q : PrimeSpectrum R).isPrime hPQ) = 1 := by
    by_contra h
    exact hord (_root_.AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one h _)
  have hheight : (Ideal.map (Ideal.Quotient.mk P)
      ((immersion f).base Q : PrimeSpectrum R).asIdeal).height = 1 := by
    rw [coheight_eq_ideal_height (R ⧸ P)
      (quotientPoint P ((immersion f).base Q).asIdeal
        ((immersion f).base Q : PrimeSpectrum R).isPrime hPQ)] at hco
    exact hco
  have hfQ : f ∈ ((immersion f).base Q : PrimeSpectrum R).asIdeal := by
    by_contra hf
    apply hord
    exact ord_algebraMap_eq_zero_of_notMem (CommRingCat.of (R ⧸ P))
      (quotientPoint P ((immersion f).base Q).asIdeal
        ((immersion f).base Q : PrimeSpectrum R).isPrime hPQ)
      (Ideal.Quotient.mk P f) (by
        intro hmem
        apply hf
        have hmap : Ideal.Quotient.mk P f ∈
            Ideal.map (Ideal.Quotient.mk P)
              ((immersion f).base Q : PrimeSpectrum R).asIdeal := hmem
        have hcomap :
            (Ideal.map (Ideal.Quotient.mk P)
              ((immersion f).base Q : PrimeSpectrum R).asIdeal).comap
                (Ideal.Quotient.mk P) = ((immersion f).base Q : PrimeSpectrum R).asIdeal := by
          rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_eq_left.mpr hPQ
        rw [← hcomap]
        exact hmap)
  have hlt : P < ((immersion f).base Q : PrimeSpectrum R).asIdeal :=
    lt_of_le_of_ne hPQ (fun heq => hP (heq ▸ hfQ))
  refine ⟨hlt, hfQ, hheight, ?_⟩
  intro Q' hQ' hPQ' hQlt hfQ'
  have hmapQ' : (Ideal.map (Ideal.Quotient.mk P) Q').IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ')
  let _ : (Ideal.map (Ideal.Quotient.mk P) Q').IsPrime := hmapQ'
  let _ : ((immersion f).base Q : PrimeSpectrum R).asIdeal.IsPrime :=
    ((immersion f).base Q : PrimeSpectrum R).isPrime
  have hmapQ : (Ideal.map (Ideal.Quotient.mk P)
      ((immersion f).base Q : PrimeSpectrum R).asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  let _ : (Ideal.map (Ideal.Quotient.mk P)
      ((immersion f).base Q : PrimeSpectrum R).asIdeal).IsPrime := hmapQ
  have hltmap : Ideal.map (Ideal.Quotient.mk P) Q' <
      Ideal.map (Ideal.Quotient.mk P)
        ((immersion f).base Q : PrimeSpectrum R).asIdeal := by
    refine lt_of_le_of_ne (Ideal.map_mono hQlt.le) ?_
    intro heq
    have hcomapQ' :
        (Ideal.map (Ideal.Quotient.mk P) Q').comap (Ideal.Quotient.mk P) = Q' := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr hPQ'
    have hcomapQ :
        (Ideal.map (Ideal.Quotient.mk P)
          ((immersion f).base Q : PrimeSpectrum R).asIdeal).comap
            (Ideal.Quotient.mk P) = ((immersion f).base Q : PrimeSpectrum R).asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr hPQ
    apply hQlt.ne
    rw [← hcomapQ', ← hcomapQ, heq]
  have hadd := Ideal.height_add_one_le_of_lt_of_isPrime hltmap
  rw [hheight] at hadd
  have h0 : (Ideal.map (Ideal.Quotient.mk P) Q').height = 0 := by
    by_contra h
    have h1 : (1 : ℕ∞) ≤ (Ideal.map (Ideal.Quotient.mk P) Q').height :=
      Order.one_le_iff_ne_zero.2 h
    have h2 : (1 : ℕ∞) + 1 ≤
        (Ideal.map (Ideal.Quotient.mk P) Q').height + 1 := by gcongr
    exact absurd (h2.trans hadd) (by decide)
  have hbot : Ideal.map (Ideal.Quotient.mk P) Q' = ⊥ :=
    Ideal.height_eq_zero_iff_eq_bot.1 h0
  have hQP : Q' = P := by
    have hcomapQ' :
        (Ideal.map (Ideal.Quotient.mk P) Q').comap (Ideal.Quotient.mk P) = Q' := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr hPQ'
    rw [← hcomapQ', hbot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact hP (hQP ▸ hfQ')

/-! ## Principal relations on the Cartier divisor -/

noncomputable def targetHom (f : R) (P : Ideal R) (hP : f ∈ P) :
    (R ⧸ Ideal.span {f}) →+* (R ⧸ P) :=
  Ideal.Quotient.lift (Ideal.span {f}) (Ideal.Quotient.mk P) (by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul])

omit [IsNoetherianRing R] in
theorem targetHom_surjective (f : R) (P : Ideal R) (hP : f ∈ P) :
    Function.Surjective (targetHom f P hP) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk (Ideal.span {f}) a, by
    simp [targetHom]
  ⟩

noncomputable def targetImmersion (f : R) (P : Ideal R) (hP : f ∈ P) :
    Spec (CommRingCat.of (R ⧸ P)) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {f})) :=
  Spec.map (CommRingCat.ofHom (targetHom f P hP))

instance targetImmersion_isClosedImmersion (f : R) (P : Ideal R) (hP : f ∈ P) :
    _root_.AlgebraicGeometry.IsClosedImmersion (targetImmersion f P hP) :=
  _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (targetHom_surjective f P hP)

omit [IsNoetherianRing R] in
theorem targetImmersion_comp_immersion (f : R) (P : Ideal R) (hP : f ∈ P) :
    targetImmersion f P hP ≫ immersion f = quotImmersion P := by
  unfold targetImmersion immersion
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  rfl

noncomputable def targetGenerator (f : R) (P : Ideal R) [P.IsPrime]
    (hP : f ∈ P) (a : R) (ha : a ∉ P) :
    RationalFunctionGenerator (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) where
  subspace :=
    { scheme := Spec (CommRingCat.of (R ⧸ P))
      inclusion := targetImmersion f P hP }
  function := elementFunction P a ha

theorem restrictCycle_elementGenerator_divisor (f : R) (P : Ideal R) [P.IsPrime]
    (hP : f ∈ P) (a : R) (ha : a ∉ P)
    (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f})))) :
    restrictCycle f ((elementGenerator P a ha).divisor dimX) =
      (targetGenerator f P hP a ha).divisor dimD := by
  apply Function.locallyFinsuppWithin.coe_injective
  funext y
  change (restrictCycle f ((elementGenerator P a ha).divisor dimX) : _ → ℚ) y = _
  simp only [restrictCycle_apply]
  change (elementGenerator P a ha).divisor dimX ((immersion f).base y) =
    _root_.AlgebraicGeometry.AlgebraicCycle.map (targetImmersion f P hP)
      (fun x ↦ (dimD : _ → ℤ) ((targetImmersion f P hP).base x))
      (dimD : _ → ℤ)
      ((Spec (CommRingCat.of (R ⧸ P))).principalCycle
        (elementFunction P a ha : (Spec (CommRingCat.of (R ⧸ P))).functionField)) y
  by_cases hle : P ≤ ((immersion f).base y : PrimeSpectrum R).asIdeal
  · let x := quotientPoint P ((immersion f).base y).asIdeal
      ((immersion f).base y : PrimeSpectrum R).isPrime hle
    have hcomp := targetImmersion_comp_immersion f P hP
    have hxQ : (quotImmersion P).base x = (immersion f).base y := by
      apply PrimeSpectrum.ext
      simpa using quotImmersion_base_quotientPoint P _ _ hle
    have hxy : (targetImmersion f P hP).base x = y := by
      apply (immersion f).isClosedEmbedding.injective
      have hx := congrArg (fun g ↦ g.base x) hcomp
      change (immersion f).base ((targetImmersion f P hP).base x) =
        (quotImmersion P).base x at hx
      rw [hxQ] at hx
      simpa [Scheme.Hom.comp_apply] using hx
    have hleft : (elementGenerator P a ha).divisor dimX ((immersion f).base y) =
        ((Spec (CommRingCat.of (R ⧸ P))).principalCycle
          (elementFunction P a ha :
            (Spec (CommRingCat.of (R ⧸ P))).functionField)) x := by
      rw [← hxQ, elementGenerator_apply_image]
      rfl
    have hright : _root_.AlgebraicGeometry.AlgebraicCycle.map
          (targetImmersion f P hP)
          (fun x ↦ (dimD : _ → ℤ) ((targetImmersion f P hP).base x))
          (dimD : _ → ℤ)
          ((Spec (CommRingCat.of (R ⧸ P))).principalCycle
            (elementFunction P a ha :
              (Spec (CommRingCat.of (R ⧸ P))).functionField)) y =
        ((Spec (CommRingCat.of (R ⧸ P))).principalCycle
          (elementFunction P a ha :
            (Spec (CommRingCat.of (R ⧸ P))).functionField)) x := by
      rw [← hxy, AlgebraicCycle.map_closedImmersion_apply_image]
    exact hleft.trans hright.symm
  · rw [elementGenerator_apply_of_not_le P a ha dimX _ hle]
    have hy : y ∉ Set.range (targetImmersion f P hP).base := by
      rintro ⟨x, hx⟩
      apply hle
      have hcomp := targetImmersion_comp_immersion f P hP
      have hx' := congrArg (fun g ↦ g.base x) hcomp
      change (immersion f).base ((targetImmersion f P hP).base x) =
        (quotImmersion P).base x at hx'
      rw [hx] at hx'
      exact (mem_range_quotImmersion_iff P ((immersion f).base y)).1
        ⟨x, hx'.symm⟩
    rw [AlgebraicCycle.map_closedImmersion_apply_of_not_mem_range
      (targetImmersion f P hP) (dimD : _ → ℤ) _ y hy]

open Classical in
noncomputable def termOf (f : R) (dimX : DimensionFunction (affineScheme R))
    (a : R) (V : affineScheme R) :
    AlgebraicCycle (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ :=
  if h : a ∉ (V : PrimeSpectrum R).asIdeal then
    restrictCycle f
      ((@elementGenerator R _ _ (V : PrimeSpectrum R).asIdeal
        (V : PrimeSpectrum R).isPrime a h).divisor dimX)
  else 0

@[simp]
theorem termOf_of_not_mem (f : R) (dimX : DimensionFunction (affineScheme R))
    (a : R) (V : affineScheme R) (h : a ∉ (V : PrimeSpectrum R).asIdeal) :
    termOf f dimX a V = restrictCycle f
      ((@elementGenerator R _ _ (V : PrimeSpectrum R).asIdeal
        (V : PrimeSpectrum R).isPrime a h).divisor dimX) := by
  classical
  rw [termOf, dif_pos h]

theorem finite_support_termOf (f : R) (dimX : DimensionFunction (affineScheme R))
    (a : R) (w : AlgebraicCycle (affineScheme R) ℚ) :
    (Function.support fun V ↦ (w : affineScheme R → ℚ) V • termOf f dimX a V).Finite :=
  (AlgebraicCycle.finite_support w).subset fun V hV hz => hV (by
    change (w : affineScheme R → ℚ) V = 0 at hz
    change (w : affineScheme R → ℚ) V • termOf f dimX a V = 0
    rw [hz, zero_smul])

theorem finsum_termOf_mem
    (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))))
    (a : R) (w : AlgebraicCycle (affineScheme R) ℚ)
    (hsupp : ∀ V : affineScheme R,
      (w : affineScheme R → ℚ) V ≠ 0 →
        f ∈ (V : PrimeSpectrum R).asIdeal ∧
        a ∉ (V : PrimeSpectrum R).asIdeal) :
    (∑ᶠ V, (w : affineScheme R → ℚ) V • termOf f dimX a V) ∈
      totalRationalRelations
        (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) dimD := by
  classical
  have hfin := finite_support_termOf f dimX a w
  have hsub : Function.support (fun V ↦
      (w : affineScheme R → ℚ) V • termOf f dimX a V) ⊆ (hfin.toFinset : Set _) := by
    intro V hV
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hz
    exact hV (by simpa using hz)
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Submodule.sum_mem _ fun V _ ↦ ?_
  by_cases hw : (w : affineScheme R → ℚ) V = 0
  · simp [hw]
  obtain ⟨hfV, haV⟩ := hsupp V hw
  refine Submodule.smul_mem _ _ ?_
  rw [termOf_of_not_mem f dimX a V haV,
    @restrictCycle_elementGenerator_divisor R _ _ f
      (V : PrimeSpectrum R).asIdeal (V : PrimeSpectrum R).isPrime hfV a haV dimX dimD]
  exact Submodule.subset_span ⟨@targetGenerator R _ _ f
    (V : PrimeSpectrum R).asIdeal (V : PrimeSpectrum R).isPrime hfV a haV, rfl⟩

/-! ## Dimension-graded form -/

/-!
The dimension formula for codimension-one components of the principal divisor `f = 0`.  The
height-one premise records the actual output of `term_support`; merely assuming `P < Q` and
`f ∈ Q` would also allow higher-codimension points.  This property is standard for the canonical
dimension functions on finite-type schemes over a field, but is kept explicit here so that the
cycle construction itself does not claim a dimension shift in an arbitrary noetherian ring.
-/
def CartierDimensionFormula (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f})))) : Prop :=
  ∀ (P : Ideal R) (hP : P.IsPrime) (_hpf : f ∉ P)
    (Q : Spec (CommRingCat.of (R ⧸ Ideal.span {f}))),
      P < ((immersion f).base Q : PrimeSpectrum R).asIdeal →
      f ∈ ((immersion f).base Q : PrimeSpectrum R).asIdeal →
      (Ideal.map (Ideal.Quotient.mk P)
        ((immersion f).base Q : PrimeSpectrum R).asIdeal).height = 1 →
      dimD Q + 1 = dimX ⟨P, hP⟩

omit [IsNoetherianRing R] in
theorem CartierDimensionFormula_of_finiteType
    {k : Type u} [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f})))) :
    CartierDimensionFormula f dimX dimD := by
  intro P hP _hpf Q hlt _hfQ hheight
  let fP : Spec (CommRingCat.of (R ⧸ P)) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ P)))
  let _ : LocallyOfFiniteType fP := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap (A := k) (B := R ⧸ P) |>.mpr inferInstance
  let dimP := FiniteTypeDimension.dimensionFunction fP
  have hcov : HomogeneityLocal.CovByDimension dimP :=
    HomogeneityLocal.covByDimension_of_dimensionFormula dimP (fun I hI ↦ by
      let _ : I.IsPrime := hI
      exact GromovWitten.Algebra.hasDimensionFormula k ((R ⧸ P) ⧸ I))
  let x := quotientPoint P ((immersion f).base Q).asIdeal
    ((immersion f).base Q : PrimeSpectrum R).isPrime hlt.le
  have hxQ : (quotImmersion P).base x = (immersion f).base Q := by
    apply PrimeSpectrum.ext
    exact quotImmersion_base_quotientPoint P _ _ hlt.le
  have hco : Order.coheight (x : PrimeSpectrum (R ⧸ P)) = 1 := by
    rw [VectorBundle.coheight_eq_ideal_height (R ⧸ P) (x : PrimeSpectrum (R ⧸ P))]
    exact hheight
  have hcovx : x ⋖ genericPoint (Spec (CommRingCat.of (R ⧸ P))) :=
    (HomogeneityLocal.coheight_eq_one_iff_covBy
      (HomogeneityLocal.isTop_genericPoint _)).1 hco
  have hdimx : dimP x = dimX ((immersion f).base Q) := by
    rw [DimensionFunction.apply_eq_of_isClosedImmersion dimP dimX (quotImmersion P) x,
      hxQ]
  have hgen : (quotImmersion P).base
      (genericPoint (Spec (CommRingCat.of (R ⧸ P)))) = ⟨P, hP⟩ := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk P)
      ((genericPoint (Spec (CommRingCat.of (R ⧸ P))) :
        PrimeSpectrum (R ⧸ P)).asIdeal) = P
    rw [genericPoint_asIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hdimgen : dimP (genericPoint (Spec (CommRingCat.of (R ⧸ P)))) = dimX ⟨P, hP⟩ := by
    rw [DimensionFunction.apply_eq_of_isClosedImmersion dimP dimX (quotImmersion P), hgen]
  have hdimD : dimD Q = dimX ((immersion f).base Q) :=
    DimensionFunction.apply_eq_of_isClosedImmersion dimD dimX (immersion f) Q
  calc
    dimD Q + 1 = dimP x + 1 := by rw [hdimD, hdimx]
    _ = dimP (genericPoint (Spec (CommRingCat.of (R ⧸ P)))) :=
      hcov x (genericPoint (Spec (CommRingCat.of (R ⧸ P)))) hcovx
    _ = dimX ⟨P, hP⟩ := hdimgen

noncomputable def gradedMap (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))))
    (i : ℤ) (hdrop : CartierDimensionFormula f dimX dimD) :
    cyclesOfDimension (affineScheme R) dimX i →ₗ[ℚ]
      cyclesOfDimension (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) dimD (i - 1) where
  toFun z := ⟨map f dimX z.1, by
    intro Q hQ
    change ((∑ᶠ V, (z.1 : affineScheme R → ℚ) V • term f dimX V) :
      AlgebraicCycle (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ) Q = 0
    rw [VectorBundle.finsum_cycle_apply
      (fun V ↦ (z.1 : affineScheme R → ℚ) V • term f dimX V)
      (finite_support_summand f dimX z.1) Q]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro P
    by_cases hzero : (z.1 : affineScheme R → ℚ) P = 0
    · simp [hzero]
    by_cases hmem : f ∈ (P : PrimeSpectrum R).asIdeal
    · simp [term_of_mem f dimX P hmem]
    have hdimP : dimX P = i := by
      by_contra hne
      exact hzero (z.2 P hne)
    have hterm : (term f dimX P : AlgebraicCycle
        (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) ℚ) Q = 0 := by
      rw [term_of_not_mem f dimX P hmem]
      by_contra hne
      obtain ⟨hlt, hfQ, hheight, _hmin⟩ := term_support f dimX
        (P : PrimeSpectrum R).asIdeal (P : PrimeSpectrum R).isPrime hmem Q hne
      have hdrop' := hdrop (P : PrimeSpectrum R).asIdeal
        (P : PrimeSpectrum R).isPrime hmem Q hlt hfQ hheight
      have hdimQ : dimD Q = i - 1 := by
        have heq : (⟨(P : PrimeSpectrum R).asIdeal,
            (P : PrimeSpectrum R).isPrime⟩ : affineScheme R) = P := by
          rfl
        rw [heq, hdimP] at hdrop'
        rw [← hdrop']
        omega
      exact hQ hdimQ
    simp [hterm]⟩
  map_add' z w := by
    apply Subtype.ext
    exact (map f dimX).map_add z.1 w.1
  map_smul' q z := by
    apply Subtype.ext
    exact (map f dimX).map_smul q z.1

/-- Over a finite-type algebra over a field, the principal-divisor cycle operation lowers
dimension by one, with the dimension formula discharged by the finite-type theorem. -/
noncomputable def gradedMapOfFiniteType
    {k : Type u} [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f})))) (i : ℤ) :
    cyclesOfDimension (affineScheme R) dimX i →ₗ[ℚ]
      cyclesOfDimension (Spec (CommRingCat.of (R ⧸ Ideal.span {f}))) dimD (i - 1) :=
  gradedMap f dimX dimD i (CartierDimensionFormula_of_finiteType (k := k) f dimX dimD)

/-- The graded operation retains the whole constructed cycle; it does not discard components
by projecting to the requested degree. -/
@[simp]
theorem gradedMapOfFiniteType_coe
    {k : Type u} [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (f : R) (dimX : DimensionFunction (affineScheme R))
    (dimD : DimensionFunction (Spec (CommRingCat.of (R ⧸ Ideal.span {f})))) (i : ℤ)
    (z : cyclesOfDimension (affineScheme R) dimX i) :
    (gradedMapOfFiniteType (k := k) f dimX dimD i z : AlgebraicCycle _ ℚ) =
      map f dimX z := rfl

end

end PrincipalGysin

end GromovWitten.AlgebraicGeometry.IntersectionTheory
