/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.Construction
import GromovWitten.AlgebraicGeometry.IntersectionTheory.ChernClasses
import GromovWitten.AlgebraicGeometry.IntersectionTheory.CycleGluing

/-!
# The no-obstruction formula: `[X]^vir = top Chern class of `E₁` cap `[X]`

Issue #66 (affine model).  Let `X = Spec (R ⧸ I)`, `L = conormalComplex k R I` and
`φ : E ⟶ L` an obstruction theory whose degree-zero term `E⁻¹ = E.degreeZero` is finite free, so
that `VirtualFundamentalClass/ResolvedCone.lean` builds the resolved cone
`C(E) ⊆ E₁ = Spec Sym(E⁻¹)`.  This file treats the "no-obstruction" case where `C(E)` is *exactly*
the zero section of `E₁`: the ideal of `C(E)` (`ResolvedCone.ideal φ`) equals the kernel of the
augmentation `bundleAugmentation φ : Sym(E⁻¹) →ₐ[R ⧸ I] R ⧸ I` (the algebra map killing every
degree-one generator, i.e. the coordinate ring of the zero-section closed immersion
`zeroSection φ : X ⟶ E₁`).

## Main declarations

* `bundleAugmentation φ`, `zeroSection φ`: the augmentation of `Sym(E⁻¹)` and the resulting
  zero-section closed immersion `X ⟶ E₁`.
* `ringEquivOfIdealEqKer`: given `hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation
  φ)`, the induced `R ⧸ I`-algebra isomorphism `ResolvedCone.ring φ ≃ₐ[R ⧸ I] R ⧸ I` identifying
  the resolved cone with `X`.
* `zeroSection_eq_comp_toBundle`: the factorisation `zeroSection φ = (specIsoOfIdealEqKer
  hzero).hom ≫ ResolvedCone.toBundle φ` through this isomorphism.
* `resolvedConeClass_eq_zeroSectionPushforward_of_ideal_eq`,
  `virtualClass_of_ideal_eq_zeroSection`: under `hzero` and purity of `X` in degree
  `coneDegree φ`, the virtual class is the zero-section Gysin pullback of the zero-section
  pushforward of the fundamental class of `X`.
* `topChern`: the top Chern class operator `s^* ∘ s_*` of a finite free module, as a linear map
  between rational Chow groups of its base.
* `virtualClass_eq_topChern_cap`: the headline formula, `[X]^vir = topChern (E.degreeZero) ∩ [X]`
  under the same hypotheses.

## What is not done

`topChern_rank_one = c1` (comparison with `IntersectionTheory/FirstChernClass.lean`) is not
attempted here; it is carried out in `VirtualFundamentalClass/TopChernRankOne.lean`, which also
shows that no lemma making the zero-section Gysin map independent of the witnessing
`RationalEquivalenceSystem` is needed (`eq_chowSystem`: that type has a single constructor, so
every system is the canonical `chowSystem dim i` of `FirstChernClass.lean`).  There
`topChern_eq_c1_trivial` identifies `topChern` in rank one with `c1` of the trivial line bundle,
and `topChern_eq_zero_of_nonempty` shows both vanish, as they must: over an affine base a finite
free `M` gives a *trivial* bundle.  The direct-sum
multiplicativity of `topChern` is not attempted either, for the same reason `ChernClasses.lean`
gives for not having Chern classes at all (no Whitney-sum-style comparison of `Sym(M₁ ⊕ M₂)`
with `Sym(M₁) ⊗ Sym(M₂)` at the level of zero-section pushforwards is available).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ObstructionBundleFormula

open IntersectionTheory hiding Scheme AlgebraicCycle
open VirtualClass ResolvedCone
open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R] {I : Ideal R}
variable {E : LinearTwoTermComplex (R ⧸ I)}
variable [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
variable (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-! ## The zero section of `E₁` -/

/-- The augmentation of the coordinate ring of `E₁ = Spec Sym(E⁻¹)`: the `R ⧸ I`-algebra map
killing every degree-one generator.  Its kernel cuts out the zero section of `E₁`. -/
noncomputable def bundleAugmentation : ResolvedCone.bundleRing φ →ₐ[R ⧸ I] R ⧸ I :=
  SymmetricAlgebra.lift (0 : E.degreeZero →ₗ[R ⧸ I] R ⧸ I)

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The augmentation retracts the structure map: it is the identity on the base ring. -/
theorem bundleAugmentation_algebraMap (s : R ⧸ I) :
    bundleAugmentation φ (algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) s) = s :=
  (bundleAugmentation φ).commutes s

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The augmentation is surjective: it is a retraction of the structure map. -/
theorem surjective_bundleAugmentation : Function.Surjective (bundleAugmentation φ) :=
  fun s => ⟨algebraMap (R ⧸ I) (ResolvedCone.bundleRing φ) s, bundleAugmentation_algebraMap φ s⟩

/-- **The zero section of `E₁`.** The closed immersion `X ⟶ E₁` cut out by the augmentation.
This is `VectorBundle.zeroSection` (`IntersectionTheory/ChernClasses.lean`) specialised to the
augmentation of the bundle `E₁`, kept reducible so that its pushforward
(`VectorBundle.zeroSectionPushforward`) and closed-immersion instance apply directly. -/
noncomputable abbrev zeroSection : Spec (CommRingCat.of (R ⧸ I)) ⟶ ResolvedCone.bundleSpace φ :=
  VectorBundle.zeroSection (bundleAugmentation φ)

/-! ## The resolved cone identified with the zero section -/

variable {φ}

/-- The `R ⧸ I`-algebra map `ring φ →ₐ[R ⧸ I] R ⧸ I` induced by the augmentation, given the
hypothesis that the ideal of the resolved cone is the kernel of the augmentation. -/
noncomputable def zeroSectionRingHom
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    ResolvedCone.ring φ →ₐ[R ⧸ I] R ⧸ I :=
  Ideal.Quotient.liftₐ (ResolvedCone.ideal φ) (bundleAugmentation φ)
    (fun _a ha => RingHom.mem_ker.mp (hzero ▸ ha))

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
@[simp]
theorem zeroSectionRingHom_mk
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (a : ResolvedCone.bundleRing φ) :
    zeroSectionRingHom hzero (Ideal.Quotient.mk (ResolvedCone.ideal φ) a) =
      bundleAugmentation φ a :=
  rfl

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The induced map on the resolved cone is surjective: the augmentation already is. -/
theorem surjective_zeroSectionRingHom
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    Function.Surjective (zeroSectionRingHom hzero) := by
  intro s
  obtain ⟨a, ha⟩ := surjective_bundleAugmentation φ s
  exact ⟨Ideal.Quotient.mk _ a, by rw [zeroSectionRingHom_mk, ha]⟩

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- The induced map on the resolved cone is injective: the ideal of the resolved cone is
*exactly* the kernel of the augmentation, not merely contained in it. -/
theorem injective_zeroSectionRingHom
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    Function.Injective (zeroSectionRingHom hzero) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, hzero, RingHom.mem_ker]
  rwa [zeroSectionRingHom_mk] at ha

/-- **The resolved cone identified with `X`.**  Given `hzero`, the coordinate ring of the
resolved cone `C(E)` is `R ⧸ I`-algebra isomorphic to `R ⧸ I` itself, via the augmentation. -/
noncomputable def ringEquivOfIdealEqKer
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    ResolvedCone.ring φ ≃ₐ[R ⧸ I] R ⧸ I :=
  AlgEquiv.ofBijective (zeroSectionRingHom hzero)
    ⟨injective_zeroSectionRingHom hzero, surjective_zeroSectionRingHom hzero⟩

/-- **The resolved cone identified with `X`, as schemes.** -/
noncomputable abbrev specIsoOfIdealEqKer
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    Spec (CommRingCat.of (R ⧸ I)) ≅ ResolvedCone.scheme φ :=
  VectorBundle.specIsoOfAlgEquiv (ringEquivOfIdealEqKer hzero)

omit [IsNoetherianRing R] [Module.Free (R ⧸ I) E.degreeZero]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **The zero section factors through the resolved cone.**  Under `hzero`, the zero section
`X ⟶ E₁` is the composite of the isomorphism `X ≅ C(E)` with the closed immersion
`C(E) ↪ E₁`. -/
theorem zeroSection_eq_comp_toBundle
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    zeroSection φ = (specIsoOfIdealEqKer hzero).hom ≫ ResolvedCone.toBundle φ := by
  rw [zeroSection, specIsoOfIdealEqKer, VectorBundle.specIsoOfAlgEquiv, ResolvedCone.toBundle,
    ← Spec.map_comp]
  congr 1

/-! ## The zero section as a pushforward of the fundamental class of `X` -/

variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (ResolvedCone.bundleSpace φ))

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- Purity of `X` in degree `coneDegree φ` transports to purity of the resolved cone `C(E)`,
under the identification `hzero`, using that the certified dimension grading is invariant under
scheme isomorphism. -/
theorem coneDimension_eq_coneDegree_of_dimX_eq
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ)
    (y : ResolvedCone.scheme φ) (hy : IsMax y) :
    coneDimension φ dimE y = coneDegree φ := by
  have hxy : (specIsoOfIdealEqKer hzero).hom.base
      ((specIsoOfIdealEqKer hzero).inv.base y) = y := by
    exact congrArg (fun g : ResolvedCone.scheme φ ⟶ ResolvedCone.scheme φ ↦ g.base y)
      (specIsoOfIdealEqKer hzero).inv_hom_id
  set x : Spec (CommRingCat.of (R ⧸ I)) := (specIsoOfIdealEqKer hzero).inv.base y with hxdef
  have hxmax : IsMax x := by
    apply (CycleGluing.isMax_map_iff (specIsoOfIdealEqKer hzero).hom x).mp
    rw [hxy]
    exact hy
  have hdimX : dimX x = coneDegree φ := hpureXtop x hxmax
  have hcomap := VectorBundle.dimension_comap_algEquiv (ringEquivOfIdealEqKer hzero)
    (coneDimension φ dimE) dimX x
  have hbase : (Spec.map (CommRingCat.ofHom
      (ringEquivOfIdealEqKer hzero).toRingEquiv.toRingHom)).base x =
      (specIsoOfIdealEqKer hzero).hom.base x := rfl
  rw [hbase, hxy] at hcomap
  rw [← hcomap, hdimX]

/-- **The pushforward of the fundamental class of `X` along the resolved-cone isomorphism is
the fundamental class of the resolved cone.** -/
theorem map_specIsoOfIdealEqKer_fundamentalCycle
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ)) :
    AlgebraicCycle.map (specIsoOfIdealEqKer hzero).hom dimX (coneDimension φ dimE)
        (Spec (CommRingCat.of (R ⧸ I))).fundamentalCycle =
      (ResolvedCone.scheme φ).fundamentalCycle := by
  have h := AlgebraicCycle.pullbackOpen_eq_map_of_isIso (specIsoOfIdealEqKer hzero).symm
    (coneDimension φ dimE) dimX (Spec (CommRingCat.of (R ⧸ I))).fundamentalCycle
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  rw [← h]
  exact AlgebraicCycle.pullbackOpen_fundamentalCycle (specIsoOfIdealEqKer hzero).inv

/-! ## Step 2: the virtual class under the zero-section hypothesis -/

variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (virtualDimension φ))
  (RE : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimE (coneDegree φ))
  (RXtop : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX (coneDegree φ))

/-- **Congruence for proper pushforward along an equality of closed immersions.**  Rewriting a
closed immersion through `properPushforward` directly runs into "motive is not type correct"
(the attached `IsProper`/`IsClosedImmersion` instances are baked into concrete, differently
unfolded terms); `subst` avoids this since it transports the instances along with the variable. -/
theorem properPushforward_congr_of_isClosedImmersion {X Y : Scheme.{u}}
    {dimension : DimensionFunction X} {dimensionY : DimensionFunction Y} {i : ℤ} {f g : X ⟶ Y}
    (h : f = g) [IsClosedImmersion f] [IsClosedImmersion g] :
    cyclesOfDimension.properPushforward (dimension := dimension) (dimensionY := dimensionY)
        (i := i) f =
      cyclesOfDimension.properPushforward (dimension := dimension) (dimensionY := dimensionY)
        (i := i) g := by
  subst h
  rfl

/-- **The resolved-cone class as a zero-section pushforward.**  Under `hzero` (the ideal of the
resolved cone is the ideal of the zero section of `E₁`) and purity of `X` in degree
`coneDegree φ`, the resolved-cone class is the zero-section pushforward of the fundamental class
of `X`. -/
theorem resolvedConeClass_eq_zeroSectionPushforward_of_ideal_eq
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ) :
    resolvedConeClass φ dimE RE =
      VectorBundle.zeroSectionPushforward (bundleAugmentation φ) RXtop RE
        (RXtop.quotientMap (cyclesOfDimension.fundamental hpureXtop)) := by
  have hpureCone : ∀ y : ResolvedCone.scheme φ, IsMax y → coneDimension φ dimE y = coneDegree φ :=
    fun y hy => coneDimension_eq_coneDegree_of_dimX_eq dimX dimE hzero hpureXtop y hy
  have hcyc : resolvedConeCycle φ dimE =
      cyclesOfDimension.properPushforward (zeroSection φ)
        (cyclesOfDimension.fundamental hpureXtop) := by
    rw [resolvedConeCycle_eq_properPushforward_fundamental φ dimE hpureCone,
      properPushforward_congr_of_isClosedImmersion (zeroSection_eq_comp_toBundle hzero),
      cyclesOfDimension.properPushforward_comp_closedImmersion (specIsoOfIdealEqKer hzero).hom
        (ResolvedCone.toBundle φ), LinearMap.comp_apply]
    congr 1
    apply Subtype.ext
    exact (map_specIsoOfIdealEqKer_fundamentalCycle dimX dimE hzero).symm
  rw [resolvedConeClass, hcyc]
  exact (VectorBundle.zeroSectionPushforward_quotientMap (bundleAugmentation φ) RXtop RE
    (cyclesOfDimension.fundamental hpureXtop)).symm

/-- **The virtual class under the zero-section hypothesis.**  If the ideal of the resolved cone
`C(E)` is the ideal of the zero section of the bundle `E₁` (`hzero`) and `X` is pure of dimension
`coneDegree φ` (its generic points all have this dimension, `hpureXtop`), then `[X]^vir` is the
zero-section Gysin pullback (`VectorBundle.zeroSectionGysin'`) of the zero-section pushforward of
the fundamental class of `X`. -/
theorem virtualClass_of_ideal_eq_zeroSection
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ)
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj =
      VectorBundle.zeroSectionGysin' (trivialization φ) dimX dimE (virtualDimension φ) RX RE hhom
        hinj (VectorBundle.zeroSectionPushforward (bundleAugmentation φ) RXtop RE
          (RXtop.quotientMap (cyclesOfDimension.fundamental hpureXtop))) := by
  rw [virtualClass, resolvedConeClass_eq_zeroSectionPushforward_of_ideal_eq dimX dimE RE RXtop
    hzero hpureXtop]

/-! ## Step 3: the top Chern class as a zero-section pullback of a zero-section pushforward -/

section TopChern

variable (S : Type u) [CommRing S] [IsNoetherianRing S] (M : Type u) [AddCommGroup M]
  [Module S M] [Module.Free S M] [Module.Finite S M]

/-- The augmentation of the coordinate ring of `Spec Sym(M)`, cutting out its zero section. -/
noncomputable def moduleAugmentation : SymmetricAlgebra S M →ₐ[S] S :=
  SymmetricAlgebra.lift (0 : M →ₗ[S] S)

variable {S M} {dimS : DimensionFunction (Spec (CommRingCat.of S))}
  {dimM : DimensionFunction (Spec (CommRingCat.of (SymmetricAlgebra S M)))} {i : ℤ}
  (RStop : RationalEquivalenceSystem (Spec (CommRingCat.of S)) dimS
    (i + (Nat.card (Module.Free.ChooseBasisIndex S M) : ℤ)))
  (RS : RationalEquivalenceSystem (Spec (CommRingCat.of S)) dimS i)
  (RM : RationalEquivalenceSystem (Spec (CommRingCat.of (SymmetricAlgebra S M))) dimM
    (i + (Nat.card (Module.Free.ChooseBasisIndex S M) : ℤ)))

/-- **The top Chern class operator** `c_top(M) ∩ - : A_{i+r}(Spec S) → A_i(Spec S)` of a finite
free module `M` of rank `r`, in the affine model: the composite `s^* ∘ s_*` of the zero-section
pushforward (`VectorBundle.zeroSectionPushforward`) with the zero-section Gysin pullback
(`VectorBundle.zeroSectionGysin'`), for the bundle `Spec Sym(M)` over `Spec S`. -/
noncomputable def topChern
    (hhom : PrincipalDivisorsHomogeneous (Spec (CommRingCat.of (SymmetricAlgebra S M))) dimM)
    (hinj : Function.Injective
      (VectorBundle.chowPullbackBundle (VectorBundle.symTrivialization S M) dimS dimM i RS RM)) :
    RStop.ChowGroup →ₗ[ℚ] RS.ChowGroup :=
  (VectorBundle.zeroSectionGysin' (VectorBundle.symTrivialization S M) dimS dimM i RS RM hhom
      hinj).toLinearMap.comp
    (VectorBundle.zeroSectionPushforward (moduleAugmentation S M) RStop RM)

end TopChern

/-! ## Step 4: the headline no-obstruction formula -/

/-- **The no-obstruction formula.**  If the ideal of the resolved cone `C(E)` is the ideal of the
zero section of the bundle `E₁ = Spec Sym(E⁻¹)` (`hzero`) and `X` is pure of dimension
`coneDegree φ = vd + rank(E₁)` (`hpureXtop`, i.e. `dim X = vd - (- rank E₁)`, the "excess
dimension" reading of `Construction.lean`'s `virtualDimension = dim X - rank E₁`), then the
virtual fundamental class is the top Chern class of `E₁` capped with the fundamental class of
`X`. -/
theorem virtualClass_eq_topChern_cap
    (hzero : ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ))
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ)
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    virtualClass φ dimX dimE RX RE hhom hinj =
      topChern RXtop RX RE hhom hinj
        (RXtop.quotientMap (cyclesOfDimension.fundamental hpureXtop)) :=
  virtualClass_of_ideal_eq_zeroSection dimX dimE RX RE RXtop hzero hpureXtop hhom hinj

/-! ## Step 5: the rank-zero case recovers the fundamental class -/

section RankZero

variable [hbase : Nontrivial (R ⧸ I)] [Subsingleton E.degreeZero]

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- At rank zero the only linear map `E⁻¹ → R ⧸ I` is `0`, so the augmentation of `E₁`'s
coordinate ring is (through `SymmetricAlgebra.lift`, an equivalence) the *unique* `R ⧸ I`-algebra
map `Sym(E⁻¹) →ₐ R ⧸ I`, matching `Construction.lean`'s trivialisation-based isomorphism. -/
theorem bundleAugmentation_eq_bundleRingEquiv :
    bundleAugmentation φ = (bundleRingEquiv φ).toAlgHom := by
  have hsub : Subsingleton (E.degreeZero →ₗ[R ⧸ I] R ⧸ I) := by
    refine ⟨fun f g => LinearMap.ext fun m => ?_⟩
    rw [Subsingleton.elim m 0, map_zero, map_zero]
  have heq := hsub.elim (SymmetricAlgebra.lift.symm (bundleAugmentation φ))
    (SymmetricAlgebra.lift.symm (bundleRingEquiv φ).toAlgHom)
  have hlift := congrArg (SymmetricAlgebra.lift (R := R ⧸ I) (M := E.degreeZero)) heq
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hlift

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- At rank zero the augmentation of `E₁`'s coordinate ring is injective (it is, up to the
identification above, the trivialisation isomorphism), so its kernel vanishes. -/
theorem ker_bundleAugmentation_eq_bot :
    RingHom.ker (bundleAugmentation φ) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [RingHom.mem_ker, bundleAugmentation_eq_bundleRingEquiv] at ha
  have ha' : (bundleRingEquiv φ) a = 0 := ha
  have ha0 : a = 0 :=
    (bundleRingEquiv φ).injective (a₂ := 0) (by rw [ha', map_zero])
  rw [ha0]
  exact Submodule.zero_mem _

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- **At rank zero the resolved cone is (via `hzero`) the zero section.**  This combines
`Construction.lean`'s `ideal_eq_bot` (`C(E) = E₁`) with the vanishing of the kernel of the
augmentation above: both are `⊥`. -/
theorem ideal_eq_ker_bundleAugmentation_of_subsingleton :
    ResolvedCone.ideal φ = RingHom.ker (bundleAugmentation φ) := by
  rw [ideal_eq_bot φ, ker_bundleAugmentation_eq_bot]

variable [Subsingleton E.degreeOne] [Subsingleton (PrimeSpectrum (R ⧸ I))]
  [_root_.IsReduced (R ⧸ I)]

/-- **The rank-zero case recovers the fundamental class.**  If `E⁻¹` is subsingleton, the
zero-section hypothesis `hzero` of the no-obstruction formula holds automatically
(`ideal_eq_ker_bundleAugmentation_of_subsingleton`), and combining `virtualClass_eq_topChern_cap`
with `Construction.lean`'s `virtualClass_eq_fundamental` (proved independently, without reference
to Chern classes) shows the two formulas for `[X]^vir` agree: the top-Chern-class value is the
class of the fundamental cycle of `X`. -/
theorem topChern_cap_eq_fundamental_of_subsingleton
    (hpureXtop : ∀ p : Spec (CommRingCat.of (R ⧸ I)), IsMax p → dimX p = coneDegree φ)
    (hhom : PrincipalDivisorsHomogeneous (ResolvedCone.bundleSpace φ) dimE)
    (hinj : Function.Injective (bundlePullback φ dimX dimE RX RE)) :
    topChern RXtop RX RE hhom hinj
        (RXtop.quotientMap (cyclesOfDimension.fundamental hpureXtop)) =
      RX.quotientMap (cyclesOfDimension.fundamental (pure_base φ dimX)) := by
  rw [← virtualClass_eq_topChern_cap dimX dimE RX RE RXtop
    ideal_eq_ker_bundleAugmentation_of_subsingleton hpureXtop hhom hinj]
  exact virtualClass_eq_fundamental φ dimX dimE RX RE hhom hinj

end RankZero

end GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.ObstructionBundleFormula
