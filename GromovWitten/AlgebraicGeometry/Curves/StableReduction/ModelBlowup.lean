/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ReesBlowupGlobal
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ArithmeticSurface

/-!
# Blowing up a model along a centre in the special fibre

Let `M` be a model of a curve over a discrete valuation ring `R` and let `I` be a quasi-coherent
ideal sheaf on its total space whose support lies in the special fibre.  This file proves that
the blowup of `M.total` along `I`, constructed in `ReesBlowupGlobal`, is again a model of the
same curve, and that the blowup projection is a proper modification of models in the sense of
`ModelModification`.  This is the elementary step of every normalized blowup sequence resolving
a proper model.

* `Model.blowup M I hI` is the blown-up model; its total space is the global Rees blowup and its
  structure map is the composite with the blowup projection.
* The blown-up model is flat over `R`.  Flatness over a discrete valuation ring is
  torsion-freeness, and torsion-freeness is checked on the affine charts of the Rees blowup: the
  homogeneous localizations of the Rees algebra of a torsion-free ring are torsion-free
  (`ReesTorsion.flat_chartMap_comp`).
* The generic fibre is untouched: the blowup is an isomorphism away from the support of `I`,
  which contains the generic fibre, so the induced map of generic fibres is an isomorphism
  (`Model.isIso_genericFiberMap`) and the blown-up model inherits the generic-fibre
  identification.
* `Model.blowupModification M I hI` is the resulting proper modification, and
  `Model.blowup_isProper` shows that blowing up preserves properness.
* `Model.blowupClosed M Z hZ` blows up the vanishing ideal of a closed subset of the special
  fibre, for instance a closed point, using `support_vanishingIdeal`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

/-! ### Torsion-freeness of the affine charts of a Rees blowup -/

namespace ReesTorsion

open AlgebraicGeometry.ReesBlowup HomogeneousLocalization

variable {A : Type u} [CommRing A]

/-- In a commutative monoid with zero, one-sided cancellation suffices for being a
nonzerodivisor. -/
theorem mem_nonZeroDivisors_of_forall {M : Type*} [CommMonoidWithZero M] {r : M}
    (h : ∀ x, x * r = 0 → x = 0) : r ∈ nonZeroDivisors M :=
  mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ h x (by rw [mul_comm]; exact hx), h⟩

/-- A constant polynomial with nonzerodivisor coefficient is a nonzerodivisor. -/
theorem C_mem_nonZeroDivisors {a : A} (ha : a ∈ nonZeroDivisors A) :
    Polynomial.C a ∈ nonZeroDivisors (Polynomial A) := by
  refine mem_nonZeroDivisors_of_forall fun p hp ↦ ?_
  ext n
  have h := congrArg (fun q : Polynomial A ↦ q.coeff n) hp
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_zero] at h
  exact (mem_nonZeroDivisors_iff.mp ha).2 _ h

/-- The constant Rees-algebra element of a nonzerodivisor is a nonzerodivisor. -/
theorem algebraMap_reesAlgebra_mem_nonZeroDivisors (J : Ideal A) {a : A}
    (ha : a ∈ nonZeroDivisors A) :
    algebraMap A (reesAlgebra J) a ∈ nonZeroDivisors (reesAlgebra J) := by
  refine mem_nonZeroDivisors_of_injective (f := (reesAlgebra J).val) Subtype.val_injective ?_
  have : (reesAlgebra J).val (algebraMap A (reesAlgebra J) a) = Polynomial.C a := by
    simp [Polynomial.algebraMap_eq]
  rw [this]
  exact C_mem_nonZeroDivisors ha

variable (J : Ideal A) (f : reesAlgebra J)

/-- The localization of the Rees algebra at a homogeneous element keeps the constant elements
of nonzerodivisors as nonzerodivisors. -/
theorem algebraMap_localization_mem_nonZeroDivisors {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap (reesAlgebra J) (Localization.Away f) (algebraMap A (reesAlgebra J) a) ∈
      nonZeroDivisors (Localization.Away f) :=
  IsLocalization.map_nonZeroDivisors_le (Submonoid.powers f) (Localization.Away f)
    ⟨_, algebraMap_reesAlgebra_mem_nonZeroDivisors J ha, rfl⟩

/-- The degree-zero inverse of `zeroEquiv` sends `a` to the constant Rees element `a`. -/
theorem coe_zeroEquiv_symm (a : A) :
    (((zeroEquiv J).symm a : grade J 0) : reesAlgebra J) = algebraMap A (reesAlgebra J) a := by
  apply Subtype.ext
  change (((component J (algebraMap A (reesAlgebra J) a) 0 : grade J 0) : reesAlgebra J) :
    Polynomial A) = _
  rw [component_coe]
  simp

/-- The structure map from the base ring into a homogeneous localization of its Rees algebra:
the affine chart of the blowup given by a homogeneous element `f`. -/
def chartMap : A →+* Away (grade J) f :=
  (fromZeroRingHom (grade J) (Submonoid.powers f)).comp (zeroEquiv J).symm.toRingHom

theorem val_chartMap (a : A) :
    (chartMap J f a).val =
      algebraMap (reesAlgebra J) (Localization.Away f) (algebraMap A (reesAlgebra J) a) := by
  change (HomogeneousLocalization.mk ⟨0, (zeroEquiv J).symm a, 1, one_mem _⟩).val = _
  rw [val_mk, ← Localization.mk_one_eq_algebraMap]
  congr 1
  exact coe_zeroEquiv_symm J a

/-- Multiplication by a nonzerodivisor of the base is injective on an affine chart of the
blowup. -/
theorem eq_zero_of_chartMap_mul_eq_zero {a : A} (ha : a ∈ nonZeroDivisors A)
    {x : Away (grade J) f} (h : chartMap J f a * x = 0) : x = 0 := by
  apply val_injective (Submonoid.powers f)
  rw [val_zero]
  have h' := congrArg HomogeneousLocalization.val h
  rw [val_mul, val_zero, val_chartMap] at h'
  exact (mem_nonZeroDivisors_iff.mp (algebraMap_localization_mem_nonZeroDivisors J f ha)).1 _ h'

variable {R : Type u} [CommRing R]

/-- A flat ring map sends nonzerodivisors to nonzerodivisors. -/
theorem mem_nonZeroDivisors_of_flat {φ : R →+* A} (hφ : φ.Flat) {r : R}
    (hr : r ∈ nonZeroDivisors R) : φ r ∈ nonZeroDivisors A := by
  let _ := φ.toAlgebra
  have hflat : Module.Flat R A := hφ
  have htor := Module.Flat.torsion_eq_bot (R := R) (M := A)
  refine mem_nonZeroDivisors_of_forall fun x hx ↦ ?_
  have hmem : x ∈ Submodule.torsion R A := by
    refine (Submodule.mem_torsion_iff x).mpr ⟨⟨r, hr⟩, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    exact hx
  rw [htor] at hmem
  exact (Submodule.mem_bot R).mp hmem

/-- Over a Bezout domain, an affine chart of the blowup of a flat algebra is flat: it is
torsion-free because multiplication by nonzero scalars is injective on it. -/
theorem flat_chartMap_comp [IsDomain R] [IsBezout R] {φ : R →+* A} (hφ : φ.Flat) :
    ((chartMap J f).comp φ).Flat := by
  let _ := ((chartMap J f).comp φ).toAlgebra
  change Module.Flat R (Away (grade J) f)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).mp hx
  rw [Submodule.mem_bot]
  refine eq_zero_of_chartMap_mul_eq_zero J f (mem_nonZeroDivisors_of_flat hφ hr) (x := x) ?_
  rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hrx
  exact hrx

set_option backward.isDefEq.respectTransparency false in
/-- The affine Rees blowup of a flat algebra over a Bezout domain is flat over the domain:
flatness is local on the source and holds on every affine chart. -/
theorem flat_projection_comp [IsDomain R] [IsBezout R] {φ : R →+* A} (hφ : φ.Flat) :
    Flat (projection J ≫ Spec.map (CommRingCat.ofHom φ)) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover
    (Proj.affineOpenCover (grade J)).openCover fun i ↦ ?_
  rw [Scheme.AffineOpenCover.openCover_f, Proj.affineOpenCover_f, ReesBlowup.projection]
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_comp, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, ← RingHom.comp_assoc]
  exact flat_chartMap_comp J _ hφ

end ReesTorsion

/-! ### The vanishing ideal of a closed subset -/

set_option backward.isDefEq.respectTransparency false in
/-- The support of the vanishing ideal sheaf of a closed subset is that closed subset. -/
theorem support_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mpr le_rfl)
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hmem : x ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) ∩
      ((((⟨U, hU⟩ : X.affineOpens) : X.Opens)) : Set X) := ⟨hx, hxU⟩
  rw [Scheme.IdealSheafData.coe_support_inter _ ⟨U, hU⟩,
    Scheme.IdealSheafData.vanishingIdeal_ideal, ← IsAffineOpen.fromSpec_image_zeroLocus hU,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (Z.isClosed.preimage hU.fromSpec.continuous).closure_eq,
    Set.image_preimage_eq_inter_range] at hmem
  exact hmem.1

/-! ### Blowing up a model -/

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

omit [IsDiscreteValuationRing R] in
set_option backward.isDefEq.respectTransparency false in
/-- The generic point map of a discrete valuation ring hits the generic point. -/
theorem genericPointMap_apply (z : Spec (.of K)) :
    genericPointMap R K z = dvrGenericPoint R := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap (algebraMap R K) z).asIdeal = ⊥
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime z.asIdeal,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

/-- The generic and special points of the spectrum of a discrete valuation ring differ. -/
theorem dvrGenericPoint_ne_dvrSpecialPoint : dvrGenericPoint R ≠ dvrSpecialPoint R := by
  intro h
  have h' : (⊥ : Ideal R) = IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal h
  exact Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal R)
    (IsDiscreteValuationRing.not_isField R) h'.symm

/-- The map on generic fibres induced by a morphism `f` of schemes over the base. -/
def genericFiberMap {B X : Scheme.{u}} (f : B ⟶ X) (p : X ⟶ Spec (.of R)) :
    pullback (f ≫ p) (genericPointMap R K) ⟶ pullback p (genericPointMap R K) :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition])

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := simp)]
theorem genericFiberMap_fst {B X : Scheme.{u}} (f : B ⟶ X) (p : X ⟶ Spec (.of R)) :
    genericFiberMap (K := K) f p ≫ pullback.fst p (genericPointMap R K) =
      pullback.fst (f ≫ p) (genericPointMap R K) ≫ f :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc (attr := simp)]
theorem genericFiberMap_snd {B X : Scheme.{u}} (f : B ⟶ X) (p : X ⟶ Spec (.of R)) :
    genericFiberMap (K := K) f p ≫ pullback.snd p (genericPointMap R K) =
      pullback.snd (f ≫ p) (genericPointMap R K) :=
  pullback.lift_snd _ _ _

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The generic fibre of the source of `f` is the pullback of the generic fibre of the target
along `f`. -/
theorem isPullback_genericFiberMap {B X : Scheme.{u}} (f : B ⟶ X) (p : X ⟶ Spec (.of R)) :
    IsPullback (pullback.fst (f ≫ p) (genericPointMap R K)) (genericFiberMap (K := K) f p) f
      (pullback.fst p (genericPointMap R K)) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback p (genericPointMap R K))
  · rw [genericFiberMap_snd]
    exact IsPullback.of_hasPullback _ _
  · rw [genericFiberMap_fst]

namespace Model

section

open GromovWitten.AlgebraicGeometry.GlobalBlowup AlgebraicGeometry.ReesBlowup

/- The index type of the gluing cover is only definitionally the type of affine opens, and
`Flat` is only definitionally a morphism property; the unifier is told not to respect
reducibility, as in `ReesBlowupGlobal` and Mathlib's `Flat` file. -/
set_option backward.isDefEq.respectTransparency false

variable (M : Model R K C toK)

/-- The total space of a model is locally Noetherian, being of finite type over the
Noetherian base. -/
instance isLocallyNoetherian_total : IsLocallyNoetherian M.total :=
  LocallyOfFiniteType.isLocallyNoetherian M.toBase

variable (I : M.total.IdealSheafData)

instance toBase_isProper : _root_.AlgebraicGeometry.IsProper (GlobalBlowup.toBase M.total I) :=
  GlobalBlowup.toBase_isProper M.total I

/-- The structure map of the total space restricted to an affine open, as a ring map. -/
def affineStructureMap (U : M.total.affineOpens) : R →+* Γ(M.total, U.1) :=
  (M.toBase.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

theorem fromSpec_comp_toBase (U : M.total.affineOpens) :
    U.2.fromSpec ≫ M.toBase = Spec.map (CommRingCat.ofHom (affineStructureMap M U)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec M.toBase (isAffineOpen_top _) U.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The affine structure maps of a model are flat. -/
theorem flat_affineStructureMap (U : M.total.affineOpens) : (affineStructureMap M U).Flat := by
  have h : Flat (U.2.fromSpec ≫ M.toBase) := inferInstance
  rw [fromSpec_comp_toBase] at h
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp h

/-- The blowup of a model along any quasi-coherent ideal sheaf is flat over the base. -/
theorem flat_blowup_toBase : Flat (GlobalBlowup.toBase M.total I ≫ M.toBase) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat)
    (fun U ↦ (affineι M.total I U).opensRange) (iSup_opensRange_affineι M.total I) fun U ↦ ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (affineι M.total I U) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (affineι M.total I U).opensRange.opensRange_ι.symm),
    Category.assoc, MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
  rw [← Category.assoc, ← (isPullback_affine M.total I U).w, Category.assoc, Category.assoc,
    ← Category.assoc ((isAffineOpen M.total U).isoSpec.inv), IsAffineOpen.isoSpec_inv_ι,
    fromSpec_comp_toBase]
  exact ReesTorsion.flat_projection_comp (I.ideal U) (flat_affineStructureMap M U)

/-- The centre of a blowup lies in the special fibre: every point of the support of the ideal
sheaf maps to the closed point of the base. -/
def IsSpecialFibreCentre : Prop :=
  ∀ x ∈ I.support, M.toBase x = dvrSpecialPoint R

/-- The generic fibre of a model misses every centre in the special fibre. -/
theorem range_fst_subset_centreComplement (hI : IsSpecialFibreCentre M I) :
    Set.range (pullback.fst M.toBase (genericPointMap R K)) ⊆
      (centreComplement M.total I : Set M.total) := by
  rintro _ ⟨y, rfl⟩
  rw [SetLike.mem_coe, mem_centreComplement]
  intro hy
  have hcond : M.toBase (pullback.fst M.toBase (genericPointMap R K) y) =
      genericPointMap R K (pullback.snd M.toBase (genericPointMap R K) y) :=
    congrArg (fun h : pullback M.toBase (genericPointMap R K) ⟶ Spec (.of R) ↦ h y)
      pullback.condition
  rw [genericPointMap_apply, hI _ hy] at hcond
  exact dvrGenericPoint_ne_dvrSpecialPoint hcond.symm

/-- Blowing up a centre in the special fibre does not change the generic fibre. -/
theorem isIso_genericFiberMap (hI : IsSpecialFibreCentre M I) :
    IsIso (genericFiberMap (K := K) (GlobalBlowup.toBase M.total I) M.toBase) := by
  set f := GlobalBlowup.toBase M.total I
  set U := centreComplement M.total I
  have hrange : Set.range (pullback.fst M.toBase (genericPointMap R K)) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact range_fst_subset_centreComplement M I hI
  set lift := IsOpenImmersion.lift U.ι (pullback.fst M.toBase (genericPointMap R K)) hrange
  have hlift : lift ≫ U.ι = pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ hrange
  have hrange₂ : Set.range (pullback.fst (f ≫ M.toBase) (genericPointMap R K)) ⊆
      Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change f (pullback.fst (f ≫ M.toBase) (genericPointMap R K) y) ∈ U
    have : f (pullback.fst (f ≫ M.toBase) (genericPointMap R K) y) =
        pullback.fst M.toBase (genericPointMap R K) (genericFiberMap (K := K) f M.toBase y) := by
      change (pullback.fst (f ≫ M.toBase) (genericPointMap R K) ≫ f) y =
        (genericFiberMap (K := K) f M.toBase ≫ pullback.fst M.toBase (genericPointMap R K)) y
      rw [genericFiberMap_fst]
    rw [this]
    exact range_fst_subset_centreComplement M I hI ⟨_, rfl⟩
  set lift₂ := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (pullback.fst (f ≫ M.toBase) _) hrange₂
  have hlift₂ : lift₂ ≫ (f ⁻¹ᵁ U).ι = pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ hrange₂
  have hsq : IsPullback lift₂ (genericFiberMap (K := K) f M.toBase) (f ∣_ U) lift := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f U).flip
    · rw [hlift₂, hlift]
      exact isPullback_genericFiberMap f M.toBase
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hlift₂,
        Category.assoc, hlift, genericFiberMap_fst]
  have hiso : IsIso (f ∣_ U) := toBase_restrict_isIso M.total I
  exact (MorphismProperty.isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) hsq
      ((MorphismProperty.isomorphisms.iff _).mpr hiso))

/-- The generic fibre of the blowup, identified with the curve through the generic fibre of the
original model. -/
def blowupGenericFiberIso (hI : IsSpecialFibreCentre M I) :
    genericFiber R K (GlobalBlowup.toBase M.total I ≫ M.toBase) ≅ Over.mk toK :=
  haveI := isIso_genericFiberMap M I hI
  Over.isoMk (f := genericFiber R K (GlobalBlowup.toBase M.total I ≫ M.toBase))
    (g := genericFiber R K M.toBase)
    (asIso (genericFiberMap (K := K) (GlobalBlowup.toBase M.total I) M.toBase))
    (by simp) ≪≫ M.genericFiberIso

theorem genericFiberMap_comp_genericFiberIso_hom_left (hI : IsSpecialFibreCentre M I) :
    genericFiberMap (K := K) (GlobalBlowup.toBase M.total I) M.toBase ≫
      M.genericFiberIso.hom.left = (blowupGenericFiberIso M I hI).hom.left := by
  have := isIso_genericFiberMap M I hI
  simp [blowupGenericFiberIso]

/-- The model obtained by blowing up a centre in the special fibre.  Its total space is the
global Rees blowup, its structure map is the composite with the blowup projection, flatness is
`flat_blowup_toBase`, and the generic-fibre identification is inherited through
`isIso_genericFiberMap`. -/
def blowup (hI : IsSpecialFibreCentre M I) : Model R K C toK where
  total := GlobalBlowup.blowup M.total I
  toBase := GlobalBlowup.toBase M.total I ≫ M.toBase
  flat := flat_blowup_toBase M I
  locallyOfFinitePresentation := inferInstance
  quasiCompact := inferInstance
  genericFiberIso := blowupGenericFiberIso M I hI

/-- The blowup projection as a morphism of models. -/
def blowupHom (hI : IsSpecialFibreCentre M I) : M.blowup I hI ⟶ M where
  hom := GlobalBlowup.toBase M.total I
  over_base := rfl
  genericFiber := genericFiberMap_comp_genericFiberIso_hom_left M I hI

/-- Blowing up a centre in the special fibre is a proper modification of models. -/
def blowupModification (hI : IsSpecialFibreCentre M I) :
    ModelModification (M.blowup I hI) M where
  hom := blowupHom M I hI
  proper := GlobalBlowup.toBase_isProper M.total I
  genericIsIso := isIso_genericFiberMap M I hI

/-- Blowing up preserves properness of a model. -/
theorem blowup_isProper (hI : IsSpecialFibreCentre M I) (hM : M.IsProper) :
    (M.blowup I hI).IsProper := by
  have : _root_.AlgebraicGeometry.IsProper M.toBase := hM
  change _root_.AlgebraicGeometry.IsProper (GlobalBlowup.toBase M.total I ≫ M.toBase)
  infer_instance

/-- The vanishing ideal of a closed subset of the special fibre is a centre in the special
fibre. -/
theorem isSpecialFibreCentre_vanishingIdeal (Z : Closeds M.total)
    (hZ : ∀ x ∈ Z, M.toBase x = dvrSpecialPoint R) :
    IsSpecialFibreCentre M (Scheme.IdealSheafData.vanishingIdeal Z) := by
  intro x hx
  rw [support_vanishingIdeal] at hx
  exact hZ x hx

/-- The blowup of a model along a closed subset of its special fibre, for instance a closed
point. -/
def blowupClosed (Z : Closeds M.total) (hZ : ∀ x ∈ Z, M.toBase x = dvrSpecialPoint R) :
    Model R K C toK :=
  M.blowup (Scheme.IdealSheafData.vanishingIdeal Z) (isSpecialFibreCentre_vanishingIdeal M Z hZ)

/-- Blowing up a closed subset of the special fibre is a proper modification of models. -/
def blowupClosedModification (Z : Closeds M.total)
    (hZ : ∀ x ∈ Z, M.toBase x = dvrSpecialPoint R) :
    ModelModification (M.blowupClosed Z hZ) M :=
  M.blowupModification _ (isSpecialFibreCentre_vanishingIdeal M Z hZ)

end

/-! ### Finite sequences of blowups -/

/-- A finite sequence of blowups of models, each centred in the special fibre of the previous
model.  `BlowupChain M N` records that `N` is obtained from `M` by such a sequence. -/
inductive BlowupChain : Model R K C toK → Model R K C toK → Type (u + 1)
  | refl (M : Model R K C toK) : BlowupChain M M
  | step {M N : Model R K C toK} (I : M.total.IdealSheafData) (hI : IsSpecialFibreCentre M I)
      (tail : BlowupChain (M.blowup I hI) N) : BlowupChain M N

namespace BlowupChain

/-- The number of blowups in a chain. -/
def length {M N : Model R K C toK} : BlowupChain M N → ℕ
  | refl _ => 0
  | step _ _ tail => tail.length + 1

/-- The proper modification obtained by composing the blowups of a chain. -/
def modification {M N : Model R K C toK} : BlowupChain M N → ModelModification N M
  | refl M => ModelModification.refl M
  | step I hI tail => tail.modification.comp (M.blowupModification I hI)

@[simp]
theorem modification_refl (M : Model R K C toK) :
    (BlowupChain.refl M).modification = ModelModification.refl M := rfl

/-- A chain of blowups of a proper model ends at a proper model. -/
theorem isProper {M N : Model R K C toK} : BlowupChain M N → M.IsProper → N.IsProper
  | refl _, h => h
  | step I hI tail, h => tail.isProper (M.blowup_isProper I hI h)

/-- Chains of blowups concatenate. -/
def comp {M N P : Model R K C toK} : BlowupChain M N → BlowupChain N P → BlowupChain M P
  | refl _, second => second
  | step I hI tail, second => step I hI (tail.comp second)

theorem length_comp {M N P : Model R K C toK} (first : BlowupChain M N)
    (second : BlowupChain N P) :
    (first.comp second).length = first.length + second.length := by
  induction first with
  | refl => simp [comp, length]
  | step I hI tail ih => simp [comp, length, ih, Nat.add_right_comm]

end BlowupChain

end Model

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
