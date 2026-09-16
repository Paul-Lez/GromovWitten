/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.ReesAlgebra

/-!
# Affine cones and affine normal cones

For an ideal `I ⊆ R`, the affine normal cone is defined from the associated graded ring

`gr_I(R) = Rees_I(R) / I Rees_I(R)`.

The degree-`n` module is recorded separately as `I^n / I^(n+1)`.  The normal sheaf is the
abelian cone with coordinate algebra `Sym_{R/I}(I/I²)`.  Its contraction maps are built using
the universal property of the symmetric algebra, so the vertex and the `𝔸¹`-scaling action are
data rather than informal annotations.
-/

open CategoryTheory AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

namespace AffineCone

variable (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]

/-- Coordinate ring of the abelian cone attached to an `A`-module. -/
abbrev coordinateRing := SymmetricAlgebra A M

/-- The affine scheme underlying the abelian cone `C(M)`. -/
noncomputable abbrev scheme : _root_.AlgebraicGeometry.Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (coordinateRing A M))

/-- The augmentation of the symmetric algebra, defining the vertex. -/
abbrev augmentation : coordinateRing A M →ₐ[A] A :=
  SymmetricAlgebra.algebraMapInv

/-- The vertex of the affine abelian cone. -/
noncomputable abbrev vertex :
    _root_.AlgebraicGeometry.Spec (.of A) ⟶ scheme A M :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (augmentation A M).toRingHom)

/-- The projection of the affine abelian cone to its base. -/
noncomputable abbrev projection :
    scheme A M ⟶ _root_.AlgebraicGeometry.Spec (.of A) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap A (coordinateRing A M)))

/-- Scaling the degree-one generators by `r` defines contraction by `r`. -/
def contraction (r : A) : coordinateRing A M →ₐ[A] coordinateRing A M :=
  SymmetricAlgebra.lift (r • SymmetricAlgebra.ι A M)

@[simp]
theorem contraction_generator (r : A) (x : M) :
    contraction A M r (SymmetricAlgebra.ι A M x) =
      r • SymmetricAlgebra.ι A M x :=
  SymmetricAlgebra.lift_ι_apply _ _

@[simp]
theorem contraction_one : contraction A M 1 = AlgHom.id A (coordinateRing A M) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [contraction]

@[simp]
theorem contraction_mul (r s : A) :
    contraction A M (r * s) = (contraction A M r).comp (contraction A M s) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp [contraction, smul_smul, mul_comm]

/-- Contraction by zero factors through the vertex augmentation. -/
@[simp]
theorem contraction_zero :
    contraction A M 0 =
      (Algebra.ofId A (coordinateRing A M)).comp (augmentation A M) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  change contraction A M 0 (SymmetricAlgebra.ι A M x) =
    algebraMap A (coordinateRing A M) ((augmentation A M) (SymmetricAlgebra.ι A M x))
  rw [contraction_generator, zero_smul, SymmetricAlgebra.algebraMapInv_ι, map_zero]

/-- The symmetric algebra of a zero module is the base ring.  The hypothesis is stated as
`Subsingleton M`, so it applies to modules proved zero without replacing their carrier by a
special syntactic zero type. -/
noncomputable def coordinateRingEquivBase [Subsingleton M] :
    coordinateRing A M ≃ₐ[A] A :=
  AlgEquiv.ofAlgHom (augmentation A M)
    (Algebra.ofId A (coordinateRing A M))
    (by
      apply AlgHom.ext
      intro r
      simp [augmentation])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro x
      rw [Subsingleton.elim x 0]
      simp [augmentation])

/-- Consequently, the affine cone of a zero module is canonically isomorphic to its affine
base. -/
noncomputable def schemeIsoBase [Subsingleton M] :
    scheme A M ≅ _root_.AlgebraicGeometry.Spec (.of A) :=
  Scheme.Spec.mapIso (coordinateRingEquivBase A M).toCommRingCatIso.symm.op

/-- The isomorphism above is the vector-bundle projection itself; no unrelated affine-scheme
isomorphism was selected. -/
@[simp]
theorem schemeIsoBase_hom [Subsingleton M] :
    (schemeIsoBase A M).hom = projection A M := by
  change _root_.AlgebraicGeometry.Spec.map _ =
    _root_.AlgebraicGeometry.Spec.map _
  rw [_root_.AlgebraicGeometry.Spec.map_inj]
  rfl

/-- An `A`-valued point of the affine cone lying over the identity point of `Spec A`. -/
abbrev Section :=
  {s : _root_.AlgebraicGeometry.Spec (.of A) ⟶ scheme A M //
    s ≫ projection A M = 𝟙 (_root_.AlgebraicGeometry.Spec (.of A))}

/-- A zero affine cone has exactly one section over its base. -/
noncomputable instance sectionUnique [Subsingleton M] : Unique (Section A M) where
  default := ⟨(schemeIsoBase A M).inv, by
    simpa only [← schemeIsoBase_hom] using (schemeIsoBase A M).inv_hom_id⟩
  uniq s := by
    apply Subtype.ext
    apply (cancel_mono (schemeIsoBase A M).hom).1
    have hs : s.1 ≫ (schemeIsoBase A M).hom =
        𝟙 (_root_.AlgebraicGeometry.Spec (.of A)) := by
      simpa only [schemeIsoBase_hom] using s.property
    exact hs.trans (schemeIsoBase A M).inv_hom_id.symm

end AffineCone

namespace AffineNormalCone

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- For the identity closed immersion, whose ideal is zero, the Rees algebra consists exactly
of the constant polynomials.  This is proved coefficientwise from the definition of the Rees
algebra rather than recorded as presentation data. -/
theorem reesAlgebra_bot_eq :
    reesAlgebra (⊥ : Ideal R) = (⊥ : Subalgebra R (Polynomial R)) := by
  ext p
  constructor
  · intro hp
    rw [Algebra.mem_bot]
    refine ⟨p.coeff 0, ?_⟩
    apply Polynomial.ext
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hcoeff : p.coeff n = 0 := by
        have := hp n
        simpa [hn] using this
      change (Polynomial.C (p.coeff 0)).coeff n = p.coeff n
      rw [Polynomial.coeff_C_of_ne_zero hn, hcoeff]
  · intro hp
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hp
    exact (reesAlgebra (⊥ : Ideal R)).algebraMap_mem r

/-- The zero-ideal Rees algebra is canonically the original ring. -/
noncomputable def reesAlgebraBotEquiv :
    reesAlgebra (⊥ : Ideal R) ≃ₐ[R] R :=
  (Subalgebra.equivOfEq _ _ (reesAlgebra_bot_eq R)).trans
    (Algebra.botEquivOfInjective Polynomial.C_injective)

/-- The degree-`n` piece `I^n / I I^n`, canonically `I^n / I^(n+1)`. -/
abbrev GradedPiece (n : ℕ) : Type u :=
  (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))

/-- The conormal module `I/I²` is the degree-one input to the normal sheaf. -/
abbrev conormalModule : Type u := I.Cotangent

/-- The Rees-algebra presentation of `gr_I(R)`.  Extending `I` to the Rees algebra and
quotienting makes its degree-`n` piece equal to `I^n/I^(n+1)`. -/
abbrev associatedGradedRing : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I

/-- The associated graded ring of the zero ideal is canonically the base ring.  Both reductions
are explicit: extension of the zero ideal is zero, and the zero-ideal Rees algebra is the ring of
constant polynomials. -/
noncomputable def associatedGradedRingBotEquiv :
    associatedGradedRing R (⊥ : Ideal R) ≃+* R :=
  (Ideal.quotEquivOfEq (by simp)).trans <|
    (RingEquiv.quotientBot (reesAlgebra (⊥ : Ideal R))).trans
      (reesAlgebraBotEquiv R).toRingEquiv

/-- The affine normal cone `Spec(gr_I(R))`. -/
noncomputable abbrev scheme : _root_.AlgebraicGeometry.Scheme.{u} :=
  _root_.AlgebraicGeometry.Spec (.of (associatedGradedRing R I))

/-- The normal cone of the identity affine closed immersion is actually isomorphic to the
original affine scheme. -/
noncomputable def schemeBotIso :
    scheme R (⊥ : Ideal R) ≅ _root_.AlgebraicGeometry.Spec (.of R) :=
  Scheme.Spec.mapIso
    (associatedGradedRingBotEquiv R).toCommRingCatIso.symm.op

/-- Coordinate algebra of the affine normal sheaf `C(I/I²)`. -/
abbrev normalSheafCoordinateRing :=
  AffineCone.coordinateRing (R ⧸ I) I.Cotangent

/-- The affine normal sheaf associated with `I/I²`. -/
noncomputable abbrev normalSheaf : _root_.AlgebraicGeometry.Scheme.{u} :=
  AffineCone.scheme (R ⧸ I) I.Cotangent

/-- The degree-zero map `R/I → gr_I(R)`.  An element of `I` maps into the ideal by which
the Rees algebra is quotiented, so the structural map from `R` factors through `R/I`. -/
noncomputable def associatedGradedBaseRingHom :
    R ⧸ I →+* associatedGradedRing R I :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)).comp
      (algebraMap R (reesAlgebra I))) (by
        intro x hx
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) hx)

/-- The associated graded ring is canonically an algebra over the degree-zero quotient `R/I`.
This instance is induced by the actual Rees-algebra quotient map. -/
noncomputable instance associatedGradedAlgebra :
    Algebra (R ⧸ I) (associatedGradedRing R I) where
  algebraMap := associatedGradedBaseRingHom R I
  smul r x := associatedGradedBaseRingHom R I r * x
  commutes' r x := mul_comm (associatedGradedBaseRingHom R I r) x
  smul_def' _ _ := rfl

/-- The `R/I`-algebra structure above is compatible with the original `R`-algebra structure. -/
noncomputable instance associatedGradedIsScalarTower :
    IsScalarTower R (R ⧸ I) (associatedGradedRing R I) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The degree-one Rees element `x t` associated with `x ∈ I`. -/
noncomputable def degreeOneRees : I →ₗ[R] reesAlgebra I :=
  LinearMap.codRestrict (reesAlgebra I).toSubmodule
    ((Polynomial.monomial 1 : R →ₗ[R] Polynomial R).comp I.subtype) (by
      intro x
      apply reesAlgebra.monomial_mem.mpr
      change (x : R) ∈ I ^ 1
      simpa only [pow_one] using x.2)

/-- Send a generator of `I` to its degree-one class in `gr_I(R)`. -/
noncomputable def degreeOneRaw :
    I →ₗ[R] associatedGradedRing R I :=
  (Ideal.Quotient.mkₐ R
    (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap.comp
      (degreeOneRees R I)

/-- Products of two elements of `I` vanish in the degree-one quotient.  This is the concrete
calculation which makes the preceding map descend from `I` to `I/I²`. -/
theorem degreeOneRaw_mul (x y : I) : degreeOneRaw R I (x * y) = 0 := by
  change Ideal.Quotient.mk _ (degreeOneRees R I (x * y)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  let q : reesAlgebra I := degreeOneRees R I y
  have hx : algebraMap R (reesAlgebra I) x.1 ∈
      Ideal.map (algebraMap R (reesAlgebra I)) I :=
    Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) x.2
  have hprod := Ideal.mul_mem_right q
    (Ideal.map (algebraMap R (reesAlgebra I)) I) hx
  convert hprod using 1
  apply Subtype.ext
  exact Polynomial.C_mul_monomial.symm

/-- The canonical `R/I`-linear map from the conormal module to the degree-one part of the
associated graded ring. -/
noncomputable def conormalToAssociatedGraded :
    I.Cotangent →ₗ[R ⧸ I] associatedGradedRing R I :=
  (Ideal.Cotangent.lift (degreeOneRaw R I)
    (degreeOneRaw_mul R I)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective

/-- If two elements of the ideal have zero product in the ambient ring, then the product of
their canonical degree-one classes is zero in the associated graded ring.  The proof computes
inside the Rees algebra; this is not a presentation-level relation supplied by a caller. -/
theorem conormalToAssociatedGraded_mul_eq_zero_of_mul_eq_zero
    (x y : I) (hxy : (x : R) * (y : R) = 0) :
    conormalToAssociatedGraded R I (I.toCotangent x) *
        conormalToAssociatedGraded R I (I.toCotangent y) = 0 := by
  unfold conormalToAssociatedGraded
  rw [LinearMap.extendScalarsOfSurjective_apply,
    LinearMap.extendScalarsOfSurjective_apply,
    Ideal.Cotangent.lift_toCotangent,
    Ideal.Cotangent.lift_toCotangent]
  change Ideal.Quotient.mk _ (degreeOneRees R I x) *
      Ideal.Quotient.mk _ (degreeOneRees R I y) = 0
  rw [← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hzero : degreeOneRees R I x * degreeOneRees R I y = 0 := by
    apply Subtype.ext
    change Polynomial.monomial 1 (x : R) * Polynomial.monomial 1 (y : R) = 0
    rw [Polynomial.monomial_mul_monomial, hxy]
    simp
  rw [hzero]
  exact Ideal.zero_mem _

/-- The degree-one Rees element attached to `z ∈ I` is the monomial `z t`. -/
@[simp]
theorem degreeOneRees_coe (z : I) :
    ((degreeOneRees R I z : reesAlgebra I) : Polynomial R) =
      Polynomial.monomial 1 (z : R) :=
  rfl

/-- The canonical degree-one map sends the conormal class of `z ∈ I` to the class of the Rees
element `z t`. -/
@[simp]
theorem conormalToAssociatedGraded_toCotangent (z : I) :
    conormalToAssociatedGraded R I (I.toCotangent z) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        (degreeOneRees R I z) := by
  unfold conormalToAssociatedGraded
  rw [LinearMap.extendScalarsOfSurjective_apply, Ideal.Cotangent.lift_toCotangent]
  rfl

/-- Membership in `I · Rees_I(R)` is detected coefficientwise: the `m`-th coefficient of such an
element already lies in `I ^ (m + 1)`.  This is the concrete description of the degree-`m` part
of `gr_I(R)` as `I^m / I^(m+1)`. -/
theorem coeff_mem_pow_succ_of_mem_map_rees :
    ∀ {q : reesAlgebra I}, q ∈ Ideal.map (algebraMap R (reesAlgebra I)) I →
      ∀ m : ℕ, (q : Polynomial R).coeff m ∈ I ^ (m + 1) := by
  intro q hq
  have hq' : q ∈ Submodule.span (reesAlgebra I)
      ((algebraMap R (reesAlgebra I)) '' (I : Set R)) := hq
  refine Submodule.span_induction
    (p := fun (y : reesAlgebra I) _ => ∀ m : ℕ, (y : Polynomial R).coeff m ∈ I ^ (m + 1))
    ?_ ?_ ?_ ?_ hq'
  · rintro y ⟨r, hr, rfl⟩ m
    have hcoe : ((algebraMap R (reesAlgebra I) r : reesAlgebra I) : Polynomial R) =
        Polynomial.C r := rfl
    rcases eq_or_ne m 0 with rfl | hm
    · rw [hcoe, Polynomial.coeff_C, if_pos rfl, pow_one]
      exact hr
    · rw [hcoe, Polynomial.coeff_C, if_neg hm]
      exact Submodule.zero_mem _
  · intro m
    simp
  · intro y z _ _ ihy ihz m
    have hcoe : ((y + z : reesAlgebra I) : Polynomial R) =
        (y : Polynomial R) + (z : Polynomial R) := rfl
    rw [hcoe, Polynomial.coeff_add]
    exact Ideal.add_mem _ (ihy m) (ihz m)
  · intro a y _ ihy m
    have hcoe : ((a • y : reesAlgebra I) : Polynomial R) =
        (a : Polynomial R) * (y : Polynomial R) := rfl
    rw [hcoe, Polynomial.coeff_mul]
    refine Ideal.sum_mem _ fun ij hij => ?_
    have hija : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
    have ha : (a : Polynomial R).coeff ij.1 ∈ I ^ ij.1 :=
      (mem_reesAlgebra_iff I _).mp a.2 ij.1
    have hprod := Ideal.mul_mem_mul ha (ihy ij.2)
    rw [← pow_add] at hprod
    have hexp : ij.1 + (ij.2 + 1) = m + 1 := by omega
    rwa [hexp] at hprod

/-- The degree-zero augmentation `gr_I(R) → R/I`, extracting the constant coefficient of a Rees
element.  It is well defined because the constant coefficient of an element of `I · Rees_I(R)`
lies in `I`; it is the algebraic counterpart of the vertex of the normal cone. -/
noncomputable def associatedGradedAugmentation :
    associatedGradedRing R I →+* R ⧸ I :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk I).comp
      ((Polynomial.evalRingHom 0).comp (reesAlgebra I).val.toRingHom)) (by
      intro q hq
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      have h0 := coeff_mem_pow_succ_of_mem_map_rees R I hq 0
      rw [pow_one] at h0
      rw [RingHom.comp_apply]
      change Polynomial.eval 0 ((q : reesAlgebra I) : Polynomial R) ∈ I
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact h0)

@[simp]
theorem associatedGradedAugmentation_mk (q : reesAlgebra I) :
    associatedGradedAugmentation R I
        (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I) q) =
      Ideal.Quotient.mk I ((q : Polynomial R).coeff 0) := by
  change Ideal.Quotient.mk I (Polynomial.eval 0 ((q : reesAlgebra I) : Polynomial R)) = _
  rw [← Polynomial.coeff_zero_eq_eval_zero]

/-- The augmentation is a retraction of the degree-zero structural map. -/
@[simp]
theorem associatedGradedAugmentation_base (r : R ⧸ I) :
    associatedGradedAugmentation R I (associatedGradedBaseRingHom R I r) = r := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change associatedGradedAugmentation R I
    (Ideal.Quotient.mk _ (algebraMap R (reesAlgebra I) r)) = _
  rw [associatedGradedAugmentation_mk]
  have hcoe : ((algebraMap R (reesAlgebra I) r : reesAlgebra I) : Polynomial R) =
      Polynomial.C r := rfl
  rw [hcoe, Polynomial.coeff_C, if_pos rfl]

/-- The projection of the affine normal cone onto its base `Spec (R/I)`. -/
noncomputable abbrev projection :
    scheme R I ⟶ _root_.AlgebraicGeometry.Spec (.of (R ⧸ I)) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (associatedGradedBaseRingHom R I))

/-- The vertex of the affine normal cone, induced by the degree-zero augmentation. -/
noncomputable abbrev vertex :
    _root_.AlgebraicGeometry.Spec (.of (R ⧸ I)) ⟶ scheme R I :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (associatedGradedAugmentation R I))

/- Quotient rings currently expose several propositionally equal but not definitionally equal
inherited semiring instances.  This reducible algebra uses exactly the `CommRing` parents that
occur in `normalSheafCoordinateRing`, allowing the symmetric-algebra universal property to be
applied without changing the underlying rings or maps. -/
private noncomputable abbrev associatedGradedLiftAlgebra :
    @Algebra (R ⧸ I) (associatedGradedRing R I)
      (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I))
      (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _
        (Ideal.Quotient.commRing
          (Ideal.map (algebraMap R (reesAlgebra I)) I)))) where
  algebraMap := {
    toFun := associatedGradedBaseRingHom R I
    map_one' := (associatedGradedBaseRingHom R I).map_one
    map_mul' := (associatedGradedBaseRingHom R I).map_mul
    map_zero' := (associatedGradedBaseRingHom R I).map_zero
    map_add' := (associatedGradedBaseRingHom R I).map_add }
  smul r x := associatedGradedBaseRingHom R I r * x
  commutes' r x := mul_comm (associatedGradedBaseRingHom R I r) x
  smul_def' _ _ := rfl

/-- The canonical coordinate-ring map from the normal sheaf to the normal cone.  It is obtained
by extending the actual degree-one map `I/I² → gr_I(R)` through the universal property of the
symmetric algebra; it is not presentation data. -/
noncomputable def normalSheafCoordinateMap :
    normalSheafCoordinateRing R I →+* associatedGradedRing R I := by
  let f := @SymmetricAlgebra.lift (R ⧸ I) I.Cotangent
    (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _
    (Ideal.instModuleQuotientCotangent I) (associatedGradedRing R I)
    (@CommRing.toCommSemiring _
      (Ideal.Quotient.commRing
        (Ideal.map (algebraMap R (reesAlgebra I)) I)))
    (associatedGradedLiftAlgebra R I) (conormalToAssociatedGraded R I)
  exact f.toRingHom

/-- The canonical coordinate map sends a symmetric-algebra generator to its actual
degree-one Rees class. -/
@[simp]
theorem normalSheafCoordinateMap_ι (x : I.Cotangent) :
    normalSheafCoordinateMap R I
        (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent x) =
      conormalToAssociatedGraded R I x := by
  unfold normalSheafCoordinateMap
  exact SymmetricAlgebra.lift_ι_apply _ x

/-- The canonical coordinate map restricts in degree zero to the constructed structural map. -/
theorem normalSheafCoordinateMap_base (r : R ⧸ I) :
    normalSheafCoordinateMap R I
        (algebraMap (R ⧸ I) (normalSheafCoordinateRing R I) r) =
      associatedGradedBaseRingHom R I r := by
  unfold normalSheafCoordinateMap
  let f := @SymmetricAlgebra.lift (R ⧸ I) I.Cotangent
    (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _
    (Ideal.instModuleQuotientCotangent I) (associatedGradedRing R I)
    (@CommRing.toCommSemiring _
      (Ideal.Quotient.commRing
        (Ideal.map (algebraMap R (reesAlgebra I)) I)))
    (associatedGradedLiftAlgebra R I) (conormalToAssociatedGraded R I)
  exact f.commutes r

/-- The canonical normal-sheaf coordinate map is surjective.  The proof uses that the Rees
algebra is generated by the degree-one monomials `x t`: those are images of conormal generators,
while constants are images through the `R/I`-algebra structure. -/
theorem normalSheafCoordinateMap_surjective :
    Function.Surjective (normalSheafCoordinateMap R I) := by
  let f := @SymmetricAlgebra.lift (R ⧸ I) I.Cotangent
    (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _
    (Ideal.instModuleQuotientCotangent I) (associatedGradedRing R I)
    (@CommRing.toCommSemiring _
      (Ideal.Quotient.commRing
        (Ideal.map (algebraMap R (reesAlgebra I)) I)))
    (associatedGradedLiftAlgebra R I) (conormalToAssociatedGraded R I)
  change Function.Surjective f
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  let generators : Set (Polynomial R) :=
    Submodule.map (Polynomial.monomial 1 : R →ₗ[R] Polynomial R) I
  have hgenerated : Algebra.adjoin R generators = reesAlgebra I :=
    adjoin_monomial_eq_reesAlgebra I
  have toRees {p : Polynomial R} (hp : p ∈ Algebra.adjoin R generators) :
      p ∈ reesAlgebra I := by
    rw [← hgenerated]
    exact hp
  let P : (p : Polynomial R) → p ∈ Algebra.adjoin R generators → Prop :=
    fun p hp ↦ ∃ s, f s = Ideal.Quotient.mk _
      (⟨p, toRees hp⟩ : reesAlgebra I)
  have hp : (p : Polynomial R) ∈ Algebra.adjoin R generators := by
    rw [hgenerated]
    exact p.2
  have hP : ∀ (a : Polynomial R) (ha : a ∈ Algebra.adjoin R generators), P a ha := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
        rcases ha with ⟨x, hx, rfl⟩
        let ix : I := ⟨x, hx⟩
        refine ⟨@SymmetricAlgebra.ι (R ⧸ I) I.Cotangent
          (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _
          (Ideal.instModuleQuotientCotangent I) (I.toCotangent ix), ?_⟩
        rw [SymmetricAlgebra.lift_ι_apply]
        rfl
    | algebraMap r =>
        let s : @SymmetricAlgebra (R ⧸ I) I.Cotangent
            (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _
            (Ideal.instModuleQuotientCotangent I) :=
          @algebraMap (R ⧸ I) _
            (@CommRing.toCommSemiring _ (Ideal.Quotient.commRing I)) _ _
            (Ideal.Quotient.mk I r)
        refine ⟨s, ?_⟩
        exact (f.commutes (Ideal.Quotient.mk I r)).trans rfl
    | add x y hx hy ihx ihy =>
        obtain ⟨sx, hsx⟩ := ihx
        obtain ⟨sy, hsy⟩ := ihy
        refine ⟨sx + sy, ?_⟩
        rw [map_add, hsx, hsy]
        rfl
    | mul x y hx hy ihx ihy =>
        obtain ⟨sx, hsx⟩ := ihx
        obtain ⟨sy, hsy⟩ := ihy
        refine ⟨sx * sy, ?_⟩
        rw [map_mul, hsx, hsy]
        rfl
  exact hP (p : Polynomial R) hp

/-- The affine normal cone maps to the affine normal sheaf by the canonical degree-one Rees
map on coordinate rings. -/
noncomputable def coneToNormalSheaf : scheme R I ⟶ normalSheaf R I :=
  Scheme.Spec.map (CommRingCat.ofHom (normalSheafCoordinateMap R I)).op

/-- The canonical affine normal-cone morphism is a closed immersion because its coordinate-ring
map is the proved surjection `Sym(I/I²) → gr_I(R)`. -/
noncomputable instance coneToNormalSheaf_isClosedImmersion :
    _root_.AlgebraicGeometry.IsClosedImmersion (coneToNormalSheaf R I) := by
  apply _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
  exact normalSheafCoordinateMap_surjective R I

/-- Substituting `r t` for `t` in a polynomial.  This is the algebraic `𝔸¹`-scaling action on
the Rees algebra, which descends to the associated graded ring. -/
noncomputable def reesScaleAux (r : R) : Polynomial R →ₐ[R] Polynomial R :=
  Polynomial.aeval (Polynomial.C r * Polynomial.X)

theorem reesScaleAux_monomial (r a : R) (m : ℕ) :
    reesScaleAux R r (Polynomial.monomial m a) = Polynomial.monomial m (r ^ m * a) := by
  rw [reesScaleAux, Polynomial.aeval_monomial, mul_pow, ← Polynomial.C_pow,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [show (algebraMap R (Polynomial R)) a = Polynomial.C a from rfl]
  rw [← mul_assoc, ← Polynomial.C_mul, mul_comm a (r ^ m)]

theorem reesScaleAux_coeff (r : R) (p : Polynomial R) (n : ℕ) :
    (reesScaleAux R r p).coeff n = r ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial m a =>
      rw [reesScaleAux_monomial, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : m = n
      · subst h
        simp
      · simp [h]

theorem reesScaleAux_mem (r : R) {p : Polynomial R} (hp : p ∈ reesAlgebra I) :
    reesScaleAux R r p ∈ reesAlgebra I := by
  rw [mem_reesAlgebra_iff] at hp ⊢
  intro n
  rw [reesScaleAux_coeff]
  exact Ideal.mul_mem_left _ _ (hp n)

/-- The `𝔸¹`-scaling action on the Rees algebra of `I`. -/
noncomputable def reesScale (r : R) : reesAlgebra I →ₐ[R] reesAlgebra I :=
  AlgHom.codRestrict ((reesScaleAux R r).comp (reesAlgebra I).val) (reesAlgebra I)
    (fun p => reesScaleAux_mem R I r p.2)

@[simp]
theorem reesScale_coe (r : R) (q : reesAlgebra I) :
    ((reesScale R I r q : reesAlgebra I) : Polynomial R) =
      reesScaleAux R r (q : Polynomial R) :=
  rfl

theorem reesScale_algebraMap (r s : R) :
    reesScale R I r (algebraMap R (reesAlgebra I) s) = algebraMap R (reesAlgebra I) s :=
  (reesScale R I r).commutes s

theorem reesScale_degreeOneRees (r : R) (w : I) :
    reesScale R I r (degreeOneRees R I w) =
      algebraMap R (reesAlgebra I) r * degreeOneRees R I w := by
  apply Subtype.ext
  rw [reesScale_coe, degreeOneRees_coe, reesScaleAux_monomial, pow_one]
  change _ = Polynomial.C r * Polynomial.monomial 1 (w : R)
  rw [Polynomial.C_mul_monomial]

/-- The `𝔸¹`-scaling action descends to the associated graded ring: the ideal `I · Rees_I(R)` is
preserved because the scaling fixes constants. -/
noncomputable def associatedGradedScale (r : R) :
    associatedGradedRing R I →+* associatedGradedRing R I :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)).comp
      (reesScale R I r).toRingHom) (by
      intro q hq
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      have hle : Ideal.map (algebraMap R (reesAlgebra I)) I ≤
          Ideal.comap (reesScale R I r).toRingHom
            (Ideal.map (algebraMap R (reesAlgebra I)) I) := by
        rw [Ideal.map_le_iff_le_comap]
        intro s hs
        rw [Ideal.mem_comap, Ideal.mem_comap]
        change reesScale R I r (algebraMap R (reesAlgebra I) s) ∈ _
        rw [reesScale_algebraMap]
        exact Ideal.mem_map_of_mem _ hs
      exact hle hq)

@[simp]
theorem associatedGradedScale_mk (r : R) (q : reesAlgebra I) :
    associatedGradedScale R I r
        (Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I) q) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R (reesAlgebra I)) I)
        (reesScale R I r q) :=
  rfl

/-- The canonical coordinate map intertwines the `𝔸¹`-contraction of the normal sheaf with the
`𝔸¹`-scaling of the normal cone. -/
theorem normalSheafCoordinateMap_contraction (r : R)
    (z : normalSheafCoordinateRing R I) :
    normalSheafCoordinateMap R I
        (AffineCone.contraction (R ⧸ I) I.Cotangent (Ideal.Quotient.mk I r) z) =
      associatedGradedScale R I r (normalSheafCoordinateMap R I z) := by
  induction z using SymmetricAlgebra.induction with
  | algebraMap s =>
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [AlgHom.commutes, normalSheafCoordinateMap_base]
      change _ = associatedGradedScale R I r
        (Ideal.Quotient.mk _ (algebraMap R (reesAlgebra I) s))
      rw [associatedGradedScale_mk, reesScale_algebraMap]
      rfl
  | ι m =>
      obtain ⟨w, rfl⟩ := I.toCotangent_surjective m
      rw [AffineCone.contraction_generator, Algebra.smul_def, map_mul,
        normalSheafCoordinateMap_base, normalSheafCoordinateMap_ι,
        conormalToAssociatedGraded_toCotangent, associatedGradedScale_mk,
        reesScale_degreeOneRees, map_mul]
      rfl
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The canonical coordinate map intertwines the vertex augmentation of the normal sheaf with
the degree-zero augmentation of the normal cone. -/
theorem associatedGradedAugmentation_normalSheafCoordinateMap
    (z : normalSheafCoordinateRing R I) :
    associatedGradedAugmentation R I (normalSheafCoordinateMap R I z) =
      AffineCone.augmentation (R ⧸ I) I.Cotangent z := by
  induction z using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [normalSheafCoordinateMap_base, associatedGradedAugmentation_base]
      exact ((AffineCone.augmentation (R ⧸ I) I.Cotangent).commutes r).symm
  | ι m =>
      obtain ⟨w, rfl⟩ := I.toCotangent_surjective m
      rw [normalSheafCoordinateMap_ι, conormalToAssociatedGraded_toCotangent,
        associatedGradedAugmentation_mk, SymmetricAlgebra.algebraMapInv_ι,
        degreeOneRees_coe, Polynomial.coeff_monomial, if_neg (by decide), map_zero]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/-- The canonical cone morphism commutes with the projections to the base `Spec (R/I)`. -/
theorem coneToNormalSheaf_comp_projection :
    coneToNormalSheaf R I ≫ AffineCone.projection (R ⧸ I) I.Cotangent =
      projection R I := by
  change _root_.AlgebraicGeometry.Spec.map _ ≫ _root_.AlgebraicGeometry.Spec.map _ =
    _root_.AlgebraicGeometry.Spec.map _
  rw [← _root_.AlgebraicGeometry.Spec.map_comp,
    _root_.AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact normalSheafCoordinateMap_base R I r

/-- The canonical cone morphism carries the vertex of the normal cone to the vertex of the
normal sheaf. -/
theorem vertex_comp_coneToNormalSheaf :
    vertex R I ≫ coneToNormalSheaf R I =
      AffineCone.vertex (R ⧸ I) I.Cotangent := by
  change _root_.AlgebraicGeometry.Spec.map _ ≫ _root_.AlgebraicGeometry.Spec.map _ =
    _root_.AlgebraicGeometry.Spec.map _
  rw [← _root_.AlgebraicGeometry.Spec.map_comp,
    _root_.AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact associatedGradedAugmentation_normalSheafCoordinateMap R I z

/-- The explicit zero-ideal associated-graded equivalence carries its degree-zero structural
map back to the original element of `R`. -/
@[simp]
theorem associatedGradedRingBotEquiv_base_mk (r : R) :
    associatedGradedRingBotEquiv R
        (associatedGradedBaseRingHom R (⊥ : Ideal R)
          (Ideal.Quotient.mk ⊥ r)) = r := by
  simp only [associatedGradedBaseRingHom, Ideal.Quotient.lift_mk,
    associatedGradedRingBotEquiv, RingEquiv.trans_apply]
  exact (reesAlgebraBotEquiv R).commutes r

/-- In degree zero for the identity ideal, the canonical map is injective.  This is proved by
the two explicit quotient-to-base equivalences, not postulated as the regular-embedding
comparison theorem. -/
private theorem associatedGradedBaseRingHom_bot_injective :
    Function.Injective
      (associatedGradedBaseRingHom R (⊥ : Ideal R)) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply (RingEquiv.quotientBot R).injective
  have h := congrArg (associatedGradedRingBotEquiv R) hxy
  rw [associatedGradedRingBotEquiv_base_mk,
    associatedGradedRingBotEquiv_base_mk] at h
  exact h

/-- For the identity ideal the canonical normal-sheaf map is injective.  Every element of the
symmetric algebra is a degree-zero element because `I/I²` is the zero module, and the degree-zero
map was proved injective above. -/
theorem normalSheafCoordinateMap_bot_injective :
    Function.Injective
      (normalSheafCoordinateMap R (⊥ : Ideal R)) := by
  let _ : Subsingleton (conormalModule R (⊥ : Ideal R)) := by
    change Subsingleton ((⊥ : Ideal R) ⧸
      ((⊥ : Ideal R) • ⊤ : Submodule R (⊥ : Ideal R)))
    infer_instance
  have existsBase (z : normalSheafCoordinateRing R (⊥ : Ideal R)) :
      ∃ r : R ⧸ (⊥ : Ideal R),
        z = algebraMap (R ⧸ (⊥ : Ideal R))
          (normalSheafCoordinateRing R (⊥ : Ideal R)) r := by
    induction z using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨r, rfl⟩
    | ι m =>
        rw [Subsingleton.elim m 0, map_zero]
        exact ⟨0, by simp⟩
    | mul x y hx hy =>
        obtain ⟨rx, rfl⟩ := hx
        obtain ⟨ry, rfl⟩ := hy
        exact ⟨rx * ry, by simp⟩
    | add x y hx hy =>
        obtain ⟨rx, rfl⟩ := hx
        obtain ⟨ry, rfl⟩ := hy
        exact ⟨rx + ry, by simp⟩
  intro x y hxy
  obtain ⟨rx, hx⟩ := existsBase x
  obtain ⟨ry, hy⟩ := existsBase y
  rw [hx, hy, normalSheafCoordinateMap_base,
    normalSheafCoordinateMap_base] at hxy
  have hr := associatedGradedBaseRingHom_bot_injective R hxy
  calc
    x = algebraMap (R ⧸ (⊥ : Ideal R))
        (normalSheafCoordinateRing R (⊥ : Ideal R)) rx := hx
    _ = algebraMap (R ⧸ (⊥ : Ideal R))
        (normalSheafCoordinateRing R (⊥ : Ideal R)) ry := congrArg _ hr
    _ = y := hy.symm

/-- The normal cone of the identity immersion is canonically its normal sheaf.  The equivalence
is built from the same Rees coordinate map used for every ideal. -/
noncomputable def normalSheafCoordinateMapBotEquiv :
    normalSheafCoordinateRing R (⊥ : Ideal R) ≃+*
      associatedGradedRing R (⊥ : Ideal R) :=
  RingEquiv.ofBijective (normalSheafCoordinateMap R (⊥ : Ideal R))
    ⟨normalSheafCoordinateMap_bot_injective R,
      normalSheafCoordinateMap_surjective R (⊥ : Ideal R)⟩

/-- On affine schemes, the canonical coordinate-ring equivalence identifies the normal cone of
the identity immersion with its normal sheaf. -/
noncomputable def schemeBotIsoNormalSheaf :
    scheme R (⊥ : Ideal R) ≅ normalSheaf R (⊥ : Ideal R) :=
  Scheme.Spec.mapIso
    (normalSheafCoordinateMapBotEquiv R).toCommRingCatIso.op

/-- For the identity ideal, the general canonical cone morphism is the hom of the coordinate
equivalence proved above. -/
@[simp]
theorem schemeBotIsoNormalSheaf_hom :
    (schemeBotIsoNormalSheaf R).hom =
      coneToNormalSheaf R (⊥ : Ideal R) :=
  by
    change _root_.AlgebraicGeometry.Spec.map _ =
      _root_.AlgebraicGeometry.Spec.map _
    rw [_root_.AlgebraicGeometry.Spec.map_inj]
    rfl

/-- The degree-one piece is definitionally the same quotient construction as the cotangent
module, after simplifying `I^1 = I`. -/
noncomputable def gradedPieceOneEquivConormal :
    GradedPiece R I 1 ≃ₗ[R] I.Cotangent := by
  change ((I ^ 1 : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ 1 : Ideal R))) ≃ₗ[R]
    (I ⧸ (I • ⊤ : Submodule R I))
  rw [show (I ^ 1 : Ideal R) = I by simp]

/-- The conormal module of the identity embedding is zero. -/
instance conormalModuleBotSubsingleton :
    Subsingleton (conormalModule R (⊥ : Ideal R)) := by
  change Subsingleton ((⊥ : Ideal R) ⧸
    ((⊥ : Ideal R) • ⊤ : Submodule R (⊥ : Ideal R)))
  infer_instance

theorem conormalModule_bot_eq_zero
    (x : conormalModule R (⊥ : Ideal R)) : x = 0 :=
  Subsingleton.elim _ _

/-- The normal sheaf of the identity affine embedding is the rank-zero cone over the base. -/
noncomputable def normalSheafBotIso :
    normalSheaf R (⊥ : Ideal R) ≅ _root_.AlgebraicGeometry.Spec (.of R) :=
  (AffineCone.schemeIsoBase (R ⧸ (⊥ : Ideal R))
    (conormalModule R (⊥ : Ideal R))).trans
      (Scheme.Spec.mapIso
        (RingEquiv.quotientBot R).toCommRingCatIso.symm.op)

/-- The canonical Rees normal-cone map, followed by the rank-zero normal-sheaf projection,
is the explicit zero-ideal associated-graded identification. -/
@[simp]
theorem schemeBotIsoNormalSheaf_hom_comp_normalSheafBotIso_hom :
    (schemeBotIsoNormalSheaf R).hom ≫ (normalSheafBotIso R).hom =
      (schemeBotIso R).hom := by
  simp only [schemeBotIsoNormalSheaf, normalSheafBotIso, schemeBotIso,
    Iso.trans_hom, AffineCone.schemeIsoBase_hom]
  change _root_.AlgebraicGeometry.Spec.map _ ≫
      _root_.AlgebraicGeometry.Spec.map _ ≫
        _root_.AlgebraicGeometry.Spec.map _ =
    _root_.AlgebraicGeometry.Spec.map _
  rw [← _root_.AlgebraicGeometry.Spec.map_comp,
    ← _root_.AlgebraicGeometry.Spec.map_comp,
    _root_.AlgebraicGeometry.Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp only [CategoryTheory.comp_apply, Iso.op_hom, Iso.symm_hom,
    Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_hom,
    RingEquiv.toCommRingCatIso_inv]
  change normalSheafCoordinateMapBotEquiv R
      (algebraMap (R ⧸ (⊥ : Ideal R))
        (normalSheafCoordinateRing R (⊥ : Ideal R))
        ((RingEquiv.quotientBot R).symm r)) =
    (associatedGradedRingBotEquiv R).symm r
  apply (associatedGradedRingBotEquiv R).injective
  rw [RingEquiv.apply_symm_apply]
  change associatedGradedRingBotEquiv R
      (normalSheafCoordinateMap R (⊥ : Ideal R)
        (algebraMap (R ⧸ (⊥ : Ideal R))
          (normalSheafCoordinateRing R (⊥ : Ideal R))
          (Ideal.Quotient.mk ⊥ r))) = r
  rw [normalSheafCoordinateMap_base,
    associatedGradedRingBotEquiv_base_mk]

end AffineNormalCone

end GromovWitten.AlgebraicGeometry
