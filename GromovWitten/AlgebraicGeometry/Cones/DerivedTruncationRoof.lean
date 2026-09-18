/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Cones.DerivedTruncation
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Resolution independence of `h¹/h⁰` without projectivity

`Cones/DerivedTruncation.lean` proves that the Picard groupoid of the two-term truncation of a
representative of a derived object does not depend on the representative, *provided* the
representative is K-projective.  This file removes that hypothesis by using the calculus of
fractions of the derived category.

## Main results

* `LinearTwoTermComplex.nonempty_truncQuotientEquivalence_of_Q_iso`: for any two cochain
  complexes `K`, `K'` of `R`-modules with `K.d 0 1 = 0` and `K'.d 0 1 = 0` whose images in the
  derived category are isomorphic, the Picard groupoids of the two-term truncations are
  equivalent.  The proof writes the isomorphism as a roof `K ← N → K'` of quasi-isomorphisms
  (`DerivedCategory.right_fac`, which uses the calculus of fractions of
  `HomotopyCategory.quasiIso`) and replaces `N` by `τ≤0 N`, which changes nothing in degrees
  `≤ 0` (`CochainComplex.quasiIsoAt_ιTruncLE`) and has no differential out of degree `0`
  (`truncLE_d_zero_one_eq_zero`).
* `TruncRep E`: a *truncation representative* of a derived object — any complex with `d⁰ = 0`
  representing `E` — with `TruncRep.picard` its Picard groupoid,
  `TruncRep.nonempty_picardEquivalence` the projectivity-free independence statement, and
  `TruncRep.vertexAutEquiv` identifying the vertex automorphisms with `H⁻¹`.
* `LinearTwoTermComplex.exists_rep_d_zero_one_eq_zero` and `TruncRep.ofIsLE`: a complex with no
  cohomology in positive degrees has such a representative, namely its canonical truncation
  `τ≤0`; so every derived object without positive cohomology has a `TruncRep`.
* `TruncPresentation.toTruncRep` and `TruncPresentation.nonempty_picardEquivalence_truncRep`,
  `CotangentComplex.PerfectComplex.GlobalTwoTermResolution.nonempty_picardEquivalence_truncRep`:
  compatibility with the K-projective presentations of `Cones/DerivedTruncation.lean` and with
  the two-term resolutions of `Cones/DerivedPicard.lean`.

The hypothesis `d 0 1 = 0` on both complexes cannot be removed: `h¹` of the truncation is the
cokernel of `d⁻¹`, which is `H⁰` only under that assumption (see `Cones/DerivedTruncation.lean`).
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace GromovWitten.AlgebraicGeometry

namespace LinearTwoTermComplex

variable {R : Type u} [CommRing R]

section Roof

attribute [local instance] HasDerivedCategory.standard

/-- A complex which is strictly supported in degrees `≤ 0` has no differential out of degree
`0`, so its two-term truncation computes `H⁻¹` and `H⁰`. -/
theorem d_zero_one_eq_zero_of_isStrictlyLE (K : CochainComplex (ModuleCat.{u} R) ℤ)
    [K.IsStrictlyLE 0] : K.d 0 1 = 0 :=
  (K.isZero_of_isStrictlyLE 0 1).eq_of_tgt _ _

/-- The canonical truncation `τ≤0 K` has no differential out of degree `0`. -/
theorem truncLE_d_zero_one_eq_zero (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (K.truncLE 0).d 0 1 = 0 :=
  d_zero_one_eq_zero_of_isStrictlyLE _

/-- **The two-term truncation only depends on the class in the derived category.**  Two
cochain complexes with no differential out of degree `0` whose images in the derived category
are isomorphic have equivalent Picard groupoids of two-term truncations.  No projectivity,
boundedness or finiteness hypothesis is needed: the isomorphism is represented by a roof
`K ← N → K'` of quasi-isomorphisms by the calculus of fractions, and `N` is replaced by its
canonical truncation `τ≤0 N`, which does not change anything in degrees `≤ 0`. -/
theorem nonempty_truncQuotientEquivalence_of_Q_iso
    (K K' : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.d 0 1 = 0) (hK' : K'.d 0 1 = 0)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K') :
    Nonempty ((twoTermTrunc K).quotient ≌ (twoTermTrunc K').quotient) := by
  obtain ⟨N, s, hs, g, hfac⟩ := DerivedCategory.right_fac e.hom
  have hgmap : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
    rw [hfac, IsIso.hom_inv_id_assoc]
  have hg : IsIso (DerivedCategory.Q.map g) := by
    rw [hgmap]
    infer_instance
  have hqs : QuasiIso s := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hs
  have hqg : QuasiIso g := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hg
  have hiNegOne : QuasiIsoAt (N.ιTruncLE 0) (-1) :=
    CochainComplex.quasiIsoAt_ιTruncLE N 0 (-1) (by norm_num)
  have hiZero : QuasiIsoAt (N.ιTruncLE 0) 0 :=
    CochainComplex.quasiIsoAt_ιTruncLE N 0 0 (by norm_num)
  have hsNegOne : QuasiIsoAt s (-1) := hqs.quasiIsoAt (-1)
  have hsZero : QuasiIsoAt s 0 := hqs.quasiIsoAt 0
  have hgNegOne : QuasiIsoAt g (-1) := hqg.quasiIsoAt (-1)
  have hgZero : QuasiIsoAt g 0 := hqg.quasiIsoAt 0
  have hN : (N.truncLE 0).d 0 1 = 0 := truncLE_d_zero_one_eq_zero N
  have hleft : QuasiIsoAt (N.ιTruncLE 0 ≫ s) (-1) := inferInstance
  have hleft' : QuasiIsoAt (N.ιTruncLE 0 ≫ s) 0 := inferInstance
  have hright : QuasiIsoAt (N.ιTruncLE 0 ≫ g) (-1) := inferInstance
  have hright' : QuasiIsoAt (N.ιTruncLE 0 ≫ g) 0 := inferInstance
  exact ⟨(truncQuotientEquivalence (N.ιTruncLE 0 ≫ s) hN hK hleft hleft').symm.trans
    (truncQuotientEquivalence (N.ιTruncLE 0 ≫ g) hN hK' hright hright')⟩

/-- **Every complex without cohomology in positive degrees is quasi-isomorphic to one with no
differential out of degree `0`**, namely to its canonical truncation `τ≤0 K`. -/
theorem exists_rep_d_zero_one_eq_zero (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsLE 0] :
    ∃ K' : CochainComplex (ModuleCat.{u} R) ℤ, K'.d 0 1 = 0 ∧
      Nonempty (DerivedCategory.Q.obj K' ≅ DerivedCategory.Q.obj K) := by
  refine ⟨K.truncLE 0, truncLE_d_zero_one_eq_zero K, ⟨?_⟩⟩
  have hiso : IsIso (DerivedCategory.Q.map (K.ιTruncLE 0)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact asIso (DerivedCategory.Q.map (K.ιTruncLE 0))

end Roof

end LinearTwoTermComplex

/-! ## `h¹/h⁰` of a derived object, without projectivity -/

section Derived

open LinearTwoTermComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A *truncation representative* of an object `E` of the derived category of `R`-modules: any
complex with no differential out of degree `0` together with an isomorphism onto `E`.  In
contrast with `TruncPresentation`, nothing is assumed about projectivity or boundedness. -/
structure TruncRep (E : DerivedCategory (ModuleCat.{u} R)) where
  /-- The representing complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  /-- It has no differential out of degree `0`, so its truncation computes `H⁻¹` and `H⁰`. -/
  d_zero_one : complex.d 0 1 = 0
  /-- It represents `E`. -/
  iso : DerivedCategory.Q.obj complex ≅ E

namespace TruncRep

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- The Picard groupoid `h¹/h⁰(E)` computed from a truncation representative. -/
abbrev picard (P : TruncRep E) := (twoTermTrunc P.complex).quotient

/-- Vertex automorphisms of `h¹/h⁰(E)` are `H⁻¹(E)`. -/
def vertexAutEquiv (P : TruncRep E) :
    (TwoTermQuotient.vertex (twoTermTrunc P.complex).differential ⟶
        TwoTermQuotient.vertex (twoTermTrunc P.complex).differential) ≃
      LinearMap.ker (twoTermTrunc P.complex).differential :=
  TwoTermQuotient.vertexAutEquivKernel _

/-- **Independence of the representative, with no hypothesis beyond `d⁰ = 0`.**  This is the
projectivity-free form of `TruncPresentation.nonempty_picardEquivalence`. -/
theorem nonempty_picardEquivalence (P P' : TruncRep E) : Nonempty (P.picard ≌ P'.picard) :=
  nonempty_truncQuotientEquivalence_of_Q_iso P.complex P'.complex P.d_zero_one P'.d_zero_one
    (P.iso ≪≫ P'.iso.symm)

/-- Transport a truncation representative along an isomorphism of the represented object. -/
noncomputable def replace {E' : DerivedCategory (ModuleCat.{u} R)} (P : TruncRep E) (e : E ≅ E') :
    TruncRep E' where
  complex := P.complex
  d_zero_one := P.d_zero_one
  iso := P.iso ≪≫ e

@[simp]
theorem replace_complex {E' : DerivedCategory (ModuleCat.{u} R)} (P : TruncRep E) (e : E ≅ E') :
    (P.replace e).complex = P.complex :=
  rfl

/-- A complex without cohomology in positive degrees gives a truncation representative of the
object it represents, through its canonical truncation `τ≤0`. -/
noncomputable def ofIsLE (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsLE 0]
    (e : DerivedCategory.Q.obj K ≅ E) : TruncRep E where
  complex := K.truncLE 0
  d_zero_one := truncLE_d_zero_one_eq_zero K
  iso :=
    have hiso : IsIso (DerivedCategory.Q.map (K.ιTruncLE 0)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    asIso (DerivedCategory.Q.map (K.ιTruncLE 0)) ≪≫ e

end TruncRep

namespace TruncPresentation

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- A truncation presentation is in particular a truncation representative. -/
def toTruncRep (P : TruncPresentation E) : TruncRep E where
  complex := P.complex
  d_zero_one := P.d_zero_one
  iso := P.iso

@[simp]
theorem toTruncRep_complex (P : TruncPresentation E) : P.toTruncRep.complex = P.complex :=
  rfl

/-- **Compatibility of the two definitions.**  The Picard groupoid computed from a K-projective
presentation is equivalent to the one computed from an arbitrary representative. -/
theorem nonempty_picardEquivalence_truncRep (P : TruncPresentation E) (P' : TruncRep E) :
    Nonempty (P.picard ≌ P'.picard) :=
  TruncRep.nonempty_picardEquivalence P.toTruncRep P'

end TruncPresentation

namespace CotangentComplex.PerfectComplex

open CotangentComplex.PerfectComplex

namespace GlobalTwoTermResolution

variable {E : DerivedCategory (ModuleCat.{u} R)}

/-- **The Picard groupoid of a global two-term resolution agrees with the truncation definition
computed from an arbitrary representative.**  Combining
`GlobalTwoTermResolution.nonempty_picardEquivalence_truncPresentation` with the
projectivity-free independence statement, `h¹/h⁰` of a perfect object of amplitude `[-1, 0]` may
be computed either from a global two-term resolution or from any complex with `d⁰ = 0`
representing it. -/
theorem nonempty_picardEquivalence_truncRep (F : GlobalTwoTermResolution E) (P : TruncRep E) :
    Nonempty (F.picard ≌ P.picard) := by
  obtain ⟨e⟩ := F.nonempty_picardEquivalence_truncPresentation
  obtain ⟨e'⟩ := F.truncPresentation.nonempty_picardEquivalence_truncRep P
  exact ⟨e.trans e'⟩

end GlobalTwoTermResolution

end CotangentComplex.PerfectComplex

end Derived

end GromovWitten.AlgebraicGeometry
