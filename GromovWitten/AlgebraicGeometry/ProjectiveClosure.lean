/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeProjective
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ClosureModel

/-!
# Scheme-theoretic closures in a relative projective family

The closure of a map into a relative projective source is its scheme-theoretic image.  The
construction records the factorisation and its map over the base.  Flatness is proved for the
existing DVR generic-fibre closure below; no flatness claim is made for an arbitrary image.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves.StableReduction

namespace GromovWitten.AlgebraicGeometry

universe u
noncomputable section

namespace ProjectiveClosure

variable {X Y U : Scheme.{u}} {p : Y ⟶ X} (P : RelativeProjective p)

/-- The scheme-theoretic closure of `U` in the relative projective family presenting `Y`. -/
abbrev closure (j : U ⟶ Y) : Scheme :=
  (j ≫ P.iso.hom).image

/-- The closed immersion of the closure into the relative projective family. -/
abbrev closureι (j : U ⟶ Y) : closure P j ⟶ RelativeProj.relativeProj X P.data :=
  (j ≫ P.iso.hom).imageι

/-- The map from the original source into its scheme-theoretic closure. -/
noncomputable abbrev factor (j : U ⟶ Y) : U ⟶ closure P j :=
  (j ≫ P.iso.hom).toImage

@[reassoc (attr := simp)] theorem factor_comp_closureι (j : U ⟶ Y) :
    factor P j ≫ closureι P j = j ≫ P.iso.hom :=
  Scheme.Hom.toImage_imageι _

theorem factor_over_base (j : U ⟶ Y) :
    factor P j ≫ closureι P j ≫ RelativeProj.toBase X P.data = j ≫ p := by
  rw [← Category.assoc, factor_comp_closureι, Category.assoc, P.iso_toBase]

theorem closure_isProper_over_base (j : U ⟶ Y) :
    IsProper (closureι P j ≫ RelativeProj.toBase X P.data) := by
  have h : IsProper (RelativeProj.toBase X P.data) :=
    @RelativeProj.toBase_isProper X P.data P.finiteType P.degreeZero
  infer_instance

/-! ### The DVR closure theorem -/

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  [IsDiscreteValuationRing R] {Z : Scheme.{u}}

/-- The generic-fibre closure model is the projective-closure image in its ambient scheme. -/
abbrev genericFiberClosure (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (toBase : Z ⟶ Spec (.of R)) : Scheme :=
  (genericFiberInclusion (K := K) toBase).image

abbrev genericFiberClosureι (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (toBase : Z ⟶ Spec (.of R)) :
    genericFiberClosure K toBase ⟶ Z :=
  (genericFiberInclusion (K := K) toBase).imageι

noncomputable abbrev genericFiberClosureFactor (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (toBase : Z ⟶ Spec (.of R)) :
    pullback toBase (genericPointMap R K) ⟶ genericFiberClosure K toBase :=
  (genericFiberInclusion (K := K) toBase).toImage

omit [IsDomain R] [IsBezout R] [IsDiscreteValuationRing R] in
theorem genericFiberClosure_eq_closureModel (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (toBase : Z ⟶ Spec (.of R)) :
    genericFiberClosure K toBase = closureModel (K := K) toBase :=
  closureModel_eq_image toBase

omit [IsBezout R] in
theorem flat_genericFiberClosure (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (toBase : Z ⟶ Spec (.of R)) :
    Flat (genericFiberClosureι K toBase ≫ toBase) := by
  simpa only [genericFiberClosureι, genericFiberClosure_eq_closureModel] using
    (flat_closureModel toBase)

omit [IsDomain R] [IsBezout R] [IsDiscreteValuationRing R] in
theorem genericFiberClosure_genericFiberIso (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (toBase : Z ⟶ Spec (.of R)) :
    IsIso (genericFiberMap (K := K) (genericFiberClosureι K toBase) toBase) := by
  simpa only [genericFiberClosureι, genericFiberClosure_eq_closureModel] using
    (inferInstance : IsIso
      (genericFiberMap (K := K)
        (closureModelι (K := K) toBase) toBase))

end ProjectiveClosure

end
end GromovWitten.AlgebraicGeometry
