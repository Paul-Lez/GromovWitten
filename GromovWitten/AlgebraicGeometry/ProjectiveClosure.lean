/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.RelativeProjective
import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ClosureModel

/-!
# Scheme-theoretic closures in a relative projective family

The closure of a map into a relative projective source is its scheme-theoretic image in that
source.  The construction records the factorisation and its map over the base.  Flatness is
proved for the DVR generic-fibre closure below; no flatness claim is made for an arbitrary image.
-/

open CategoryTheory Limits AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves.StableReduction

namespace GromovWitten.AlgebraicGeometry

universe u
noncomputable section

namespace ProjectiveClosure

variable {X Y U : Scheme.{u}} {p : Y ⟶ X} (P : RelativeProjective p)

/-- The scheme-theoretic closure of `U` in the relative projective family presenting `Y`. -/
abbrev closure (_P : RelativeProjective p) (j : U ⟶ Y) : Scheme :=
  j.image

/-- The closed immersion of the closure into the relative projective family. -/
abbrev closureι (P : RelativeProjective p) (j : U ⟶ Y) : closure P j ⟶ Y :=
  j.imageι

/-- The map from the original source into its scheme-theoretic closure. -/
noncomputable abbrev factor (P : RelativeProjective p) (j : U ⟶ Y) : U ⟶ closure P j :=
  j.toImage

@[reassoc (attr := simp)] theorem factor_comp_closureι (j : U ⟶ Y) :
    factor P j ≫ closureι P j = j :=
  Scheme.Hom.toImage_imageι _

theorem factor_over_base (j : U ⟶ Y) :
    factor P j ≫ closureι P j ≫ p = j ≫ p := by
  rw [← Category.assoc, factor_comp_closureι]

theorem closure_isProper_over_base (j : U ⟶ Y) :
    IsProper (closureι P j ≫ p) := by
  have h : IsProper p := P.isProper
  infer_instance

/-! ### The DVR closure theorem -/

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  [IsDiscreteValuationRing R] {Z : Scheme.{u}}

/-- The generic-fibre closure model is the projective-closure image in its ambient scheme. -/
abbrev genericFiberClosure (toBase : Z ⟶ Spec (.of R)) (P : RelativeProjective toBase)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] : Scheme :=
  closure P (genericFiberInclusion (K := K) toBase)

abbrev genericFiberClosureι (toBase : Z ⟶ Spec (.of R)) (P : RelativeProjective toBase)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    genericFiberClosure toBase P K ⟶ Z :=
  closureι P (genericFiberInclusion (K := K) toBase)

noncomputable abbrev genericFiberClosureFactor (toBase : Z ⟶ Spec (.of R))
    (P : RelativeProjective toBase) (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    pullback toBase (genericPointMap R K) ⟶ genericFiberClosure toBase P K :=
  factor P (genericFiberInclusion (K := K) toBase)

omit [IsDomain R] [IsBezout R] [IsDiscreteValuationRing R] in
theorem genericFiberClosure_eq_closureModel (toBase : Z ⟶ Spec (.of R))
    (P : RelativeProjective toBase) (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    genericFiberClosure toBase P K = closureModel (K := K) toBase :=
  closureModel_eq_image toBase

omit [IsBezout R] in
theorem flat_genericFiberClosure (toBase : Z ⟶ Spec (.of R))
    (P : RelativeProjective toBase) (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Flat (genericFiberClosureι toBase P K ≫ toBase) := by
  simpa only [genericFiberClosureι, genericFiberClosure_eq_closureModel] using
    (flat_closureModel toBase)

omit [IsDomain R] [IsBezout R] [IsDiscreteValuationRing R] in
theorem genericFiberClosure_genericFiberIso (toBase : Z ⟶ Spec (.of R))
    (P : RelativeProjective toBase) (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    IsIso (genericFiberMap (K := K) (genericFiberClosureι toBase P K) toBase) := by
  simpa only [genericFiberClosureι, genericFiberClosure_eq_closureModel] using
    (inferInstance : IsIso
      (genericFiberMap (K := K)
        (closureModelι (K := K) toBase) toBase))

end ProjectiveClosure

end
end GromovWitten.AlgebraicGeometry
