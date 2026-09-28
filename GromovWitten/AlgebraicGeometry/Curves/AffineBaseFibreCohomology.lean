/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ArithmeticGenus
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Cohomology of affine-base fibres

The fibre over a point of an affine base is represented by the actual scheme
pullback. This file records its cohomology module and the pullback facts used
to supply local Noetherianity in later fibre arguments.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.Curves

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The cohomology module of the fibre over a point of the affine base. -/
def affineBaseFibreCohomology (s : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (q : PrimeSpectrum R) (n : ℕ) :
    ModuleCat q.asIdeal.ResidueField :=
  cohomologyModuleCat q.asIdeal.ResidueField
    (Limits.pullback.snd s
      (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))))
    ((Scheme.Modules.pullback
      (Limits.pullback.fst s
        (Spec.map (CommRingCat.ofHom
          (algebraMap R q.asIdeal.ResidueField))))).obj M) n

/-- The fibre scheme is locally Noetherian when the original morphism is locally of finite type. -/
lemma affineBaseFibre_isLocallyNoetherian
    (s : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType s]
    (q : PrimeSpectrum R) :
    IsLocallyNoetherian
      (Limits.pullback s
        (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))
  let _ : IsLocallyNoetherian (Spec (CommRingCat.of q.asIdeal.ResidueField)) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian
    (Limits.pullback.snd s f)

/-- The two projections of the affine-base fibre form the canonical pullback square. -/
lemma affineBaseFibre_isPullback (s : X ⟶ Spec (CommRingCat.of R))
    (q : PrimeSpectrum R) :
    IsPullback
      (Limits.pullback.fst s
        (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))))
      (Limits.pullback.snd s
        (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))) )
      s (Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField))) := by
  exact IsPullback.of_hasPullback _ _

end GromovWitten.AlgebraicGeometry.Curves
