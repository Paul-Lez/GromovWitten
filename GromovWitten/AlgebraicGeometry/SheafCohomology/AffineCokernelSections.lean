/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentKernels

/-!
# Cokernels of affine global sections

This file transports the cokernel of a morphism of quasi-coherent modules on an affine scheme
through global sections.  The projection formula recorded below is the characteristic equation
used by the affine Cech model for degree-one cohomology.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The affine global-sections cokernel comparison induced by the tilde adjunction. -/
def moduleSpecΓCokernelIso
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    cokernel ((moduleSpecΓFunctor (R := R)).map f) ≅
      (moduleSpecΓFunctor (R := R)).obj (cokernel f) :=
  asIso ((tilde.adjunction (R := R)).unit.app
      (cokernel ((moduleSpecΓFunctor (R := R)).map f))) ≪≫
    (moduleSpecΓFunctor (R := R)).mapIso (tildeCokernelIso f)

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel projection commutes with `moduleSpecΓCokernelIso`. -/
lemma moduleSpecΓCokernelIso_comp_cokernel_π
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    cokernel.π ((moduleSpecΓFunctor (R := R)).map f) ≫
        (moduleSpecΓCokernelIso f).hom =
      (moduleSpecΓFunctor (R := R)).map (cokernel.π f) := by
  let eN : (tilde.functor R).obj (moduleSpecΓFunctor.obj N) ≅ N :=
    asIso N.fromTildeΓ
  have heQ : (tilde.functor R).map
        (cokernel.π ((moduleSpecΓFunctor (R := R)).map f)) ≫
        (tildeCokernelIso f).hom =
      eN.hom ≫ cokernel.π f := by
    dsimp [tildeCokernelIso]
    erw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp [cokernel.mapIso, eN]
  change cokernel.π ((moduleSpecΓFunctor (R := R)).map f) ≫
      (tilde.adjunction (R := R)).unit.app _ ≫
        (moduleSpecΓFunctor (R := R)).map (tildeCokernelIso f).hom = _
  have hnat := (tilde.adjunction (R := R)).unit.naturality
    (cokernel.π ((moduleSpecΓFunctor (R := R)).map f))
  rw [← Category.assoc]
  erw [hnat]
  rw [Category.assoc]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp, heQ]
  have htri : (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj N) ≫
      (moduleSpecΓFunctor (R := R)).map eN.hom = 𝟙 _ :=
    (tilde.adjunction (R := R)).right_triangle_components N
  rw [Functor.map_comp, ← Category.assoc, htri]
  exact Category.id_comp _

end GromovWitten.AlgebraicGeometry.SheafCohomology
