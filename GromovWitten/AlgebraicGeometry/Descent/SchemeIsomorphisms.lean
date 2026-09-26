/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Descent.EtaleMorphisms

/-!
# Effective descent of scheme isomorphisms

This file packages two genuine inverse maps on the base change of schemes along a surjective
étale morphism.  The effective-epimorphism construction in `EtaleMorphisms` descends each map,
and the local inverse equations then descend to an actual scheme isomorphism.  In particular,
the construction keeps the local maps themselves as data; it does not assert the existence of
an unspecified global isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

namespace EtaleMorphisms

open _root_.AlgebraicGeometry.Scheme

variable {S U Y Z : Scheme.{u}} (e : U ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S)
  [Etale e] [Surjective e]

/-- A pair of actual local maps with actual inverse equations over a surjective étale cover. -/
structure SchemeLocalIsoData where
  hom : SchemeLocalMapData e y z
  inv : SchemeLocalMapData e z y
  hom_inv :
    baseChangeHom e y z hom ≫ inv.hom = pullback.fst y e
  inv_hom :
    baseChangeHom e z y inv ≫ hom.hom = pullback.fst z e

/-- The global forward morphism obtained from the local forward map. -/
noncomputable def schemeIsoHom (D : SchemeLocalIsoData e y z) : Y ⟶ Z :=
  schemeDescend e y z D.hom

/-- The global inverse morphism obtained from the local inverse map. -/
noncomputable def schemeIsoInv (D : SchemeLocalIsoData e y z) : Z ⟶ Y :=
  schemeDescend e z y D.inv

@[reassoc (attr := simp)]
theorem schemeIsoHom_fac (D : SchemeLocalIsoData e y z) :
    pullback.fst y e ≫ schemeIsoHom e y z D = D.hom.hom :=
  schemeDescend_fac e y z D.hom

@[reassoc (attr := simp)]
theorem schemeIsoInv_fac (D : SchemeLocalIsoData e y z) :
    pullback.fst z e ≫ schemeIsoInv e y z D = D.inv.hom :=
  schemeDescend_fac e z y D.inv

theorem schemeIsoHom_over (D : SchemeLocalIsoData e y z) :
    schemeIsoHom e y z D ≫ z = y :=
  schemeDescend_comp e y z D.hom

theorem schemeIsoInv_over (D : SchemeLocalIsoData e y z) :
    schemeIsoInv e y z D ≫ y = z :=
  schemeDescend_comp e z y D.inv

theorem schemeIsoHom_inv (D : SchemeLocalIsoData e y z) :
    schemeIsoHom e y z D ≫ schemeIsoInv e y z D = 𝟙 Y := by
  apply (cancel_epi (pullback.fst y e)).1
  rw [← Category.assoc, schemeIsoHom_fac]
  calc
    D.hom.hom ≫ schemeIsoInv e y z D =
        (baseChangeHom e y z D.hom ≫ pullback.fst z e) ≫
          schemeIsoInv e y z D := by rw [baseChangeHom_fst]
    _ = baseChangeHom e y z D.hom ≫
        (pullback.fst z e ≫ schemeIsoInv e y z D) := by rw [Category.assoc]
    _ = baseChangeHom e y z D.hom ≫ D.inv.hom := by rw [schemeIsoInv_fac]
    _ = pullback.fst y e := D.hom_inv
    _ = pullback.fst y e ≫ 𝟙 Y := by rw [Category.comp_id]

theorem schemeIsoInv_hom (D : SchemeLocalIsoData e y z) :
    schemeIsoInv e y z D ≫ schemeIsoHom e y z D = 𝟙 Z := by
  apply (cancel_epi (pullback.fst z e)).1
  rw [← Category.assoc, schemeIsoInv_fac]
  calc
    D.inv.hom ≫ schemeIsoHom e y z D =
        (baseChangeHom e z y D.inv ≫ pullback.fst y e) ≫
          schemeIsoHom e y z D := by rw [baseChangeHom_fst]
    _ = baseChangeHom e z y D.inv ≫
        (pullback.fst y e ≫ schemeIsoHom e y z D) := by rw [Category.assoc]
    _ = baseChangeHom e z y D.inv ≫ D.hom.hom := by rw [schemeIsoHom_fac]
    _ = pullback.fst z e := D.inv_hom
    _ = pullback.fst z e ≫ 𝟙 Z := by rw [Category.comp_id]

/-- The actual global isomorphism represented by local inverse maps. -/
noncomputable def schemeIso (D : SchemeLocalIsoData e y z) : Y ≅ Z where
  hom := schemeIsoHom e y z D
  inv := schemeIsoInv e y z D
  hom_inv_id := schemeIsoHom_inv e y z D
  inv_hom_id := schemeIsoInv_hom e y z D

@[simp]
theorem schemeIso_hom (D : SchemeLocalIsoData e y z) :
    (schemeIso e y z D).hom = schemeIsoHom e y z D := rfl

@[simp]
theorem schemeIso_inv (D : SchemeLocalIsoData e y z) :
    (schemeIso e y z D).inv = schemeIsoInv e y z D := rfl

theorem schemeIso_pullback_hom (D : SchemeLocalIsoData e y z) :
    pullback.fst y e ≫ (schemeIso e y z D).hom = D.hom.hom :=
  schemeIsoHom_fac e y z D

theorem schemeIso_pullback_inv (D : SchemeLocalIsoData e y z) :
    pullback.fst z e ≫ (schemeIso e y z D).inv = D.inv.hom :=
  schemeIsoInv_fac e y z D

theorem schemeIso_hom_over (D : SchemeLocalIsoData e y z) :
    (schemeIso e y z D).hom ≫ z = y :=
  schemeIsoHom_over e y z D

theorem schemeIso_inv_over (D : SchemeLocalIsoData e y z) :
    (schemeIso e y z D).inv ≫ y = z :=
  schemeIsoInv_over e y z D

/-- The descended forward map is unique among maps with the prescribed local pullback. -/
theorem schemeIso_hom_unique (D : SchemeLocalIsoData e y z) {g : Y ⟶ Z}
    (hg : pullback.fst y e ≫ g = D.hom.hom) :
    g = (schemeIso e y z D).hom := by
  exact schemeDescend_unique e y z D.hom hg

/-- The descended inverse map is unique among maps with the prescribed local pullback. -/
theorem schemeIso_inv_unique (D : SchemeLocalIsoData e y z) {g : Z ⟶ Y}
    (hg : pullback.fst z e ≫ g = D.inv.hom) :
    g = (schemeIso e y z D).inv := by
  exact schemeDescend_unique e z y D.inv hg

/-- Two global isomorphisms with the same local forward map are equal. -/
theorem schemeIso_unique (D : SchemeLocalIsoData e y z) {g : Y ≅ Z}
    (hg : pullback.fst y e ≫ g.hom = D.hom.hom) :
    g = schemeIso e y z D := by
  apply Iso.ext
  exact schemeIso_hom_unique e y z D hg

end EtaleMorphisms

end

end GromovWitten.AlgebraicGeometry
