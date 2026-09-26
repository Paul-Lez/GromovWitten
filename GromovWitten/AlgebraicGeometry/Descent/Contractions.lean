/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Descent.BaseChange

/-!
# Factorizations through descended contraction targets

The statements here assume that the source, target, and local factorization maps already exist.
They only descend the factorization and compare two such existing targets; no object-effectivity
claim is made.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

namespace EtaleMorphisms

open _root_.AlgebraicGeometry.Scheme

variable {S U X Y Z Z' : Scheme.{u}} (e : U ⟶ S) (x : X ⟶ S) (y : Y ⟶ S)
  (z : Z ⟶ S) [Etale e] [Surjective e]

/-- The pullback of a source map along the chosen cover. -/
noncomputable def sourceBaseChangeMap {q : X ⟶ Y} (hq : q ≫ y = x) :
    pullback x e ⟶ pullback y e :=
  pullback.lift (pullback.fst x e ≫ q) (pullback.snd x e) (by
    rw [Category.assoc, hq, pullback.condition])

omit [Etale e] [Surjective e] in
@[simp]
theorem sourceBaseChangeMap_fst {q : X ⟶ Y} (hq : q ≫ y = x) :
    sourceBaseChangeMap e x y hq ≫ pullback.fst y e = pullback.fst x e ≫ q := by
  exact pullback.lift_fst _ _ _

omit [Etale e] [Surjective e] in
@[simp]
theorem sourceBaseChangeMap_snd {q : X ⟶ Y} (hq : q ≫ y = x) :
    sourceBaseChangeMap e x y hq ≫ pullback.snd y e = pullback.snd x e := by
  exact pullback.lift_snd _ _ _

/-- A locally prescribed contraction factorization descends to the actual target. -/
theorem descend_factorization {q : X ⟶ Y} {g : X ⟶ Z} (hq : q ≫ y = x)
    (D : SchemeLocalMapData e y z)
    (hlocal : sourceBaseChangeMap e x y hq ≫ D.hom = pullback.fst x e ≫ g) :
    q ≫ schemeDescend e y z D = g := by
  apply (cancel_epi (pullback.fst x e)).1
  rw [← Category.assoc, ← sourceBaseChangeMap_fst e x y hq, Category.assoc,
    schemeDescend_fac, hlocal]

/-- Uniqueness of a contraction factorization when its source map is an epimorphism. -/
theorem contraction_factorization_unique {q : X ⟶ Y} [Epi q] {h₁ h₂ : Y ⟶ Z}
    (factor : q ≫ h₁ = q ≫ h₂) : h₁ = h₂ :=
  (cancel_epi q).1 factor

section CompareTargets

variable (z' : Z' ⟶ S)

/-- The canonical isomorphism between two existing targets whose compatible local transition maps
    and inverse transition maps have been supplied. -/
noncomputable def contractionTargetIso (F : SchemeLocalIsoData e z z') : Z ≅ Z' :=
  schemeIso e z z' F

theorem contractionTargetIso_hom_factorization
    (D : SchemeLocalMapData e y z) (D' : SchemeLocalMapData e y z')
    (F : SchemeLocalIsoData e z z')
    (hforward : baseChangeHom e y z D ≫ F.hom.hom = D'.hom) :
    schemeDescend e y z D ≫ (contractionTargetIso e z z' F).hom =
      schemeDescend e y z' D' := by
  have hdesc : schemeDescend e y z' D' =
      schemeDescend e y z' (SchemeLocalMapData.comp (e := e) (y := y)
        (z := z') (w := z) D F.hom) := by
    apply schemeDescend_unique e y z'
    rw [schemeDescend_fac]
    exact hforward.symm
  rw [hdesc, schemeDescend_compose]
  rfl

theorem contractionTargetIso_inv_factorization
    (D : SchemeLocalMapData e y z) (D' : SchemeLocalMapData e y z')
    (F : SchemeLocalIsoData e z z')
    (hinverse : baseChangeHom e y z' D' ≫ F.inv.hom = D.hom) :
    schemeDescend e y z' D' ≫ (contractionTargetIso e z z' F).inv =
      schemeDescend e y z D := by
  have hdesc : schemeDescend e y z D =
      schemeDescend e y z (SchemeLocalMapData.comp (e := e) (y := y)
        (z := z) (w := z') D' F.inv) := by
    apply schemeDescend_unique e y z
    rw [schemeDescend_fac]
    exact hinverse.symm
  rw [hdesc, schemeDescend_compose]
  rfl

end CompareTargets

end EtaleMorphisms

end

end GromovWitten.AlgebraicGeometry
