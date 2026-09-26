/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Descent.SchemeIsomorphisms

/-!
# Base change for effective étale descent

This file records the coherence of the genuine scheme-morphism descent construction under an
arbitrary map of bases.  All comparison maps are the canonical maps between the chosen pullbacks;
the statements therefore identify the descended arrow by its pullback along the base-changed
cover, rather than silently identifying iterated pullbacks by definitional equality.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

namespace EtaleMorphisms

open _root_.AlgebraicGeometry.Scheme

variable {S U Y Z T : Scheme.{u}} (e : U ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S)
  [Etale e] [Surjective e]

section CanonicalMaps

variable (b : T ⟶ S)

/-- The canonical comparison from the iterated local source over `T` to the original local source.
-/
noncomputable def localSourceBaseChangeMap :
    pullback (pullback.snd y b) (pullback.snd e b) ⟶ pullback y e :=
  pullback.lift
    (pullback.fst (pullback.snd y b) (pullback.snd e b) ≫
      pullback.fst y b)
    (pullback.snd (pullback.snd y b) (pullback.snd e b) ≫
      pullback.fst e b) (by
      simp only [Category.assoc]
      rw [pullback.condition (f := y) (g := b),
        pullback.condition (f := e) (g := b)]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b)
        (pullback.condition (f := pullback.snd y b) (g := pullback.snd e b)))

omit [Etale e] [Surjective e] in
@[simp]
theorem localSourceBaseChangeMap_fst :
    localSourceBaseChangeMap e y b ≫ pullback.fst y e =
      pullback.fst (pullback.snd y b) (pullback.snd e b) ≫
        pullback.fst y b :=
  pullback.lift_fst _ _ _

omit [Etale e] [Surjective e] in
@[simp]
theorem localSourceBaseChangeMap_snd :
    localSourceBaseChangeMap e y b ≫ pullback.snd y e =
      pullback.snd (pullback.snd y b) (pullback.snd e b) ≫
        pullback.fst e b :=
  pullback.lift_snd _ _ _

section DescendedData

variable (D : SchemeLocalMapData e y z)

/-- The actual local map obtained from `D` after arbitrary base change. -/
noncomputable def schemeBaseChangeData :
    SchemeLocalMapData (pullback.snd e b) (pullback.snd y b) (pullback.snd z b) where
  hom := pullback.lift
    (localSourceBaseChangeMap e y b ≫ D.hom)
    (pullback.snd (pullback.snd y b) (pullback.snd e b) ≫ pullback.snd e b) (by
      simp only [Category.assoc]
      rw [D.over, ← Category.assoc, localSourceBaseChangeMap_snd,
        Category.assoc, pullback.condition (f := e) (g := b)])
  over := by
    rw [pullback.lift_snd]
  compat := by
    intro R a c hac
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
      apply D.compat (a ≫ localSourceBaseChangeMap e y b)
        (c ≫ localSourceBaseChangeMap e y b)
      rw [Category.assoc, Category.assoc, localSourceBaseChangeMap_fst,
        ← Category.assoc, ← Category.assoc, hac]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd]
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hac]

/-- The pullback of a global map over `S` to the base `T`. -/
noncomputable def baseChangeMap {g : Y ⟶ Z} (hg : g ≫ z = y) :
    pullback y b ⟶ pullback z b :=
  pullback.lift (pullback.fst y b ≫ g) (pullback.snd y b) (by
    rw [Category.assoc, hg, pullback.condition])

theorem baseChangeMap_fst {g : Y ⟶ Z} (hg : g ≫ z = y) :
    baseChangeMap y z b hg ≫ pullback.fst z b = pullback.fst y b ≫ g := by
  exact pullback.lift_fst _ _ _

theorem baseChangeMap_snd {g : Y ⟶ Z} (hg : g ≫ z = y) :
    baseChangeMap y z b hg ≫ pullback.snd z b = pullback.snd y b := by
  exact pullback.lift_snd _ _ _

theorem schemeDescend_baseChange (D : SchemeLocalMapData e y z) :
    schemeDescend (pullback.snd e b) (pullback.snd y b) (pullback.snd z b)
        (schemeBaseChangeData e y z b D) =
      baseChangeMap y z b (schemeDescend_comp e y z D) := by
  symm
  apply schemeDescend_unique (pullback.snd e b) (pullback.snd y b) (pullback.snd z b)
  rw [schemeBaseChangeData]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, baseChangeMap_fst, ← Category.assoc,
      ← localSourceBaseChangeMap_fst, Category.assoc, schemeDescend_fac]
  · rw [pullback.lift_snd, Category.assoc, baseChangeMap_snd]
    simpa only [Category.assoc] using
      (pullback.condition (f := pullback.snd y b) (g := pullback.snd e b))

end DescendedData

section Isomorphisms

/-- The actual base change of the descended isomorphism. -/
noncomputable def schemeIsoBaseChange (D : SchemeLocalIsoData e y z) (b : T ⟶ S) :
    pullback y b ≅ pullback z b where
  hom := baseChangeMap y z b (schemeIso_hom_over e y z D)
  inv := baseChangeMap z y b (schemeIso_inv_over e y z D)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.id_comp]
      calc
        (baseChangeMap y z b (schemeIso_hom_over e y z D) ≫
            baseChangeMap z y b (schemeIso_inv_over e y z D)) ≫
            pullback.fst y b =
          baseChangeMap y z b (schemeIso_hom_over e y z D) ≫
            (baseChangeMap z y b (schemeIso_inv_over e y z D) ≫
              pullback.fst y b) := by rw [Category.assoc]
        _ = baseChangeMap y z b (schemeIso_hom_over e y z D) ≫
            (pullback.fst z b ≫ (schemeIso e y z D).inv) := by
          rw [baseChangeMap_fst]
        _ = (baseChangeMap y z b (schemeIso_hom_over e y z D) ≫
            pullback.fst z b) ≫ (schemeIso e y z D).inv := by
          rw [Category.assoc]
        _ = (pullback.fst y b ≫ (schemeIso e y z D).hom) ≫
            (schemeIso e y z D).inv := by
          rw [baseChangeMap_fst]
        _ = pullback.fst y b := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp only [Category.id_comp]
      rw [Category.assoc, baseChangeMap_snd, baseChangeMap_snd]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.id_comp]
      calc
        (baseChangeMap z y b (schemeIso_inv_over e y z D) ≫
            baseChangeMap y z b (schemeIso_hom_over e y z D)) ≫
            pullback.fst z b =
          baseChangeMap z y b (schemeIso_inv_over e y z D) ≫
            (baseChangeMap y z b (schemeIso_hom_over e y z D) ≫
              pullback.fst z b) := by rw [Category.assoc]
        _ = baseChangeMap z y b (schemeIso_inv_over e y z D) ≫
            (pullback.fst y b ≫ (schemeIso e y z D).hom) := by
          rw [baseChangeMap_fst]
        _ = (baseChangeMap z y b (schemeIso_inv_over e y z D) ≫
            pullback.fst y b) ≫ (schemeIso e y z D).hom := by
          rw [Category.assoc]
        _ = (pullback.fst z b ≫ (schemeIso e y z D).inv) ≫
            (schemeIso e y z D).hom := by
          rw [baseChangeMap_fst]
        _ = pullback.fst z b := by
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp only [Category.id_comp]
      rw [Category.assoc, baseChangeMap_snd, baseChangeMap_snd]

theorem schemeIso_baseChange_hom (D : SchemeLocalIsoData e y z) (b : T ⟶ S) :
    (schemeIsoBaseChange e y z D b).hom =
      baseChangeMap y z b (schemeIso_hom_over e y z D) := rfl

theorem schemeIso_baseChange_inv (D : SchemeLocalIsoData e y z) (b : T ⟶ S) :
    (schemeIsoBaseChange e y z D b).inv =
      baseChangeMap z y b (schemeIso_inv_over e y z D) := rfl

theorem schemeIso_baseChange_hom_descend (D : SchemeLocalIsoData e y z) (b : T ⟶ S) :
    (schemeIsoBaseChange e y z D b).hom =
      schemeDescend (pullback.snd e b) (pullback.snd y b) (pullback.snd z b)
        (schemeBaseChangeData e y z b D.hom) := by
  change baseChangeMap y z b (schemeIso_hom_over e y z D) = _
  rw [schemeDescend_baseChange]
  congr 1

theorem schemeIso_baseChange_inv_descend (D : SchemeLocalIsoData e y z) (b : T ⟶ S) :
    (schemeIsoBaseChange e y z D b).inv =
      schemeDescend (pullback.snd e b) (pullback.snd z b) (pullback.snd y b)
        (schemeBaseChangeData e z y b D.inv) := by
  change baseChangeMap z y b (schemeIso_inv_over e y z D) = _
  rw [schemeDescend_baseChange]
  congr 1

end Isomorphisms

end CanonicalMaps

end EtaleMorphisms

end

end GromovWitten.AlgebraicGeometry
