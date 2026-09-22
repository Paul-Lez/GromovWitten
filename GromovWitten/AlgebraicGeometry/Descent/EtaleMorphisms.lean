/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStack

/-!
# Descent of scheme morphisms along a covering sieve

This file isolates the part of effective descent which is available without constructing a
scheme from a descent datum.  A family of arrows from the base changes of `Y` to `Z`, indexed
by a covering sieve on `S`, glues as a morphism of fppf sheaves.  Since `Y` and `Z` are already
schemes, Yoneda then turns the glued sheaf map into the unique actual scheme morphism.

The construction deliberately takes the local arrows in the fibre-product sheaf.  Thus the
statement is about genuine arrows and not a supplier record saying that some arrow exists.  An
surjective étale cover is a special case through
`Scheme.Hom.singleton_mem_fppfPrecoverage`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

noncomputable section

namespace EtaleMorphisms

open _root_.AlgebraicGeometry.Scheme

/-- A compatible family of local maps from `Y` to `Z` over `S`.

For a member `f : T ⟶ S` of `R`, `hom f hf` is a map from the sheaf represented by the
base change of `Y` to the sheaf represented by `Z`.  The last equation says that it is over
`S`; `compat` is the equality after any refinement in the sieve.
-/
structure LocalMapData {S Y Z : Scheme.{u}} (y : Y ⟶ S) (z : Z ⟶ S)
    {R : Sieve S} (hR : R ∈ Scheme.fppfTopology S) where
  hom {T : Scheme.{u}} (f : T ⟶ S) (hf : R.arrows f) :
    pullback (fppfYoneda.map y) (fppfYoneda.map f) ⟶ fppfYoneda.obj Z
  over {T : Scheme.{u}} (f : T ⟶ S) (hf : R.arrows f) :
    hom f hf ≫ fppfYoneda.map z =
      pullback.snd (fppfYoneda.map y) (fppfYoneda.map f) ≫ fppfYoneda.map f
  compat {T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T) (h : U ⟶ S)
      (hh : g ≫ f = h) (hf : R.arrows f) (hh' : R.arrows h) :
    hom h hh' =
      relBaseChange (fppfYoneda.map y) f g h hh ≫ hom f hf

/-- Forget the over-`S` equation, obtaining the family used by the sheaf gluing theorem. -/
def LocalMapData.toRelHomFamily {S Y Z : Scheme.{u}} {y : Y ⟶ S} {z : Z ⟶ S}
    {R : Sieve S} {hR : R ∈ Scheme.fppfTopology S} (D : LocalMapData y z hR) :
    RelHomFamily (fppfYoneda.map y) (fppfYoneda.obj Z) R where
  hom := D.hom
  compat := D.compat

variable {S Y Z : Scheme.{u}} {y : Y ⟶ S} {z : Z ⟶ S}
  {R : Sieve S} {hR : R ∈ Scheme.fppfTopology S}

/-- The sheaf morphism obtained by gluing a compatible local family. -/
noncomputable def gluedSheafMap (D : LocalMapData y z hR) :
    fppfYoneda.obj Y ⟶ fppfYoneda.obj Z :=
  (D.toRelHomFamily).glue hR

/-- The glued sheaf map is over the original base morphisms. -/
theorem gluedSheafMap_over (D : LocalMapData y z hR) :
    gluedSheafMap D ≫ fppfYoneda.map z = fppfYoneda.map y := by
  apply hom_ext_of_cover (fppfYoneda.map y) hR
  intro T f hf
  change (pullback.fst (fppfYoneda.map y) (fppfYoneda.map f) ≫
      (D.toRelHomFamily).glue hR) ≫ fppfYoneda.map z = _
  rw [(D.toRelHomFamily).glue_spec hR f hf]
  change D.hom f hf ≫ fppfYoneda.map z = _
  rw [D.over]
  exact pullback.condition.symm

/-- The actual scheme morphism represented by the glued sheaf map. -/
noncomputable def descend (D : LocalMapData y z hR) : Y ⟶ Z :=
  fppfYoneda.preimage (gluedSheafMap D)

@[simp]
theorem map_descend (D : LocalMapData y z hR) :
    fppfYoneda.map (descend D) = gluedSheafMap D :=
  fppfYoneda.map_preimage _

/-- Projection equation for the descended scheme morphism. -/
theorem descend_comp (D : LocalMapData y z hR) : descend D ≫ z = y := by
  apply fppfYoneda.map_injective
  rw [fppfYoneda.map_comp, map_descend, gluedSheafMap_over]

/-- Pullback of the descended morphism agrees with the prescribed local morphism. -/
theorem descend_local (D : LocalMapData y z hR) {T : Scheme.{u}} (f : T ⟶ S)
    (hf : R.arrows f) :
    pullback.fst (fppfYoneda.map y) (fppfYoneda.map f) ≫ gluedSheafMap D = D.hom f hf :=
  (D.toRelHomFamily).glue_spec hR f hf

/-- Uniqueness of the descended scheme morphism from its compatible local maps. -/
theorem descend_unique {g : Y ⟶ Z} (D : LocalMapData y z hR)
    (hg : ∀ {T : Scheme.{u}} (f : T ⟶ S) (hf : R.arrows f),
      pullback.fst (fppfYoneda.map y) (fppfYoneda.map f) ≫ fppfYoneda.map g = D.hom f hf) :
    g = descend D := by
  apply fppfYoneda.map_injective
  apply hom_ext_of_cover (fppfYoneda.map y) hR
  intro T f hf
  rw [map_descend]
  exact (hg f hf).trans (descend_local D f hf).symm

/-- Two local descent data defining the same arrows define the same descended scheme morphism. -/
theorem descend_congr {D D' : LocalMapData y z hR}
    (h : ∀ {T : Scheme.{u}} (f : T ⟶ S) (hf : R.arrows f), D.hom f hf = D'.hom f hf) :
    descend D = descend D' := by
  apply fppfYoneda.map_injective
  apply hom_ext_of_cover (fppfYoneda.map y) hR
  intro T f hf
  rw [map_descend, map_descend]
  exact (descend_local D f hf).trans ((h f hf).trans (descend_local D' f hf).symm)

/-! ### A single genuine étale cover

The following API is independent of the sheaf-level construction above.  It uses the effective
epimorphism supplied by Mathlib for a surjective étale morphism.  The local source is the actual
scheme pullback, and the compatibility field is the kernel-pair equation required by
`EffectiveEpi.desc`.
-/

section SingleCover

variable {S U Y Z : Scheme.{u}} (e : U ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S)
  [Etale e] [Surjective e]

/-- A genuine local scheme morphism over a surjective étale cover. -/
structure SchemeLocalMapData (e : U ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S) where
  hom : pullback y e ⟶ Z
  over : hom ≫ z = pullback.snd y e ≫ e
  compat : ∀ {T : Scheme.{u}} (a b : T ⟶ pullback y e),
    a ≫ pullback.fst y e = b ≫ pullback.fst y e → a ≫ hom = b ≫ hom

/-- The descended morphism obtained by the effective-epimorphic projection
`Y ×_S U ⟶ Y`. -/
noncomputable def schemeDescend (D : SchemeLocalMapData e y z) : Y ⟶ Z :=
  EffectiveEpi.desc (pullback.fst y e) D.hom D.compat

@[reassoc (attr := simp)]
theorem schemeDescend_fac (D : SchemeLocalMapData e y z) :
    pullback.fst y e ≫ schemeDescend e y z D = D.hom :=
  EffectiveEpi.fac (pullback.fst y e) D.hom D.compat

/-- The descended morphism is over `S`; this is the explicit projection equation. -/
theorem schemeDescend_comp (D : SchemeLocalMapData e y z) :
    schemeDescend e y z D ≫ z = y := by
  apply (cancel_epi (pullback.fst y e)).1
  rw [← Category.assoc, schemeDescend_fac, D.over]
  exact pullback.condition.symm

/-- Uniqueness of a morphism with the prescribed local pullback. -/
theorem schemeDescend_unique {g : Y ⟶ Z} (D : SchemeLocalMapData e y z)
    (hg : pullback.fst y e ≫ g = D.hom) :
    g = schemeDescend e y z D := by
  apply (cancel_epi (pullback.fst y e)).1
  rw [schemeDescend_fac, hg]

/-- A global morphism is recovered from its prescribed local pullback. -/
theorem schemeDescend_of_global {g : Y ⟶ Z} (D : SchemeLocalMapData e y z)
    (hlocal : D.hom = pullback.fst y e ≫ g) :
    schemeDescend e y z D = g := by
  symm
  exact schemeDescend_unique e y z D hlocal.symm

/-- The map on the second pullback leg induced by a local map over `S`. -/
noncomputable def baseChangeHom {W : Scheme.{u}} (w : W ⟶ S)
    (D : SchemeLocalMapData e y w) : pullback y e ⟶ pullback w e :=
  pullback.lift D.hom (pullback.snd y e) D.over

omit [Etale e] [Surjective e] in
@[simp]
theorem baseChangeHom_fst {W : Scheme.{u}} (w : W ⟶ S)
    (D : SchemeLocalMapData e y w) :
    baseChangeHom e y w D ≫ pullback.fst w e = D.hom :=
  pullback.lift_fst _ _ _

omit [Etale e] [Surjective e] in
@[simp]
theorem baseChangeHom_snd {W : Scheme.{u}} (w : W ⟶ S)
    (D : SchemeLocalMapData e y w) :
    baseChangeHom e y w D ≫ pullback.snd w e = pullback.snd y e :=
  pullback.lift_snd _ _ _

/-- Composition of local maps, with the canonical pullback of the first local map. -/
noncomputable def SchemeLocalMapData.comp {W : Scheme.{u}} (w : W ⟶ S)
    (D : SchemeLocalMapData e y w) (E : SchemeLocalMapData e w z) :
    SchemeLocalMapData e y z where
  hom := baseChangeHom e y w D ≫ E.hom
  over := by
    rw [Category.assoc, E.over, ← Category.assoc, baseChangeHom_snd]
  compat := by
    intro T a b hab
    apply E.compat (a ≫ baseChangeHom e y w D) (b ≫ baseChangeHom e y w D)
    change a ≫ (baseChangeHom e y w D ≫ pullback.fst w e) =
      b ≫ (baseChangeHom e y w D ≫ pullback.fst w e)
    rw [baseChangeHom_fst, D.compat a b hab]

/-- Descent commutes with composition of compatible local maps. -/
theorem schemeDescend_compose {W : Scheme.{u}} (w : W ⟶ S)
    (D : SchemeLocalMapData e y w) (E : SchemeLocalMapData e w z) :
    schemeDescend e y z (SchemeLocalMapData.comp (e := e) (y := y) (z := z)
      (w := w) D E) =
      schemeDescend e y w D ≫ schemeDescend e w z E := by
  symm
  apply schemeDescend_unique e y z
    (SchemeLocalMapData.comp (e := e) (y := y) (z := z) (w := w) D E)
  rw [← Category.assoc, schemeDescend_fac]
  change D.hom ≫ schemeDescend e w z E =
    baseChangeHom e y w D ≫ E.hom
  calc
    D.hom ≫ schemeDescend e w z E =
        (baseChangeHom e y w D ≫ pullback.fst w e) ≫
          schemeDescend e w z E := by rw [baseChangeHom_fst]
    _ = baseChangeHom e y w D ≫
        (pullback.fst w e ≫ schemeDescend e w z E) := by rw [Category.assoc]
    _ = baseChangeHom e y w D ≫ E.hom := by rw [schemeDescend_fac]

end SingleCover

section KernelPair

variable {S U Y Z : Scheme.{u}} (e : U ⟶ S) (y : Y ⟶ S) (z : Z ⟶ S)

/-- Construct local descent data from the single Čech kernel-pair equation. -/
noncomputable def SchemeLocalMapData.ofKernelPair (h : pullback y e ⟶ Z)
    (hover : h ≫ z = pullback.snd y e ≫ e)
    (hcompat : pullback.fst (pullback.fst y e) (pullback.fst y e) ≫ h =
      pullback.snd (pullback.fst y e) (pullback.fst y e) ≫ h) :
    SchemeLocalMapData e y z where
  hom := h
  over := hover
  compat := by
    intro T a b hab
    let l : T ⟶ pullback (pullback.fst y e) (pullback.fst y e) :=
      pullback.lift a b hab
    calc
      a ≫ h = (l ≫ pullback.fst (pullback.fst y e) (pullback.fst y e)) ≫ h := by
        rw [pullback.lift_fst]
      _ = l ≫ (pullback.fst (pullback.fst y e) (pullback.fst y e) ≫ h) := by
        rw [Category.assoc]
      _ = l ≫ (pullback.snd (pullback.fst y e) (pullback.fst y e) ≫ h) := by
        rw [hcompat]
      _ = (l ≫ pullback.snd (pullback.fst y e) (pullback.fst y e)) ≫ h := by
        rw [Category.assoc]
      _ = b ≫ h := by
        rw [pullback.lift_snd]

end KernelPair

end EtaleMorphisms

end

end GromovWitten.AlgebraicGeometry
