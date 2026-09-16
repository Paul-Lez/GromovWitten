/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.Fibers
import GromovWitten.AlgebraicGeometry.Curves.RelativeLineBundles

/-!
# Models of curves over discrete valuation rings

This file starts Layer 0 of the stable-reduction roadmap.  A model remembers an explicit
identification of its generic fibre with the curve being modelled.  In particular, morphisms
of models cannot silently change that identification.

Finite extensions of the base DVR and the generic/special fibre constructions live in
`DVRExtension` and `Fibers`, respectively.
-/

open CategoryTheory Limits
open AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

/-- A flat finitely presented model carrying its generic-fibre identification. -/
structure Model (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : Scheme.{u}) (toK : C ⟶ Spec (.of K)) where
  total : Scheme.{u}
  toBase : total ⟶ Spec (.of R)
  flat : Flat toBase
  locallyOfFinitePresentation : LocallyOfFinitePresentation toBase
  quasiCompact : QuasiCompact toBase
  genericFiberIso : genericFiber R K toBase ≅ Over.mk toK

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The morphism on generic fibres induced by a morphism over the base. -/
def baseChangeHom {M N : Model R K C toK} (f : M.total ⟶ N.total)
    (over_base : f ≫ N.toBase = M.toBase) :
    pullback M.toBase (genericPointMap R K) ⟶ pullback N.toBase (genericPointMap R K) :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (by
    rw [Category.assoc, over_base]
    exact pullback.condition)

/-- A morphism of models commutes with the base maps and the chosen generic-fibre maps. -/
structure Hom (M N : Model R K C toK) where
  hom : M.total ⟶ N.total
  over_base : hom ≫ N.toBase = M.toBase
  genericFiber :
    baseChangeHom (R := R) (K := K) hom over_base ≫ N.genericFiberIso.hom.left =
      M.genericFiberIso.hom.left

instance (M : Model R K C toK) : Flat M.toBase := M.flat

instance (M : Model R K C toK) : LocallyOfFinitePresentation M.toBase :=
  M.locallyOfFinitePresentation

instance (M : Model R K C toK) : QuasiCompact M.toBase := M.quasiCompact

/-- Properness is an additional property of a model, not bundled model data. -/
abbrev IsProper (M : Model R K C toK) : Prop := _root_.AlgebraicGeometry.IsProper M.toBase

/-- A nodal model is one whose structural morphism is at worst nodal on every geometric
fibre. -/
abbrev IsNodal (M : Model R K C toK) : Prop :=
  GromovWitten.AlgebraicGeometry.Curves.AtWorstNodal M.toBase

/-- Relative dualizing data carried by a model. -/
abbrev DualizingSheaf (M : Model R K C toK) :=
  GromovWitten.AlgebraicGeometry.Curves.RelativeDualizingSheaf M.toBase

/-- A model is semistable relative to chosen dualizing data when it is proper and nodal and the
dualizing degree is nonnegative on every geometric component. -/
abbrev IsSemistable (M : Model R K C toK) (D : M.DualizingSheaf) : Prop :=
  D.IsSemistable

/-- A model is stable relative to chosen dualizing data when it is proper and nodal and the
dualizing degree is positive on every geometric component. -/
abbrev IsStable (M : Model R K C toK) (D : M.DualizingSheaf) : Prop :=
  D.IsStable

@[ext]
lemma Hom.ext {M N : Model R K C toK} {f g : Hom M N} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[simp]
lemma baseChangeHom_id (M : Model R K C toK) :
    baseChangeHom (R := R) (K := K) (𝟙 M.total) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [baseChangeHom]
  · simp [baseChangeHom]

lemma baseChangeHom_comp {M N P : Model R K C toK} (f : Hom M N) (g : Hom N P) :
    baseChangeHom (R := R) (K := K) (f.hom ≫ g.hom) (by
      rw [Category.assoc, g.over_base, f.over_base]) =
      baseChangeHom (R := R) (K := K) f.hom f.over_base ≫
        baseChangeHom (R := R) (K := K) g.hom g.over_base := by
  apply pullback.hom_ext
  · simp only [baseChangeHom, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
  · simp only [baseChangeHom, pullback.lift_snd, Category.assoc]

/-- Models of a fixed generic fibre form a category. -/
instance : Category (Model R K C toK) where
  Hom := Hom
  id M :=
    { hom := 𝟙 M.total
      over_base := by simp
      genericFiber := by
        dsimp only [genericFiber]
        rw [baseChangeHom_id, Category.id_comp] }
  comp f g :=
    { hom := f.hom ≫ g.hom
      over_base := by rw [Category.assoc, g.over_base, f.over_base]
      genericFiber := by
        dsimp only [genericFiber] at f g ⊢
        rw [baseChangeHom_comp, Category.assoc, g.genericFiber, f.genericFiber] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

/-- A model, regarded as its structural morphism over the DVR. -/
@[simps]
def toOverFunctor : Model R K C toK ⥤ Over (Spec (.of R)) where
  obj M := Over.mk M.toBase
  map f := Over.homMk f.hom f.over_base
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance toOverFunctor_faithful :
    (toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).Faithful where
  map_injective {_ _} f g h := by
    apply Hom.ext
    exact congrArg Over.Hom.left h

/-- A morphism of models is an isomorphism as soon as its map of total spaces is an
isomorphism.  Compatibility of the inverse with the chosen generic-fibre identifications
follows from that of the original morphism. -/
lemma Hom.isIso_of_hom_isIso {M N : Model R K C toK} (f : M ⟶ N)
    [IsIso f.hom] : IsIso f := by
  let overBase : inv f.hom ≫ M.toBase = N.toBase := by
    rw [← f.over_base]
    simp
  have hbaseChange :
      baseChangeHom (R := R) (K := K) (inv f.hom) overBase ≫
          baseChangeHom (R := R) (K := K) f.hom f.over_base = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [baseChangeHom, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.assoc]
      simp
    · simp only [baseChangeHom, pullback.lift_snd, Category.assoc]
      simp
  let g : N ⟶ M :=
    { hom := inv f.hom
      over_base := overBase
      genericFiber := by
        rw [← f.genericFiber, ← Category.assoc, hbaseChange, Category.id_comp] }
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply Hom.ext
    change f.hom ≫ inv f.hom = 𝟙 _
    exact IsIso.hom_inv_id f.hom
  · apply Hom.ext
    change inv f.hom ≫ f.hom = 𝟙 _
    exact IsIso.inv_hom_id_assoc f.hom (𝟙 _)

/-- Forgetting a model to its structural morphism reflects isomorphisms. -/
instance toOverFunctor_reflectsIsomorphisms :
    (toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).ReflectsIsomorphisms where
  reflects f _ := by
    have hhom : IsIso f.hom := by
      change IsIso ((Over.forget (Spec (.of R))).map
        ((toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map f))
      infer_instance
    apply Hom.isIso_of_hom_isIso (f := f)

/-- Generic fibre as a functor on models of the fixed generic curve. -/
abbrev genericFiberModelFunctor :
    Model R K C toK ⥤ Over (Spec (.of K)) :=
  toOverFunctor (R := R) (K := K) (C := C) (toK := toK) ⋙ genericFiberFunctor R K

/-- Special fibre as a functor on models of the fixed generic curve. -/
abbrev specialFiberModelFunctor :
    Model R K C toK ⥤ Over (Spec (.of (specialResidueField R))) :=
  toOverFunctor (R := R) (K := K) (C := C) (toK := toK) ⋙ specialFiberFunctor R

/-- The identifications carried by models form a natural isomorphism from their generic
fibres to the constant functor at the fixed curve. -/
noncomputable def genericFiberIdentificationNatIso :
    genericFiberModelFunctor (R := R) (K := K) (C := C) (toK := toK) ≅
      (Functor.const (Model R K C toK)).obj (Over.mk toK) :=
  NatIso.ofComponents (fun M ↦ M.genericFiberIso) (fun {M N} f ↦ by
    ext
    exact f.genericFiber)

/-- The chosen generic-fibre identification, regarded as an isomorphism of arrows. -/
noncomputable def genericFiberArrowIso (M : Model R K C toK) :
    Arrow.mk (genericFiber R K M.toBase).hom ≅ Arrow.mk toK :=
  Arrow.isoMk ((Over.forget _).mapIso M.genericFiberIso) (Iso.refl _) M.genericFiberIso.hom.w

/-- The fixed generic curve is flat whenever it admits a model. -/
theorem genericCurve_flat (M : Model R K C toK) : Flat toK := by
  have h : Flat (M.genericFiberIso.inv.left ≫ (genericFiber R K M.toBase).hom) := by
    infer_instance
  rw [M.genericFiberIso.inv.w] at h
  exact h

/-- The generic fibre of a proper model is proper over the fraction field. -/
instance genericFiber_isProper (M : Model R K C toK) [M.IsProper] :
    _root_.AlgebraicGeometry.IsProper (genericFiber R K M.toBase).hom := by
  change _root_.AlgebraicGeometry.IsProper
    (pullback.snd M.toBase (genericPointMap R K))
  infer_instance

/-- A proper model certifies properness of the fixed generic curve. -/
theorem genericCurve_isProper (M : Model R K C toK) [M.IsProper] :
    _root_.AlgebraicGeometry.IsProper toK := by
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := @_root_.AlgebraicGeometry.IsProper) (genericFiberArrowIso M)).mp inferInstance

/-- The special fibre of a proper model is proper over the residue field.  This is the
properness input needed by later good-reduction statements; smoothness remains separate. -/
instance specialFiber_isProper (M : Model R K C toK) [M.IsProper] :
    _root_.AlgebraicGeometry.IsProper (specialFiber R M.toBase).hom := by
  change _root_.AlgebraicGeometry.IsProper
    (pullback.snd M.toBase (specialPointMap R))
  infer_instance

section BaseChange

variable (E : FiniteDVRExtension R K)

/-- Base change of the generic curve to the extension field. -/
abbrev baseChangedCurve : Over (Spec (.of E.extensionField)) :=
  (Over.pullback (FiniteDVRExtension.extensionSpecMap R K E)).obj (Over.mk toK)

/-- The total space after base change to the selected extension DVR. -/
abbrev baseChangedTotal (M : Model R K C toK) : Over (Spec (.of E.localRing)) :=
  (Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).obj (Over.mk M.toBase)

/-- The scheme-level comparison between the two orders of base change in the commuting
generic-point square attached to `E`. -/
noncomputable def iteratedBaseChangeIso (X : Over (Spec (.of R))) :
    pullback
        ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).obj X).hom
        (genericPointMap E.localRing E.extensionField) ≅
      pullback ((Over.pullback (genericPointMap R K)).obj X).hom
        (FiniteDVRExtension.extensionSpecMap R K E) :=
  pullbackLeftPullbackSndIso X.hom (FiniteDVRExtension.baseSpecMap R K E)
      (genericPointMap E.localRing E.extensionField) ≪≫
    pullback.congrHom rfl
      (FiniteDVRExtension.genericPointMap_baseSpecMap R K E) ≪≫
    (pullbackLeftPullbackSndIso X.hom (genericPointMap R K)
      (FiniteDVRExtension.extensionSpecMap R K E)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma iteratedBaseChangeIso_hom_snd (X : Over (Spec (.of R))) :
    (iteratedBaseChangeIso E X).hom ≫
        pullback.snd ((Over.pullback (genericPointMap R K)).obj X).hom
          (FiniteDVRExtension.extensionSpecMap R K E) =
      pullback.snd
        ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).obj X).hom
        (genericPointMap E.localRing E.extensionField) := by
  simp [iteratedBaseChangeIso]

/-- The iterated-base-change comparison as an isomorphism over the extension field. -/
noncomputable def iteratedBaseChangeOverIso (X : Over (Spec (.of R))) :
    (Over.pullback (FiniteDVRExtension.baseSpecMap R K E) ⋙
        Over.pullback (genericPointMap E.localRing E.extensionField)).obj X ≅
      (Over.pullback (genericPointMap R K) ⋙
        Over.pullback (FiniteDVRExtension.extensionSpecMap R K E)).obj X :=
  Over.isoMk (iteratedBaseChangeIso E X) (iteratedBaseChangeIso_hom_snd E X)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical, natural comparison between the two iterated base-change functors. -/
noncomputable def iteratedBaseChangeNatIso :
    Over.pullback (FiniteDVRExtension.baseSpecMap R K E) ⋙
        Over.pullback (genericPointMap E.localRing E.extensionField) ≅
      Over.pullback (genericPointMap R K) ⋙
        Over.pullback (FiniteDVRExtension.extensionSpecMap R K E) :=
  NatIso.ofComponents (iteratedBaseChangeOverIso E) (by
    intro X Y f
    ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [iteratedBaseChangeOverIso, iteratedBaseChangeIso, Over.pullback]
      · simp [iteratedBaseChangeOverIso, iteratedBaseChangeIso, Over.pullback]
    · simp [iteratedBaseChangeOverIso, iteratedBaseChangeIso, Over.pullback])

/-- The generic-fibre identification inherited by the base-changed model. -/
noncomputable def baseChangedGenericFiberIso (M : Model R K C toK) :
    genericFiber E.localRing E.extensionField (baseChangedTotal E M).hom ≅
      baseChangedCurve (C := C) (toK := toK) E :=
  (iteratedBaseChangeNatIso E).app (Over.mk M.toBase) ≪≫
    (Over.pullback (FiniteDVRExtension.extensionSpecMap R K E)).mapIso
      M.genericFiberIso

/-- A model pulled back to the selected extension DVR, with generic curve simultaneously
pulled back to the extension field. -/
noncomputable def baseChangeObj (M : Model R K C toK) :
    Model E.localRing E.extensionField
      (baseChangedCurve (C := C) (toK := toK) E).left
      (baseChangedCurve (C := C) (toK := toK) E).hom where
  total := (baseChangedTotal E M).left
  toBase := (baseChangedTotal E M).hom
  flat := by
    dsimp [baseChangedTotal, Over.pullback]
    infer_instance
  locallyOfFinitePresentation := by
    dsimp [baseChangedTotal, Over.pullback]
    infer_instance
  quasiCompact := by
    dsimp [baseChangedTotal, Over.pullback]
    infer_instance
  genericFiberIso := baseChangedGenericFiberIso E M

/-- Relative dualizing data pulls back to the finite-DVR base-changed model. -/
noncomputable def baseChangeDualizingSheaf (M : Model R K C toK)
    (D : M.DualizingSheaf) : (baseChangeObj E M).DualizingSheaf :=
  D.pullback (FiniteDVRExtension.baseSpecMap R K E)

/-- Semistability of a model is preserved by finite-DVR-extension base change. -/
theorem baseChangeObj_isSemistable (M : Model R K C toK) (D : M.DualizingSheaf)
    (h : M.IsSemistable D) :
    (baseChangeObj E M).IsSemistable (baseChangeDualizingSheaf E M D) :=
  D.pullback_isSemistable (FiniteDVRExtension.baseSpecMap R K E) h

/-- Stability of a model is preserved by finite-DVR-extension base change. -/
theorem baseChangeObj_isStable (M : Model R K C toK) (D : M.DualizingSheaf)
    (h : M.IsStable D) :
    (baseChangeObj E M).IsStable (baseChangeDualizingSheaf E M D) :=
  D.pullback_isStable (FiniteDVRExtension.baseSpecMap R K E) h

/-- Properness of models is preserved by finite-DVR-extension base change. -/
instance baseChangeObj_isProper (M : Model R K C toK) [M.IsProper] :
    (baseChangeObj E M).IsProper := by
  change _root_.AlgebraicGeometry.IsProper
    (pullback.snd M.toBase (FiniteDVRExtension.baseSpecMap R K E))
  infer_instance

/-- Regard a morphism of models as a morphism over the original DVR. -/
private abbrev asOverHom {M N : Model R K C toK} (f : Hom M N) :
    Over.mk M.toBase ⟶ Over.mk N.toBase :=
  (toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map f

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the inherited generic-fibre identifications. -/
lemma baseChangedGenericFiberIso_naturality {M N : Model R K C toK} (f : Hom M N) :
    ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E) ⋙
        Over.pullback (genericPointMap E.localRing E.extensionField)).map (asOverHom f)) ≫
        (baseChangedGenericFiberIso E N).hom =
      (baseChangedGenericFiberIso E M).hom := by
  have hOrig :
      (Over.pullback (genericPointMap R K)).map (asOverHom f) ≫
          N.genericFiberIso.hom =
        M.genericFiberIso.hom := by
    ext
    exact f.genericFiber
  change ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E) ⋙
      Over.pullback (genericPointMap E.localRing E.extensionField)).map (asOverHom f)) ≫
      (iteratedBaseChangeNatIso E).hom.app (Over.mk N.toBase) ≫
        (Over.pullback (FiniteDVRExtension.extensionSpecMap R K E)).map
          N.genericFiberIso.hom =
    (iteratedBaseChangeNatIso E).hom.app (Over.mk M.toBase) ≫
      (Over.pullback (FiniteDVRExtension.extensionSpecMap R K E)).map
        M.genericFiberIso.hom
  rw [(iteratedBaseChangeNatIso E).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, hOrig]

set_option backward.isDefEq.respectTransparency false in
/-- Base change of a morphism of models. -/
noncomputable def baseChangeMap {M N : Model R K C toK} (f : Hom M N) :
    Hom (baseChangeObj E M) (baseChangeObj E N) where
  hom := ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
    (asOverHom f)).left
  over_base := Over.w ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
    (asOverHom f))
  genericFiber := by
    have h := congrArg Over.Hom.left (baseChangedGenericFiberIso_naturality E f)
    change ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E) ⋙
        Over.pullback (genericPointMap E.localRing E.extensionField)).map
          (asOverHom f)).left ≫
        (baseChangedGenericFiberIso E N).hom.left =
      (baseChangedGenericFiberIso E M).hom.left
    exact h

@[simp]
private lemma asOverHom_id (M : Model R K C toK) : asOverHom (𝟙 M) = 𝟙 _ := by
  ext
  rfl

@[simp]
private lemma asOverHom_comp {M N P : Model R K C toK} (f : M ⟶ N) (g : N ⟶ P) :
    asOverHom (f ≫ g) = asOverHom f ≫ asOverHom g := by
  ext
  rfl

/-- Pullback along a chosen finite DVR extension, as a functor on models. -/
noncomputable def baseChangeFunctor :
    Model R K C toK ⥤
      Model E.localRing E.extensionField
        (baseChangedCurve (C := C) (toK := toK) E).left
        (baseChangedCurve (C := C) (toK := toK) E).hom where
  obj := baseChangeObj E
  map := baseChangeMap E
  map_id M := by
    apply Hom.ext
    change ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
      (asOverHom (𝟙 M))).left = 𝟙 _
    rw [asOverHom_id]
    exact congrArg Over.Hom.left
      ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map_id
        (Over.mk M.toBase))
  map_comp f g := by
    apply Hom.ext
    change ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
        (asOverHom (f ≫ g))).left =
      ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
        (asOverHom f)).left ≫
      ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
        (asOverHom g)).left
    rw [asOverHom_comp]
    exact congrArg Over.Hom.left
      ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map_comp
        (asOverHom f) (asOverHom g))

/-- Finite-DVR-extension base change is faithful on model morphisms.  Thus two morphisms of
models agree whenever their pullbacks to the selected faithfully flat extension DVR agree. -/
instance baseChangeFunctor_faithful :
    (baseChangeFunctor (R := R) (K := K) (C := C) (toK := toK) E).Faithful where
  map_injective {M N} f g h := by
    apply (toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map_injective
    apply (Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map_injective
    ext
    exact congrArg Hom.hom h

/-- Finite-DVR-extension base change reflects isomorphisms of models. -/
instance baseChangeFunctor_reflectsIsomorphisms :
    (baseChangeFunctor (R := R) (K := K) (C := C) (toK := toK) E).ReflectsIsomorphisms where
  reflects f _ := by
    have hpullback :
        IsIso ((Over.pullback (FiniteDVRExtension.baseSpecMap R K E)).map
          ((toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map f)) := by
      change IsIso
        ((toOverFunctor (R := E.localRing) (K := E.extensionField)
          (C := (baseChangedCurve (C := C) (toK := toK) E).left)
          (toK := (baseChangedCurve (C := C) (toK := toK) E).hom)).map
            ((baseChangeFunctor (R := R) (K := K) (C := C) (toK := toK) E).map f))
      infer_instance
    have horiginal :
        IsIso ((toOverFunctor (R := R) (K := K) (C := C) (toK := toK)).map f) := by
      apply isIso_of_reflects_iso _
        (Over.pullback (FiniteDVRExtension.baseSpecMap R K E))
    apply isIso_of_reflects_iso f
      (toOverFunctor (R := R) (K := K) (C := C) (toK := toK))

end BaseChange

/-- Isomorphisms of models are categorical isomorphisms. -/
abbrev Iso (M N : Model R K C toK) := M ≅ N

end Model

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
