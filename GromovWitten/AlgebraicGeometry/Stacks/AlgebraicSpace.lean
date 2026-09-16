/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Stacks.Scheme

/-!
# Algebraic spaces as discrete groupoid-valued stacks

An algebraic space is already an fppf sheaf of types, so it determines a discrete
groupoid-valued fppf stack.  This file proves the resulting embedding is bicategorically fully
faithful: every strong transformation between two such discrete stacks comes from a unique
morphism of algebraic spaces, up to a constructed invertible modification.  Identity,
composition, and equivalences are all obtained from the underlying sheaf maps.

No presentation or atlas is used in this comparison.  In particular, the construction does not
add a second notion of morphism for algebraic spaces and does not ask for any geometric theorem
as input.
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace GromovWitten.AlgebraicGeometry

universe u

namespace FppfStack

/-- An algebraic space, regarded as the discrete fppf stack of its functor of points. -/
noncomputable def ofAlgebraicSpace (X : AlgebraicSpace.{u}) : FppfStack.{u} :=
  ofSheaf X.toSheaf

/-- The discrete stack associated to an algebraic space, viewed as an object of the full
bicategory of fppf stacks. -/
noncomputable def ofAlgebraicSpaceObj (X : AlgebraicSpace.{u}) : FppfBicategory.{u} :=
  asBicategory (ofAlgebraicSpace X)

/-- A morphism of algebraic spaces induces a strong transformation of their discrete stacks. -/
def mapOfAlgebraicSpaceHom {X Y : AlgebraicSpace.{u}} (f : X ⟶ Y) :
    StackHom (ofAlgebraicSpace X) (ofAlgebraicSpace Y) :=
  mapOfSheafHom f.hom

/-- Extract the unique algebraic-space morphism underlying a strong transformation between
discrete algebraic-space stacks. -/
def algebraicSpaceHomOfMap {X Y : AlgebraicSpace.{u}}
    (η : StackHom (ofAlgebraicSpace X) (ofAlgebraicSpace Y)) : X ⟶ Y :=
  AlgebraicSpace.homMk (sheafHomOfMap η)

/-- Extracting the morphism of a promoted algebraic-space morphism recovers the original
morphism. -/
@[simp]
theorem algebraicSpaceHomOfMap_mapOfAlgebraicSpaceHom
    {X Y : AlgebraicSpace.{u}} (f : X ⟶ Y) :
    algebraicSpaceHomOfMap (mapOfAlgebraicSpaceHom f) = f := by
  apply InducedCategory.hom_ext
  apply ObjectProperty.hom_ext
  exact Pseudofunctor.natTransOfStrongTrans_strongTransOfNatTrans _

/-- Extracting the algebraic-space morphism underlying the identity strong transformation gives
the identity morphism. -/
@[simp]
theorem algebraicSpaceHomOfMap_id (X : AlgebraicSpace.{u}) :
    algebraicSpaceHomOfMap
      (Pseudofunctor.StrongTrans.id (ofAlgebraicSpace X).toPseudofunctor) = 𝟙 X := by
  apply InducedCategory.hom_ext
  apply ObjectProperty.hom_ext
  ext T x
  rfl

/-- Every strong transformation between discrete algebraic-space stacks is invertibly
2-isomorphic to the promotion of its extracted algebraic-space morphism. -/
def mapOfAlgebraicSpaceHom_algebraicSpaceHomOfMap_iso
    {X Y : AlgebraicSpace.{u}}
    (η : StackHom (ofAlgebraicSpace X) (ofAlgebraicSpace Y)) :
    StackIso2 (mapOfAlgebraicSpaceHom (algebraicSpaceHomOfMap η)) η := by
  rw [mapOfAlgebraicSpaceHom, algebraicSpaceHomOfMap, mapOfSheafHom]
  exact
    { hom := Pseudofunctor.discreteCounitHom η
      inv := Pseudofunctor.discreteCounitInv η
      hom_inv_id := (Pseudofunctor.discreteCounitIso2 η).hom_inv_id
      inv_hom_id := (Pseudofunctor.discreteCounitIso2 η).inv_hom_id }

/-- Promotion of the identity algebraic-space morphism is invertibly 2-isomorphic to the
identity stack morphism. -/
noncomputable def mapOfAlgebraicSpaceHom_id_iso (X : AlgebraicSpace.{u}) :
    StackIso2 (mapOfAlgebraicSpaceHom (𝟙 X))
      (Pseudofunctor.StrongTrans.id (ofAlgebraicSpace X).toPseudofunctor) := by
  simpa only [algebraicSpaceHomOfMap_id] using
    mapOfAlgebraicSpaceHom_algebraicSpaceHomOfMap_iso
      (Pseudofunctor.StrongTrans.id (ofAlgebraicSpace X).toPseudofunctor)

/-- The discrete-stack embedding is faithful even after allowing invertible 2-morphisms. -/
theorem mapOfAlgebraicSpaceHom_injective_up_to_iso
    {X Y : AlgebraicSpace.{u}} {f g : X ⟶ Y}
    (e : StackIso2 (mapOfAlgebraicSpaceHom f) (mapOfAlgebraicSpaceHom g)) : f = g := by
  apply InducedCategory.hom_ext
  apply ObjectProperty.hom_ext
  exact Pseudofunctor.natTransOfStrongTrans_eq_of_modification e.hom

private theorem algebraicSpaceHom_vcomp_mapOfAlgebraicSpaceHom
    {X Y Z : AlgebraicSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicSpaceHomOfMap
      (Pseudofunctor.StrongTrans.vcomp
        (mapOfAlgebraicSpaceHom f) (mapOfAlgebraicSpaceHom g)) = f ≫ g := by
  apply InducedCategory.hom_ext
  apply ObjectProperty.hom_ext
  ext T x
  rfl

/-- Promotion respects composition through a constructed invertible modification. -/
noncomputable def mapOfAlgebraicSpaceHom_comp_iso
    {X Y Z : AlgebraicSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    StackIso2
      (Pseudofunctor.StrongTrans.vcomp
        (mapOfAlgebraicSpaceHom f) (mapOfAlgebraicSpaceHom g))
      (mapOfAlgebraicSpaceHom (f ≫ g)) := by
  let c := Pseudofunctor.StrongTrans.vcomp
    (mapOfAlgebraicSpaceHom f) (mapOfAlgebraicSpaceHom g)
  have e := mapOfAlgebraicSpaceHom_algebraicSpaceHomOfMap_iso c
  rw [algebraicSpaceHom_vcomp_mapOfAlgebraicSpaceHom f g] at e
  exact e.symm

/-- Modifications between arbitrary strong transformations of discrete algebraic-space stacks
are unique when they exist.  This is proved componentwise from discreteness of the fibres; it is
not imposed on general stacks. -/
theorem algebraicSpaceModification_subsingleton
    {X Y : AlgebraicSpace.{u}}
    (f g : ofAlgebraicSpaceObj X ⟶ ofAlgebraicSpaceObj Y) :
    Subsingleton (f ⟶ g) :=
  ⟨fun m n ↦ by
    apply InducedBicategory.hom₂_ext
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change @Eq (ULift (PLift (_ = _))) _ _
    exact Subsingleton.elim _ _⟩

/-- On every pair of objects, promotion sends the discrete category of algebraic-space
morphisms to the full hom-category of strong transformations and modifications. -/
noncomputable def algebraicSpaceHomFunctor (X Y : AlgebraicSpace.{u}) :
    Discrete (X ⟶ Y) ⥤ (ofAlgebraicSpaceObj X ⟶ ofAlgebraicSpaceObj Y) where
  obj f := InducedBicategory.mkHom (mapOfAlgebraicSpaceHom f.as)
  map {f g} m := by
    exact eqToHom (InducedBicategory.hom_ext
      (congrArg mapOfAlgebraicSpaceHom (Discrete.eq_of_hom m)))
  map_id := by
    intro f
    apply (algebraicSpaceModification_subsingleton _ _).elim
  map_comp := by
    intro f g h m n
    apply (algebraicSpaceModification_subsingleton _ _).elim

/-- The local hom functor is fully faithful, including at the modification level.  A
modification forces equality of the underlying sheaf maps, hence equality of the original
algebraic-space morphisms. -/
noncomputable def algebraicSpaceHomFunctorFullyFaithful (X Y : AlgebraicSpace.{u}) :
    (algebraicSpaceHomFunctor X Y).FullyFaithful where
  preimage {f g} m := Discrete.eqToHom (by
    apply InducedCategory.hom_ext
    apply ObjectProperty.hom_ext
    exact Pseudofunctor.natTransOfStrongTrans_eq_of_modification m.hom.as)
  map_preimage {f g} m := (algebraicSpaceModification_subsingleton _ _).elim _ _
  preimage_map {f g} m := Subsingleton.elim _ _

theorem algebraicSpaceHomFunctorEssSurj (X Y : AlgebraicSpace.{u}) :
    (algebraicSpaceHomFunctor X Y).EssSurj where
  mem_essImage η :=
    ⟨Discrete.mk (algebraicSpaceHomOfMap η.hom),
      ⟨stackIso2ToBicategoryIso
        (mapOfAlgebraicSpaceHom_algebraicSpaceHomOfMap_iso η.hom)⟩⟩

/-- Promotion induces an equivalence from the discrete category of algebraic-space morphisms to
the complete hom-category between the corresponding discrete stacks. -/
noncomputable def algebraicSpaceHomEquivalence (X Y : AlgebraicSpace.{u}) :
    Discrete (X ⟶ Y) ≌ (ofAlgebraicSpaceObj X ⟶ ofAlgebraicSpaceObj Y) := by
  let F := algebraicSpaceHomFunctor X Y
  letI : F.IsEquivalence :=
    { faithful := (algebraicSpaceHomFunctorFullyFaithful X Y).faithful
      full := (algebraicSpaceHomFunctorFullyFaithful X Y).full
      essSurj := algebraicSpaceHomFunctorEssSurj X Y }
  exact F.asEquivalence

/-- Algebraic spaces embed as discrete fppf stacks by a bundled pseudofunctor.  Its unitor and
compositor are the constructed invertible modifications above.  Their coherence follows from
the proved uniqueness of modifications between maps of discrete stacks. -/
noncomputable def algebraicSpaceEmbedding :
    LocallyDiscrete AlgebraicSpace.{u} ⥤ᵖ FppfBicategory.{u} :=
  LocallyDiscrete.mkPseudofunctor
    ofAlgebraicSpaceObj
    (fun f ↦ InducedBicategory.mkHom (mapOfAlgebraicSpaceHom f))
    (fun X ↦ stackIso2ToBicategoryIso (mapOfAlgebraicSpaceHom_id_iso X))
    (fun f g ↦ stackIso2ToBicategoryIso (mapOfAlgebraicSpaceHom_comp_iso f g).symm)
    (by
      intro X Y Z W f g h
      apply (algebraicSpaceModification_subsingleton _ _).elim)
    (by
      intro X Y f
      apply (algebraicSpaceModification_subsingleton _ _).elim)
    (by
      intro X Y f
      apply (algebraicSpaceModification_subsingleton _ _).elim)

/-- An isomorphism of algebraic spaces induces an equivalence of their discrete fppf stacks.
Both inverse 2-cells are derived from the actual inverse laws of the isomorphism. -/
noncomputable def stackEquivalenceOfAlgebraicSpaceIso
    {X Y : AlgebraicSpace.{u}} (e : X ≅ Y) :
    StackEquivalenceData (ofAlgebraicSpace X) (ofAlgebraicSpace Y) where
  hom := mapOfAlgebraicSpaceHom e.hom
  inv := mapOfAlgebraicSpaceHom e.inv
  homInv := by
    have h := mapOfAlgebraicSpaceHom_comp_iso e.hom e.inv
    rw [e.hom_inv_id] at h
    exact h.trans (mapOfAlgebraicSpaceHom_id_iso X)
  invHom := by
    have h := mapOfAlgebraicSpaceHom_comp_iso e.inv e.hom
    rw [e.inv_hom_id] at h
    exact h.trans (mapOfAlgebraicSpaceHom_id_iso Y)

/-- A sheaf morphism from a represented scheme determines a genuine scheme chart of the
associated discrete stack. -/
noncomputable def sheafChart (P : FppfSheaf.{u}) (U : Scheme.{u})
    (p : fppfYoneda.obj U ⟶ P) : StackChart (ofSheaf P) where
  scheme := U
  map := mapOfSheafHom p

private theorem sheafChart_pullback_eq
    (P : FppfSheaf.{u}) (U T : Scheme.{u})
    (p : fppfYoneda.obj U ⟶ P) (hp : FppfSheaf.IsRepresentable p)
    (x : StackFiber (ofSheaf P) T) :
    p.hom.app (Opposite.op (hp.pullback
        ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as)))
        (hp.fst' ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as)) =
      P.obj.map
        (hp.snd ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as)).op
        x.as := by
  let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
    GrothendieckTopology Scheme.{u})
  let g := J.yonedaEquiv.symm x.as
  have h := hp.w g
  rw [← hp.map_fst' g] at h
  have h' := congrArg J.yonedaEquiv h
  change p.hom.app (Opposite.op (hp.pullback g))
      (J.yonedaEquiv (J.yoneda.map (hp.fst' g))) =
    g.hom.app (Opposite.op (hp.pullback g))
      (J.yonedaEquiv (J.yoneda.map (hp.snd g))) at h'
  rw [J.yonedaEquiv_yoneda_map, J.yonedaEquiv_yoneda_map] at h'
  change p.hom.app (Opposite.op (hp.pullback g)) (hp.fst' g) =
    P.obj.map (hp.snd g).op x.as at h'
  exact h'

/-- The base change of a representable scheme-to-sheaf chart is the actual representing scheme
chosen by relative representability.  Its full universal property is transported from the
sheaf pullback square. -/
noncomputable def sheafChartPullbackPresentation
    (P : FppfSheaf.{u}) (U T : Scheme.{u})
    (p : fppfYoneda.obj U ⟶ P) (hp : FppfSheaf.IsRepresentable p)
    (x : StackFiber (ofSheaf P) T) :
    (sheafChart P U p).PullbackPresentation T x := by
  let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
    GrothendieckTopology Scheme.{u})
  let g := J.yonedaEquiv.symm x.as
  let comparison :
      (sheafChart P U p).obj (hp.pullback g) (hp.fst' g) ≅
        (stackPullback (ofSheaf P) (hp.snd g)).obj x :=
    Discrete.eqToIso (sheafChart_pullback_eq P U T p hp x)
  exact
    { space := hp.pullback g
      fst := hp.snd g
      snd := hp.fst' g
      comparison := comparison
      lift := fun {S} toBase toChart c ↦ by
        change S ⟶ U at toChart
        have hc := Discrete.eq_of_hom c.hom
        change p.hom.app _ toChart = P.obj.map toBase.op x.as at hc
        apply hp.lift' toChart toBase
        apply J.yonedaEquiv.injective
        change p.hom.app (Opposite.op S)
            (J.yonedaEquiv (J.yoneda.map toChart)) =
          g.hom.app (Opposite.op S) (J.yonedaEquiv (J.yoneda.map toBase))
        rw [J.yonedaEquiv_yoneda_map, J.yonedaEquiv_yoneda_map]
        change p.hom.app _ toChart = P.obj.map toBase.op x.as
        exact hc
      lift_fst := by
        intro S toBase toChart c
        exact hp.lift'_snd _ _ _
      lift_snd := by
        intro S toBase toChart c
        exact hp.lift'_fst _ _ _
      lift_compatible := by
        intro S toBase toChart c
        refine ⟨hp.lift'_snd _ _ _, hp.lift'_fst _ _ _, ?_⟩
        apply Iso.ext
        change @Eq (ULift (PLift (_ = _))) _ _
        apply Subsingleton.elim
      lift_unique := by
        intro S toBase toChart c m compatible
        obtain ⟨hmBase, hmChart, -⟩ := compatible
        apply hp.hom_ext'
        · exact hmChart.trans (hp.lift'_fst _ _ _).symm
        · exact hmBase.trans (hp.lift'_snd _ _ _).symm }

/-- Any presentation of the same discrete chart pullback is canonically isomorphic to the
scheme selected by the sheaf-level pullback.  The inverse laws use both projection equations;
the comparison equation is unique because all target fibres are discrete. -/
noncomputable def sheafChartPullbackPresentationIso
    (P : FppfSheaf.{u}) (U T : Scheme.{u})
    (p : fppfYoneda.obj U ⟶ P) (hp : FppfSheaf.IsRepresentable p)
    (x : StackFiber (ofSheaf P) T)
    (r : (sheafChart P U p).PullbackPresentation T x) :
    r.space ≅ (sheafChartPullbackPresentation P U T p hp x).space := by
  let q := sheafChartPullbackPresentation P U T p hp x
  let hom : r.space ⟶ q.space := q.lift r.fst r.snd r.comparison
  let inv : q.space ⟶ r.space := r.lift q.fst q.snd q.comparison
  have hhomFst : hom ≫ q.fst = r.fst := q.lift_fst _ _ _
  have hhomSnd : hom ≫ q.snd = r.snd := q.lift_snd _ _ _
  have hinvFst : inv ≫ r.fst = q.fst := r.lift_fst _ _ _
  have hinvSnd : inv ≫ r.snd = q.snd := r.lift_snd _ _ _
  have hidR : 𝟙 r.space = r.lift r.fst r.snd r.comparison := by
    apply r.lift_unique r.fst r.snd r.comparison
    refine ⟨by simp, by simp, ?_⟩
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  have hcompR : hom ≫ inv = r.lift r.fst r.snd r.comparison := by
    apply r.lift_unique r.fst r.snd r.comparison
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Category.assoc, hinvFst] using hhomFst
    · simpa only [Category.assoc, hinvSnd] using hhomSnd
    · apply Iso.ext
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
  have hidQ : 𝟙 q.space = q.lift q.fst q.snd q.comparison := by
    apply q.lift_unique q.fst q.snd q.comparison
    refine ⟨by simp, by simp, ?_⟩
    apply Iso.ext
    change @Eq (ULift (PLift (_ = _))) _ _
    apply Subsingleton.elim
  have hcompQ : inv ≫ hom = q.lift q.fst q.snd q.comparison := by
    apply q.lift_unique q.fst q.snd q.comparison
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Category.assoc, hhomFst] using hinvFst
    · simpa only [Category.assoc, hhomSnd] using hinvSnd
    · apply Iso.ext
      change @Eq (ULift (PLift (_ = _))) _ _
      apply Subsingleton.elim
  exact
    { hom := hom
      inv := inv
      hom_inv_id := hcompR.trans hidR.symm
      inv_hom_id := hcompQ.trans hidQ.symm }

/-- A representable property of the original sheaf chart gives the same property to the
corresponding stack chart.  The condition for every stack presentation is derived by comparing
it to the actual sheaf pullback, rather than postulated. -/
theorem sheafChart_hasRepresentableProperty
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (P : FppfSheaf.{u}) (U : Scheme.{u}) (p : fppfYoneda.obj U ⟶ P)
    (hp : FppfSheaf.HasRepresentableProperty Q p) :
    (sheafChart P U p).HasRepresentableProperty Q := by
  constructor
  · intro T x
    exact ⟨sheafChartPullbackPresentation P U T p hp.rep x⟩
  · intro T x r
    let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
      GrothendieckTopology Scheme.{u})
    let g := J.yonedaEquiv.symm x.as
    let q := sheafChartPullbackPresentation P U T p hp.rep x
    let e := sheafChartPullbackPresentationIso P U T p hp.rep x r
    have hq : Q q.fst := by
      change Q (hp.rep.snd g)
      exact hp.property_snd g
    let _ : IsIso e.hom := e.isIso_hom
    have hcomp : Q (e.hom ≫ q.fst) :=
      MorphismProperty.RespectsIso.precomp Q e.hom q.fst hq
    have heq : e.hom ≫ q.fst = r.fst := by
      exact q.lift_fst r.fst r.snd r.comparison
    rw [heq] at hcomp
    exact hcomp

/-- The defining etale-surjective atlas of an algebraic space becomes an actual
etale-surjective scheme chart of its discrete stack. -/
theorem ofAlgebraicSpace_hasEtaleSurjectiveAtlas (X : AlgebraicSpace.{u}) :
    ∃ A : StackChart (ofAlgebraicSpace X), A.IsEtaleSurjective := by
  obtain ⟨U, p, hp⟩ := X.atlas
  let _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let _ : MorphismProperty.RespectsIso
      ((@_root_.AlgebraicGeometry.Etale ⊓
        @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  exact ⟨sheafChart X.toSheaf U p,
    sheafChart_hasRepresentableProperty _ X.toSheaf U p hp⟩

/-- The same defining atlas is smooth and surjective, since every etale scheme morphism is
smooth. -/
theorem ofAlgebraicSpace_hasSmoothSurjectiveAtlas (X : AlgebraicSpace.{u}) :
    ∃ A : StackChart (ofAlgebraicSpace X), A.IsSmoothSurjective := by
  obtain ⟨U, p, hp⟩ := X.atlas
  let _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let _ : MorphismProperty.RespectsIso
      ((@_root_.AlgebraicGeometry.Smooth ⊓
        @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.inf _ _
  have hmono :
      ((@_root_.AlgebraicGeometry.Etale ⊓
          @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) ≤
        ((@_root_.AlgebraicGeometry.Smooth ⊓
          @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) := by
    intro S T f hf
    let _ : _root_.AlgebraicGeometry.Etale f := hf.1
    exact ⟨inferInstance, hf.2⟩
  have hp' : FppfSheaf.HasRepresentableProperty
      ((@_root_.AlgebraicGeometry.Smooth ⊓
        @_root_.AlgebraicGeometry.Surjective) : MorphismProperty Scheme.{u}) p :=
    MorphismProperty.relative_monotone hmono p hp
  exact ⟨sheafChart X.toSheaf U p,
    sheafChart_hasRepresentableProperty _ X.toSheaf U p hp'⟩

private theorem sheafDiagonal_pullback_eq
    (P : FppfSheaf.{u}) (T : Scheme.{u})
    (hp : FppfSheaf.IsRepresentable (Limits.diag P))
    (x y : StackFiber (ofSheaf P) T) :
    P.obj.map
        (hp.snd (prod.lift
          ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as)
          ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm y.as))).op x.as =
      P.obj.map
        (hp.snd (prod.lift
          ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as)
          ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm y.as))).op y.as := by
  let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
    GrothendieckTopology Scheme.{u})
  let x0 : P.obj.obj (Opposite.op T) := x.as
  let y0 : P.obj.obj (Opposite.op T) := y.as
  let xMap := J.yonedaEquiv.symm x0
  let yMap := J.yonedaEquiv.symm y0
  let h := prod.lift xMap yMap
  have hw := hp.w h
  have hfst := congrArg (fun q ↦ q ≫ prod.fst) hw
  have hsnd := congrArg (fun q ↦ q ≫ prod.snd) hw
  simp only [h, Category.assoc, prod.comp_diag, prod.lift_fst] at hfst
  simp only [h, Category.assoc, prod.comp_diag, prod.lift_snd] at hsnd
  have hxy : J.yoneda.map (hp.snd h) ≫ xMap =
      J.yoneda.map (hp.snd h) ≫ yMap := hfst.symm.trans hsnd
  have hxy' := congrArg J.yonedaEquiv hxy
  rw [J.yonedaEquiv_comp, J.yonedaEquiv_comp] at hxy'
  change P.obj.map (hp.snd h).op x0 = P.obj.map (hp.snd h).op y0 at hxy'
  simpa only [x0, y0] using hxy'

private theorem sheafDiagonal_test_eq
    (P : FppfSheaf.{u}) {S T : Scheme.{u}} (f : S ⟶ T)
    (x y : StackFiber (ofSheaf P) T)
    (e : (stackPullback (ofSheaf P) f).obj x ≅
      (stackPullback (ofSheaf P) f).obj y) :
    ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yoneda.map f) ≫
        ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm x.as) =
      ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yoneda.map f) ≫
        ((_root_.AlgebraicGeometry.Scheme.fppfTopology).yonedaEquiv.symm y.as) := by
  let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
    GrothendieckTopology Scheme.{u})
  let x0 : P.obj.obj (Opposite.op T) := x.as
  let y0 : P.obj.obj (Opposite.op T) := y.as
  have he := Discrete.eq_of_hom e.hom
  change P.obj.map f.op x0 = P.obj.map f.op y0 at he
  apply J.yonedaEquiv.injective
  rw [J.yonedaEquiv_comp, J.yonedaEquiv_comp]
  change P.obj.map f.op x0 = P.obj.map f.op y0
  exact he

/-- The scheme selected by representability of a sheaf diagonal represents the isomorphism
sheaf between two objects of the associated discrete stack. -/
noncomputable def sheafDiagonalPresentation
    (P : FppfSheaf.{u}) (T : Scheme.{u})
    (hp : FppfSheaf.IsRepresentable (Limits.diag P))
    (x y : StackFiber (ofSheaf P) T) :
    DiagonalPresentation (ofSheaf P) T x y := by
  let J := (_root_.AlgebraicGeometry.Scheme.fppfTopology :
    GrothendieckTopology Scheme.{u})
  let xMap := J.yonedaEquiv.symm x.as
  let yMap := J.yonedaEquiv.symm y.as
  let h := prod.lift xMap yMap
  exact
    { space := hp.pullback h
      map := hp.snd h
      universalIso := Discrete.eqToIso (sheafDiagonal_pullback_eq P T hp x y)
      lift := fun {S} f e ↦ by
        apply hp.lift (J.yoneda.map f ≫ xMap) f
        apply prod.hom_ext
        · simp only [h, Category.assoc, prod.comp_diag, prod.lift_fst]
          change J.yoneda.map f ≫ xMap = J.yoneda.map f ≫ xMap
          rfl
        · simpa only [h, xMap, yMap, Category.assoc, prod.comp_diag,
            prod.lift_snd, prod.lift_snd_assoc] using
            sheafDiagonal_test_eq P f x y e
      lift_map := by
        intro S f e
        exact hp.lift_snd _ _ _
      lift_compatible := by
        intro S f e
        refine ⟨hp.lift_snd _ _ _, ?_⟩
        apply Iso.ext
        change @Eq (ULift (PLift (_ = _))) _ _
        apply Subsingleton.elim
      lift_unique := by
        intro S f e g compatible
        obtain ⟨hmap, -⟩ := compatible
        apply hp.hom_ext
        · apply (cancel_mono (Limits.diag P)).1
          simp only [Category.assoc]
          rw [hp.w]
          rw [← Category.assoc, ← fppfYoneda.map_comp, hmap,
            ← Category.assoc, ← fppfYoneda.map_comp, hp.lift_snd]
        · exact hmap.trans (hp.lift_snd _ _ _).symm }

/-- The diagonal of the discrete stack associated to an algebraic space is represented by the
actual scheme pullbacks supplied by the algebraic-space diagonal. -/
theorem ofAlgebraicSpace_hasRepresentableDiagonal (X : AlgebraicSpace.{u}) :
    HasRepresentableDiagonal (ofAlgebraicSpace X) := by
  intro T x y
  exact ⟨sheafDiagonalPresentation X.toSheaf T X.diagonal_representable x y⟩

/-- Every algebraic space becomes an algebraic stack.  Its diagonal and smooth-surjective atlas
are constructed from the defining sheaf-level witnesses. -/
noncomputable def ofAlgebraicSpaceAlgebraicStack (X : AlgebraicSpace.{u}) :
    AlgebraicStack.{u} where
  toStack := ofAlgebraicSpace X
  diagonal_representable := ofAlgebraicSpace_hasRepresentableDiagonal X
  smoothAtlas := ofAlgebraicSpace_hasSmoothSurjectiveAtlas X

/-- Every algebraic space becomes a Deligne--Mumford stack through the same constructed
etale-surjective atlas. -/
noncomputable def ofAlgebraicSpaceDeligneMumfordStack (X : AlgebraicSpace.{u}) :
    DeligneMumfordStack.{u} where
  toAlgebraicStack := ofAlgebraicSpaceAlgebraicStack X
  etaleAtlas := ofAlgebraicSpace_hasEtaleSurjectiveAtlas X

end FppfStack

end GromovWitten.AlgebraicGeometry
