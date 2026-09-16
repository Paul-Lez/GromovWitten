/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Sites.Comparison
import GromovWitten.AlgebraicGeometry.Stacks.Algebraic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The big fppf, lisse-etale, and small etale sites of a stack

The three sites in this file are different Lean types.  Their objects are taken from the actual
Grothendieck construction of the stack pseudofunctor, so an object retains a scheme, an object in
the corresponding fibre groupoid, and cartesian arrows.  Smooth and etale objects are selected
by representable chart presentations.  Covering topologies are induced from the corresponding
Mathlib topology on the underlying schemes.

The structure sheaf is the sheafification of `T ↦ Γ(T, O_T)`.  Ringed-site comparisons therefore
carry both the inverse-image functor and its structure-sheaf isomorphism; the two sites are never
identified by definitional equality.
-/

open CategoryTheory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Sites

universe w v u

/-- A chart presentation of an object in the Grothendieck construction of a stack. -/
structure StackObjectPresentation (X : FppfStack.{u}) (z : X.total) where
  chart : StackChart X
  chartScheme : z.base = chart.scheme
  comparison : chart.obj z.base (eqToHom chartScheme) ≅ z.fiber

/-- An object of a stack is lisse when it admits a representably smooth chart presentation. -/
def IsLisseObject (X : FppfStack.{u}) (z : X.total) : Prop :=
  ∃ p : StackObjectPresentation X z, p.chart.IsSmooth

/-- An object of a stack is small-etale when it admits a representably etale chart
presentation. -/
def IsEtaleObject (X : FppfStack.{u}) (z : X.total) : Prop :=
  ∃ p : StackObjectPresentation X z, p.chart.IsEtale

/-- Objects of the lisse-etale site. -/
structure LisseEtaleObject (X : FppfStack.{u}) where
  underlying : X.total
  lisse : IsLisseObject X underlying

/-- Objects of the small etale site of a Deligne--Mumford stack. -/
structure SmallEtaleStackObject (X : DeligneMumfordStack.{u}) where
  underlying : X.toStack.total
  etale : IsEtaleObject X.toStack underlying

/-- The big fppf site is the full Grothendieck construction of stack objects. -/
abbrev BigFppfStackSite (X : FppfStack.{u}) := X.total

/-- The lisse-etale category, with all arrows in the total category between lisse objects. -/
abbrev LisseEtaleStackSite (X : FppfStack.{u}) :=
  InducedCategory X.total (fun z : LisseEtaleObject X ↦ z.underlying)

/-- The small etale category, with all arrows in the total category between etale objects. -/
abbrev SmallEtaleStackSite (X : DeligneMumfordStack.{u}) :=
  InducedCategory X.toStack.total (fun z : SmallEtaleStackObject X ↦ z.underlying)

/-- Forget a lisse-etale object to the total category of all stack objects. -/
abbrev lisseEtaleForget (X : FppfStack.{u}) :
    LisseEtaleStackSite X ⥤ X.total :=
  inducedFunctor (fun z : LisseEtaleObject X ↦ z.underlying)

/-- Forget a small-etale object to the total category of all stack objects. -/
abbrev smallEtaleForget (X : DeligneMumfordStack.{u}) :
    SmallEtaleStackSite X ⥤ X.toStack.total :=
  inducedFunctor (fun z : SmallEtaleStackObject X ↦ z.underlying)

/-- Underlying-scheme functor on the lisse-etale site. -/
abbrev lisseEtaleToScheme (X : FppfStack.{u}) :
    LisseEtaleStackSite X ⥤ Scheme.{u} :=
  lisseEtaleForget X ⋙ X.projection

/-- Underlying-scheme functor on the small-etale site. -/
abbrev smallEtaleStackToScheme (X : DeligneMumfordStack.{u}) :
    SmallEtaleStackSite X ⥤ Scheme.{u} :=
  smallEtaleForget X ⋙ X.toStack.projection

/-- Every étale stack chart is smooth, so every small-étale object is a lisse object. -/
theorem isLisseObject_of_isEtaleObject {X : FppfStack.{u}} {z : X.total}
    (hz : IsEtaleObject X z) : IsLisseObject X z := by
  obtain ⟨p, hp⟩ := hz
  refine ⟨p, ?_⟩
  refine ⟨hp.1, ?_⟩
  intro T x q
  let : _root_.AlgebraicGeometry.Etale q.fst := hp.2 T x q
  infer_instance

/-- The genuine inclusion of the small étale site into the lisse-étale site. -/
def smallEtaleToLisse (X : DeligneMumfordStack.{u}) :
    SmallEtaleStackSite X ⥤ LisseEtaleStackSite X.toStack where
  obj z := ⟨z.underlying, isLisseObject_of_isEtaleObject z.etale⟩
  map f := InducedCategory.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On underlying schemes, the small-to-lisse inclusion is strictly the identity. -/
def smallEtaleToLisse_schemeIso (X : DeligneMumfordStack.{u}) :
    smallEtaleToLisse X ⋙ lisseEtaleToScheme X.toStack ≅
      smallEtaleStackToScheme X :=
  Iso.refl _

/-- The big fppf topology on objects over a stack, induced from schemes. -/
def bigFppfStackTopology (X : FppfStack.{u}) :
    GrothendieckTopology (BigFppfStackSite X) :=
  X.projection.inducedTopology Scheme.fppfTopology

/-- The lisse-etale topology, induced from the big etale topology on underlying schemes. -/
def lisseEtaleStackTopology (X : FppfStack.{u}) :
    GrothendieckTopology (LisseEtaleStackSite X) :=
  (lisseEtaleToScheme X).inducedTopology Scheme.etaleTopology

/-- The small etale topology of a Deligne--Mumford stack. -/
def smallEtaleStackTopology (X : DeligneMumfordStack.{u}) :
    GrothendieckTopology (SmallEtaleStackSite X) :=
  (smallEtaleStackToScheme X).inducedTopology Scheme.etaleTopology

/-- The canonical structure sheaf on the big fppf site of a stack. -/
def bigFppfStructureSheaf (X : FppfStack.{u}) :
    Sheaf (bigFppfStackTopology X) CommRingCat.{u + 1} :=
  inducedRegularFunctionsCommRingSheaf X.projection Scheme.fppfTopology
    regularFunctionsCommRing_isFppfSheaf

/-- The canonical structure sheaf on the lisse-étale site of a stack. -/
def lisseEtaleStructureSheaf (X : FppfStack.{u}) :
    Sheaf (lisseEtaleStackTopology X) CommRingCat.{u + 1} :=
  inducedRegularFunctionsCommRingSheaf (lisseEtaleToScheme X) Scheme.etaleTopology
    regularFunctionsCommRing_isEtaleSheaf

/-- The canonical structure sheaf on the small étale site of a Deligne--Mumford stack. -/
def smallEtaleStructureSheaf (X : DeligneMumfordStack.{u}) :
    Sheaf (smallEtaleStackTopology X) CommRingCat.{u + 1} :=
  inducedRegularFunctionsCommRingSheaf (smallEtaleStackToScheme X) Scheme.etaleTopology
    regularFunctionsCommRing_isEtaleSheaf

/-- The presheaf of regular functions pulled back along an underlying-scheme functor. -/
def stackStructurePresheaf {C : Type u} [Category.{v} C]
    (toScheme : C ⥤ Scheme.{w}) : Cᵒᵖ ⥤ CommRingCat.{w} :=
  toScheme.op ⋙ Scheme.Γ

/-- Forget commutativity from a sheaf of commutative rings.  The sheaf condition is preserved
because the forgetful functor creates limits. -/
def forgetCommRingSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{max u v, w}] :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J RingCat.{w} where
  obj F := {
    obj := F.obj ⋙ forget₂ CommRingCat RingCat
    property := Presheaf.isSheaf_comp_of_isSheaf J F.obj _ F.property }
  map f := ⟨Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)⟩

/-- A ringed site, with its topology and an actual sheaf of commutative rings. -/
structure RingedSite (C : Type u) [Category.{v} C] [UnivLE.{max u v, w}] where
  topology : GrothendieckTopology C
  structureSheaf : Sheaf topology CommRingCat.{w}

namespace RingedSite

/-- The underlying ring sheaf used by Mathlib's sheaves-of-modules API. -/
noncomputable abbrev ringStructureSheaf
    {C : Type u} [Category.{v} C] [UnivLE.{max u v, w}]
    (S : RingedSite.{w} C) : Sheaf S.topology RingCat.{w} :=
  (forgetCommRingSheaf S.topology).obj S.structureSheaf

end RingedSite

/-- The big fppf site with its canonical, representable regular-function sheaf. -/
def canonicalBigFppfRingedSite (X : FppfStack.{u}) :
    RingedSite.{u + 1} (BigFppfStackSite X) where
  topology := bigFppfStackTopology X
  structureSheaf := bigFppfStructureSheaf X

/-- The lisse-étale site with its canonical regular-function sheaf. -/
def canonicalLisseEtaleRingedSite (X : FppfStack.{u}) :
    RingedSite.{u + 1} (LisseEtaleStackSite X) where
  topology := lisseEtaleStackTopology X
  structureSheaf := lisseEtaleStructureSheaf X

/-- The small étale site with its canonical regular-function sheaf. -/
def canonicalSmallEtaleRingedSite (X : DeligneMumfordStack.{u}) :
    RingedSite.{u + 1} (SmallEtaleStackSite X) where
  topology := smallEtaleStackTopology X
  structureSheaf := smallEtaleStructureSheaf X

namespace RingedSite

/-- Sheaves of modules over the structure sheaf of a ringed site. -/
abbrev Modules {C : Type u} [Category.{v} C] [UnivLE.{max u v, w}]
    (S : RingedSite.{w} C) :=
  SheafOfModules.{w} S.ringStructureSheaf

/-- The actual full category of quasi-coherent module sheaves on a ringed site. -/
abbrev QuasiCoherentModules {C : Type u} [Category.{v} C] [UnivLE.{max u v, w}]
    (S : RingedSite.{w} C)
    [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
    [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] :=
  ObjectProperty.FullSubcategory
    (fun M : S.Modules ↦ SheafOfModules.IsQuasicoherent M)

end RingedSite

/-- The big fppf ringed site of a stack, with no external structure-sheaf choice. -/
abbrev bigFppfRingedSite (X : FppfStack.{u}) :=
  canonicalBigFppfRingedSite X

/-- The lisse-étale ringed site of a stack, with no external structure-sheaf choice. -/
abbrev lisseEtaleRingedSite (X : FppfStack.{u}) :=
  canonicalLisseEtaleRingedSite X

/-- The small étale ringed site of a Deligne--Mumford stack. -/
abbrev smallEtaleStackRingedSite (X : DeligneMumfordStack.{u}) :=
  canonicalSmallEtaleRingedSite X

/-- A morphism of ringed sites.  The inverse-image functor and the comparison of structure
sheaves are explicit, so site changes cannot silently coerce module categories. -/
structure RingedSiteMorphism
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    [UnivLE.{max u v, w}]
    (S : RingedSite.{w} C) (T : RingedSite.{w} D) where
  siteFunctor : C ⥤ D
  continuous : siteFunctor.IsContinuous S.topology T.topology
  structureIso :
    letI := continuous
    (siteFunctor.sheafPushforwardContinuous CommRingCat.{w} S.topology T.topology).obj
      T.structureSheaf ≅ S.structureSheaf

attribute [instance] RingedSiteMorphism.continuous

namespace RingedSiteMorphism

variable [UnivLE.{max u v, w}]

/-- The identity morphism of a ringed site.  Its structure-sheaf comparison is the canonical
identity comparison for continuous pushforward, rather than additional caller-supplied data. -/
def id
    {C : Type u} [Category.{v} C] (S : RingedSite.{w} C) :
    RingedSiteMorphism S S where
  siteFunctor := 𝟭 C
  continuous := inferInstance
  structureIso :=
    (Functor.sheafPushforwardContinuousId CommRingCat.{w} S.topology).app S.structureSheaf

/-- Composition of morphisms of ringed sites.  The comparison on structure sheaves is obtained
by the canonical comparison between iterated and composite continuous pushforward, followed by
the two given structure-sheaf comparisons. -/
noncomputable def comp
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {E : Type u} [Category.{v} E]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D} {U : RingedSite.{w} E}
    (f : RingedSiteMorphism S T) (g : RingedSiteMorphism T U) :
    RingedSiteMorphism S U where
  siteFunctor := f.siteFunctor ⋙ g.siteFunctor
  continuous :=
    Functor.isContinuous_comp f.siteFunctor g.siteFunctor
      S.topology T.topology U.topology
  structureIso :=
    letI := Functor.isContinuous_comp f.siteFunctor g.siteFunctor
      S.topology T.topology U.topology
    (Functor.sheafPushforwardContinuousComp f.siteFunctor g.siteFunctor CommRingCat.{w}
      S.topology T.topology U.topology).app U.structureSheaf |>.symm ≪≫
      (f.siteFunctor.sheafPushforwardContinuous CommRingCat.{w}
        S.topology T.topology).mapIso g.structureIso ≪≫
      f.structureIso

/-- Forgetting commutativity sends the structure-sheaf comparison to the comparison used for
module restriction. -/
noncomputable def ringStructureIso
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D}
    (f : RingedSiteMorphism S T) :
    letI := f.continuous
    (f.siteFunctor.sheafPushforwardContinuous RingCat.{w} S.topology T.topology).obj
        T.ringStructureSheaf ≅ S.ringStructureSheaf :=
  (forgetCommRingSheaf S.topology).mapIso f.structureIso

/-- Restriction of sheaves along the underlying continuous site functor. -/
noncomputable def inverseImage
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D}
    (f : RingedSiteMorphism S T) :
    Sheaf T.topology RingCat.{w} ⥤ Sheaf S.topology RingCat.{w} :=
  f.siteFunctor.sheafPushforwardContinuous RingCat.{w} S.topology T.topology

/-- Restriction of module sheaves, with scalars transported through the structure-sheaf
comparison. -/
noncomputable def moduleInverseImage
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D}
    (f : RingedSiteMorphism S T) : T.Modules ⥤ S.Modules :=
  SheafOfModules.pushforward f.ringStructureIso.inv

omit [UnivLE.{max u v, w}] in
/-- Pullback of module sheaves along a small ringed-site morphism.  This is the actual left
adjoint constructed by Mathlib from presheaf pullback followed by sheafification.  The shared
universe hypothesis is the one under which Mathlib constructs the required presheaf adjoint; no
adjoint or pullback functor is supplied by the caller. -/
noncomputable def modulePullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {S : RingedSite.{u} C} {T : RingedSite.{u} D}
    (f : RingedSiteMorphism.{u} S T)
    [HasWeakSheafify T.topology AddCommGrpCat.{u}]
    [T.topology.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    S.Modules ⥤ T.Modules := by
  letI : (PresheafOfModules.pushforward f.ringStructureIso.inv.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward f.ringStructureIso.inv.hom
  exact SheafOfModules.pullback f.ringStructureIso.inv

omit [UnivLE.{max u v, w}] in
/-- The constructed module pullback is left adjoint to the already constructed restriction of
module sheaves. -/
noncomputable def modulePullbackModuleInverseImageAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {S : RingedSite.{u} C} {T : RingedSite.{u} D}
    (f : RingedSiteMorphism.{u} S T)
    [HasWeakSheafify T.topology AddCommGrpCat.{u}]
    [T.topology.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    f.modulePullback ⊣ f.moduleInverseImage := by
  letI : (PresheafOfModules.pushforward f.ringStructureIso.inv.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward f.ringStructureIso.inv.hom
  exact SheafOfModules.pullbackPushforwardAdjunction f.ringStructureIso.inv

/-- Restriction of sheaves along the identity ringed-site morphism is canonically the identity
functor. -/
def inverseImageId
    {C : Type u} [Category.{v} C] (S : RingedSite.{w} C) :
    (id S).inverseImage ≅ 𝟭 (Sheaf S.topology RingCat.{w}) :=
  Functor.sheafPushforwardContinuousId RingCat.{w} S.topology

/-- Restriction of sheaves along a composite ringed-site morphism agrees with iterated
restriction. -/
def inverseImageComp
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {E : Type u} [Category.{v} E]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D} {U : RingedSite.{w} E}
    (f : RingedSiteMorphism S T) (g : RingedSiteMorphism T U) :
    g.inverseImage ⋙ f.inverseImage ≅ (f.comp g).inverseImage :=
  Functor.sheafPushforwardContinuousComp f.siteFunctor g.siteFunctor RingCat.{w}
    S.topology T.topology U.topology

/-- Restriction of module sheaves along the identity ringed-site morphism is canonically the
identity functor.  This is Mathlib's constructed module-pushforward identity comparison. -/
noncomputable def moduleInverseImageId
    {C : Type u} [Category.{v} C] (S : RingedSite.{w} C) :
    (id S).moduleInverseImage ≅ 𝟭 S.Modules :=
  SheafOfModules.pushforwardId S.ringStructureSheaf

/-- Restriction of module sheaves along a composite ringed-site morphism agrees with iterated
restriction.  The isomorphism is inherited from the actual continuous-site and scalar-restriction
constructions, so composition is not an axiom of `RingedSiteMorphism`. -/
noncomputable def moduleInverseImageComp
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {E : Type u} [Category.{v} E]
    {S : RingedSite.{w} C} {T : RingedSite.{w} D} {U : RingedSite.{w} E}
    (f : RingedSiteMorphism S T) (g : RingedSiteMorphism T U) :
    g.moduleInverseImage ⋙ f.moduleInverseImage ≅
      (f.comp g).moduleInverseImage :=
  SheafOfModules.pushforwardComp f.ringStructureIso.inv g.ringStructureIso.inv

omit [UnivLE.{max u v, w}] in
/-- Pullback of module sheaves along the identity small ringed-site morphism is canonically the
identity functor. -/
noncomputable def modulePullbackId
    {C : Type u} [SmallCategory C] (S : RingedSite.{u} C)
    [HasWeakSheafify S.topology AddCommGrpCat.{u}]
    [S.topology.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (id S).modulePullback ≅ 𝟭 S.Modules :=
  SheafOfModules.pullbackId S.ringStructureSheaf

omit [UnivLE.{max u v, w}] in
/-- Iterated module pullback agrees with pullback along the composite small ringed-site
morphism.  This is Mathlib's left-adjoint composition comparison, not a coherence field. -/
noncomputable def modulePullbackComp
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {S : RingedSite.{u} C} {T : RingedSite.{u} D} {U : RingedSite.{u} E}
    (f : RingedSiteMorphism.{u} S T) (g : RingedSiteMorphism.{u} T U)
    [HasWeakSheafify T.topology AddCommGrpCat.{u}]
    [T.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify U.topology AddCommGrpCat.{u}]
    [U.topology.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    f.modulePullback ⋙ g.modulePullback ≅ (f.comp g).modulePullback := by
  letI : (f.siteFunctor ⋙ g.siteFunctor).IsContinuous S.topology U.topology :=
    Functor.isContinuous_comp f.siteFunctor g.siteFunctor
      S.topology T.topology U.topology
  letI : (PresheafOfModules.pushforward f.ringStructureIso.inv.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward f.ringStructureIso.inv.hom
  letI : (PresheafOfModules.pushforward g.ringStructureIso.inv.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward g.ringStructureIso.inv.hom
  exact SheafOfModules.pullbackComp f.ringStructureIso.inv g.ringStructureIso.inv

end RingedSiteMorphism

/-
Retired provisional Deligne--Mumford site comparison.  The ringed-site morphisms, sheafification
instances, and quasi-coherent derived equivalence were supplied as fields.  The three concrete
site types, their canonical structure sheaves, and `RingedSiteMorphism` remain active.

/-- The small-etale/lisse-etale comparison package for a Deligne--Mumford stack. -/
structure DeligneMumfordSiteComparison (X : DeligneMumfordStack.{u}) where
  smallToLisse :
    RingedSiteMorphism (smallEtaleStackRingedSite X)
      (lisseEtaleRingedSite X.toStack)
  lisseToBig :
    RingedSiteMorphism (lisseEtaleRingedSite X.toStack)
      (bigFppfRingedSite X.toStack)
  [smallWeakSheafify (Z : SmallEtaleStackSite X) :
    HasWeakSheafify ((smallEtaleStackRingedSite X).topology.over Z)
      AddCommGrpCat.{u + 1}]
  [smallWEquals (Z : SmallEtaleStackSite X) :
    ((smallEtaleStackRingedSite X).topology.over Z).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  [lisseWeakSheafify (Z : LisseEtaleStackSite X.toStack) :
    HasWeakSheafify ((lisseEtaleRingedSite X.toStack).topology.over Z)
      AddCommGrpCat.{u + 1}]
  [lisseWEquals (Z : LisseEtaleStackSite X.toStack) :
    ((lisseEtaleRingedSite X.toStack).topology.over Z).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1}]
  smallEtaleQC :
    (smallEtaleStackRingedSite X).QuasiCoherentModules ≌
      (lisseEtaleRingedSite X.toStack).QuasiCoherentModules

/-- The comparison functor from small-etale modules to lisse-etale modules is visible and is
not a definitional coercion. -/
noncomputable def smallToLisseModules {X : DeligneMumfordStack.{u}}
    (C : DeligneMumfordSiteComparison X) :
    (lisseEtaleRingedSite X.toStack).Modules ⥤
      (smallEtaleStackRingedSite X).Modules :=
  C.smallToLisse.moduleInverseImage

/-- The comparison functor from lisse-etale modules to big-fppf modules. -/
noncomputable def lisseToBigModules {X : DeligneMumfordStack.{u}}
    (C : DeligneMumfordSiteComparison X) :
    (bigFppfRingedSite X.toStack).Modules ⥤
      (lisseEtaleRingedSite X.toStack).Modules :=
  C.lisseToBig.moduleInverseImage

-/

end GromovWitten.AlgebraicGeometry.Sites
