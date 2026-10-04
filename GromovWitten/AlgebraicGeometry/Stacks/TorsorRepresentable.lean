/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.QuotientStackAtlas
import GromovWitten.AlgebraicGeometry.Stacks.ChartBaseChange
import GromovWitten.AlgebraicGeometry.Sites.StackSiteContinuity
import GromovWitten.AlgebraicGeometry.Descent.ZariskiRepresentability
import GromovWitten.AlgebraicGeometry.Descent.AffineRepresentability
import GromovWitten.AlgebraicGeometry.Stacks.TorsorAffineCover
import GromovWitten.AlgebraicGeometry.Stacks.TorsorAffineRefinement
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Representable torsors and the atlas of `[U/G]`

This file shows that the atlas chart `U₀ → [U/G]` of a quotient stack is étale and surjective
as soon as fppf `G`-torsors are represented by schemes étale and surjective over their base,
and reduces that representability to torsors over affine bases with an affine descent input.

The chart side is a comparison of fibre points: a fibre point of
`schemeAtlasChart G U X₀ a` over a torsor `P` and a test map `tb : S ⟶ T` is, through
`ActionTorsor.atlasFibreEquiv`, a section of the sheaf `P.P` over `tb`
(`ActionTorsor.atlasFibrePointSection`).  The only real content is the naturality of this
correspondence under pullback of test schemes
(`ActionTorsor.atlasFibrePointSection_pullbackPoint`), proved from the computation of the
pseudonaturality cell of the chart on unit sections
(`ActionTorsor.trivialSection_comp_schemeAtlasChart_naturality`).  With it, a scheme
representing `P.P` over `T` is a pullback presentation of the chart.

For `G = affineGroup R grp` with `R` étale and finite over `ℤ` and `Spec R → Spec ℤ`
surjective, the representability is proved here unconditionally
(`FppfTorsor.exists_torsorRepresentation_affineGroup`), and hence so are the étale surjective
atlases of `[U₀/G]` and `BG` (`ActionTorsor.atlasChart_affineGroup_isEtaleSurjective'`,
`ActionTorsor.classifyingAtlasChart_affineGroup_isEtaleSurjective'`).

The representable diagonal of `[U/G]` is **not** proved here, so no `DeligneMumfordStack`
structure on `[U/G]` or `BG` is constructed in this file.

## Main results

* `TorsorRepresentation P`: a scheme over `T` with an identification of its functor of points
  with the torsor `P.P` over `T`.
* `ActionTorsor.schemeAtlasPullbackPresentation`, `ActionTorsor.atlasPullbackPresentation`:
  the pullback presentation of the atlas chart over a torsor represented by a scheme.
* `ActionTorsor.schemeAtlasChart_hasRepresentableProperty_of_representation`,
  `ActionTorsor.atlasChart_isEtaleSurjective_of_representation`,
  `ActionTorsor.classifyingAtlasChart_isEtaleSurjective_of_representation`: the atlas charts
  of `[U/G]` and of `BG` are étale and surjective, under the hypothesis that every torsor is
  represented by a scheme étale and surjective over the base.
* `TorsorRepresentation.exists_of_affine`: Zariski reduction of that hypothesis (with
  finiteness) to torsors over affine schemes.
* `TorsorRepresentation.exists_of_affineDescentInput`: the affine case, from an
  `AffineDescentInput` with étale, finite and surjective `Spec M → Spec B`.
* `TorsorRepresentation.exists_affineGroup_of_trivialisation` (blueprint B4.1, conditional):
  for `G = affineGroup R grp` with `R` étale and finite over `ℤ` and `Spec R → Spec ℤ`
  surjective, every fppf `G`-torsor is represented by a scheme étale, finite and surjective over
  the base, **under the hypothesis** that torsors over affine bases admit a
  `TorsorAffineTrivialisation`.
* `ActionTorsor.atlasChart_affineGroup_isEtaleSurjective`,
  `ActionTorsor.classifyingAtlasChart_affineGroup_isEtaleSurjective`: the resulting étale
  surjective atlases of `[U₀/G]` and `BG`, under the same hypotheses.
* `FppfTorsor.exists_torsorRepresentation_affineGroup`,
  `ActionTorsor.atlasChart_affineGroup_isEtaleSurjective'`,
  `ActionTorsor.classifyingAtlasChart_affineGroup_isEtaleSurjective'`: the unconditional
  forms, discharging the trivialisation hypothesis by
  `FppfTorsor.nonempty_torsorAffineTrivialisation` (`Stacks/TorsorAffineRefinement.lean`).
-/

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u

/-- The Yoneda equivalence of the fppf site turns the image of a scheme morphism `tc` under a
sheaf morphism `a` into the composite `fppfYoneda.map tc ≫ a`. -/
theorem fppfYonedaEquiv_symm_app_eq_map_comp {X₀ S : Scheme.{u}} {F : FppfSheaf.{u}}
    (a : fppfYoneda.obj X₀ ⟶ F) (tc : S ⟶ X₀) :
    fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S) tc) = fppfYoneda.map tc ≫ a := by
  rw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  congr 1

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

/-! ### The pseudonaturality cell of a scheme atlas chart on unit sections -/

/-- **The pseudonaturality cell of the chart `schemeAtlasChart` carries the unit section to the
base change of the unit section.**  The chart is the composite of the discrete map induced by
`a` with the atlas map; its cell along `m` is an `eqToHom` (from the naturality of `a`)
followed by `atlasNaturalityIsoApp`, and both are computed on unit sections by the section
calculus of `QuotientStackAtlas.lean`. -/
theorem trivialSection_comp_schemeAtlasChart_naturality (X₀ : Scheme.{u})
    (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) {S S' : Scheme.{u}}
    (m : S' ⟶ S) (tc : S ⟶ X₀) :
    ConeQuotient.trivialSection (U := U)
        (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S') (m ≫ tc))) ≫
      ((Cat.Hom.toNatIso ((schemeAtlasChart G U X₀ a).map.naturality ⟨m.op⟩)).app
        (Discrete.mk (ULift.up tc))).hom.iso.hom =
      ConeQuotient.pullbackSection (trivialTorsor (G := G)
          (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S) tc)))
        (ConeQuotient.trivialSection (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S) tc)))
        (ConeQuotient.trivialSection_projection _) m := by
  have h1 := Sites.SiteChart.comp_naturality_app (FppfStack.mapOfSheafHom a) (atlasMap G U) m
    (Discrete.mk (ULift.up tc))
  change ConeQuotient.trivialSection (U := U)
        (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S') (m ≫ tc))) ≫
      (((Pseudofunctor.StrongTrans.vcomp (FppfStack.mapOfSheafHom a) (atlasMap G U)).naturality
        ⟨m.op⟩).hom.toNatTrans.app (Discrete.mk (ULift.up tc))).iso.hom = _
  rw [h1]
  have e : fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S') (m ≫ tc)) =
      fppfJ.yonedaEquiv.symm (U.space.toSheaf.obj.map m.op (a.hom.app (Opposite.op S) tc)) :=
    congrArg _ (congrFun (congrArg (fun f => f.hom) (a.hom.naturality m.op)) tc)
  change ConeQuotient.trivialSection (U := U)
        (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S') (m ≫ tc))) ≫
      (eqToHom (congrArg trivialTorsor e) ≫
        (atlasNaturalityIsoApp G U m (a.hom.app (Opposite.op S) tc)).hom).iso.hom = _
  rw [comp_iso_hom, ← Category.assoc, ConeQuotient.trivialSection_comp_eqToHom e,
    trivialSection_comp_atlasNaturalityIsoApp]

/-- The composition comparison of base change in `[U/G]` is the inverse of
`ActionTorsor.pullbackCompIsoApp`.  This is `rfl`. -/
theorem stackPullbackCompIso_quotientStack_hom {T S S' : Scheme.{u}} (m : S' ⟶ S)
    (b : S ⟶ T) (P : ActionTorsor G U T) :
    (stackPullbackCompIso (quotientStack G U) m b P).hom = (pullbackCompIsoApp m b P).inv :=
  rfl

/-- The inverse of the composition comparison of base change, followed by the projection to
the torsor, is the iterated projection. -/
@[reassoc]
theorem pullbackCompIsoApp_inv_iso_hom_fst {T S S' : Scheme.{u}} (m : S' ⟶ S) (b : S ⟶ T)
    (P : ActionTorsor G U T) :
    (pullbackCompIsoApp m b P).inv.iso.hom ≫
        Limits.pullback.fst P.projection (fppfYoneda.map (m ≫ b)) =
      Limits.pullback.fst (Limits.pullback.snd P.projection (fppfYoneda.map b))
          (fppfYoneda.map m) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map b) := by
  have h := congrArg (fun k => k.iso.hom) (pullbackCompIsoApp m b P).inv_hom_id
  simp only [comp_iso_hom, id_iso_hom, pullbackCompIsoApp_hom_iso_hom] at h
  rw [← FppfTorsor.pullbackCompIso_hom_fst_fst P.toFppfTorsor m b, reassoc_of% h]

/-- The identification of `U.space` with the algebraic space of a scheme, used by
`atlasChart`, is an isomorphism of fppf sheaves. -/
instance isIso_atlasChart_eqToHom {X₀ : Scheme.{u}}
    (h : U.space = AlgebraicSpace.ofScheme.obj X₀) :
    IsIso (eqToHom (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm :
      fppfYoneda.obj X₀ ⟶ U.space.toSheaf) :=
  (eqToIso (congrArg (fun Y : AlgebraicSpace.{u} => Y.toSheaf) h).symm).isIso_hom

/-! ### Fibre points of a scheme atlas chart are sections of the torsor -/

section FibrePoints

variable (X₀ : Scheme.{u}) (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) {T : Scheme.{u}}
  (P : ActionTorsor G U T)

/-- **The section of a fibre point of the atlas chart.**  A fibre point of
`schemeAtlasChart G U X₀ a` over `P` lying over `tb : S ⟶ T` is a map `tc : S ⟶ X₀` with an
isomorphism between the trivial torsor of the point `a ∘ tc` and `P|_S`; under
`atlasFibreEquiv` it is a section of the sheaf `P.P` over `tb`. -/
noncomputable def atlasFibrePointSection {S : Scheme.{u}} {tb : S ⟶ T}
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) : fppfYoneda.obj S ⟶ P.P :=
  ((atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) p.1)).symm p.2).1

variable {X₀ a P}

/-- The section of a fibre point lies over the test map. -/
theorem atlasFibrePointSection_projection {S : Scheme.{u}} {tb : S ⟶ T}
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) :
    atlasFibrePointSection X₀ a P p ≫ P.projection = fppfYoneda.map tb :=
  ((atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) p.1)).symm p.2).2.1

set_option backward.isDefEq.respectTransparency false in
/-- The point of `U` attached to the section of a fibre point is `a ∘ tc`. -/
theorem atlasFibrePointSection_target {S : Scheme.{u}} {tb : S ⟶ T}
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) :
    atlasFibrePointSection X₀ a P p ≫ P.target = fppfYoneda.map p.1 ≫ a := by
  rw [← fppfYonedaEquiv_symm_app_eq_map_comp]
  exact ((atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) p.1)).symm p.2).2.2

/-- The section of a fibre point, computed: the unit section of the trivial torsor, pushed
through the given isomorphism to `P|_S` and projected to `P`.  This is `rfl`. -/
theorem atlasFibrePointSection_eq {S : Scheme.{u}} {tb : S ⟶ T}
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) :
    atlasFibrePointSection X₀ a P p =
      (ConeQuotient.trivialSection (U := U)
          (fppfJ.yonedaEquiv.symm (a.hom.app (Opposite.op S) p.1)) ≫ p.2.hom.iso.hom) ≫
        Limits.pullback.fst P.projection (fppfYoneda.map tb) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a fibre point along an equality of test maps does not change its section. -/
@[simp]
theorem atlasFibrePointSection_castPoint {S : Scheme.{u}} {tb tb' : S ⟶ T} (h : tb = tb')
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) :
    atlasFibrePointSection X₀ a P ((schemeAtlasChart G U X₀ a).castPoint P h p) =
      atlasFibrePointSection X₀ a P p := by
  subst h
  rw [StackChart.castPoint_rfl]

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the section of a fibre point under pullback of test schemes.**  The
section of the pullback of a fibre point along `m : S' ⟶ S` is the precomposition of its
section with `fppfYoneda.map m`.  This is the only real content of the comparison between the
chart's 2-categorical fibre points and the sheaf `P.P`. -/
theorem atlasFibrePointSection_pullbackPoint {S S' : Scheme.{u}} (m : S' ⟶ S) {tb : S ⟶ T}
    (p : (schemeAtlasChart G U X₀ a).FibrePoint P tb) :
    atlasFibrePointSection X₀ a P ((schemeAtlasChart G U X₀ a).pullbackPoint P m p) =
      fppfYoneda.map m ≫ atlasFibrePointSection X₀ a P p := by
  obtain ⟨tc, c⟩ := p
  rw [atlasFibrePointSection_eq, atlasFibrePointSection_eq]
  simp only [StackChart.pullbackPoint, StackChart.inducedComparison, Iso.trans_hom]
  rw [comp_iso_hom, comp_iso_hom, Functor.mapIso_hom, stackPullbackCompIso_quotientStack_hom]
  simp only [Category.assoc]
  rw [pullbackCompIsoApp_inv_iso_hom_fst]
  erw [FppfTorsor.pullbackMap_fst_assoc]
  · rw [← Category.assoc (ConeQuotient.trivialSection _),
      trivialSection_comp_schemeAtlasChart_naturality]
    erw [ConeQuotient.pullbackSection_fst_assoc]
  · exact c.hom.over

/-- **Fibre points are determined by their sections**, when `a` is a monomorphism (e.g. an
isomorphism, as for `atlasChart`). -/
theorem atlasFibrePointSection_injective [Mono a] {S : Scheme.{u}} {tb : S ⟶ T}
    {p q : (schemeAtlasChart G U X₀ a).FibrePoint P tb}
    (h : atlasFibrePointSection X₀ a P p = atlasFibrePointSection X₀ a P q) : p = q := by
  obtain ⟨tc, c⟩ := p
  obtain ⟨tc', c'⟩ := q
  have ht : tc = tc' := by
    have h1 := atlasFibrePointSection_target (X₀ := X₀) (a := a) (P := P) ⟨tc, c⟩
    have h2 := atlasFibrePointSection_target (X₀ := X₀) (a := a) (P := P) ⟨tc', c'⟩
    rw [h] at h1
    exact fppfYoneda.map_injective ((cancel_mono a).1 (h1.symm.trans h2))
  subst ht
  have hc : (atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) tc)).symm c =
      (atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) tc)).symm c' := Subtype.ext h
  rw [(atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S) tc)).symm.injective hc]

variable (a P) in
/-- **The fibre point of a section**, when `a` is an isomorphism: a section `τ` of `P.P` over
`tb` determines the chart map `tc` (the scheme map whose image under `a` is the point
`τ ≫ P.target` of `U`) and, through `atlasFibreEquiv`, the isomorphism of the trivial torsor
of that point with `P|_S`. -/
noncomputable def atlasFibrePointOfSection [IsIso a] {S : Scheme.{u}} {tb : S ⟶ T}
    (τ : fppfYoneda.obj S ⟶ P.P) (hτ : τ ≫ P.projection = fppfYoneda.map tb) :
    (schemeAtlasChart G U X₀ a).FibrePoint P tb :=
  ⟨(fppfYoneda.preimage (τ ≫ P.target ≫ inv a) : S ⟶ X₀),
    atlasFibreEquiv G U P tb (a.hom.app (Opposite.op S)
      (fppfYoneda.preimage (τ ≫ P.target ≫ inv a) : S ⟶ X₀)) ⟨τ, hτ, by
        rw [fppfYonedaEquiv_symm_app_eq_map_comp, Functor.map_preimage, Category.assoc,
          Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

/-- The section of the fibre point of a section is that section. -/
@[simp]
theorem atlasFibrePointSection_ofSection [IsIso a] {S : Scheme.{u}} {tb : S ⟶ T}
    (τ : fppfYoneda.obj S ⟶ P.P) (hτ : τ ≫ P.projection = fppfYoneda.map tb) :
    atlasFibrePointSection X₀ a P (atlasFibrePointOfSection a P τ hτ) = τ := by
  exact congrArg Subtype.val (Equiv.symm_apply_apply _ _)

end FibrePoints

/-! ### Representable torsors give pullback presentations of the atlas chart -/

end ActionTorsor

/-- **A representation of an fppf torsor by a scheme**: a scheme `space` over the base `T`
together with an isomorphism of fppf sheaves `fppfYoneda.obj space ≅ P.P` over `T`.  (This is
data; that every torsor under a suitable group admits one is a theorem, not a field.) -/
structure TorsorRepresentation {G : AlgebraicSpaceGroup.{u}} {T : Scheme.{u}}
    (P : FppfTorsor G T) where
  /-- The representing scheme. -/
  space : Scheme.{u}
  /-- Its structure morphism to the base. -/
  toBase : space ⟶ T
  /-- The identification of its functor of points with the torsor. -/
  iso : fppfYoneda.obj space ≅ P.P
  /-- The identification lies over the base. -/
  iso_hom_projection : iso.hom ≫ P.projection = fppfYoneda.map toBase

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}

section Presentation

variable (X₀ : Scheme.{u}) (a : fppfYoneda.obj X₀ ⟶ U.space.toSheaf) [IsIso a] {T : Scheme.{u}}
  (P : ActionTorsor G U T)

/-- The universal fibre point of the atlas chart over a torsor `P` represented by a scheme:
the fibre point of the section `R.iso.hom` over `R.toBase`. -/
noncomputable def representationFibrePoint (R : TorsorRepresentation P.toFppfTorsor) :
    (schemeAtlasChart G U X₀ a).FibrePoint P R.toBase :=
  atlasFibrePointOfSection a P R.iso.hom R.iso_hom_projection

variable {X₀ a P}

set_option backward.isDefEq.respectTransparency false in
/-- **Classification by a representing scheme.**  A map `m : S ⟶ R.space` classifies the fibre
point `(tb, tc, c)` relative to the universal fibre point iff the section `m` defines through
`R.iso` is the section of `(tc, c)`. -/
theorem classifies_representationFibrePoint_iff (R : TorsorRepresentation P.toFppfTorsor)
    {S : Scheme.{u}} (tb : S ⟶ T) (tc : S ⟶ X₀)
    (c : (schemeAtlasChart G U X₀ a).obj S tc ≅ (stackPullback (quotientStack G U) tb).obj P)
    (m : S ⟶ R.space) :
    (schemeAtlasChart G U X₀ a).Classifies R.toBase (representationFibrePoint X₀ a P R).1
        (representationFibrePoint X₀ a P R).2 tb tc c m ↔
      fppfYoneda.map m ≫ R.iso.hom = atlasFibrePointSection X₀ a P ⟨tc, c⟩ := by
  rw [StackChart.classifies_iff_pullbackPoint]
  constructor
  · rintro ⟨h, e⟩
    have e' := congrArg (atlasFibrePointSection X₀ a P) e
    rwa [atlasFibrePointSection_castPoint, atlasFibrePointSection_pullbackPoint,
      representationFibrePoint, atlasFibrePointSection_ofSection] at e'
  · intro hm
    have h : m ≫ R.toBase = tb := by
      apply fppfYoneda.map_injective
      rw [Functor.map_comp, ← R.iso_hom_projection, ← Category.assoc, hm,
        atlasFibrePointSection_projection]
    refine ⟨h, atlasFibrePointSection_injective ?_⟩
    rw [atlasFibrePointSection_castPoint, atlasFibrePointSection_pullbackPoint,
      representationFibrePoint, atlasFibrePointSection_ofSection, hm]

variable (X₀ a P)

/-- **The pullback presentation of the atlas chart from a representing scheme.**  If the
torsor `P` (an object of `[U/G]` over `T`) is represented by a scheme `R.space` over `T`, then
`R.space`, with first projection `R.toBase`, is the 2-fibre product `X₀ ×_{[U/G]} T` of the
chart `schemeAtlasChart G U X₀ a` (with `a` an isomorphism) and `P`: the universal comparison
is the fibre point of the section `R.iso.hom`, and the lift of a fibre point `(tb, tc, c)` is
the scheme map whose section is the section of `(tc, c)`. -/
noncomputable def schemeAtlasPullbackPresentation (R : TorsorRepresentation P.toFppfTorsor) :
    (schemeAtlasChart G U X₀ a).PullbackPresentation T P where
  space := R.space
  fst := R.toBase
  snd := (representationFibrePoint X₀ a P R).1
  comparison := (representationFibrePoint X₀ a P R).2
  lift tb tc c := fppfYoneda.preimage (atlasFibrePointSection X₀ a P ⟨tc, c⟩ ≫ R.iso.inv)
  lift_fst tb tc c := by
    obtain ⟨h, -, -⟩ := (classifies_representationFibrePoint_iff (X₀ := X₀) (a := a) R tb tc c _).2
      (by rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact h
  lift_snd tb tc c := by
    obtain ⟨-, h, -⟩ := (classifies_representationFibrePoint_iff (X₀ := X₀) (a := a) R tb tc c _).2
      (by rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact h
  lift_compatible tb tc c :=
    (classifies_representationFibrePoint_iff (X₀ := X₀) (a := a) R tb tc c _).2
      (by rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  lift_unique tb tc c m hm := by
    have h := (classifies_representationFibrePoint_iff (X₀ := X₀) (a := a) R tb tc c m).1 hm
    apply fppfYoneda.map_injective
    rw [Functor.map_preimage, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The representing scheme is the space of the presentation. -/
@[simp]
theorem schemeAtlasPullbackPresentation_space (R : TorsorRepresentation P.toFppfTorsor) :
    (schemeAtlasPullbackPresentation X₀ a P R).space = R.space :=
  rfl

/-- The first projection of the presentation is the structure map of the representing
scheme. -/
@[simp]
theorem schemeAtlasPullbackPresentation_fst (R : TorsorRepresentation P.toFppfTorsor) :
    (schemeAtlasPullbackPresentation X₀ a P R).fst = R.toBase :=
  rfl

/-- **A chart property from representable torsors.**  If every fppf `G`-torsor over every
scheme is represented by a scheme whose structure map has the property `Q` (respecting
isomorphisms), then the chart `schemeAtlasChart G U X₀ a` of `[U/G]` (with `a` an isomorphism)
has `Q` on every scheme base change. -/
theorem schemeAtlasChart_hasRepresentableProperty_of_representation
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hrep : ∀ (T : Scheme.{u}) (P : FppfTorsor G T), ∃ R : TorsorRepresentation P, Q R.toBase) :
    (schemeAtlasChart G U X₀ a).HasRepresentableProperty Q :=
  Sites.SiteChart.hasRepresentableProperty_of_exists _ Q inferInstance (fun T x => by
    obtain ⟨R, hR⟩ := hrep T (ActionTorsor.toFppfTorsor (G := G) (U := U) (T := T) x)
    exact ⟨schemeAtlasPullbackPresentation X₀ a x R, hR⟩)

/-- **The atlas chart is étale and surjective once torsors are representable**: if every fppf
`G`-torsor over every scheme is represented by a scheme étale and surjective over the base,
then `schemeAtlasChart G U X₀ a` (with `a` an isomorphism) is an étale surjective chart of
`[U/G]`.  The representability is a hypothesis here. -/
theorem schemeAtlasChart_isEtaleSurjective_of_representation
    (hrep : ∀ (T : Scheme.{u}) (P : FppfTorsor G T), ∃ R : TorsorRepresentation P,
      _root_.AlgebraicGeometry.Etale R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase) :
    (schemeAtlasChart G U X₀ a).IsEtaleSurjective :=
  have : ((@_root_.AlgebraicGeometry.Etale ⊓ @_root_.AlgebraicGeometry.Surjective) :
      MorphismProperty Scheme.{u}).RespectsIso :=
    have : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    MorphismProperty.RespectsIso.inf _ _
  schemeAtlasChart_hasRepresentableProperty_of_representation X₀ a _ hrep

end Presentation

/-- **The pullback presentation of `atlasChart` from a representing scheme**: the special case
of `schemeAtlasPullbackPresentation` for the chart attached to an identification of `U.space`
with the algebraic space of the scheme `X₀`. -/
noncomputable def atlasPullbackPresentation (X₀ : Scheme.{u})
    (h : U.space = AlgebraicSpace.ofScheme.obj X₀) {T : Scheme.{u}} (P : ActionTorsor G U T)
    (R : TorsorRepresentation P.toFppfTorsor) :
    (atlasChart G U X₀ h).PullbackPresentation T P :=
  have := isIso_atlasChart_eqToHom h
  schemeAtlasPullbackPresentation X₀ _ P R

/-- **The atlas chart `U₀ → [U/G]` is étale and surjective once torsors are representable**
(by schemes étale and surjective over the base); the representability is a hypothesis. -/
theorem atlasChart_isEtaleSurjective_of_representation (X₀ : Scheme.{u})
    (h : U.space = AlgebraicSpace.ofScheme.obj X₀)
    (hrep : ∀ (T : Scheme.{u}) (P : FppfTorsor G T), ∃ R : TorsorRepresentation P,
      _root_.AlgebraicGeometry.Etale R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase) :
    (atlasChart G U X₀ h).IsEtaleSurjective :=
  have := isIso_atlasChart_eqToHom h
  schemeAtlasChart_isEtaleSurjective_of_representation X₀ _ hrep

/-- **The atlas `pt → BG` of the classifying stack**: the atlas chart of
`classifyingStack G = [pt/G]`, with chart scheme the terminal scheme `⊤_ Scheme` (that is,
`Spec ℤ`) carrying the trivial action. -/
noncomputable abbrev classifyingAtlasChart (G : AlgebraicSpaceGroup.{u}) :
    StackChart (classifyingStack G) :=
  atlasChart G (AlgebraicSpaceAction.pointAction G) (⊤_ Scheme.{u}) rfl

/-- **The atlas `pt → BG` is étale and surjective once torsors are representable** (by
schemes étale and surjective over the base); the representability is a hypothesis. -/
theorem classifyingAtlasChart_isEtaleSurjective_of_representation
    (G : AlgebraicSpaceGroup.{u})
    (hrep : ∀ (T : Scheme.{u}) (P : FppfTorsor G T), ∃ R : TorsorRepresentation P,
      _root_.AlgebraicGeometry.Etale R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase) :
    (classifyingAtlasChart G).IsEtaleSurjective :=
  atlasChart_isEtaleSurjective_of_representation (⊤_ Scheme.{u}) rfl hrep

end ActionTorsor

end GromovWitten.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

/-! ### Zariski reduction: representability over affine bases suffices -/

namespace TorsorRepresentation

variable {G : AlgebraicSpaceGroup.{u}}

/-- The comparison `P ×_T U ≅ P ×_T Spec Γ(T, U)` of the base changes of an fppf sheaf over
`T` along an affine open `U` and along its presentation `Spec Γ(T, U) ≅ U → T`. -/
noncomputable def affineOpenPullbackIso {T : Scheme.{u}} {F : FppfSheaf.{u}}
    (π : F ⟶ fppfYoneda.obj T) {V : T.Opens} (hV : IsAffineOpen V) :
    Limits.pullback π (fppfYoneda.map V.ι) ≅
      Limits.pullback π (fppfYoneda.map (hV.isoSpec.inv ≫ V.ι)) :=
  asIso (Limits.pullback.map π (fppfYoneda.map V.ι) π
    (fppfYoneda.map (hV.isoSpec.inv ≫ V.ι)) (𝟙 _) (fppfYoneda.map hV.isoSpec.hom) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id, ← Functor.map_comp, Iso.hom_inv_id_assoc]))

@[reassoc]
theorem affineOpenPullbackIso_hom_snd {T : Scheme.{u}} {F : FppfSheaf.{u}}
    (π : F ⟶ fppfYoneda.obj T) {V : T.Opens} (hV : IsAffineOpen V) :
    (affineOpenPullbackIso π hV).hom ≫
        Limits.pullback.snd π (fppfYoneda.map (hV.isoSpec.inv ≫ V.ι)) =
      Limits.pullback.snd π (fppfYoneda.map V.ι) ≫ fppfYoneda.map hV.isoSpec.hom :=
  Limits.pullback.lift_snd _ _ _

/-- **Zariski reduction for the representability of torsors.**  If every fppf `G`-torsor over
every affine scheme `Spec A` is represented by a scheme étale, finite and surjective over
`Spec A`, then so is every fppf `G`-torsor over every scheme: the representing schemes of the
base changes of the torsor to the affine opens of the base glue
(`LocallyRepresentable`, Zariski gluing). -/
theorem exists_of_affine
    (haff : ∀ (A : Type u) [CommRing A] (P : FppfTorsor G (Spec (CommRingCat.of A))),
      ∃ R : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale R.toBase ∧
        IsFinite R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase)
    {T : Scheme.{u}} (P : FppfTorsor G T) :
    ∃ R : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale R.toBase ∧
      IsFinite R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase := by
  choose R hR using fun i : T.affineOpens =>
    haff Γ(T, (i : T.Opens)) (P.pullbackTorsor (i.2.isoSpec.inv ≫ (i : T.Opens).ι))
  let L : LocallyRepresentable P.P P.projection :=
    { ι := T.affineOpens
      U := fun i => i
      iSup_U := iSup_affineOpens_eq_top T
      X := fun i => (R i).space
      g := fun i => (R i).toBase ≫ i.2.isoSpec.inv
      θ := fun i => affineOpenPullbackIso P.projection i.2 ≪≫ (R i).iso.symm
      θ_over := fun i => by
        have h := (R i).iso_hom_projection
        rw [← Iso.eq_inv_comp] at h
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
        rw [← Category.assoc (R i).iso.inv, ← h]
        erw [affineOpenPullbackIso_hom_snd_assoc]
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.id_comp] }
  refine ⟨⟨L.scheme, L.toBase, L.iso, L.iso_hom_comp⟩, ?_, ?_, ?_⟩
  · refine L.etale_toBase fun i => ?_
    have := (hR i).1
    change _root_.AlgebraicGeometry.Etale ((R i).toBase ≫ i.2.isoSpec.inv)
    infer_instance
  · refine L.isFinite_toBase fun i => ?_
    have := (hR i).2.1
    change IsFinite ((R i).toBase ≫ i.2.isoSpec.inv)
    infer_instance
  · refine L.surjective_toBase fun i => ?_
    have := (hR i).2.2
    change _root_.AlgebraicGeometry.Surjective ((R i).toBase ≫ i.2.isoSpec.inv)
    infer_instance

/-- **Affine step: a torsor over `Spec A` with an affine descent input is representable.**
Given a faithfully flat, finitely presented `A`-algebra `B` and an identification of
`P ×_{Spec A} Spec B` with `Spec M` over `Spec B` (an `AffineDescentInput`) such that `M` is
étale and finite over `B` and `Spec M → Spec B` is surjective, the descended algebra
`C = D.descended` represents `P` (`AffineDescentInput.toSpec`), and `Spec C → Spec A` is
étale, finite and surjective. -/
theorem exists_of_affineDescentInput {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    {P : FppfTorsor G (Spec (CommRingCat.of A))} (D : AffineDescentInput A B P.P P.projection)
    [Algebra.Etale B D.M] [Module.Finite B D.M]
    (hsurj : _root_.AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap B D.M)))) :
    ∃ R : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale R.toBase ∧
      IsFinite R.toBase ∧ _root_.AlgebraicGeometry.Surjective R.toBase := by
  have hiso := D.isIso_toSpec
  have hcomp := D.toSpec_comp
  refine ⟨⟨Spec (CommRingCat.of D.descended),
    Spec.map (CommRingCat.ofHom (algebraMap A D.descended)), (asIso D.toSpec).symm, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, hcomp]
  · have := D.etale_descended
    change _root_.AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom _))
    rw [HasRingHomProperty.Spec_iff (P := @_root_.AlgebraicGeometry.Etale)]
    exact RingHom.etale_algebraMap.2 this
  · have := D.finite_descended
    change IsFinite (Spec.map (CommRingCat.ofHom _))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this
  · change _root_.AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom _))
    have hB : _root_.AlgebraicGeometry.Surjective
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
      ((flat_and_surjective_SpecMap_iff _).2
        (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)).2
    have hfac : Spec.map (CommRingCat.ofHom (algebraMap B D.M)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A B)) =
        Spec.map (CommRingCat.ofHom (D.descended.val.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A D.descended)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply A B D.M x).symm.trans
        (D.descended.val.commutes x).symm
    have : _root_.AlgebraicGeometry.Surjective
        (Spec.map (CommRingCat.ofHom (D.descended.val.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A D.descended))) := by
      rw [← hfac]
      infer_instance
    exact _root_.AlgebraicGeometry.Surjective.of_comp
      (Spec.map (CommRingCat.ofHom (D.descended.val.toRingHom))) _

/-- **Torsors under an affine étale finite group are schemes (B4.1), given affine
trivialisations.**  Let `G = affineGroup R grp` with `R` étale and finite over `ℤ` (here
`TorsorZu = ULift ℤ`) and `Spec R → Spec ℤ` surjective.  Assume that every `G`-torsor over every
affine scheme `Spec A` admits a `TorsorAffineTrivialisation` (an affine faithfully flat finitely
presented cover with a section; this existence is the hypothesis `htriv`).  Then every fppf
`G`-torsor over every scheme `T` is represented by a scheme étale, finite and surjective over
`T`. -/
theorem exists_affineGroup_of_trivialisation {R : Type u} [CommRing R]
    {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    (htriv : ∀ (A : Type u) [CommRing A]
      (P : FppfTorsor (affineGroup R grp) (Spec (CommRingCat.of A))),
      Nonempty (TorsorAffineTrivialisation P))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    ∃ Rp : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale Rp.toBase ∧
      IsFinite Rp.toBase ∧ _root_.AlgebraicGeometry.Surjective Rp.toBase := by
  refine exists_of_affine (fun A _ P' => ?_) P
  obtain ⟨D⟩ := htriv A P'
  have := D.etale_descentInput hEtale
  have := D.finite_descentInput
  exact exists_of_affineDescentInput D.descentInput (D.surjective_descentInput hR)

end TorsorRepresentation

end GromovWitten.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

/-! ### The atlas of `[U₀/G]` and `BG` for an affine étale finite group -/

namespace ActionTorsor

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}

/-- **The atlas `U₀ → [U₀/G]` is étale and surjective** for `G = affineGroup R grp` with `R`
étale and finite over `ℤ` and `Spec R → Spec ℤ` surjective, under the hypothesis `htriv` that
torsors over affine bases admit affine faithfully flat trivialisations.  The representable
diagonal of `[U₀/G]` is not proved here, so no `DeligneMumfordStack` is constructed. -/
theorem atlasChart_affineGroup_isEtaleSurjective
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    (htriv : ∀ (A : Type u) [CommRing A]
      (P : FppfTorsor (affineGroup R grp) (Spec (CommRingCat.of A))),
      Nonempty (TorsorAffineTrivialisation P))
    (U : AlgebraicSpaceAction (affineGroup R grp)) (X₀ : Scheme.{u})
    (h : U.space = AlgebraicSpace.ofScheme.obj X₀) :
    (atlasChart (affineGroup R grp) U X₀ h).IsEtaleSurjective :=
  atlasChart_isEtaleSurjective_of_representation X₀ h fun _ P => by
    obtain ⟨Rp, h1, -, h3⟩ :=
      TorsorRepresentation.exists_affineGroup_of_trivialisation hEtale hR htriv P
    exact ⟨Rp, h1, h3⟩

/-- **The atlas `pt → BG` is étale and surjective** for `G = affineGroup R grp` with `R` étale
and finite over `ℤ` and `Spec R → Spec ℤ` surjective, under the hypothesis `htriv` that torsors
over affine bases admit affine faithfully flat trivialisations.  The representable diagonal of
`BG` is not proved here, so no `DeligneMumfordStack` is constructed. -/
theorem classifyingAtlasChart_affineGroup_isEtaleSurjective
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    (htriv : ∀ (A : Type u) [CommRing A]
      (P : FppfTorsor (affineGroup R grp) (Spec (CommRingCat.of A))),
      Nonempty (TorsorAffineTrivialisation P)) :
    (classifyingAtlasChart (affineGroup R grp)).IsEtaleSurjective :=
  atlasChart_affineGroup_isEtaleSurjective hEtale hR htriv _ _ rfl

/-- **The atlas `U₀ → [U₀/G]` is étale and surjective** (unconditional form) for
`G = affineGroup R grp` with `R` étale and finite over `ℤ` (`TorsorZu = ULift ℤ`) and
`Spec R → Spec ℤ` surjective, for any action `U` whose space is the algebraic space of the
scheme `U₀`.  The representable diagonal of `[U₀/G]` is not proved here, so no
`DeligneMumfordStack` is constructed. -/
theorem atlasChart_affineGroup_isEtaleSurjective'
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    (U : AlgebraicSpaceAction (affineGroup R grp)) (U₀ : Scheme.{u})
    (h : U.space = AlgebraicSpace.ofScheme.obj U₀) :
    (atlasChart (affineGroup R grp) U U₀ h).IsEtaleSurjective :=
  atlasChart_affineGroup_isEtaleSurjective hEtale hR
    (fun _ _ P => FppfTorsor.nonempty_torsorAffineTrivialisation P) U U₀ h

/-- **The atlas `pt → BG` is étale and surjective** (unconditional form) for
`G = affineGroup R grp` with `R` étale and finite over `ℤ` (`TorsorZu = ULift ℤ`) and
`Spec R → Spec ℤ` surjective.  The representable diagonal of `BG` is not proved here, so no
`DeligneMumfordStack` is constructed. -/
theorem classifyingAtlasChart_affineGroup_isEtaleSurjective'
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    (classifyingAtlasChart (affineGroup R grp)).IsEtaleSurjective :=
  classifyingAtlasChart_affineGroup_isEtaleSurjective hEtale hR
    (fun _ _ P => FppfTorsor.nonempty_torsorAffineTrivialisation P)

end ActionTorsor

namespace FppfTorsor

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}

/-- **Torsors under an affine étale finite group are schemes (blueprint B4.1, unconditional).**
For `G = affineGroup R grp` with `R` étale and finite over `ℤ` (`TorsorZu = ULift ℤ`) and
`Spec R → Spec ℤ` surjective, every fppf `G`-torsor over every scheme `T` is represented by a
scheme étale, finite and surjective over `T`. -/
theorem exists_torsorRepresentation_affineGroup
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    ∃ Rp : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale Rp.toBase ∧
      IsFinite Rp.toBase ∧ _root_.AlgebraicGeometry.Surjective Rp.toBase :=
  TorsorRepresentation.exists_affineGroup_of_trivialisation hEtale hR
    (fun _ _ P => nonempty_torsorAffineTrivialisation P) P

/-- **A chosen representing scheme of a torsor under an affine étale finite group**
(`Classical.choose` of `exists_torsorRepresentation_affineGroup`). -/
noncomputable def representation
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) : TorsorRepresentation P :=
  (exists_torsorRepresentation_affineGroup hEtale hR P).choose

/-- The chosen representing scheme is étale over the base. -/
theorem etale_representation_toBase
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    _root_.AlgebraicGeometry.Etale (representation hEtale hR P).toBase :=
  (exists_torsorRepresentation_affineGroup hEtale hR P).choose_spec.1

/-- The chosen representing scheme is finite over the base. -/
theorem isFinite_representation_toBase
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    IsFinite (representation hEtale hR P).toBase :=
  (exists_torsorRepresentation_affineGroup hEtale hR P).choose_spec.2.1

/-- The chosen representing scheme is surjective over the base. -/
theorem surjective_representation_toBase
    (hEtale : @Algebra.Etale TorsorZu.{u} R _ _ (torsorZuAlgebra R))
    [Module.Finite TorsorZu.{u} R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    _root_.AlgebraicGeometry.Surjective (representation hEtale hR P).toBase :=
  (exists_torsorRepresentation_affineGroup hEtale hR P).choose_spec.2.2

/-- `exists_torsorRepresentation_affineGroup` with the ordinary hypotheses
`[Algebra.Etale ℤ R] [Module.Finite ℤ R]` (through `etale_torsorZu_of_etale` and
`finite_torsorZu_of_finite`). -/
theorem exists_torsorRepresentation_affineGroup_of_int [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    {T : Scheme.{u}} (P : FppfTorsor (affineGroup R grp) T) :
    ∃ Rp : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale Rp.toBase ∧
      IsFinite Rp.toBase ∧ _root_.AlgebraicGeometry.Surjective Rp.toBase :=
  have := finite_torsorZu_of_finite (R := R)
  exists_torsorRepresentation_affineGroup etale_torsorZu_of_etale hR P

end FppfTorsor

namespace ActionTorsor

variable {R : Type u} [CommRing R] {grp : GrpObj (fppfYoneda.obj (Spec (CommRingCat.of R)))}

/-- `atlasChart_affineGroup_isEtaleSurjective'` with the ordinary hypotheses
`[Algebra.Etale ℤ R] [Module.Finite ℤ R]`. -/
theorem atlasChart_affineGroup_isEtaleSurjective_of_int [Algebra.Etale ℤ R] [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R)))))
    (U : AlgebraicSpaceAction (affineGroup R grp)) (U₀ : Scheme.{u})
    (h : U.space = AlgebraicSpace.ofScheme.obj U₀) :
    (atlasChart (affineGroup R grp) U U₀ h).IsEtaleSurjective :=
  have := finite_torsorZu_of_finite (R := R)
  atlasChart_affineGroup_isEtaleSurjective' etale_torsorZu_of_etale hR U U₀ h

/-- `classifyingAtlasChart_affineGroup_isEtaleSurjective'` with the ordinary hypotheses
`[Algebra.Etale ℤ R] [Module.Finite ℤ R]`. -/
theorem classifyingAtlasChart_affineGroup_isEtaleSurjective_of_int [Algebra.Etale ℤ R]
    [Module.Finite ℤ R]
    (hR : _root_.AlgebraicGeometry.Surjective
      (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of R)
        (CommRingCat.ofHom (@algebraMap TorsorZu.{u} R _ _ (torsorZuAlgebra R))))) :
    (classifyingAtlasChart (affineGroup R grp)).IsEtaleSurjective :=
  have := finite_torsorZu_of_finite (R := R)
  classifyingAtlasChart_affineGroup_isEtaleSurjective' etale_torsorZu_of_etale hR

end ActionTorsor

end GromovWitten.AlgebraicGeometry
