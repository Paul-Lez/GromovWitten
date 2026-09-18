/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorStackEffective
import GromovWitten.AlgebraicGeometry.Stacks.SieveCover

/-!
# Removing the single-cover hypothesis from effective descent for `[U/G]`

`Stacks/TorsorStackEffective.lean` proves effectiveness of fppf descent for the quotient
prestack `[U/G]` along a covering sieve `R` on `S`, but the resulting equivariant torsor is
only produced once one knows an fppf-local section of the glued sheaf, and the only
unconditional source of such a section there is a *single* member `w : W ⟶ S` of the sieve
which is flat, locally of finite presentation and surjective.

This file removes that hypothesis.  The missing ingredient is exactly the statement that an
fppf sheaf of sets sends a coproduct of schemes to a product of sets: the local sections of
the glued sheaf over the members of a small covering family then assemble into a single local
section over their coproduct, and the coproduct map is flat, locally of finite presentation and
surjective by `IsZariskiLocalAtSource.sigmaDesc` and joint surjectivity.

The product statement is deduced from Mathlib's
`AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology` (Zariski sheaves
preserve products) together with `Scheme.zariskiTopology ≤ Scheme.fppfTopology`.

## Main declarations

* `GromovWitten.AlgebraicGeometry.zariskiTopology_le_fppfTopology`: every Zariski covering sieve
  is an fppf covering sieve.
* `GromovWitten.AlgebraicGeometry.FppfSheaf.exists_sigma_section`: an fppf sheaf of sets sends a
  coproduct of schemes to a product; stated as the existence of a section over `∐ V` restricting
  to prescribed sections over the `V i`.
* `GromovWitten.AlgebraicGeometry.FppfSheaf.exists_hom_sigma`: the same statement read on
  morphisms out of representable sheaves.
* `GromovWitten.AlgebraicGeometry.FppfLocalSection.ofFamily`: an fppf-local section built from a
  jointly surjective family of flat, locally finitely presented local sections.
* `GromovWitten.AlgebraicGeometry.ActionTorsor.TorsorGlue.localSectionOfSieve`: the fppf-local
  section of the glued sheaf, produced from the covering sieve alone.
* `GromovWitten.AlgebraicGeometry.ActionTorsor.exists_torsor_of_torsorDescentDatum'`:
  **effectiveness of fppf descent for `[U/G]` along an arbitrary covering sieve**.
* `GromovWitten.AlgebraicGeometry.ActionTorsor.TorsorStack'` and
  `ActionTorsor.torsorStack'`: the hypothesis-free form of `ActionTorsor.TorsorStack`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace GromovWitten.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- Every Zariski covering sieve of schemes is an fppf covering sieve. -/
theorem zariskiTopology_le_fppfTopology :
    Scheme.zariskiTopology.{u} ≤ Scheme.fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage

namespace FppfSheaf

/-- The opposite of the coproduct cofan of a family of schemes, mapped through an fppf sheaf, is
a limit fan of sets.  This is the sheaf-theoretic content of "an fppf sheaf sends coproducts of
schemes to products of sets"; it is `preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology`
applied to the sheaf, which is a Zariski sheaf because `Scheme.zariskiTopology ≤
Scheme.fppfTopology`. -/
noncomputable def sigmaFanIsLimit {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u}) :
    IsLimit (A.obj.mapCone (Cofan.op (Cofan.mk (∐ V) (Sigma.ι V)))) := by
  have hz : Presieve.IsSheaf Scheme.zariskiTopology.{u} A.obj := fun _ Sv hSv =>
    GromovWitten.SheafGluing.isSheafOfType A _ (zariskiTopology_le_fppfTopology _ hSv)
  have hpres : PreservesLimitsOfShape (Discrete ι) A.obj :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hz
  exact isLimitOfPreserves A.obj (Cofan.IsColimit.op (coproductIsCoproduct V))

/-- The test cone with one-point vertex used to read off the sections of an fppf sheaf over a
coproduct of schemes. -/
def sigmaTestCone {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    (a : ∀ i, A.obj.obj (op (V i))) : Cone (Discrete.functor (fun i => op (V i)) ⋙ A.obj) where
  pt := PUnit.{u + 1}
  π := Discrete.natTrans fun i => TypeCat.ofHom fun _ => a i.as

@[simp]
theorem sigmaTestCone_π_app {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    (a : ∀ i, A.obj.obj (op (V i))) (i : ι) :
    (sigmaTestCone V A a).π.app ⟨i⟩ = TypeCat.ofHom fun _ => a i :=
  rfl

/-- **An fppf sheaf of sets sends a coproduct of schemes to a product of sets.**  Concretely,
prescribed sections over the members `V i` of a family of schemes come from a section over the
coproduct `∐ V`. -/
theorem exists_sigma_section {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    (a : ∀ i, A.obj.obj (op (V i))) :
    ∃ x : A.obj.obj (op (∐ V)), ∀ i, A.obj.map (Sigma.ι V i).op x = a i := by
  refine ⟨(sigmaFanIsLimit V A).lift (sigmaTestCone V A a) PUnit.unit, fun i => ?_⟩
  have h1 := (sigmaFanIsLimit V A).fac (sigmaTestCone V A a) ⟨i⟩
  have h2 := congrArg (fun t : PUnit.{u + 1} ⟶ A.obj.obj (op (V i)) => t PUnit.unit) h1
  exact h2

/-- **Separatedness of an fppf sheaf along a coproduct of schemes**: a section over `∐ V` is
determined by its restrictions to the members `V i`. -/
theorem sigma_section_ext {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    {x y : A.obj.obj (op (∐ V))}
    (h : ∀ i, A.obj.map (Sigma.ι V i).op x = A.obj.map (Sigma.ι V i).op y) : x = y := by
  have key := (sigmaFanIsLimit V A).hom_ext
    (f := TypeCat.ofHom fun _ : PUnit.{u + 1} => x)
    (f' := TypeCat.ofHom fun _ : PUnit.{u + 1} => y) ?_
  · exact congrArg (fun t : PUnit.{u + 1} ⟶ A.obj.obj (op (∐ V)) => t PUnit.unit) key
  · rintro ⟨i⟩
    ext _
    simpa using h i

/-- **An fppf sheaf of sets sends a coproduct of schemes to a product of sets**, read on
morphisms out of representable sheaves. -/
theorem exists_hom_sigma {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    (l : ∀ i, fppfYoneda.obj (V i) ⟶ A) :
    ∃ L : fppfYoneda.obj (∐ V) ⟶ A, ∀ i, fppfYoneda.map (Sigma.ι V i) ≫ L = l i := by
  obtain ⟨x, hx⟩ := exists_sigma_section V A fun i =>
    Scheme.fppfTopology.yonedaEquiv (l i)
  refine ⟨Scheme.fppfTopology.yonedaEquiv.symm x, fun i => ?_⟩
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← GrothendieckTopology.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  exact hx i

/-- **Separatedness of an fppf sheaf along a coproduct of schemes**, read on morphisms out of
representable sheaves. -/
theorem hom_sigma_ext {ι : Type u} (V : ι → Scheme.{u}) (A : FppfSheaf.{u})
    {L₁ L₂ : fppfYoneda.obj (∐ V) ⟶ A}
    (h : ∀ i, fppfYoneda.map (Sigma.ι V i) ≫ L₁ = fppfYoneda.map (Sigma.ι V i) ≫ L₂) :
    L₁ = L₂ := by
  apply Scheme.fppfTopology.yonedaEquiv.injective
  refine sigma_section_ext V A fun i => ?_
  rw [GrothendieckTopology.yonedaEquiv_naturality,
    GrothendieckTopology.yonedaEquiv_naturality, h i]

end FppfSheaf

/-- **An fppf-local section built from a family.**  If a jointly surjective family of flat,
locally finitely presented morphisms `p i : V i ⟶ T` each carries a section of `P`, then the
coproduct `∐ V ⟶ T` carries a single one; this is the `FppfLocalSection` demanded by
`FppfTorsor`, without any hypothesis that a single member of the family is already surjective. -/
noncomputable def FppfLocalSection.ofFamily {P : FppfSheaf.{u}} {T : Scheme.{u}}
    {π : P ⟶ fppfYoneda.obj T} {ι : Type u} {V : ι → Scheme.{u}} (p : ∀ i, V i ⟶ T)
    (hflat : ∀ i, Flat (p i)) (hlfp : ∀ i, LocallyOfFinitePresentation (p i))
    (hsurj : ∀ x : T, ∃ i, x ∈ Set.range (p i))
    (l : ∀ i, fppfYoneda.obj (V i) ⟶ P) (hl : ∀ i, l i ≫ π = fppfYoneda.map (p i)) :
    FppfLocalSection P T π :=
  { coverScheme := ∐ V
    cover := Sigma.desc p
    flat := by
      let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
      exact IsZariskiLocalAtSource.sigmaDesc hflat
    locallyOfFinitePresentation := by
      let _ := HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
      exact IsZariskiLocalAtSource.sigmaDesc hlfp
    surjective := by
      refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨i, hi⟩ := hsurj x
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    localLift := (FppfSheaf.exists_hom_sigma V P l).choose
    localLift_over := by
      have hspec := (FppfSheaf.exists_hom_sigma V P l).choose_spec
      refine FppfSheaf.hom_sigma_ext V _ fun i => ?_
      rw [← Category.assoc, hspec i, hl i, ← Functor.map_comp, Sigma.ι_desc] }

namespace ActionTorsor

variable {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G} {S : Scheme.{u}}
  {R : Sieve S} {D : TorsorDescentDatum G U S R}

namespace TorsorGlue

variable (T : TorsorGlue D)

/-- **The fppf-local section of the glued sheaf, from the covering sieve alone.**  A covering
sieve contains a small jointly surjective family of flat morphisms locally of finite
presentation (`exists_covering_family`); composing the trivialising covers of the corresponding
members of the descent datum with that family gives a jointly surjective family of flat,
locally finitely presented morphisms over which the glued sheaf has sections, and these sections
assemble into one over the coproduct by `FppfSheaf.exists_hom_sigma`. -/
theorem nonempty_localSectionOfSieve (hR : R ∈ fppfJ.{u} S) :
    Nonempty (FppfLocalSection T.base S T.over) := by
  obtain ⟨ι, X, g, hgR, hmem⟩ := exists_covering_family hR
  rw [mem_fppfPrecoverage_iff] at hmem
  obtain ⟨hsurj, hprop⟩ := hmem
  refine ⟨FppfLocalSection.ofFamily
    (V := fun i => (D.torsor (g i) (hgR i)).locallyTrivial.coverScheme)
    (fun i => (D.torsor (g i) (hgR i)).locallyTrivial.cover ≫ g i)
    (fun i => ?_) (fun i => ?_) (fun x => ?_)
    (fun i => (D.torsor (g i) (hgR i)).locallyTrivial.localLift ≫ T.str (g i) (hgR i))
    (fun i => ?_)⟩
  · have h1 := (D.torsor (g i) (hgR i)).locallyTrivial.flat
    have h2 := (hprop i).1
    infer_instance
  · have h1 := (D.torsor (g i) (hgR i)).locallyTrivial.locallyOfFinitePresentation
    have h2 := (hprop i).2
    infer_instance
  · obtain ⟨i, hi⟩ := hsurj x
    have h1 := (D.torsor (g i) (hgR i)).locallyTrivial.surjective
    exact ⟨i, (mem_range_iff_of_surjective _ (g i)
      (D.torsor (g i) (hgR i)).locallyTrivial.cover rfl x).2 hi⟩
  · rw [Category.assoc, T.str_over (g i) (hgR i), ← Category.assoc,
      (D.torsor (g i) (hgR i)).locallyTrivial.localLift_over, ← Functor.map_comp]

/-- A choice of fppf-local section of the glued sheaf, produced from the covering sieve alone. -/
noncomputable def localSectionOfSieve (hR : R ∈ fppfJ.{u} S) :
    FppfLocalSection T.base S T.over :=
  (T.nonempty_localSectionOfSieve hR).some

end TorsorGlue

/-- **Effectiveness of fppf descent for the quotient stack `[U/G]`, with no hypothesis on the
covering sieve.**  Every descent datum for equivariant torsors along an fppf covering sieve `R`
on `S` comes from an equivariant torsor `N` over `S`, compatibly with the transition arrows.
This is `exists_torsor_of_torsorDescentDatum` with its single-cover hypothesis removed, using
`TorsorGlue.localSectionOfSieve` in place of `TorsorGlue.localSectionOfCover`. -/
theorem exists_torsor_of_torsorDescentDatum' {R : Sieve S} (hR : R ∈ fppfJ.{u} S)
    (D : TorsorDescentDatum G U S R) :
    ∃ (N : ActionTorsor G U S) (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
        D.torsor f hf ≅ pullbackObj f N),
      ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
        (hf : R.arrows f) (hh' : R.arrows h),
        (ε h hh').hom.iso.hom ≫ proj N h =
          (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
            (ε f hf).hom.iso.hom ≫ proj N f := by
  obtain ⟨T⟩ := nonempty_torsorGlue hR D
  exact ⟨T.torsor hR (T.localSectionOfSieve hR), fun f hf ↦ T.compIso hR _ f hf,
    fun f g h hh hf hh' ↦ T.compIso_trans hR _ f g h hh hf hh'⟩

/-- **The quotient prestack `[U/G]` is a stack for the big fppf topology**, in the
repository-level formulation with explicit data and with no hypothesis on the covering sieve:
descent of arrows (`ActionTorsor.TorsorPrestack`) together with effectiveness of descent of
objects along an arbitrary fppf covering sieve. -/
def TorsorStack' (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) : Prop :=
  TorsorPrestack G U ∧
    ∀ (S : Scheme.{u}) (R : Sieve S), R ∈ fppfJ.{u} S → ∀ D : TorsorDescentDatum G U S R,
      ∃ (N : ActionTorsor G U S) (ε : ∀ {X : Scheme.{u}} (f : X ⟶ S) (hf : R.arrows f),
          D.torsor f hf ≅ pullbackObj f N),
        ∀ {X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) (h : Y ⟶ S) (hh : g ≫ f = h)
          (hf : R.arrows f) (hh' : R.arrows h),
          (ε h hh').hom.iso.hom ≫ proj N h =
            (D.trans f g h hh hf hh').iso.hom ≫ proj (D.torsor f hf) g ≫
              (ε f hf).hom.iso.hom ≫ proj N f

/-- **`[U/G]` is a stack**, unconditionally and with no hypothesis on the covering sieves. -/
theorem torsorStack' (G : AlgebraicSpaceGroup.{u}) (U : AlgebraicSpaceAction G) :
    TorsorStack' G U :=
  ⟨torsorPrestack G U, fun _ _ hR D ↦ exists_torsor_of_torsorDescentDatum' hR D⟩

/-- The hypothesis-free stack property implies the form proved in
`Stacks/TorsorStackEffective.lean`. -/
theorem TorsorStack'.toTorsorStack {G : AlgebraicSpaceGroup.{u}} {U : AlgebraicSpaceAction G}
    (h : TorsorStack' G U) : TorsorStack G U :=
  ⟨h.1, fun S R hR D _ _ _ _ _ _ ↦ h.2 S R hR D⟩

end ActionTorsor

end GromovWitten.AlgebraicGeometry
