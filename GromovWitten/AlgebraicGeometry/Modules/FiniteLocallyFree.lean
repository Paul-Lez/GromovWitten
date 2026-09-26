/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Modules.Stack
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Direct sums of finite locally free module sheaves

Restriction preserves local bases. Products of charts give a common refinement of independent
trivializing covers, on which the direct sum has the combined basis and rank `r + s`.
-/

open CategoryTheory CategoryTheory.Limits

namespace GromovWitten.AlgebraicGeometry.Modules

set_option linter.style.haveILetI false

universe w v u v' u'

open _root_.GromovWitten.AlgebraicGeometry.Sites

variable {C : Type u} [Category.{v} C]
  [UnivLE.{max u v, w}]
  (S : RingedSite.{w} C)
  [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ## Restriction and finite coproducts -/

section Restriction

variable [HasBinaryProducts C]
  [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/- The restriction functor is the pushforward along the forgetful functor from an over-site.
It is a left adjoint because the forgetful functor has the `star` right adjoint. -/
noncomputable instance overFunctor_isLeftAdjoint (X : C) :
    Functor.IsLeftAdjoint (SheafOfModules.overFunctor S.ringStructureSheaf X) := by
  exact ⟨_, ⟨SheafOfModules.overPushforwardOverAdj X⟩⟩

/- In particular, restriction preserves finite coproducts. -/
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}] in
theorem overFunctor_preservesFiniteCoproducts (X : C) :
    PreservesFiniteCoproducts (SheafOfModules.overFunctor S.ringStructureSheaf X) := by
  infer_instance

noncomputable def overFunctor_binaryCoproductIso (X : C) (M N : S.Modules) :
    (SheafOfModules.overFunctor S.ringStructureSheaf X).obj (M ⨿ N) ≅
      (SheafOfModules.overFunctor S.ringStructureSheaf X).obj M ⨿
        (SheafOfModules.overFunctor S.ringStructureSheaf X).obj N := by
  exact (PreservesColimitPair.iso
    (SheafOfModules.overFunctor S.ringStructureSheaf X) M N).symm

end Restriction

section CommonCover

variable [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C]
  [∀ X, HasSheafify (S.topology.over X) AddCommGrpCat.{w}]

/- A local finite-free presentation of each of two modules on one and the same cover.
The cover and the local bases are data; the resulting direct-sum assertion below is derived. -/
structure CommonFiniteLocallyFreeCoverData
    (M N : S.Modules) (r s : ℕ) where
  I : Type u
  X : I → C
  coversTop : S.topology.CoversTop X
  generatorsM (i : I) : (M.over (X i)).GeneratingSections
  locallyFreeM (i : I) : IsIso (generatorsM i).π
  rankM (i : I) : Nonempty ((generatorsM i).I ≃ Fin r)
  generatorsN (i : I) : (N.over (X i)).GeneratingSections
  locallyFreeN (i : I) : IsIso (generatorsN i).π
  rankN (i : I) : Nonempty ((generatorsN i).I ≃ Fin s)

namespace CommonFiniteLocallyFreeCoverData

variable {M N : S.Modules} {r s : ℕ}

noncomputable def localGeneratorsM
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    M.LocalGeneratorsData where
  I := d.I
  X := d.X
  coversTop := d.coversTop
  generators := d.generatorsM

noncomputable def localGeneratorsN
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    N.LocalGeneratorsData where
  I := d.I
  X := d.X
  coversTop := d.coversTop
  generators := d.generatorsN

noncomputable def sumGeneratingSections
    (X : C) {P Q : SheafOfModules.{w} (S.ringStructureSheaf.over X)}
    (p : P.GeneratingSections)
    (q : Q.GeneratingSections) :
    (P ⨿ Q).GeneratingSections where
  I := p.I ⊕ q.I
  s := (P ⨿ Q).freeHomEquiv
    ((SheafOfModules.freeSumIso (R := S.ringStructureSheaf.over X) p.I q.I).inv ≫
      coprod.map p.π q.π)
  epi := by
    change Epi ((P ⨿ Q).freeHomEquiv.symm
      ((P ⨿ Q).freeHomEquiv
        ((SheafOfModules.freeSumIso (R := S.ringStructureSheaf.over X) p.I q.I).inv ≫
          coprod.map p.π q.π)))
    rw [Equiv.symm_apply_apply]
    infer_instance

omit [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C] in
theorem sumGeneratingSections_pi
    (X : C) {P Q : SheafOfModules.{w} (S.ringStructureSheaf.over X)}
    (p : P.GeneratingSections)
    (q : Q.GeneratingSections) :
    (sumGeneratingSections S X p q).π =
      (SheafOfModules.freeSumIso (R := S.ringStructureSheaf.over X) p.I q.I).inv ≫
        coprod.map p.π q.π := by
  dsimp [sumGeneratingSections]
  change (P ⨿ Q).freeHomEquiv.symm _ = _
  rw [Equiv.symm_apply_apply]

omit [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C] in
theorem sumGeneratingSections_isIso
    (X : C) {P Q : SheafOfModules.{w} (S.ringStructureSheaf.over X)}
    (p : P.GeneratingSections)
    (q : Q.GeneratingSections)
    [IsIso p.π] [IsIso q.π] :
    IsIso (sumGeneratingSections S X p q).π := by
  rw [sumGeneratingSections_pi]
  let e := (SheafOfModules.freeSumIso (R := S.ringStructureSheaf.over X) p.I q.I).symm ≪≫
    coprod.mapIso (asIso p.π) (asIso q.π)
  exact e.isIso_hom

omit [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C] in
theorem transported_sumGeneratingSections_pi
    (X : C) {P Q T : SheafOfModules.{w} (S.ringStructureSheaf.over X)}
    (p : P.GeneratingSections)
    (q : Q.GeneratingSections)
    (e : (P ⨿ Q) ≅ T) :
    (SheafOfModules.GeneratingSections.equivOfIso e
      (sumGeneratingSections S X p q)).π =
      (sumGeneratingSections S X p q).π ≫ e.hom := by
  change ((sumGeneratingSections S X p q).ofEpi e.hom).π = _
  rw [SheafOfModules.GeneratingSections.ofEpi_π]

private noncomputable def localGeneratorsSum
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    ((directSum S).obj (M, N)).LocalGeneratorsData where
  I := d.I
  X := d.X
  coversTop := d.coversTop
  generators i :=
    SheafOfModules.GeneratingSections.equivOfIso
      (overFunctor_binaryCoproductIso S (d.X i) M N).symm
      (sumGeneratingSections S (d.X i)
        (d.generatorsM i) (d.generatorsN i))

private theorem localGeneratorsSum_isLocallyFreeData
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    (localGeneratorsSum S d).IsLocallyFreeData := by
  unfold localGeneratorsSum
  refine { isIso := fun i ↦ ?_ }
  change IsIso ((SheafOfModules.GeneratingSections.equivOfIso
    (overFunctor_binaryCoproductIso S (d.X i) M N).symm
    (sumGeneratingSections S (d.X i)
      (d.generatorsM i) (d.generatorsN i))).π)
  haveI : IsIso (d.generatorsM i).π := d.locallyFreeM i
  haveI : IsIso (d.generatorsN i).π := d.locallyFreeN i
  let e := (overFunctor_binaryCoproductIso S (d.X i) M N).symm
  haveI : IsIso e.hom := e.isIso_hom
  rw [transported_sumGeneratingSections_pi]
  let eSum :=
    (SheafOfModules.freeSumIso (R := S.ringStructureSheaf.over (d.X i))
      (d.generatorsM i).I (d.generatorsN i).I).symm ≪≫
      coprod.mapIso (asIso (d.generatorsM i).π) (asIso (d.generatorsN i).π)
  have hSum : (sumGeneratingSections S (d.X i)
      (d.generatorsM i) (d.generatorsN i)).π = eSum.hom := by
    dsimp [eSum]
    rw [sumGeneratingSections_pi]
    rfl
  rw [hSum]
  change IsIso (eSum.hom ≫ e.hom)
  exact (eSum ≪≫ e).isIso_hom

private theorem localGeneratorsSum_rank
    (d : CommonFiniteLocallyFreeCoverData S M N r s)
    (i : (localGeneratorsSum S d).I) :
    Nonempty (((localGeneratorsSum S d).generators i).I ≃ Fin (r + s)) := by
  dsimp [localGeneratorsSum]
  let eM := Classical.choice (d.rankM i)
  let eN := Classical.choice (d.rankN i)
  exact ⟨(Equiv.sumCongr eM eN).trans finSumFinEquiv⟩

private theorem localGeneratorsSum_isFinitePresentation
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    IsFinitePresentation S ((directSum S).obj (M, N)) := by
  let q := localGeneratorsSum S d
  haveI : q.IsLocallyFreeData := localGeneratorsSum_isLocallyFreeData S d
  refine ⟨q.quasiCoherentData, ?_⟩
  refine { isFinite_presentation := fun i ↦ ?_ }
  refine { isFiniteType_generators := ?_, isFiniteType_relations := ?_ }
  · refine ⟨?_⟩
    dsimp [q, localGeneratorsSum]
    change Finite ((d.generatorsM i).I ⊕ (d.generatorsN i).I)
    let eM := Classical.choice (d.rankM i)
    let eN := Classical.choice (d.rankN i)
    haveI : Finite (d.generatorsM i).I := Finite.of_injective eM eM.injective
    haveI : Finite (d.generatorsN i).I := Finite.of_injective eN eN.injective
    infer_instance
  · refine ⟨?_⟩
    change Finite (ULift Empty)
    infer_instance

/- The direct sum has constant rank `r + s` whenever both summands are free of those ranks on a
common actual cover. -/
noncomputable def directSumData
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    FiniteLocallyFreeOfRankData S ((directSum S).obj (M, N)) (r + s) := by
  let q := localGeneratorsSum S d
  haveI : q.IsLocallyFreeData := localGeneratorsSum_isLocallyFreeData S d
  refine {
    trivialization := q
    locallyFreeData := inferInstance
    finitePresentation := localGeneratorsSum_isFinitePresentation S d
    rank := localGeneratorsSum_rank S d }

end CommonFiniteLocallyFreeCoverData

theorem directSum_isFiniteLocallyFreeOfRank_of_commonCover
    {M N : S.Modules} {r s : ℕ}
    (d : CommonFiniteLocallyFreeCoverData S M N r s) :
    IsFiniteLocallyFreeOfRank S ((directSum S).obj (M, N)) (r + s) :=
  ⟨CommonFiniteLocallyFreeCoverData.directSumData S d⟩

/-! ### Common refinements

The next construction makes the geometric input needed to compare two independently chosen
trivializations explicit.  A refinement supplies, for every refined chart, maps to one chart of
each original cover.  Pulling generating sections along those maps preserves both their index and
their isomorphism property.  This avoids identifying the two original indexing types. -/

section CommonRefinement

variable [HasPullbacks C]

namespace CommonFiniteLocallyFreeCoverData

noncomputable def restrictGeneratingSections
    {M : S.Modules} {X Y : C} (f : X ⟶ Y)
    (p : (M.over Y).GeneratingSections) : (M.over X).GeneratingSections :=
  p.map (SheafOfModules.overMap S.ringStructureSheaf f)
    (SheafOfModules.overMapUnitIso f).symm

omit [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasBinaryProducts C] in
theorem restrictGeneratingSections_isIso
    {M : S.Modules} {X Y : C} (f : X ⟶ Y)
    (p : (M.over Y).GeneratingSections) (hp : IsIso p.π) :
    IsIso (restrictGeneratingSections S f p).π := by
  haveI : IsIso p.π := hp
  change IsIso ((p.map (SheafOfModules.overMap S.ringStructureSheaf f)
    (SheafOfModules.overMapUnitIso f).symm).π)
  rw [SheafOfModules.GeneratingSections.map_π_eq]
  haveI : IsIso ((SheafOfModules.overMap S.ringStructureSheaf f).map p.π) :=
    (SheafOfModules.overMap S.ringStructureSheaf f).map_isIso p.π
  let e := SheafOfModules.mapFreeIso (SheafOfModules.overMap S.ringStructureSheaf f)
    p.I (SheafOfModules.overMapUnitIso f).symm
  exact (e ≪≫ asIso ((SheafOfModules.overMap S.ringStructureSheaf f).map p.π)).isIso_hom

/-- A common cover with maps to both independently chosen local-free covers. -/
structure RefinementData
    {M N : S.Modules} {r s : ℕ}
    (dM : FiniteLocallyFreeOfRankData S M r)
    (dN : FiniteLocallyFreeOfRankData S N s) where
  I : Type u
  X : I → C
  coversTop : S.topology.CoversTop X
  indexM : I → dM.trivialization.I
  indexN : I → dN.trivialization.I
  mapM : (i : I) → X i ⟶ dM.trivialization.X (indexM i)
  mapN : (i : I) → X i ⟶ dN.trivialization.X (indexN i)

/-- Products of the charts construct a common refinement of two arbitrary covering families. -/
noncomputable def RefinementData.ofProducts
    {M N : S.Modules} {r s : ℕ}
    (dM : FiniteLocallyFreeOfRankData S M r)
    (dN : FiniteLocallyFreeOfRankData S N s) : RefinementData S dM dN where
  I := dM.trivialization.I × dN.trivialization.I
  X i := dM.trivialization.X i.1 ⨯ dN.trivialization.X i.2
  coversTop X := by
    apply S.topology.superset_covering _
      (S.topology.intersection_covering
        (dM.trivialization.coversTop X) (dN.trivialization.coversTop X))
    rintro Y f ⟨⟨i, ⟨a⟩⟩, ⟨j, ⟨b⟩⟩⟩
    exact ⟨(i, j), ⟨Limits.prod.lift a b⟩⟩
  indexM := Prod.fst
  indexN := Prod.snd
  mapM _ := Limits.prod.fst
  mapN _ := Limits.prod.snd

noncomputable def ofRefinement
    {M N : S.Modules} {r s : ℕ}
    (dM : FiniteLocallyFreeOfRankData S M r)
    (dN : FiniteLocallyFreeOfRankData S N s)
    (h : RefinementData S dM dN) :
    CommonFiniteLocallyFreeCoverData S M N r s where
  I := h.I
  X := h.X
  coversTop := h.coversTop
  generatorsM i :=
    restrictGeneratingSections S (h.mapM i)
      (dM.trivialization.generators (h.indexM i))
  locallyFreeM i := by
    exact restrictGeneratingSections_isIso S (h.mapM i)
      (dM.trivialization.generators (h.indexM i))
      (dM.locallyFreeData.isIso (h.indexM i))
  rankM i := dM.rank (h.indexM i)
  generatorsN i :=
    restrictGeneratingSections S (h.mapN i)
      (dN.trivialization.generators (h.indexN i))
  locallyFreeN i := by
    exact restrictGeneratingSections_isIso S (h.mapN i)
      (dN.trivialization.generators (h.indexN i))
      (dN.locallyFreeData.isIso (h.indexN i))
  rankN i := dN.rank (h.indexN i)

end CommonFiniteLocallyFreeCoverData

end CommonRefinement

/- The refinement constructor feeds the common-cover direct-sum theorem, so the only extra
geometric input is the actual common cover and its maps to both chosen covers. -/
theorem directSum_isFiniteLocallyFreeOfRank_of_refinement
    {M N : S.Modules} {r s : ℕ}
    [HasPullbacks C]
    (dM : FiniteLocallyFreeOfRankData S M r)
    (dN : FiniteLocallyFreeOfRankData S N s)
    (h : CommonFiniteLocallyFreeCoverData.RefinementData S dM dN) :
    IsFiniteLocallyFreeOfRank S ((directSum S).obj (M, N)) (r + s) :=
  directSum_isFiniteLocallyFreeOfRank_of_commonCover S
    (CommonFiniteLocallyFreeCoverData.ofRefinement S dM dN h)

/-- Direct sum preserves finite local freeness and adds ranks.  A common trivializing cover is
constructed from products of the charts of the two independent witnesses. -/
theorem directSum_isFiniteLocallyFreeOfRank
    {M N : S.Modules} {r s : ℕ} [HasPullbacks C]
    (hM : IsFiniteLocallyFreeOfRank S M r)
    (hN : IsFiniteLocallyFreeOfRank S N s) :
    IsFiniteLocallyFreeOfRank S ((directSum S).obj (M, N)) (r + s) := by
  obtain ⟨dM⟩ := hM
  obtain ⟨dN⟩ := hN
  exact directSum_isFiniteLocallyFreeOfRank_of_refinement S dM dN
    (CommonFiniteLocallyFreeCoverData.RefinementData.ofProducts S dM dN)

end CommonCover

end GromovWitten.AlgebraicGeometry.Modules
