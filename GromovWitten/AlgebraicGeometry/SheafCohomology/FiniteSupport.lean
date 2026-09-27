/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.Flasque
import GromovWitten.AlgebraicGeometry.SheafCohomology.OpenRestriction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Flasque sheaves with finite closed support

An abelian sheaf whose stalks vanish outside finitely many closed points is
flasque. Induction on the support uses the stalk-to-skyscraper unit and its
kernel. Hence its positive derived global sections vanish.
-/

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

attribute [local instance] Classical.propDecidable

/-! ### The one-point support step -/

/-- The unit from a sheaf to the skyscraper sheaf on one of its stalks. -/
noncomputable def stalkSkyscraperUnit {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (x : Y) :
    F ⟶ skyscraperSheaf x
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1) :=
  ObjectProperty.homMk
    ((skyscraperSheafForgetAdjunction x).unit.app F.1)

theorem stalkSkyscraperUnit_stalk_iso {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (x : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((TopCat.Sheaf.forget AddCommGrpCat Y).map (stalkSkyscraperUnit F x))) := by
  let adj := skyscraperSheafForgetAdjunction (C := AddCommGrpCat.{u}) x
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (adj.unit.app F.1))
  have hIsoCounit : IsIso (adj.counit.app
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)) := by
    change IsIso (skyscraperPresheafStalkOfSpecializes x _ specializes_rfl).hom
    exact Iso.isIso_hom _
  have hIsoComp : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (adj.unit.app F.1) ≫ adj.counit.app
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)) := by
    have htri := adj.left_triangle_components F.1
    rw [htri]
    exact IsIso.id _
  have hIsoUnit : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (adj.unit.app F.1)) :=
    IsIso.of_isIso_comp_right
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (adj.unit.app F.1))
      (adj.counit.app ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1))
  infer_instance

/-- A sheaf whose only possibly nonzero stalk is at one closed point is flasque. -/
theorem isFlasque_of_single_closed_support {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (x : Y) (hx : IsClosed ({x} : Set Y))
    (hF : ∀ y : Y, y ≠ x →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.1)) :
    TopCat.Sheaf.IsFlasque F := by
  let φ := stalkSkyscraperUnit F x
  have hφ : IsIso φ := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ).mpr
    intro y
    by_cases hxy : y = x
    · subst y
      exact stalkSkyscraperUnit_stalk_iso F x
    · have hF_y := hF y hxy
      have hnot : ¬x ⤳ y := by
        intro h
        have hymem : y ∈ closure ({x} : Set Y) :=
          specializes_iff_mem_closure.mp h
        rw [hx.closure_eq] at hymem
        exact hxy hymem
      have hsky : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj
          (skyscraperSheaf x
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)).1) := by
        have ht := skyscraperPresheafStalkOfNotSpecializesIsTerminal
          x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1) hnot
        exact (isZero_zero AddCommGrpCat).of_iso
          (ht.uniqueUpToIso terminalIsTerminal ≪≫ HasZeroObject.zeroIsoTerminal.symm)
      exact isIso_of_source_target_iso_zero _ hF_y.isoZero hsky.isoZero
  have hIsoφ : IsIso φ := hφ
  have hSkyFlasque : TopCat.Sheaf.IsFlasque
      (skyscraperSheaf x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)) :=
    isFlasque_skyscraperSheaf_of_hasZeroObject x _
  exact TopCat.Sheaf.isFlasque_of_iso (asIso φ).symm

/-! ### Finite support induction -/

private theorem epi_of_stalk_epi {Y : TopCat.{u}}
    {F G : Y.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G)
    (hf : ∀ y : Y, Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map f.1)) :
    Epi f := by
  apply Preadditive.epi_of_isZero_cokernel f
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (C := AddCommGrpCat) (X := Y) (cokernel f)).mpr
  intro y
  let K := TopCat.Sheaf.forget AddCommGrpCat Y ⋙
    TopCat.Presheaf.stalkFunctor (X := Y) AddCommGrpCat y
  have hEpi : Epi (K.map f) := hf y
  let e := PreservesCokernel.iso K f
  apply IsZero.of_iso (isZero_cokernel_of_epi (K.map f))
  exact e

private theorem isZero_kernel_stalk_of_isIso_stalk
    {Y : TopCat.{u}} {F G : Y.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (y : Y)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map f.1) := by infer_instance) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj (kernel f).1) := by
  let K := TopCat.Sheaf.forget AddCommGrpCat Y ⋙
    TopCat.Presheaf.stalkFunctor (X := Y) AddCommGrpCat y
  have hIso : IsIso (K.map f) := hiso
  let e := PreservesKernel.iso K f
  have hz : IsZero (kernel (K.map f)) := isZero_kernel_of_mono (K.map f)
  exact IsZero.of_iso hz e

private theorem isZero_kernel_stalk_of_source_zero
    {Y : TopCat.{u}} {F G : Y.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) (y : Y)
    (hzero : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.1)) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj (kernel f).1) := by
  let K := TopCat.Sheaf.forget AddCommGrpCat Y ⋙
    TopCat.Presheaf.stalkFunctor (X := Y) AddCommGrpCat y
  apply IsZero.of_mono (K.map (kernel.ι f))
  exact hzero

private theorem isFlasque_of_shortExact_of_isFlasque₁₃ {Y : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y)}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁]
    [TopCat.Sheaf.IsFlasque S.X₃] : TopCat.Sheaf.IsFlasque S.X₂ where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨qU, hqU⟩ :=
      (AddCommGrpCat.epi_iff_surjective (S.X₃.obj.map i)).mp (inferInstance :
        Epi (S.X₃.obj.map i)) (S.g.hom.app V s)
    obtain ⟨tU, htU⟩ :=
      (AddCommGrpCat.epi_iff_surjective (S.g.hom.app U)).mp
        (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U.unop) hS) qU
    let dV := s - S.X₂.obj.map i tU
    have hdV : S.g.hom.app V dV = 0 := by
      dsimp [dV]
      rw [map_sub]
      change (S.g.hom.app V) s -
        ((S.X₂.obj.map i ≫ S.g.hom.app V) tU) = 0
      rw [S.g.hom.naturality i]
      simp only [ConcreteCategory.comp_apply, htU, hqU, sub_self]
    obtain ⟨kV, hkV⟩ := TopCat.Sheaf.sections_exact_of_left_exact hS.1 hS.2 dV hdV
    obtain ⟨kU, hkU⟩ :=
      (AddCommGrpCat.epi_iff_surjective (S.X₁.obj.map i)).mp (inferInstance :
        Epi (S.X₁.obj.map i)) kV
    refine ⟨tU + S.f.hom.app U kU, ?_⟩
    rw [map_add]
    have hf := congrArg (fun φ => φ kU) (S.f.hom.naturality i)
    have hf' : (S.f.hom.app V) ((S.X₁.obj.map i) kU) =
        (S.X₂.obj.map i) ((S.f.hom.app U) kU) := by
      simpa only [ConcreteCategory.comp_apply] using hf
    change (S.X₂.obj.map i) tU +
      (S.X₂.obj.map i) ((S.f.hom.app U) kU) = s
    rw [← hf', hkU, hkV]
    dsimp [dV]
    abel

/-- An abelian sheaf supported on finitely many closed points is flasque. -/
theorem isFlasque_of_finite_closed_support {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (s : Finset Y)
    (hs : ∀ x ∈ s, IsClosed ({x} : Set Y))
    (hF : ∀ y : Y, y ∉ s →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.1)) :
    TopCat.Sheaf.IsFlasque F := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
      have hzero : IsZero F :=
        (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero F).mpr (fun y ↦ hF y (by simp))
      have hInjective : Injective F := hzero.injective
      exact TopCat.Sheaf.isFlasque_of_injective Y F
  | @insert x s hx ih =>
      let u := stalkSkyscraperUnit F x
      let K := kernel u
      have hK : ∀ y : Y, y ∉ s →
          IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj K.1) := by
        intro y hy
        by_cases hxy : y = x
        · subst y
          exact isZero_kernel_stalk_of_isIso_stalk u x
            (hiso := stalkSkyscraperUnit_stalk_iso F x)
        · apply isZero_kernel_stalk_of_source_zero u y
          exact hF y (by simp [hy, hxy])
      have hs' : ∀ z ∈ s, IsClosed ({z} : Set Y) :=
        fun z hz ↦ hs z (by simp [hz])
      have hKfl : TopCat.Sheaf.IsFlasque K := ih K hs' hK
      have hKInstance : TopCat.Sheaf.IsFlasque K := hKfl
      have hSkyInstance : TopCat.Sheaf.IsFlasque
          (skyscraperSheaf x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)) :=
        isFlasque_skyscraperSheaf_of_hasZeroObject x _
      have hu_epi : Epi u := by
        apply epi_of_stalk_epi u
        intro y
        by_cases hxy : y = x
        · subst y
          change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((TopCat.Sheaf.forget AddCommGrpCat Y).map (stalkSkyscraperUnit F x)))
          have hIsoStalk : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((TopCat.Sheaf.forget AddCommGrpCat Y).map (stalkSkyscraperUnit F x))) :=
            stalkSkyscraperUnit_stalk_iso F x
          infer_instance
        · have hnot : ¬x ⤳ y := by
            intro h
            have hymem : y ∈ closure ({x} : Set Y) := specializes_iff_mem_closure.mp h
            rw [(hs x (by simp)).closure_eq] at hymem
            exact hxy hymem
          have hsky : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj
              (skyscraperSheaf x
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1)).1) := by
            have ht := skyscraperPresheafStalkOfNotSpecializesIsTerminal
              x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.1) hnot
            exact (isZero_zero AddCommGrpCat).of_iso
              (ht.uniqueUpToIso terminalIsTerminal ≪≫ HasZeroObject.zeroIsoTerminal.symm)
          exact hsky.epi _
      have hEpi : Epi u := hu_epi
      let S := ShortComplex.mk (kernel.ι u) u (kernel.condition u)
      have hS : S.ShortExact := ⟨ShortComplex.exact_kernel u⟩
      exact isFlasque_of_shortExact_of_isFlasque₁₃ hS

/-- Positive derived global sections vanish for a sheaf with finite closed support. -/
theorem isZero_rightDerived_sections_of_finite_closed_support {Y : TopCat.{u}}
    (F : Y.Sheaf AddCommGrpCat.{u}) (s : Finset Y)
    (hs : ∀ x ∈ s, IsClosed ({x} : Set Y))
    (hF : ∀ y : Y, y ∉ s →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).obj F.1)) (n : ℕ) :
    IsZero (((sections (⊤ : Opens Y)).rightDerived (n + 1)).obj F) := by
  have hFlasque : TopCat.Sheaf.IsFlasque F := isFlasque_of_finite_closed_support F s hs hF
  have hz := TopCat.Sheaf.isZero_rightDerived_pushforward_of_isFlasque
    (toPoint Y) F n
  have hg := Functor.map_isZero PointSheaves.globalSections.{u} hz
  exact IsZero.of_iso hg (derivedSectionsTopIso Y F (n + 1))

end GromovWitten.AlgebraicGeometry.SheafCohomology
