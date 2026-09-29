/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.Flasque
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
/-!
# Pushforward of bounded-below flasque complexes

An exact bounded-below complex of flasque sheaves has flasque cycles, starting from
the zero cycles below its lower bound. Pushforward preserves its cycle short exact
sequences and therefore its exactness. Applying this to mapping cones shows that
pushforward preserves quasi-isomorphisms between bounded-below flasque complexes.
This is the comparison principle needed to compute derived pushforwards using
flasque resolutions.
-/

open CategoryTheory Limits Opposite TopologicalSpace
universe u
noncomputable section
namespace TopCat.Sheaf
variable {X : TopCat.{u}}
/-- Zero abelian sheaves are flasque. -/
lemma isFlasque_of_isZero (F : Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) :
    IsFlasque F where
  epi {U V} i := by
    have hz (W : (Opens X)ᵒᵖ) : IsZero (F.obj.obj W) :=
      ((sheafToPresheaf _ _).comp ((CategoryTheory.evaluation _ _).obj W)).map_isZero hF
    have := (hz U).isIso (hz V) (F.obj.map i)
    infer_instance
end TopCat.Sheaf

namespace CochainComplex
variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ)
/-- The short sequence from consecutive cycles of an integer-indexed cochain complex. -/
def cycleSequence (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc,
      HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])

/-- The cycle sequence is short exact when the complex is exact at its final degree. -/
lemma cycleSequence_shortExact (n : ℤ) (hK : K.ExactAt (n + 1)) :
    (K.cycleSequence n).ShortExact := by
  have hepi : Epi (K.toCycles n (n + 1)) := by
    rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' n (n + 1) (n + 2)
      (by simp) (by simp; omega)).hom, HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp; omega)] at hK
    exact hK.epi_toCycles
  have : Mono (K.cycleSequence n).f := by
    change Mono (K.iCycles n)
    infer_instance
  refine { exact := ?_, mono_f := inferInstance, epi_g := hepi }
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  change A ⟶ K.X n at k
  change k ≫ K.toCycles n (n + 1) = 0 at hk
  have hk' : k ≫ K.d n (n + 1) = 0 := by
    calc
      k ≫ K.d n (n + 1) = (k ≫ K.toCycles n (n + 1)) ≫ K.iCycles (n + 1) := by
        rw [Category.assoc, K.toCycles_i]
      _ = 0 := by rw [hk, zero_comp]
  exact ⟨K.liftCycles k (n + 1) (by simp) hk',
    K.liftCycles_i k (n + 1) (by simp) hk'⟩
end CochainComplex

namespace TopCat.Sheaf
variable {X : TopCat.{u}} (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- All cycles of an exact bounded-below complex of flasque sheaves are flasque. -/
lemma acyclic_cycles_isFlasque (hK : K.Acyclic) (hF : ∀ n, IsFlasque (K.X n))
    (a : ℤ) [K.IsStrictlyGE a] (n : ℤ) : IsFlasque (K.cycles n) := by
  by_cases hn : n < a
  · exact isFlasque_of_isZero _ (IsZero.of_mono (K.iCycles n)
      (K.isZero_of_isStrictlyGE a n hn))
  have hn' : a - 1 ≤ n := by omega
  clear hn
  induction n, hn' using Int.leInduction with
  | base =>
    exact isFlasque_of_isZero _ (IsZero.of_mono (K.iCycles (a - 1))
      (K.isZero_of_isStrictlyGE a (a - 1) (by omega)))
  | succ n hn ih =>
    have : IsFlasque (K.cycleSequence n).X₁ := ih
    have : IsFlasque (K.cycleSequence n).X₂ := hF n
    exact IsFlasque.of_shortExact_of_isFlasque₁₂ (K.cycleSequence_shortExact n (hK _))

variable {Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]
/-- Pushforward preserves exactness of bounded-below complexes of flasque sheaves. -/
lemma pushforward_acyclic_of_boundedBelow_flasque (hK : K.Acyclic)
    (hF : ∀ n, IsFlasque (K.X n)) (a : ℤ) [K.IsStrictlyGE a] :
    ((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℤ) |>.obj K).Acyclic := by
  intro m
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by omega⟩
  let P := pushforward AddCommGrpCat.{u} f
  have hc (k : ℤ) : IsFlasque (K.cycleSequence k).X₁ :=
    acyclic_cycles_isFlasque K hK hF a k
  have hepi : Epi (P.map (K.toCycles n (n + 1))) :=
    epi_pushforward_of_shortExact f (K.cycleSequence_shortExact n (hK _))
  have hmono : Mono (P.map (K.iCycles (n + 1 + 1))) := inferInstance
  have hs := shortExact_pushforward_of_isFlasque f (K.cycleSequence_shortExact (n + 1) (hK _))
  have ht := @ShortComplex.Exact.precomp_epi _ _ _ _ _ hs.exact
    (P.map (K.toCycles n (n + 1))) hepi
  have ht' := @ShortComplex.Exact.postcomp_mono _ _ _ _ _ ht
    (P.map (K.iCycles (n + 1 + 1))) hmono
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  change (ShortComplex.mk (P.map (K.d n (n + 1))) (P.map (K.d (n + 1) (n + 1 + 1))) _).Exact
  change (ShortComplex.mk
    (P.map (K.toCycles n (n + 1)) ≫ P.map (K.iCycles (n + 1)))
    (P.map (K.toCycles (n + 1) (n + 1 + 1)) ≫ P.map (K.iCycles (n + 1 + 1))) _).Exact at ht'
  simpa only [← P.map_comp, HomologicalComplex.toCycles_i] using ht'

end TopCat.Sheaf

namespace TopCat.Sheaf
variable {X : TopCat.{u}}
/-- The direct sum of two flasque abelian sheaves is flasque. -/
lemma isFlasque_biprod (F G : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] [IsFlasque G] :
    IsFlasque (F ⊞ G) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective (F.obj.map i)).mp
      inferInstance ((biprod.fst : F ⊞ G ⟶ F).hom.app V s)
    obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective (G.obj.map i)).mp
      inferInstance ((biprod.snd : F ⊞ G ⟶ G).hom.app V s)
    refine ⟨(biprod.inl : F ⟶ F ⊞ G).hom.app U a +
      (biprod.inr : G ⟶ F ⊞ G).hom.app U b, ?_⟩
    rw [map_add]
    have hinl := ConcreteCategory.congr_hom ((biprod.inl : F ⟶ F ⊞ G).hom.naturality i) a
    have hinr := ConcreteCategory.congr_hom ((biprod.inr : G ⟶ F ⊞ G).hom.naturality i) b
    change (biprod.inl : F ⟶ F ⊞ G).hom.app V (F.obj.map i a) = _ at hinl
    change (biprod.inr : G ⟶ F ⊞ G).hom.app V (G.obj.map i b) = _ at hinr
    calc
      _ = (biprod.inl : F ⟶ F ⊞ G).hom.app V (F.obj.map i a) +
          (biprod.inr : G ⟶ F ⊞ G).hom.app V (G.obj.map i b) :=
        congrArg₂ (· + ·) hinl.symm hinr.symm
      _ = (biprod.inl : F ⟶ F ⊞ G).hom.app V
            ((biprod.fst : F ⊞ G ⟶ F).hom.app V s) +
          (biprod.inr : G ⟶ F ⊞ G).hom.app V
            ((biprod.snd : F ⊞ G ⟶ G).hom.app V s) :=
        congrArg₂ (· + ·) (congrArg _ ha) (congrArg _ hb)
      _ = s := congrArg (fun t : F ⊞ G ⟶ F ⊞ G => t.hom.app V s)
        (biprod.total (X := F) (Y := G))
end TopCat.Sheaf

namespace CochainComplex
variable {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ}
/-- A map of cochain complexes is a quasi-isomorphism exactly when its cone is exact. -/
lemma quasiIso_iff_mappingCone_acyclic (φ : K ⟶ L) :
    QuasiIso φ ↔ (mappingCone φ).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic (mappingCone φ))
end CochainComplex

namespace TopCat.Sheaf
variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]
open CochainComplex HomologicalComplex
lemma pushforward_quasiIso_of_boundedBelow_flasque
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, IsFlasque (K.X n)) (hL : ∀ n, IsFlasque (L.X n))
    (a b : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE b] :
    QuasiIso (((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℤ)).map φ) := by
  let P := pushforward AddCommGrpCat.{u} f
  have hcone : (mappingCone φ).Acyclic := (quasiIso_iff_mappingCone_acyclic φ).mp inferInstance
  have hflasque (n : ℤ) : IsFlasque ((mappingCone φ).X n) := by
    have := hK (n + 1)
    have := hL n
    have := isFlasque_biprod (K.X (n + 1)) (L.X n)
    exact isFlasque_of_iso (homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm
  have : (mappingCone φ).IsStrictlyGE (min (a - 1) b) :=
    isStrictlyGE_mappingCone φ a b _ (by omega) (by omega)
  have hp := pushforward_acyclic_of_boundedBelow_flasque (mappingCone φ) f hcone hflasque
    (min (a - 1) b)
  apply (quasiIso_iff_mappingCone_acyclic _).mpr
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (mappingCone.mapHomologicalComplexIso φ P).hom n).mp (hp n)
end TopCat.Sheaf

end
