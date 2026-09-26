/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
/-!
# Flasque sheaves are acyclic for pushforward

Injective abelian sheaves are flasque: the free abelian sheaf represented by an open
represents sections, and an inclusion of opens induces a monomorphism between these
free sheaves. Injectivity therefore extends sections across every open inclusion.

For a flasque sheaf, the cycles of an injective resolution remain flasque. Pushforward
preserves the resulting short exact sequences, so the pushed-forward resolution is
exact in positive degree. Consequently all positive right derived pushforwards vanish.
-/

open CategoryTheory CategoryTheory.Functor Limits Opposite TopologicalSpace

universe u
noncomputable section
namespace TopCat.Sheaf
variable (X : TopCat.{u})

/-- The free abelian sheaf represented by an open subset. -/
def freeAbelianOpen : Opens X ⥤ Sheaf AddCommGrpCat.{u} X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf _ _

/-- Maps from the free sheaf represented by `U` are sections over `U`. -/
def freeAbelianOpenHomEquiv (U : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    ((freeAbelianOpen X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).comp
    (sheafificationAdjunction _ _)).homEquiv _ _).trans yonedaEquiv

instance freeAbelianOpen_map_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((freeAbelianOpen X).map i) := by
  change Mono ((presheafToSheaf _ _).map
    (whiskerRight (yoneda.map i) AddCommGrpCat.free))
  have : ∀ W, Mono ((whiskerRight (yoneda.map i) AddCommGrpCat.free).app W) := by
    intro W
    change Mono (AddCommGrpCat.free.map ((yoneda.map i).app W))
    infer_instance
  have : Mono (whiskerRight (yoneda.map i) AddCommGrpCat.free) :=
    NatTrans.mono_of_mono_app _
  infer_instance

lemma freeAbelianOpenHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (F : Sheaf AddCommGrpCat.{u} X) (a : (freeAbelianOpen X).obj V ⟶ F) :
    freeAbelianOpenHomEquiv X U F ((freeAbelianOpen X).map i ≫ a) =
      F.obj.map i.op (freeAbelianOpenHomEquiv X V F a) := by
  let adj := (AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let φ := (adj.homEquiv (yoneda.obj V) F) a
  exact (congrArg yonedaEquiv
    (adj.homEquiv_naturality_left (yoneda.map i) a)).trans
      (yonedaEquiv_naturality φ i).symm

/-- Injective abelian sheaves have surjective restriction maps. -/
instance isFlasque_of_injective (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    IsFlasque F where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    let a := (freeAbelianOpenHomEquiv X V.unop F).symm s
    let b := Injective.factorThru a ((freeAbelianOpen X).map i.unop)
    refine ⟨freeAbelianOpenHomEquiv X U.unop F b, ?_⟩
    calc
      F.obj.map i (freeAbelianOpenHomEquiv X U.unop F b) =
          freeAbelianOpenHomEquiv X V.unop F ((freeAbelianOpen X).map i.unop ≫ b) :=
        (freeAbelianOpenHomEquiv_naturality X i.unop F b).symm
      _ = s := by
        rw [Injective.comp_factorThru]
        exact (freeAbelianOpenHomEquiv X V.unop F).apply_symm_apply s

end TopCat.Sheaf

namespace CategoryTheory.InjectiveResolution
variable {C : Type*} [Category C] [Abelian C] {Z : C} (I : InjectiveResolution Z)

/-- The short sequence from consecutive cycles of an injective resolution. -/
def cycleSequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (I.cocomplex.iCycles n) (I.cocomplex.toCycles n (n + 1)) (by
    rw [← cancel_mono (I.cocomplex.iCycles (n + 1)), Category.assoc,
      HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp])

/-- Consecutive cycles form a short exact sequence with the resolution object. -/
lemma cycleSequence_shortExact (n : ℕ) : (I.cycleSequence n).ShortExact := by
  let K := I.cocomplex
  have hepi : Epi (K.toCycles n (n + 1)) := by
    rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' n (n + 1) (n + 2)
      (by simp) (by simp)).hom, HomologicalComplex.toCycles_cyclesIsoSc'_hom]
    exact (I.exact_succ n).epi_toCycles
  have : Mono (I.cycleSequence n).f := by
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

end CategoryTheory.InjectiveResolution

namespace TopCat.Sheaf
variable {X : TopCat.{u}}

lemma isFlasque_of_iso {F G : Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) [IsFlasque F] :
    IsFlasque G where
  epi {U V} i := by
    let e' := (sheafToPresheaf _ _).mapIso e
    have : Epi (F.obj.map i ≫ e'.hom.app V) := inferInstance
    exact epi_of_epi_fac
      (show e'.hom.app U ≫ G.obj.map i = F.obj.map i ≫ e'.hom.app V from
        (e'.hom.naturality i).symm)

/-- All cycles in an injective resolution of a flasque sheaf are flasque. -/
lemma injectiveResolution_cycles_isFlasque (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] (I : InjectiveResolution F) (n : ℕ) : IsFlasque (I.cocomplex.cycles n) := by
  induction n with
  | zero =>
    let e : F ≅ I.cocomplex.cycles 0 :=
      I.isLimitKernelFork.conePointUniqueUpToIso
        (I.cocomplex.cyclesIsKernel 0 1 (by simp))
    exact isFlasque_of_iso e
  | succ n ih =>
    have := ih
    have : IsFlasque (I.cycleSequence n).X₁ := ih
    have : IsFlasque (I.cycleSequence n).X₂ := isFlasque_of_injective X (I.cocomplex.X n)
    exact IsFlasque.of_shortExact_of_isFlasque₁₂ (I.cycleSequence_shortExact n)

end TopCat.Sheaf

namespace TopCat.Sheaf
variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Pushforward preserves the epimorphism in a short exact sequence with flasque kernel. -/
lemma epi_pushforward_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] : Epi ((pushforward AddCommGrpCat f).map S.g) := by
  have : ∀ U, Epi (((pushforward AddCommGrpCat f).map S.g).hom.app U) := by
    intro U
    change Epi (S.g.hom.app (op ((Opens.map f).obj U.unop)))
    exact IsFlasque.epi_of_shortExact hS
  have hepi : Epi ((pushforward AddCommGrpCat f).map S.g).hom :=
    NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat).epi_of_epi_map hepi

/-- A short exact sequence with flasque first term remains exact under pushforward. -/
lemma shortExact_pushforward_of_isFlasque
    [(pushforward AddCommGrpCat.{u} f).Additive]
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) [IsFlasque S.X₁] :
    (S.map (pushforward AddCommGrpCat f)).ShortExact := by
  have := hS.mono_f
  refine { exact := ?_, mono_f := ?_, epi_g := epi_pushforward_of_shortExact f hS }
  swap
  · change Mono ((pushforward AddCommGrpCat f).map S.f)
    infer_instance
  exact hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance

end TopCat.Sheaf

namespace CategoryTheory.ShortComplex
variable {C : Type*} [Category C] [Abelian C] {S : ShortComplex C}

/-- Precomposing the first map by an epimorphism preserves exactness. -/
lemma Exact.precomp_epi {A : C} (hS : S.Exact) (q : A ⟶ S.X₁) [Epi q] :
    (ShortComplex.mk (q ≫ S.f) S.g (by simp)).Exact := by
  let T := ShortComplex.mk (q ≫ S.f) S.g (by simp)
  let φ : T ⟶ S := { τ₁ := q, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  exact (exact_iff_of_epi_of_isIso_of_mono φ).mpr hS

/-- Postcomposing the second map by a monomorphism preserves exactness. -/
lemma Exact.postcomp_mono {A : C} (hS : S.Exact) (j : S.X₃ ⟶ A) [Mono j] :
    (ShortComplex.mk S.f (S.g ≫ j) (by simp)).Exact := by
  let T := ShortComplex.mk S.f (S.g ≫ j) (by simp)
  let φ : S ⟶ T := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := j }
  exact (exact_iff_of_epi_of_isIso_of_mono φ).mp hS

end CategoryTheory.ShortComplex

namespace TopCat.Sheaf
variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]

/-- Pushforward of an injective resolution of a flasque sheaf is exact in positive degree. -/
lemma pushforward_injectiveResolution_exactAt_succ (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] (I : InjectiveResolution F) (n : ℕ) :
    ((pushforward AddCommGrpCat f).mapHomologicalComplex (ComplexShape.up ℕ) |>.obj
      I.cocomplex).ExactAt (n + 1) := by
  let P := pushforward AddCommGrpCat.{u} f
  let K := I.cocomplex
  have hc (k : ℕ) : IsFlasque (I.cycleSequence k).X₁ :=
    injectiveResolution_cycles_isFlasque F I k
  have hepi : Epi (P.map (K.toCycles n (n + 1))) :=
    epi_pushforward_of_shortExact f (I.cycleSequence_shortExact n)
  have hmono : Mono (P.map (K.iCycles (n + 2))) := inferInstance
  have hs := shortExact_pushforward_of_isFlasque f (I.cycleSequence_shortExact (n + 1))
  have ht := @ShortComplex.Exact.precomp_epi _ _ _ _ _ hs.exact
    (P.map (K.toCycles n (n + 1))) hepi
  have ht' := @ShortComplex.Exact.postcomp_mono _ _ _ _ _ ht
    (P.map (K.iCycles (n + 2))) hmono
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk (P.map (K.d n (n + 1)))
    (P.map (K.d (n + 1) (n + 2))) _).Exact
  change (ShortComplex.mk
    (P.map (K.toCycles n (n + 1)) ≫ P.map (K.iCycles (n + 1)))
    (P.map (K.toCycles (n + 1) (n + 2)) ≫ P.map (K.iCycles (n + 2))) _).Exact at ht'
  simpa only [← P.map_comp, HomologicalComplex.toCycles_i] using ht'

end TopCat.Sheaf

namespace TopCat.Sheaf
variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]
variable [EnoughInjectives (Sheaf AddCommGrpCat.{u} X)]

/-- Flasque abelian sheaves are acyclic for pushforward along any continuous map. -/
lemma isZero_rightDerived_pushforward_of_isFlasque (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] (n : ℕ) :
    IsZero (((pushforward AddCommGrpCat f).rightDerived (n + 1)).obj F) := by
  let I := InjectiveResolution.of F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (pushforward AddCommGrpCat f) (n + 1))
  exact (pushforward_injectiveResolution_exactAt_succ f F I n).isZero_homology

end TopCat.Sheaf

end
