/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global functions on proper fibres

The first geometric input for the structure morphism of a prestable family is the usual
proper-global-functions statement.  This file records the integral-fibre case in a form that can
be used directly on a geometric fibre.  The proof is entirely geometric: properness makes the
map on global sections integral, and algebraic closedness then makes that map bijective.

The connected reduced extension below uses only finite simple subalgebras of the global section
ring, so it applies to reducible fibres as well and does not strengthen prestability to
irreducibility.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X : Scheme.{u}}

/-- The map from the ground field to global functions on an integral universally closed fibre is
bijective.  The map is written through `ΓSpecIso` so its source is literally `K`, rather than the
canonically isomorphic ring `Γ(Spec K, ⊤)`.

Only universal closedness is used here; properness supplies it through the usual instance. -/
theorem globalSections_scalar_bijective_of_integral
    (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f] :
    Function.Bijective (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) := by
  let hbase : ((Scheme.ΓSpecIso (.of K)).inv.hom).IsIntegral := by
    apply RingHom.isIntegral_of_surjective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2
  apply IsAlgClosed.ringHom_bijective_of_isIntegral _
  exact RingHom.IsIntegral.trans _ _ hbase (isIntegral_appTop_of_universallyClosed f)

/-- A reduced connected scheme has no non-trivial idempotent global functions.

The proof pulls the basic open of an idempotent back from `Spec Γ(X, ⊤)`.  The corresponding
basic open is clopen because an idempotent and its complement multiply to zero and add to one;
connectedness makes it empty or the whole space, and reducedness identifies a section whose basic
open is empty with zero. -/
theorem global_idempotent_eq_zero_or_one {X : Scheme.{u}} [IsReduced X]
    [ConnectedSpace X] (e : Γ(X, ⊤)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hclopen : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum Γ(X, ⊤))) :=
    PrimeSpectrum.isClopen_basicOpen_of_mul_add e (1 - e)
      (by simp [mul_sub, he.eq]) (by simp)
  have hclopenX : IsClopen (X.basicOpen e : Set X) := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen X e]
    exact hclopen.preimage X.toSpecΓ.continuous
  rcases isClopen_iff.mp hclopenX with hempty | huniv
  · left
    apply eq_zero_of_basicOpen_eq_bot e
    apply TopologicalSpace.Opens.ext
    exact hempty
  · right
    have htop : X.basicOpen e = ⊤ := by
      apply TopologicalSpace.Opens.ext
      exact huniv
    have hcomp : X.basicOpen (1 - e) = ⊥ := by
      have hmul : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
        rw [← X.basicOpen_mul]
        simp [mul_sub, he.eq]
      simpa only [htop, top_inf_eq] using hmul
    have hzero : 1 - e = 0 := eq_zero_of_basicOpen_eq_bot (1 - e) hcomp
    exact (sub_eq_zero.mp hzero).symm

lemma subsingleton_of_connected_finite_t1 {α : Type*} [TopologicalSpace α]
    [Finite α] [T1Space α] (hconn : ConnectedSpace α) : Subsingleton α := by
  constructor
  intro x y
  have hdisc : DiscreteTopology α := Finite.instDiscreteTopology
  have hc : IsClopen ({x} : Set α) :=
    ⟨@isClosed_discrete _ _ hdisc _, @isOpen_discrete _ _ hdisc _⟩
  have hu : ({x} : Set α) = Set.univ :=
    @IsClopen.eq_univ α _ hconn.toPreconnectedSpace _ hc ⟨x, rfl⟩
  have hy : y ∈ ({x} : Set α) := hu ▸ Set.mem_univ y
  exact Set.mem_singleton_iff.mp hy |>.symm

lemma connectedSpace_of_trivial_idempotents {R : Type u} [CommRing R]
    [Nontrivial R]
    (htriv : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    ConnectedSpace (PrimeSpectrum R) := by
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases htriv e he with rfl | rfl <;> simp

theorem scalar_bijective_of_trivial_idempotents
    {K A : Type u} [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Nontrivial A] [IsReduced A]
    [Algebra.IsIntegral K A]
    (htriv : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (algebraMap K A) := by
  have hsurj : Function.Surjective (algebraMap K A) := by
    intro x
    let B : Subalgebra K A := Algebra.adjoin K ({x} : Set A)
    let _ : Module.Finite K B :=
      Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
    let _ : IsArtinianRing B := IsArtinianRing.of_finite K B
    let _ : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
    let _ : T1Space (PrimeSpectrum B) :=
      ⟨fun p => (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2
        (IsArtinianRing.isMaximal_of_isPrime p.asIdeal)⟩
    have htrivB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := by
      intro e he
      rcases htriv e.1 (he.map B.val) with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
    have hconn : ConnectedSpace (PrimeSpectrum B) :=
      connectedSpace_of_trivial_idempotents htrivB
    have hsub : Subsingleton (PrimeSpectrum B) :=
      subsingleton_of_connected_finite_t1 hconn
    have hfield : IsField B :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hsub
    let _ : IsDomain B := hfield.isDomain
    have hbijection : Function.Bijective (algebraMap K B) :=
      IsAlgClosed.ringHom_bijective_of_isIntegral (algebraMap K B)
        (algebraMap_isIntegral_iff.mpr inferInstance)
    obtain ⟨k, hk⟩ := hbijection.2 ⟨x, Algebra.subset_adjoin (by simp)⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg (fun z : B => (B.val z : A)) hk
    simpa using hk'
  refine ⟨RingHom.injective (algebraMap K A), hsurj⟩

/-- Global functions on a connected reduced universally closed fibre over an algebraically closed
field are scalars.  The finite-adjoin argument applies to each individual section, so no
irreducibility assumption is needed. -/
theorem globalSections_scalar_bijective_of_reduced_connected
    (f : X ⟶ Spec (.of K)) [IsReduced X] [ConnectedSpace X]
    [UniversallyClosed f] :
    Function.Bijective (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom) := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  let g : K →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom
  let _ : Algebra K Γ(X, ⊤) := RingHom.toAlgebra g
  have hAint : Algebra.IsIntegral K Γ(X, ⊤) := by
    apply algebraMap_isIntegral_iff.mp
    change g.IsIntegral
    let hbase : ((Scheme.ΓSpecIso (.of K)).inv.hom).IsIntegral := by
      apply RingHom.isIntegral_of_surjective
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2
    exact RingHom.IsIntegral.trans _ _ hbase (isIntegral_appTop_of_universallyClosed f)
  have htriv : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    exact global_idempotent_eq_zero_or_one e he
  exact scalar_bijective_of_trivial_idempotents htriv

/-! ## The structure sheaf map and its geometric-fibre specialization -/

/-- The canonical map exists for every scheme morphism.  The later isomorphism theorem is
  specialized to geometric fibres over `Spec K`. -/
def structureSheafMap {Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.unit.{u, u, u} Y.ringCatSheaf : Y.Modules) ⟶
      (Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit.{u, u, u} X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp]
lemma structureSheafMap_val_app_apply {Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (a : (Y.ringCatSheaf.obj.obj (.op U))) :
    (structureSheafMap f).val.app (.op U) a = f.toRingCatSheafHom.hom.app (.op U) a := by
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply _ _

lemma subsingleton_module_sections_of_subsingleton {Y : Scheme.{u}} (M : Y.Modules)
    [Subsingleton Γ(Y, (⊥ : Y.Opens))] : Subsingleton Γ(M, (⊥ : Y.Opens)) := by
  constructor
  intro x y
  calc
    x = (1 : Γ(Y, (⊥ : Y.Opens))) • x := by rw [one_smul]
    _ = (0 : Γ(Y, (⊥ : Y.Opens))) • x := by
      rw [Subsingleton.elim (1 : Γ(Y, (⊥ : Y.Opens))) 0]
    _ = 0 := zero_smul _ _
    _ = (0 : Γ(Y, (⊥ : Y.Opens))) • y := (zero_smul _ _).symm
    _ = (1 : Γ(Y, (⊥ : Y.Opens))) • y := by
      rw [Subsingleton.elim (1 : Γ(Y, (⊥ : Y.Opens))) 0]
    _ = y := one_smul _ _

lemma structureSheafMap_appTop_bijective (f : X ⟶ Spec (.of K))
    [IsReduced X] [ConnectedSpace X] [UniversallyClosed f] :
    Function.Bijective ((Scheme.Modules.Hom.app (structureSheafMap f) ⊤)) := by
  have hglobal := globalSections_scalar_bijective_of_reduced_connected f
  have hbase : Function.Bijective
      ((Scheme.ΓSpecIso (.of K)).inv.hom : K → Γ(Spec (.of K), ⊤)) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)
  have htop : Function.Bijective f.appTop.hom := by
    apply (Function.Bijective.of_comp_iff f.appTop.hom hbase).mp
    exact hglobal
  change Function.Bijective f.appTop.hom
  exact htop

/-- For a reduced connected universally closed scheme over an algebraically closed field, the
canonical structure-sheaf map over `Spec K` is an isomorphism.  The proof checks every component:
the only opens of `Spec K` are the empty open and the whole space, with the latter component the
global-functions map proved above. -/
theorem structureSheafMap_isIso (f : X ⟶ Spec (.of K))
    [IsReduced X] [ConnectedSpace X] [UniversallyClosed f] :
    @IsIso (Spec (.of K)).Modules
      (Scheme.Modules.instCategory)
      _ _ (structureSheafMap f) := by
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).2
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain rfl | rfl := TopologicalSpace.Opens.eq_bot_or_top U
  · let _ : Subsingleton Γ((SheafOfModules.unit (Spec (.of K)).ringCatSheaf),
        (⊥ : (Spec (.of K)).Opens)) :=
      subsingleton_module_sections_of_subsingleton _
    let _ : Subsingleton Γ(((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)), (⊥ : (Spec (.of K)).Opens)) :=
      subsingleton_module_sections_of_subsingleton _
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact structureSheafMap_appTop_bijective f

theorem geometricFiber_structureSheafMap_isIso
    {S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [GeometricallyReduced f] [GeometricallyConnected f]
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ S) :
    @IsIso (Spec (.of K)).Modules
      (Scheme.Modules.instCategory)
      _ _ (structureSheafMap (CategoryTheory.Limits.pullback.snd f y)) := by
  let _ : IsReduced (CategoryTheory.Limits.pullback f y : Scheme.{u}) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (IsPullback.of_hasPullback f y)
  let _ : ConnectedSpace (CategoryTheory.Limits.pullback f y : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace y
      (CategoryTheory.Limits.pullback.fst f y)
      (CategoryTheory.Limits.pullback.snd f y) (IsPullback.of_hasPullback f y)
  exact structureSheafMap_isIso (CategoryTheory.Limits.pullback.snd f y)

end
end GromovWitten.AlgebraicGeometry.Curves
