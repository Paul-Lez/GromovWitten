/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Conductors and the normalization conductor sequence

For a ring map `f : A →+* B`, the conductor is the largest ideal of `B` contained in the
range of `f`.  This file constructs that ideal, its pullback to `A`, the induced map on the two
conductor quotients, and the standard exact sequence

`0 → A → B × A/I → B/J → 0`.

The construction applies in particular to the map from a domain to its integral closure.  No
finiteness or Noetherian hypothesis is needed for the algebraic exactness statement.

For affine schemes in one universe, the sequence is also bundled as a short complex of
structure-sheaf modules.  Exactness follows from the general theorem proved here that the affine
tilde functor preserves short exact sequences.
-/

namespace GromovWitten.AlgebraicGeometry

universe u v

noncomputable section

namespace RingHomConductor

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The largest ideal of the target contained in the range of a ring map.  Equivalently, these
are the target elements whose product with every target element comes from the source. -/
def conductor (f : A →+* B) : Ideal B where
  carrier := {b | ∀ c : B, b * c ∈ Set.range f}
  zero_mem' := by
    intro c
    exact ⟨0, by simp⟩
  add_mem' := by
    intro b d hb hd c
    obtain ⟨a, ha⟩ := hb c
    obtain ⟨a', ha'⟩ := hd c
    exact ⟨a + a', by simp only [map_add, ha, ha', add_mul]⟩
  smul_mem' := by
    intro b d hd c
    obtain ⟨a, ha⟩ := hd (b * c)
    refine ⟨a, ha.trans ?_⟩
    simp only [smul_eq_mul]
    ring

theorem mem_conductor_iff (f : A →+* B) (b : B) :
    b ∈ conductor f ↔ ∀ c : B, b * c ∈ Set.range f :=
  Iff.rfl

/-- Every conductor element lies in the image of the source. -/
theorem conductor_le_range (f : A →+* B) :
    (conductor f : Set B) ⊆ Set.range f := by
  intro b hb
  obtain ⟨a, ha⟩ := hb 1
  exact ⟨a, by simpa using ha⟩

/-- The conductor is the largest target ideal contained in the image of the source. -/
theorem ideal_le_conductor_iff (f : A →+* B) (J : Ideal B) :
    J ≤ conductor f ↔ (J : Set B) ⊆ Set.range f := by
  constructor
  · intro h
    exact Set.Subset.trans h (conductor_le_range f)
  · intro h b hb c
    exact h (J.mul_mem_right c hb)

/-- The source conductor ideal, obtained by pulling back the target conductor. -/
def sourceConductor (f : A →+* B) : Ideal A :=
  (conductor f).comap f

@[simp] theorem mem_sourceConductor_iff (f : A →+* B) (a : A) :
    a ∈ sourceConductor f ↔ f a ∈ conductor f :=
  Iff.rfl

/-- The map between the source and target conductor quotients. -/
def quotientMap (f : A →+* B) :
    A ⧸ sourceConductor f →+* B ⧸ conductor f :=
  Ideal.Quotient.lift (sourceConductor f)
    ((Ideal.Quotient.mk (conductor f)).comp f) (by
      intro a ha
      change f a ∈ conductor f at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha)

@[simp] theorem quotientMap_mk (f : A →+* B) (a : A) :
    quotientMap f (Ideal.Quotient.mk (sourceConductor f) a) =
      Ideal.Quotient.mk (conductor f) (f a) := by
  rfl

/-- The diagonal map in the conductor sequence. -/
def diagonal (f : A →+* B) : A →+ B × (A ⧸ sourceConductor f) where
  toFun a := (f a, Ideal.Quotient.mk (sourceConductor f) a)
  map_zero' := by simp
  map_add' := by simp

@[simp] theorem diagonal_apply (f : A →+* B) (a : A) :
    diagonal f a = (f a, Ideal.Quotient.mk (sourceConductor f) a) :=
  rfl

/-- The difference map in the conductor sequence. -/
def difference (f : A →+* B) : B × (A ⧸ sourceConductor f) →+
    B ⧸ conductor f where
  toFun z := Ideal.Quotient.mk (conductor f) z.1 - quotientMap f z.2
  map_zero' := by simp
  map_add' := by
    intro x y
    simp only [map_add, Prod.fst_add, Prod.snd_add]
    abel

@[simp] theorem difference_apply (f : A →+* B)
    (z : B × (A ⧸ sourceConductor f)) :
    difference f z = Ideal.Quotient.mk (conductor f) z.1 - quotientMap f z.2 :=
  rfl

/-- Exactness at the middle term of the normalization conductor sequence. -/
theorem exact_diagonal_difference (f : A →+* B) :
    Function.Exact (diagonal f) (difference f) := by
  intro z
  constructor
  · intro hz
    rcases z with ⟨b, z⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (conductor f) b -
        Ideal.Quotient.mk (conductor f) (f a) = 0 at hz
    rw [← map_sub] at hz
    have hz' : b - f a ∈ conductor f :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨c, hc⟩ := conductor_le_range f hz'
    refine ⟨a + c, ?_⟩
    apply Prod.ext
    · change f (a + c) = b
      rw [map_add, hc]
      abel
    · change Ideal.Quotient.mk (sourceConductor f) (a + c) =
        Ideal.Quotient.mk (sourceConductor f) a
      rw [Ideal.Quotient.eq]
      have hc' : c ∈ sourceConductor f := by
        change f c ∈ conductor f
        rw [hc]
        exact hz'
      simpa only [add_sub_cancel_left] using hc'
  · rintro ⟨a, rfl⟩
    simp [diagonal, difference]

/-- The right-hand map of the conductor sequence is surjective. -/
theorem difference_surjective (f : A →+* B) :
    Function.Surjective (difference f) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨(b, 0), by simp [difference]⟩

/-- If the original ring map is injective, so is the left-hand map of the conductor
sequence. -/
theorem diagonal_injective (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (diagonal f) := by
  intro a b h
  exact hf (congrArg Prod.fst h)

/-- The full short-exactness package for an injective ring map. -/
theorem shortExact (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (diagonal f) ∧
      Function.Exact (diagonal f) (difference f) ∧
        Function.Surjective (difference f) :=
  ⟨diagonal_injective f hf, exact_diagonal_difference f, difference_surjective f⟩

section AffineSheafification

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The diagonal conductor map, regarded as a linear map over the source ring. -/
def diagonalLinear : A →ₗ[A] B × (A ⧸ sourceConductor (algebraMap A B)) where
  __ := diagonal (algebraMap A B)
  map_smul' a x := by
    simp [diagonal, Algebra.smul_def]

/-- The difference conductor map, regarded as a linear map over the source ring. -/
def differenceLinear :
    B × (A ⧸ sourceConductor (algebraMap A B)) →ₗ[A]
      B ⧸ conductor (algebraMap A B) where
  __ := difference (algebraMap A B)
  map_smul' a z := by
    obtain ⟨b, z⟩ := z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp [difference, quotientMap, Algebra.smul_def, mul_sub]

@[simp] theorem diagonalLinear_apply (a : A) :
    diagonalLinear (A := A) (B := B) a =
      (algebraMap A B a, Ideal.Quotient.mk (sourceConductor (algebraMap A B)) a) :=
  rfl

@[simp] theorem differenceLinear_apply
    (z : B × (A ⧸ sourceConductor (algebraMap A B))) :
    differenceLinear (A := A) (B := B) z =
      Ideal.Quotient.mk (conductor (algebraMap A B)) z.1 -
        quotientMap (algebraMap A B) z.2 :=
  rfl

/-- The conductor sequence as a short complex of modules over the source ring. -/
def moduleComplex : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk (diagonalLinear (A := A) (B := B))
    (differenceLinear (A := A) (B := B)) (by
      apply LinearMap.ext
      intro a
      simp)

/-- Exactness of the conductor complex at its middle term. -/
theorem moduleComplex_exact : (moduleComplex (A := A) (B := B)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_diagonal_difference (algebraMap A B)

/-- The module-valued conductor complex is short exact for an injective algebra map. -/
theorem moduleComplex_shortExact (h : Function.Injective (algebraMap A B)) :
    (moduleComplex (A := A) (B := B)).ShortExact := by
  apply ShortComplex.ShortExact.mk' (moduleComplex_exact (A := A) (B := B))
  · rw [ModuleCat.mono_iff_injective]
    exact diagonal_injective (algebraMap A B) h
  · rw [ModuleCat.epi_iff_surjective]
    exact difference_surjective (algebraMap A B)

section TildeExact

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

set_option linter.style.haveILetI false in
/-- An injective linear map induces an injective map on the locally-fraction sections used to
construct its associated tilde sheaf. -/
theorem structureSheaf_comapₗ_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (U : TopologicalSpace.Opens (PrimeSpectrum.Top R)) :
    Function.Injective (StructureSheaf.comapₗ f U U .rfl) := by
  intro s t h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun y ↦ y.1 x) h
  dsimp only [StructureSheaf.comapₗ, StructureSheaf.comapFun] at hx
  letI : x.1.asIdeal.IsPrime := x.1.2
  let p : PrimeSpectrum R := x.1
  have hcf : Function.Injective (StructureSheaf.Localizations.comapFun f p) := by
    intro z w hzw
    obtain ⟨⟨m, d⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      (p.comap (RingHom.id R)).asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M) z
    obtain ⟨⟨n, e⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
      (p.comap (RingHom.id R)).asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M) w
    apply IsLocalizedModule.map_injective
      (p.comap (RingHom.id R)).asIdeal.primeCompl
      (LocalizedModule.mkLinearMap
        (p.comap (RingHom.id R)).asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap
        (p.comap (RingHom.id R)).asIdeal.primeCompl N) f hf
    change StructureSheaf.Localizations.comapFun f p
        (IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap
            (p.comap (RingHom.id R)).asIdeal.primeCompl M) m d) =
      StructureSheaf.Localizations.comapFun f p
        (IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap
            (p.comap (RingHom.id R)).asIdeal.primeCompl M) n e) at hzw
    rw [← IsLocalizedModule.mk_eq_mk', ← IsLocalizedModule.mk_eq_mk',
      StructureSheaf.Localizations.comapFun_mk,
      StructureSheaf.Localizations.comapFun_mk] at hzw
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk'] at hzw
    change IsLocalizedModule.map (p.comap (RingHom.id R)).asIdeal.primeCompl
        (LocalizedModule.mkLinearMap (p.comap (RingHom.id R)).asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap (p.comap (RingHom.id R)).asIdeal.primeCompl N) f
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap
              (p.comap (RingHom.id R)).asIdeal.primeCompl M) m d) =
      IsLocalizedModule.map (p.comap (RingHom.id R)).asIdeal.primeCompl
        (LocalizedModule.mkLinearMap (p.comap (RingHom.id R)).asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap (p.comap (RingHom.id R)).asIdeal.primeCompl N) f
          (IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap
              (p.comap (RingHom.id R)).asIdeal.primeCompl M) n e)
    rw [IsLocalizedModule.map_mk', IsLocalizedModule.map_mk']
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at hzw ⊢
    simp only [PrimeSpectrum.comap_id, RingHom.id_apply] at hzw
    let a := hzw.choose
    let aq : (p.comap (RingHom.id R)).asIdeal.primeCompl :=
      ⟨a.1, by simpa only [PrimeSpectrum.comap_id] using a.2⟩
    refine ⟨aq, ?_⟩
    change aq.1 • d.1 • f n = aq.1 • e.1 • f m
    simpa only [aq, a, Submonoid.smul_def] using hzw.choose_spec
  exact hcf hx

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Tilde sends an injective linear map to a monomorphism of structure-sheaf modules. -/
theorem tilde_map_mono_of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Mono (tilde.map (R := CommRingCat.of R) (ModuleCat.ofHom (R := R) f)) := by
  letI : (modulesSpecToSheaf (R := CommRingCat.of R)).Faithful :=
    (SpecModulesToSheafFullyFaithful (R := CommRingCat.of R)).faithful
  letI : (modulesSpecToSheaf (R := CommRingCat.of R)).ReflectsMonomorphisms :=
    Functor.reflectsMonomorphisms_of_faithful _
  apply (modulesSpecToSheaf (R := CommRingCat.of R)).mono_of_mono_map
  constructor
  intro Z g h e
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  haveI : Mono (ModuleCat.ofHom (R := R)
      (StructureSheaf.comapₗ f U.unop U.unop .rfl)) := by
    rw [ModuleCat.mono_iff_injective]
    exact structureSheaf_comapₗ_injective f hf U.unop
  haveI : Mono
      (((modulesSpecToSheaf (R := CommRingCat.of R)).map
        (tilde.map (R := CommRingCat.of R) (ModuleCat.ofHom (R := R) f))).hom.app U) := by
    change Mono ((tilde.modulesSpecToSheafIso (ModuleCat.of R M)).hom.app U ≫
      ModuleCat.ofHom (R := R)
        (StructureSheaf.comapₗ f U.unop U.unop .rfl) ≫
      (tilde.modulesSpecToSheafIso (ModuleCat.of R N)).inv.app U)
    infer_instance
  apply (cancel_mono
    (((modulesSpecToSheaf (R := CommRingCat.of R)).map
      (tilde.map (R := CommRingCat.of R) (ModuleCat.ofHom (R := R) f))).hom.app U)).1
  have eU := congrArg (fun k ↦ k.hom.app U) e
  change g.hom.app U ≫
      ((modulesSpecToSheaf (R := CommRingCat.of R)).map
        (tilde.map (R := CommRingCat.of R) (ModuleCat.ofHom (R := R) f))).hom.app U =
    h.hom.app U ≫
      ((modulesSpecToSheaf (R := CommRingCat.of R)).map
        (tilde.map (R := CommRingCat.of R) (ModuleCat.ofHom (R := R) f))).hom.app U at eU
  exact eU

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Tilde preserves short exact sequences of modules. -/
theorem tilde_map_shortExact (R' : CommRingCat.{u})
    (S : ShortComplex (ModuleCat.{u} R')) (hS : S.ShortExact) :
    (S.map (tilde.functor R')).ShortExact := by
  have hright : ∀ (T : ShortComplex (ModuleCat.{u} R')), T.ShortExact →
      (T.map (tilde.functor R')).Exact ∧
        Epi ((tilde.functor R').map T.g) :=
    (Functor.preservesFiniteColimits_tfae
      (tilde.functor R')).out 3 0 |>.mp (by infer_instance)
  have hm := hright S hS
  haveI : Mono ((tilde.functor R').map S.f) := by
    have hff : ModuleCat.ofHom S.f.hom = S.f := rfl
    rw [← hff]
    exact tilde_map_mono_of_injective S.f.hom hS.moduleCat_injective_f
  have hfmono : Mono ((S.map (tilde.functor R')).f) := by
    change Mono ((tilde.functor R').map S.f)
    infer_instance
  exact ShortComplex.ShortExact.mk' hm.1 hfmono hm.2

/-- The tilde functor on an affine scheme preserves finite limits; combined with its existing
left-adjoint structure, it is therefore exact. -/
noncomputable instance tildeFunctorPreservesFiniteLimits (R' : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R') := by
  have h : PreservesFiniteLimits (tilde.functor R') ∧
      PreservesFiniteColimits (tilde.functor R') :=
    (Functor.exact_tfae (tilde.functor R')).out 0 3 |>.mp
      (tilde_map_shortExact R')
  exact h.1

/-- Tilde preserves exactness of every short complex of modules. -/
theorem tilde_map_exact (R' : CommRingCat.{u})
    (S : ShortComplex (ModuleCat.{u} R')) (hS : S.Exact) :
    (S.map (tilde.functor R')).Exact := by
  have h : ∀ (T : ShortComplex (ModuleCat.{u} R')), T.Exact →
      (T.map (tilde.functor R')).Exact :=
    (Functor.exact_tfae (tilde.functor R')).out 0 1 |>.mp
      (tilde_map_shortExact R')
  exact h S hS

end TildeExact

/-- The conductor sequence sheafified on the affine scheme `Spec A`. -/
def sheafComplex (A' : CommRingCat.{u}) (B' : Type u) [CommRing B'] [Algebra A' B'] :
    ShortComplex (Spec A').Modules := by
  letI : (tilde.functor A').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (tilde.functor A')
  exact (moduleComplex (A := A') (B := B')).map (tilde.functor A')

/-- The sheafified conductor sequence is short exact for an injective algebra map. -/
theorem sheafComplex_shortExact (A' : CommRingCat.{u}) (B' : Type u)
    [CommRing B'] [Algebra A' B'] (h : Function.Injective (algebraMap A' B')) :
    (sheafComplex A' B').ShortExact := by
  simpa only [sheafComplex] using tilde_map_shortExact A' _
    (moduleComplex_shortExact (A := A') (B := B') h)

/-- Exactness at the middle term of the sheafified conductor sequence. -/
theorem sheafComplex_exact (A' : CommRingCat.{u}) (B' : Type u)
    [CommRing B'] [Algebra A' B'] (h : Function.Injective (algebraMap A' B')) :
    (sheafComplex A' B').Exact :=
  (sheafComplex_shortExact A' B' h).exact

end AffineSheafification

end RingHomConductor

namespace NormalizationConductor

variable (A : Type u) (K : Type v) [CommRing A] [CommRing K] [Algebra A K]

/-- The canonical conductor of a ring inside its integral closure in an overring. -/
abbrev ideal : Ideal (integralClosure A K) :=
  RingHomConductor.conductor (algebraMap A (integralClosure A K))

/-- The corresponding conductor ideal in the original ring. -/
abbrev sourceIdeal : Ideal A :=
  RingHomConductor.sourceConductor (algebraMap A (integralClosure A K))

/-- The normalization conductor sequence is short exact whenever the map to the integral
closure is injective. -/
theorem shortExact (h : Function.Injective (algebraMap A (integralClosure A K))) :
    Function.Injective
        (RingHomConductor.diagonal (algebraMap A (integralClosure A K))) ∧
      Function.Exact
          (RingHomConductor.diagonal (algebraMap A (integralClosure A K)))
          (RingHomConductor.difference (algebraMap A (integralClosure A K))) ∧
        Function.Surjective
          (RingHomConductor.difference (algebraMap A (integralClosure A K))) :=
  RingHomConductor.shortExact _ h

section AffineSheafification

open CategoryTheory
open _root_.AlgebraicGeometry

variable (A' : CommRingCat.{u}) (K' : Type u) [CommRing K'] [Algebra A' K']

/-- The normalization-conductor sequence as a short complex of structure-sheaf modules on
`Spec A`. -/
abbrev sheafComplex : ShortComplex (Spec A').Modules :=
  RingHomConductor.sheafComplex A' (integralClosure A' K')

/-- The sheafified normalization-conductor sequence is short exact whenever normalization embeds
the source ring. -/
theorem sheafComplex_shortExact
    (h : Function.Injective (algebraMap A' (integralClosure A' K'))) :
    (sheafComplex A' K').ShortExact :=
  RingHomConductor.sheafComplex_shortExact A' (integralClosure A' K') h

/-- Exactness at the middle term of the sheafified normalization-conductor sequence. -/
theorem sheafComplex_exact
    (h : Function.Injective (algebraMap A' (integralClosure A' K'))) :
    (sheafComplex A' K').Exact :=
  (sheafComplex_shortExact A' K' h).exact

end AffineSheafification

end NormalizationConductor

end

end GromovWitten.AlgebraicGeometry
