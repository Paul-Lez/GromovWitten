/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Fulton's symmetric local identity for orders of vanishing

Let `D` be a Noetherian domain, `Q` a prime ideal of `D` and `a, s` two nonzero elements of `D`.
Assume that

* there is no chain `⊥ < q' < q < Q` of prime ideals (so `Q` has "height at most two"), and
* the only prime `q ≤ Q` containing both `a` and `s` is `Q` itself.

Then the two "intersection numbers"

`∑_{q < Q, s ∈ q} ord_{D_q}(s) · ord_{D_Q/qD_Q}(a)`  and  `∑_{q < Q, a ∈ q} ord_{D_q}(a) ·
ord_{D_Q/qD_Q}(s)`

agree.  This is the local identity behind the symmetry of intersection multiplicities in
Fulton, *Intersection Theory*, Appendix A.2–A.3, and it is the coefficientwise statement used
to prove that the Gysin map of a section of a trivial line bundle kills principal divisors.

## Main definitions and results

* `GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle.LocalOrdSymmetry`: the
  proposition above, stated as a `Prop` so that downstream files can take it as a hypothesis
  before it is available.
* `GromovWitten.AlgebraicGeometry.IntersectionTheory.VectorBundle.localOrdSymmetry`: its proof.

Auxiliary general-purpose lemmas live in the namespace
`GromovWitten.AlgebraicGeometry.IntersectionTheory.LocalOrdSymmetry`; the most reusable ones are

* `length_eq_of_bijective`: `Module.length` is invariant under a bijective semilinear map;
* `ord_ringEquiv`: `Ring.ord` is invariant under ring isomorphisms.

-/

universe u

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace LocalOrdSymmetry

/-- `Module.length` is invariant under a bijective semilinear map: if `σ : R →+* S` is a
surjective ring hom and `f : M →ₛₗ[σ] N` is bijective, then `M` and `N` have the same length
over `R` and `S` respectively. -/
theorem length_eq_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

/-- The order of vanishing is invariant under ring isomorphisms. -/
theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  have hs : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  have hJ : Ideal.span {e x} = (Ideal.span {x}).map (e : R →+* S) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let φ := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e hJ
  have hsmulR : ∀ r y : R, r • (Ideal.Quotient.mk (Ideal.span {x}) y)
      = Ideal.Quotient.mk (Ideal.span {x}) (r * y) := fun _ _ ↦ rfl
  have hsmulS : ∀ r y : S, r • (Ideal.Quotient.mk (Ideal.span {e x}) y)
      = Ideal.Quotient.mk (Ideal.span {e x}) (r * y) := fun _ _ ↦ rfl
  let f : (R ⧸ Ideal.span {x}) →ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := by
        intro r y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [hsmulR, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, RingHom.coe_coe,
          map_mul, hsmulS] }
  have := length_eq_of_bijective (e : R →+* S) f φ.bijective
  simpa [Ring.ord] using this.symm

section Additivity

variable {A : Type*} [CommRing A]

/-- The length of `M ⧸ b • M`, the "cokernel part" of the multiplicity of `b` on `M`. -/
noncomputable def chiCoker (b : A) (M : Type*) [AddCommGroup M] [Module A M] : ℕ∞ :=
  Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M b))

/-- The length of the `b`-torsion submodule `{x | b • x = 0}` of `M`, the "kernel part" of the
multiplicity of `b` on `M`. -/
noncomputable def chiKer (b : A) (M : Type*) [AddCommGroup M] [Module A M] : ℕ∞ :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A M b))

/-- The length of a module is the length of the kernel plus the length of the range of any
linear map out of it. -/
theorem length_eq_ker_add_range {M P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup P]
    [Module A P] (f : M →ₗ[A] P) :
    Module.length A M
      = Module.length A (LinearMap.ker f) + Module.length A (LinearMap.range f) := by
  have h := LinearMap.exact_subtype_ker_map f.rangeRestrict
  rw [LinearMap.ker_rangeRestrict] at h
  exact Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _)
    f.surjective_rangeRestrict h

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- `chiKer` is invariant under linear isomorphisms. -/
theorem chiKer_congr (b : A) (e : M ≃ₗ[A] N) : chiKer b M = chiKer b N := by
  have hmap : Submodule.map (e : M →ₗ[A] N) (LinearMap.ker (LinearMap.lsmul A M b))
      = LinearMap.ker (LinearMap.lsmul A N b) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← map_smul, hx, map_zero]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_smul, e.apply_symm_apply, hy, map_zero]
  exact LinearEquiv.length_eq (e.submoduleMap _ ≪≫ₗ LinearEquiv.ofEq _ _ hmap)

/-- `chiCoker` is invariant under linear isomorphisms. -/
theorem chiCoker_congr (b : A) (e : M ≃ₗ[A] N) : chiCoker b M = chiCoker b N := by
  have hmap : Submodule.map (e : M →ₗ[A] N) (LinearMap.range (LinearMap.lsmul A M b))
      = LinearMap.range (LinearMap.lsmul A N b) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, by rw [map_smul]⟩
    · rintro ⟨y', rfl⟩
      exact ⟨b • e.symm y', ⟨e.symm y', rfl⟩, by rw [map_smul, e.apply_symm_apply]⟩
  exact LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e hmap)

/-- The length of `Submodule.comap X.subtype Y` agrees with the length of `X ⊓ Y`. -/
theorem length_comap_subtype (X Y : Submodule A M) :
    Module.length A (Submodule.comap X.subtype Y) = Module.length A (X ⊓ Y : Submodule A M) := by
  have h : Submodule.comap X.subtype Y = Submodule.comap X.subtype (X ⊓ Y) := by
    ext x
    simp [Submodule.mem_comap]
  rw [h]
  exact LinearEquiv.length_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)

/-- Additivity of the pair `(chiCoker, chiKer)` along a short exact sequence
`0 → N → M → M ⧸ N → 0`.  This is the "snake lemma" input of Fulton's Appendix A.2, written
additively so that no subtraction in `ℕ∞` is needed. -/
theorem chi_add_submodule (b : A) (P : Submodule A M) :
    chiCoker b M + chiKer b P + chiKer b (M ⧸ P)
      = chiKer b M + chiCoker b P + chiCoker b (M ⧸ P) := by
  classical
  set LM := LinearMap.lsmul A M b with hLM
  set LP := LinearMap.lsmul A P b with hLP
  set LQ := LinearMap.lsmul A (M ⧸ P) b with hLQ
  set K := LinearMap.ker LM with hK
  set Rg := LinearMap.range LM with hRg
  set RP := LinearMap.range LP with hRP
  set KQ := LinearMap.ker LQ with hKQ
  set C : Submodule A M := Submodule.comap LM P with hC
  -- the map `P ⧸ bP → M ⧸ bM`
  have hu : RP ≤ Submodule.comap P.subtype Rg := by
    rintro x ⟨y, rfl⟩
    exact ⟨(y : M), rfl⟩
  set u : (P ⧸ RP) →ₗ[A] (M ⧸ Rg) := Submodule.mapQ RP Rg P.subtype hu with hudef
  -- the map `M ⧸ bM → (M ⧸ P) ⧸ b (M ⧸ P)`
  have hv : Rg ≤ Submodule.comap P.mkQ (LinearMap.range LQ) := by
    rintro x ⟨y, rfl⟩
    exact ⟨P.mkQ y, by simp [hLM, hLQ]⟩
  set v : (M ⧸ Rg) →ₗ[A] ((M ⧸ P) ⧸ LinearMap.range LQ) :=
    Submodule.mapQ Rg (LinearMap.range LQ) P.mkQ hv with hvdef
  -- the surjection `C ↠ ker (b • ·) on M ⧸ P`
  have hψ : ∀ x : C, P.mkQ (x : M) ∈ KQ := by
    rintro ⟨x, hx⟩
    simp only [hKQ, hLQ, LinearMap.mem_ker, LinearMap.lsmul_apply]
    rw [← P.mkQ.map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  set ψ : C →ₗ[A] KQ := (P.mkQ ∘ₗ C.subtype).codRestrict KQ hψ with hψdef
  have hψapp : ∀ x : C, (ψ x : M ⧸ P) = P.mkQ (x : M) := fun _ ↦ rfl
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := P.mkQ_surjective y
    have hyC : y ∈ C := by
      simp only [hKQ, hLQ, LinearMap.mem_ker, LinearMap.lsmul_apply] at hy
      rw [← P.mkQ.map_smul] at hy
      exact (Submodule.Quotient.mk_eq_zero P).1 hy
    exact ⟨⟨y, hyC⟩, rfl⟩
  -- the map `C → P ⧸ bP`, `x ↦ [b • x]`
  have hres : ∀ x ∈ C, LM x ∈ P := fun _ hx ↦ hx
  set θ₀ : C →ₗ[A] (P ⧸ RP) := RP.mkQ ∘ₗ LM.restrict hres with hθ₀def
  have hθ₀app : ∀ x : C, θ₀ x = Submodule.Quotient.mk ⟨b • (x : M), hres x x.2⟩ := fun _ ↦ rfl
  have hker : LinearMap.ker ψ ≤ LinearMap.ker θ₀ := by
    intro x hx
    have hxP : (x : M) ∈ P := by
      have : P.mkQ (x : M) = 0 := congrArg Subtype.val hx
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    rw [LinearMap.mem_ker, hθ₀app]
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨⟨(x : M), hxP⟩, ?_⟩
    rfl
  set θ : KQ →ₗ[A] (P ⧸ RP) :=
    (Submodule.liftQ _ θ₀ hker) ∘ₗ
      (LinearMap.quotKerEquivOfSurjective ψ hψsurj).symm.toLinearMap
    with hθdef
  have hθψ : ∀ x : C, θ (ψ x) = θ₀ x := by
    intro x
    have h1 : (LinearMap.quotKerEquivOfSurjective ψ hψsurj).symm (ψ x)
        = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [hθdef, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
      Submodule.liftQ_apply]
  -- the map `ker (b • ·) on M → ker (b • ·) on M ⧸ P`
  have hw : ∀ x : K, P.mkQ (x : M) ∈ KQ := by
    rintro ⟨x, hx⟩
    simp only [hK, hLM, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx
    simp only [hKQ, hLQ, LinearMap.mem_ker, LinearMap.lsmul_apply]
    rw [← P.mkQ.map_smul, hx, map_zero]
  set w : K →ₗ[A] KQ := (P.mkQ ∘ₗ K.subtype).codRestrict KQ hw with hwdef
  have huapp : ∀ y : P, u (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y : M) := by
    intro y; rw [hudef, Submodule.mapQ_apply]; rfl
  have hvapp : ∀ x : M, v (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (Submodule.Quotient.mk x : M ⧸ P) := by
    intro x; rw [hvdef, Submodule.mapQ_apply]; rfl
  have hwapp : ∀ k : K, (w k : M ⧸ P) = Submodule.Quotient.mk (k : M) := fun _ ↦ rfl
  have hψapp' : ∀ x : C, (ψ x : M ⧸ P) = Submodule.Quotient.mk (x : M) := fun _ ↦ rfl
  -- (F1) the kernel of `v` is the range of `u`
  have hF1 : LinearMap.ker v = LinearMap.range u := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Rg z
      rw [LinearMap.mem_ker, hvapp, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨t, ht⟩ := hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P t
      have ht' : (Submodule.Quotient.mk (b • y) : M ⧸ P) = Submodule.Quotient.mk x := by
        rw [← ht, hLQ]
        rw [LinearMap.lsmul_apply]
        exact (Submodule.Quotient.mk_smul P b y).symm
      have hmem : x - b • y ∈ P := by
        have := (Submodule.Quotient.eq P).1 ht'
        simpa using neg_mem this
      refine ⟨Submodule.Quotient.mk ⟨x - b • y, hmem⟩, ?_⟩
      rw [huapp, Submodule.Quotient.eq]
      have : x - b • y - x = -(b • y) := by abel
      rw [this]
      exact neg_mem ⟨y, rfl⟩
    · rintro z ⟨y, rfl⟩
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective RP y
      rw [LinearMap.mem_ker, huapp, hvapp, (Submodule.Quotient.mk_eq_zero P).2 n.2,
        Submodule.Quotient.mk_zero]
  -- (F2) `v` is surjective
  have hF2 : Function.Surjective v := by
    intro z
    obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range LQ) z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P t
    exact ⟨Submodule.Quotient.mk x, hvapp x⟩
  -- (F3) the range of `θ` is the kernel of `u`
  have hF3 : LinearMap.range θ = LinearMap.ker u := by
    apply le_antisymm
    · rintro z ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hψsurj x
      rw [hθψ, hθ₀app, LinearMap.mem_ker, huapp]
      exact (Submodule.Quotient.mk_eq_zero Rg).2 ⟨(y : M), rfl⟩
    · intro z hz
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective RP z
      rw [LinearMap.mem_ker, huapp, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨y, hy⟩ := hz
      have hyC : y ∈ C := by
        rw [hC, Submodule.mem_comap]
        rw [hy]
        exact n.2
      refine ⟨ψ ⟨y, hyC⟩, ?_⟩
      rw [hθψ, hθ₀app]
      congr 1
      exact Subtype.ext hy
  -- (F4) the kernel of `θ` is the range of `w`
  have hF4 : LinearMap.ker θ = LinearMap.range w := by
    ext x
    obtain ⟨y, rfl⟩ := hψsurj x
    rw [LinearMap.mem_ker, hθψ, hθ₀app, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨n, hn⟩
      have hn' : b • (n : M) = b • (y : M) := congrArg Subtype.val hn
      have hk : (y : M) - (n : M) ∈ K := by
        rw [hK, hLM, LinearMap.mem_ker, LinearMap.lsmul_apply, smul_sub, hn', sub_self]
      refine ⟨⟨(y : M) - (n : M), hk⟩, ?_⟩
      apply Subtype.ext
      rw [hψapp', hwapp, Submodule.Quotient.eq]
      have : (y : M) - (n : M) - (y : M) = -(n : M) := by abel
      rw [this]
      exact neg_mem n.2
    · rintro ⟨k, hk⟩
      have hk' : (Submodule.Quotient.mk (k : M) : M ⧸ P) = Submodule.Quotient.mk (y : M) := by
        rw [← hwapp, ← hψapp', hk]
      have hmem : (y : M) - (k : M) ∈ P := by
        have := (Submodule.Quotient.eq P).1 hk'
        simpa using neg_mem this
      have hkK : b • (k : M) = 0 := k.2
      refine ⟨⟨(y : M) - (k : M), hmem⟩, ?_⟩
      apply Subtype.ext
      rw [hLP, LinearMap.lsmul_apply]
      change b • ((y : M) - (k : M)) = b • (y : M)
      rw [smul_sub, hkK, sub_zero]
  -- (F5) the two "intersection" kernels
  have hkerw : LinearMap.ker w = Submodule.comap K.subtype P := by
    ext k
    rw [LinearMap.mem_ker, Submodule.mem_comap, ← Submodule.coe_eq_zero, hwapp,
      Submodule.Quotient.mk_eq_zero]
    rfl
  have hkerLP : LinearMap.ker LP = Submodule.comap P.subtype K := by
    ext n
    rw [LinearMap.mem_ker, Submodule.mem_comap, hLP, LinearMap.lsmul_apply,
      ← Submodule.coe_eq_zero, hK, hLM]
    exact Iff.rfl
  -- assembling the four exact sequences
  have hA : Module.length A (P ⧸ RP)
      = Module.length A (LinearMap.ker u) + Module.length A (LinearMap.range u) :=
    length_eq_ker_add_range u
  have hB : Module.length A (M ⧸ Rg)
      = Module.length A (LinearMap.range u) + Module.length A ((M ⧸ P) ⧸ LinearMap.range LQ) := by
    rw [length_eq_ker_add_range v, hF1, LinearMap.range_eq_top.2 hF2, Module.length_top]
  have hC' : Module.length A KQ
      = Module.length A (LinearMap.range w) + Module.length A (LinearMap.ker u) := by
    rw [length_eq_ker_add_range θ, hF4, hF3]
  have hD : Module.length A K
      = Module.length A (K ⊓ P : Submodule A M) + Module.length A (LinearMap.range w) := by
    rw [length_eq_ker_add_range w, hkerw, length_comap_subtype]
  have hE : Module.length A (LinearMap.ker LP)
      = Module.length A (K ⊓ P : Submodule A M) := by
    rw [hkerLP, length_comap_subtype, inf_comm]
  simp only [chiCoker, chiKer]
  rw [hA, hB, hC', hD, hE]
  ring

end Additivity

section LengthAt

variable {B : Type*} [CommRing B]

/-- The length of the localization `M_p` of `M` at a prime ideal `p`, as a module over the
local ring `B_p`. -/
noncomputable def lengthAt (p : Ideal B) [p.IsPrime] (M : Type*) [AddCommGroup M] [Module B M] :
    ℕ∞ :=
  Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M)

variable (p : Ideal B) [p.IsPrime]

/-- `lengthAt` is invariant under linear isomorphisms. -/
theorem lengthAt_congr {M N : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (e : M ≃ₗ[B] N) : lengthAt p M = lengthAt p N := by
  have hinj := IsLocalizedModule.map_injective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) (LocalizedModule.mkLinearMap p.primeCompl N)
    (e : M →ₗ[B] N) e.injective
  have hsurj := IsLocalizedModule.map_surjective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) (LocalizedModule.mkLinearMap p.primeCompl N)
    (e : M →ₗ[B] N) e.surjective
  exact LinearEquiv.length_eq
    ((LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization p.primeCompl
      (Localization.AtPrime p))

/-- Localization is exact, so `lengthAt` is additive along short exact sequences. -/
theorem lengthAt_add {M : Type*} [AddCommGroup M] [Module B M] (P : Submodule B M) :
    lengthAt p M = lengthAt p P + lengthAt p (M ⧸ P) := by
  have hg := IsLocalizedModule.map_injective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl P) (LocalizedModule.mkLinearMap p.primeCompl M)
    P.subtype (Submodule.subtype_injective P)
  have hh := IsLocalizedModule.map_surjective p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ P)) P.mkQ (Submodule.mkQ_surjective P)
  have hex := IsLocalizedModule.map_exact p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl P) (LocalizedModule.mkLinearMap p.primeCompl M)
    (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ P)) P.subtype P.mkQ
    (LinearMap.exact_subtype_mkQ P)
  exact Module.length_eq_add_of_exact
    ((IsLocalizedModule.map p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl P)
        (LocalizedModule.mkLinearMap p.primeCompl M)
        P.subtype).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p))
    ((IsLocalizedModule.map p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
        (LocalizedModule.mkLinearMap p.primeCompl (M ⧸ P))
        P.mkQ).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)) hg hh hex

/-- A module killed by an element outside `p` has vanishing length at `p`. -/
theorem lengthAt_eq_zero {M : Type*} [AddCommGroup M] [Module B M] {t : B} (ht : t ∉ p)
    (h : ∀ m : M, t • m = 0) : lengthAt p M = 0 := by
  have : Subsingleton (LocalizedModule p.primeCompl M) :=
    LocalizedModule.subsingleton_iff.2 fun m ↦ ⟨t, ht, h m⟩
  exact Module.length_eq_zero

/-- The localization of `B ⧸ I` at a prime `p` is `B_p ⧸ I B_p`. -/
theorem lengthAt_quotient (I : Ideal B) :
    lengthAt p (B ⧸ I) = Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap B (Localization.AtPrime p))) := by
  have hloc : Submodule.localized' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap B (Localization.AtPrime p)) (I : Submodule B B)
      = I.map (algebraMap B (Localization.AtPrime p)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  have e₁ := IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (B ⧸ I))
    (Submodule.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap B (Localization.AtPrime p)) (I : Submodule B B))
  have e₂ := (e₁.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)).trans
    (Submodule.quotEquivOfEq _ _ hloc)
  rw [lengthAt, LinearEquiv.length_eq e₂]

/-- The localization of `B ⧸ (x)` at a prime `p` computes the order of vanishing of `x` in
`B_p`. -/
theorem lengthAt_quotient_span (x : B) :
    lengthAt p (B ⧸ Ideal.span {x})
      = Ring.ord (Localization.AtPrime p) (algebraMap B (Localization.AtPrime p) x) := by
  rw [lengthAt_quotient, Ideal.map_span, Set.image_singleton]
  rfl

/-- The localization of `B ⧸ p` at `p` is the residue field of `B_p`, of length one. -/
theorem lengthAt_quotient_self : lengthAt p (B ⧸ p) = 1 := by
  have hloc : Submodule.localized' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap B (Localization.AtPrime p)) (p : Submodule B B)
      = IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Submodule.localized'_eq_span, ← IsLocalization.AtPrime.map_eq_maximalIdeal p]
    rfl
  have hsimple : IsSimpleModule (Localization.AtPrime p)
      ((Localization.AtPrime p) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
    isSimpleModule_iff_isCoatom.2
      (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p)).out
  have e₁ := IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (B ⧸ p))
    (Submodule.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap B (Localization.AtPrime p)) (p : Submodule B B))
  have e₂ := (e₁.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)).trans
    (Submodule.quotEquivOfEq _ _ hloc)
  rw [lengthAt, LinearEquiv.length_eq e₂]
  exact Module.length_eq_one _ _

end LengthAt

section Devissage

variable {B : Type*} [CommRing B] (b : B)

/-- Cancellation of a finite summand in `ℕ∞`. -/
theorem enat_add_right_cancel {x y z : ℕ∞} (hz : z ≠ ⊤) (h : x + z = y + z) : x = y := by
  have hc := ENat.addLECancellable_of_ne_top hz
  have h' : z + x = z + y := by rw [add_comm z x, add_comm z y]; exact h
  exact le_antisymm (hc h'.le) (hc h'.ge)

/-- The cokernel multiplicity of the zero module vanishes. -/
theorem chiCoker_eq_zero {M : Type*} [AddCommGroup M] [Module B M] [Subsingleton M] :
    chiCoker b M = 0 := Module.length_eq_zero

/-- The kernel multiplicity of the zero module vanishes. -/
theorem chiKer_eq_zero {M : Type*} [AddCommGroup M] [Module B M] [Subsingleton M] :
    chiKer b M = 0 := Module.length_eq_zero

/-- The length at a prime of the zero module vanishes. -/
theorem lengthAt_eq_zero_of_subsingleton (p : Ideal B) [p.IsPrime] {M : Type*} [AddCommGroup M]
    [Module B M] [Subsingleton M] : lengthAt p M = 0 := Module.length_eq_zero

/-- An element of an ideal `I` annihilates `B ⧸ I`. -/
theorem smul_quotient_eq_zero {I : Ideal B} {t : B} (ht : t ∈ I) (m : B ⧸ I) : t • m = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I m
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
  exact (Submodule.Quotient.mk_eq_zero I).2 (Ideal.mul_mem_right y I ht)

/-- The cokernel multiplicity of `b` on `B ⧸ I` is the length of `B ⧸ (I + (b))`. -/
theorem chiCoker_quotient (I : Ideal B) :
    chiCoker b (B ⧸ I) = Module.length B (B ⧸ (I ⊔ Ideal.span {b})) := by
  have hr : LinearMap.range (LinearMap.lsmul B (B ⧸ I) b)
      = Submodule.map I.mkQ (Ideal.span {b}) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I y
      exact ⟨b * y, Ideal.mem_span_singleton.2 ⟨y, rfl⟩, by
        rw [Submodule.mkQ_apply, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hy
      exact ⟨Submodule.Quotient.mk c, by
        rw [Submodule.mkQ_apply, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]⟩
  rw [chiCoker, hr]
  exact LinearEquiv.length_eq (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {b}))

/-- For a maximal ideal `p`, multiplication by `b` on the residue field `B ⧸ p` is either zero
or bijective, so the two multiplicity terms agree. -/
theorem chi_eq_of_isMaximal (p : Ideal B) [hp : p.IsMaximal] :
    chiCoker b (B ⧸ p) = chiKer b (B ⧸ p) := by
  by_cases hb : b ∈ p
  · have hzero : LinearMap.lsmul B (B ⧸ p) b = 0 :=
      LinearMap.ext fun m ↦ smul_quotient_eq_zero hb m
    rw [chiCoker, chiKer, hzero, LinearMap.range_zero, LinearMap.ker_zero, Module.length_top]
    exact LinearEquiv.length_eq (Submodule.quotEquivOfEqBot _ rfl)
  · obtain ⟨c, i, hi, hci⟩ := hp.exists_inv hb
    have hinv : ∀ m : B ⧸ p, (c * b) • m = m := by
      intro m
      have h1 : i • m = 0 := smul_quotient_eq_zero hi m
      have h2 : (c * b + i) • m = m := by rw [hci, one_smul]
      rw [add_smul, h1, add_zero] at h2
      exact h2
    have hrange : LinearMap.range (LinearMap.lsmul B (B ⧸ p) b) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro m
      exact ⟨c • m, by rw [LinearMap.lsmul_apply, smul_smul, mul_comm b c, hinv]⟩
    have hker : LinearMap.ker (LinearMap.lsmul B (B ⧸ p) b) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro m hm
      rw [LinearMap.lsmul_apply] at hm
      calc m = (c * b) • m := (hinv m).symm
        _ = c • (b • m) := by rw [mul_smul]
        _ = 0 := by rw [hm, smul_zero]
    have hsub : Subsingleton ((B ⧸ p) ⧸ (⊤ : Submodule B (B ⧸ p))) := by
      constructor
      intro y z
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    rw [chiCoker, chiKer, hrange, hker, Module.length_bot, Module.length_eq_zero]

variable [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- If `B ⧸ (I + (b))` is an Artinian `B`-module then `chiCoker b (B ⧸ J)` is finite for every
ideal `J` containing `I`. -/
theorem chiCoker_ne_top (I : Ideal B) (hart : IsArtinian B (B ⧸ (I ⊔ Ideal.span {b})))
    [IsNoetherianRing B] (J : Ideal B) (hJ : I ≤ J) : chiCoker b (B ⧸ J) ≠ ⊤ := by
  have hb : I ⊔ Ideal.span {b}
      ≤ LinearMap.ker ((LinearMap.range (LinearMap.lsmul B (B ⧸ J) b)).mkQ ∘ₗ J.mkQ) := by
    refine sup_le (fun y hy ↦ ?_) ?_
    · rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
      simp only [Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero J).2 (hJ hy), Submodule.Quotient.mk_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      refine (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.Quotient.mk 1, ?_⟩
      rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rfl
  have hsurj : Function.Surjective (Submodule.liftQ (I ⊔ Ideal.span {b}) _ hb) := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective J w
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have _ : IsArtinian B ((B ⧸ J) ⧸ LinearMap.range (LinearMap.lsmul B (B ⧸ J) b)) :=
    isArtinian_of_surjective _ _ hsurj
  exact Module.length_ne_top

omit [IsNoetherianRing B] in
/-- Base case of the dévissage: the statement for the cyclic modules `B ⧸ p`, `p` a prime
containing `I`. -/
theorem devissage_base (I : Ideal B) (T : Finset (PrimeSpectrum B))
    (hTmin : ∀ q : PrimeSpectrum B, q.asIdeal ∈ I.minimalPrimes → q ∈ T)
    (hTmem : ∀ q ∈ T, q.asIdeal ∈ I.minimalPrimes)
    (hdim : ∀ q : Ideal B, q.IsPrime → I ≤ q → q ∈ I.minimalPrimes ∨ q.IsMaximal)
    (p : Ideal B) [hp : p.IsPrime] (hIp : I ≤ p) :
    chiCoker b (B ⧸ p) + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiKer b (B ⧸ q.asIdeal)
      = chiKer b (B ⧸ p) + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiCoker b (B ⧸ q.asIdeal) := by
  have hzero : ∀ q : PrimeSpectrum B, ¬ (p ≤ q.asIdeal) → lengthAt q.asIdeal (B ⧸ p) = 0 := by
    intro q hq
    obtain ⟨t, htp, htq⟩ := SetLike.not_le_iff_exists.1 hq
    exact lengthAt_eq_zero _ htq fun m ↦ smul_quotient_eq_zero htp m
  by_cases hmin : p ∈ I.minimalPrimes
  · have hpT : (⟨p, hp⟩ : PrimeSpectrum B) ∈ T := hTmin _ hmin
    have hsum : ∀ g : PrimeSpectrum B → ℕ∞,
        ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * g q = g ⟨p, hp⟩ := by
      intro g
      rw [Finset.sum_eq_single (⟨p, hp⟩ : PrimeSpectrum B)]
      · rw [lengthAt_quotient_self, one_mul]
      · intro q hqT hqne
        refine (congrArg (· * g q) (hzero q ?_)).trans (zero_mul _)
        intro hle
        have hqmin := hTmem q hqT
        exact hqne (PrimeSpectrum.ext (le_antisymm (hqmin.2 ⟨hp, hIp⟩ hle) hle))
      · intro h; exact absurd hpT h
    rw [hsum, hsum, add_comm]
  · have hmax : p.IsMaximal := (hdim p hp hIp).resolve_left hmin
    have hsum : ∀ g : PrimeSpectrum B → ℕ∞,
        ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * g q = 0 := by
      intro g
      refine Finset.sum_eq_zero fun q hqT ↦ ?_
      refine (congrArg (· * g q) (hzero q ?_)).trans (zero_mul _)
      intro hle
      have hqmin := hTmem q hqT
      exact hmin (le_antisymm (hqmin.2 ⟨hp, hIp⟩ hle) hle ▸ hqmin)
    rw [hsum, hsum, add_zero, add_zero]
    exact chi_eq_of_isMaximal b p

/-- Dévissage (Fulton, *Intersection Theory*, Lemma A.2.7): if every prime of `B` containing `I`
is either minimal over `I` or maximal, and `B ⧸ (I + (b))` is Artinian, then the multiplicity of
`b` on `B ⧸ J` (for `J ⊇ I`) is computed from the multiplicities on the `B ⧸ q`, `q` minimal over
`I`, weighted by the lengths of the localizations. -/
theorem devissage (I : Ideal B) (hart : IsArtinian B (B ⧸ (I ⊔ Ideal.span {b})))
    (T : Finset (PrimeSpectrum B))
    (hTmin : ∀ q : PrimeSpectrum B, q.asIdeal ∈ I.minimalPrimes → q ∈ T)
    (hTmem : ∀ q ∈ T, q.asIdeal ∈ I.minimalPrimes)
    (hdim : ∀ q : Ideal B, q.IsPrime → I ≤ q → q ∈ I.minimalPrimes ∨ q.IsMaximal)
    (J : Ideal B) (hIJ : I ≤ J) :
    chiCoker b (B ⧸ J) + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiKer b (B ⧸ q.asIdeal)
      = chiKer b (B ⧸ J) + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiCoker b (B ⧸ q.asIdeal) := by
  refine IsNoetherian.induction
    (P := fun J : Ideal B ↦ I ≤ J → chiCoker b (B ⧸ J)
      + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiKer b (B ⧸ q.asIdeal)
      = chiKer b (B ⧸ J) + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiCoker b (B ⧸ q.asIdeal))
    ?_ J hIJ
  clear hIJ J
  intro J ih hIJ
  rcases subsingleton_or_nontrivial (B ⧸ J) with hJ | hJ
  · rw [chiCoker_eq_zero, chiKer_eq_zero]
    simp only [lengthAt_eq_zero_of_subsingleton, zero_mul, Finset.sum_const_zero]
  · obtain ⟨p, hp⟩ := associatedPrimes.nonempty B (B ⧸ J)
    have hpp : p.IsPrime := hp.1
    obtain ⟨x, hx⟩ := (isAssociatedPrime_iff.1 hp).2
    have hJp : J ≤ p := by
      intro r hr
      rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact smul_quotient_eq_zero hr x
    have hxne : x ≠ 0 := by
      intro h
      refine hpp.ne_top ?_
      rw [hx, h]
      refine eq_top_iff.2 fun r _ ↦ ?_
      rw [Submodule.mem_colon_singleton, smul_zero]
      exact Submodule.zero_mem _
    have hkerf : LinearMap.ker (LinearMap.toSpanSingleton B (B ⧸ J) x) = p := by
      ext r
      rw [LinearMap.mem_ker, hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
      rfl
    have eP : (B ⧸ p) ≃ₗ[B] LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x) :=
      (Submodule.quotEquivOfEq p _ hkerf.symm).trans
        (LinearMap.quotKerEquivRange (LinearMap.toSpanSingleton B (B ⧸ J) x))
    have hJle : J ≤ Submodule.comap J.mkQ
        (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)) := by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero J).2 hy]
      exact Submodule.zero_mem _
    have hmap : Submodule.map J.mkQ (Submodule.comap J.mkQ
        (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
        = LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x) :=
      Submodule.map_comap_eq_self (by rw [J.range_mkQ]; exact le_top)
    have hJlt : J < Submodule.comap J.mkQ
        (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)) := by
      refine lt_of_le_of_ne hJle fun hEq ↦ hxne ?_
      have hx1 : x ∈ LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x) := ⟨1, one_smul _ _⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective J x
      have : y ∈ J := by rw [hEq]; exact hx1
      exact (Submodule.Quotient.mk_eq_zero J).2 this
    have eQ : ((B ⧸ J) ⧸ LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)) ≃ₗ[B]
        (B ⧸ Submodule.comap J.mkQ
          (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))) :=
      (Submodule.quotEquivOfEq _ _ hmap.symm).trans
        ((Submodule.quotientQuotientEquivQuotientSup J _).trans
          (Submodule.quotEquivOfEq _ _ (sup_eq_right.2 hJlt.le)))
    have hstep := chi_add_submodule b (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))
    rw [← chiKer_congr b eP, ← chiCoker_congr b eP, chiKer_congr b eQ,
      chiCoker_congr b eQ] at hstep
    have hL : ∀ q : PrimeSpectrum B, lengthAt q.asIdeal (B ⧸ J)
        = lengthAt q.asIdeal (B ⧸ p) + lengthAt q.asIdeal
            (B ⧸ Submodule.comap J.mkQ
              (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))) := by
      intro q
      rw [lengthAt_add q.asIdeal (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)),
        ← lengthAt_congr q.asIdeal eP, lengthAt_congr q.asIdeal eQ]
    have hbase := devissage_base b I T hTmin hTmem hdim p (hIJ.trans hJp)
    have hih := ih _ hJlt (hIJ.trans hJlt.le)
    have hsumK : ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiKer b (B ⧸ q.asIdeal)
        = (∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiKer b (B ⧸ q.asIdeal))
          + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
              (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
              * chiKer b (B ⧸ q.asIdeal) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [hL q, add_mul]
    have hsumA : ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ J) * chiCoker b (B ⧸ q.asIdeal)
        = (∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiCoker b (B ⧸ q.asIdeal))
          + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
              (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
              * chiCoker b (B ⧸ q.asIdeal) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [hL q, add_mul]
    rw [hsumK, hsumA]
    refine enat_add_right_cancel (z := chiCoker b (B ⧸ p) + chiCoker b
      (B ⧸ Submodule.comap J.mkQ (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))))
      (by
        rw [Ne, ENat.add_eq_top]
        push Not
        exact ⟨chiCoker_ne_top b I hart p (hIJ.trans hJp),
          chiCoker_ne_top b I hart _ (hIJ.trans hJlt.le)⟩) ?_
    calc chiCoker b (B ⧸ J) + ((∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiKer b (B ⧸ q.asIdeal))
            + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                * chiKer b (B ⧸ q.asIdeal))
          + (chiCoker b (B ⧸ p) + chiCoker b (B ⧸ Submodule.comap J.mkQ
              (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))))
        = chiCoker b (B ⧸ J)
            + (chiCoker b (B ⧸ p)
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiKer b (B ⧸ q.asIdeal))
            + (chiCoker b (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                  * chiKer b (B ⧸ q.asIdeal)) := by ring
      _ = chiCoker b (B ⧸ J)
            + (chiKer b (B ⧸ p)
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiCoker b (B ⧸ q.asIdeal))
            + (chiKer b (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                  * chiCoker b (B ⧸ q.asIdeal)) := by rw [hbase, hih]
      _ = (chiCoker b (B ⧸ J) + chiKer b (B ⧸ p)
            + chiKer b (B ⧸ Submodule.comap J.mkQ
                (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))))
            + ((∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiCoker b (B ⧸ q.asIdeal))
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                  * chiCoker b (B ⧸ q.asIdeal)) := by ring
      _ = (chiKer b (B ⧸ J) + chiCoker b (B ⧸ p)
            + chiCoker b (B ⧸ Submodule.comap J.mkQ
                (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x))))
            + ((∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p) * chiCoker b (B ⧸ q.asIdeal))
              + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                  (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                  * chiCoker b (B ⧸ q.asIdeal)) := by rw [hstep]
      _ = chiKer b (B ⧸ J) + ((∑ q ∈ T, lengthAt q.asIdeal (B ⧸ p)
              * chiCoker b (B ⧸ q.asIdeal))
            + ∑ q ∈ T, lengthAt q.asIdeal (B ⧸ Submodule.comap J.mkQ
                (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))
                * chiCoker b (B ⧸ q.asIdeal))
          + (chiCoker b (B ⧸ p) + chiCoker b (B ⧸ Submodule.comap J.mkQ
              (LinearMap.range (LinearMap.toSpanSingleton B (B ⧸ J) x)))) := by ring

end Devissage

section Transfer

/-- The range of multiplication by `x` on `R` itself is the principal ideal `(x)`. -/
theorem range_lsmul_self (R : Type*) [CommRing R] (x : R) :
    LinearMap.range (LinearMap.lsmul R R x) = Ideal.span {x} := by
  ext y
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- The cokernel multiplicity of `x` on `R` itself is the order of vanishing of `x`. -/
theorem chiCoker_self (R : Type*) [CommRing R] (x : R) : chiCoker x R = Ring.ord R x := by
  rw [chiCoker, range_lsmul_self]
  rfl

variable {A B : Type*} [CommRing A] [CommRing B]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module B M]

/-- Length of a submodule computed over a ring and over a quotient of it agree, provided the
two actions on the ambient module are related by the (surjective) ring map. -/
theorem length_subtype_eq_of_smul (σ : A →+* B) (hσ : Function.Surjective σ)
    (hsmul : ∀ (a : A) (m : M), a • m = σ a • m)
    (N₁ : Submodule A M) (N₂ : Submodule B M) (hN : ∀ m, m ∈ N₁ ↔ m ∈ N₂) :
    Module.length A N₁ = Module.length B N₂ := by
  have _ : RingHomSurjective σ := ⟨hσ⟩
  refine length_eq_of_bijective σ
    { toFun := fun x ↦ ⟨(x : M), (hN _).1 x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ Subtype.ext (hsmul a (x : M)) } ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (congrArg (fun z : N₂ ↦ (z : M)) h)
  · intro y
    exact ⟨⟨(y : M), (hN _).2 y.2⟩, rfl⟩

/-- Length of a quotient module computed over a ring and over a quotient of it agree, provided
the two actions on the ambient module are related by the (surjective) ring map. -/
theorem length_quotient_eq_of_smul (σ : A →+* B) (hσ : Function.Surjective σ)
    (hsmul : ∀ (a : A) (m : M), a • m = σ a • m)
    (N₁ : Submodule A M) (N₂ : Submodule B M) (hN : ∀ m, m ∈ N₁ ↔ m ∈ N₂) :
    Module.length A (M ⧸ N₁) = Module.length B (M ⧸ N₂) := by
  have _ : RingHomSurjective σ := ⟨hσ⟩
  have hle : N₁ ≤ Submodule.comap
      ({ toFun := id, map_add' := fun _ _ ↦ rfl,
         map_smul' := fun a m ↦ hsmul a m } : M →ₛₗ[σ] M) N₂ :=
    fun m hm ↦ (hN m).1 hm
  refine length_eq_of_bijective σ (Submodule.mapQ N₁ N₂ _ hle) ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N₁ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N₁ y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at h
    exact (Submodule.Quotient.eq N₁).2 ((hN _).2 h)
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N₂ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end Transfer

section QuotientOrd

variable {B : Type*} [CommRing B] (b : B)

/-- The cokernel multiplicity of `b` on `B ⧸ I` is the order of vanishing of the image of `b`
in the quotient ring `B ⧸ I`. -/
theorem chiCoker_quotient_ord (I : Ideal B) :
    chiCoker b (B ⧸ I) = Ring.ord (B ⧸ I) (Ideal.Quotient.mk I b) := by
  rw [chiCoker, Ring.ord]
  refine length_quotient_eq_of_smul (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (fun c m ↦ ?_) _ _ (fun m ↦ ?_)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I m
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
    rfl
  · rw [LinearMap.mem_range, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩

end QuotientOrd

section Koszul

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- The Koszul relation module `{(x, y) | a * x = s * y}` inside `A × A`. -/
noncomputable def koszulRel (a s : A) : Submodule A (A × A) :=
  LinearMap.ker (a • LinearMap.fst A A A - s • LinearMap.snd A A A)

omit [IsDomain A] in
/-- Membership in the Koszul relation module. -/
theorem mem_koszulRel {a s : A} {p : A × A} : p ∈ koszulRel a s ↔ a * p.1 = s * p.2 := by
  rw [koszulRel, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    smul_eq_mul, sub_eq_zero]

/-- Koszul symmetry: over a domain, the `a`-torsion of `A ⧸ (s)` and the `s`-torsion of
`A ⧸ (a)` are isomorphic, hence have the same length. -/
theorem chiKer_quotient_comm (a s : A) (ha : a ≠ 0) (hs : s ≠ 0) :
    chiKer a (A ⧸ Ideal.span {s}) = chiKer s (A ⧸ Ideal.span {a}) := by
  set g₁ : koszulRel a s →ₗ[A] (A ⧸ Ideal.span {s}) :=
    (Ideal.span {s}).mkQ ∘ₗ (LinearMap.fst A A A) ∘ₗ (koszulRel a s).subtype with hg₁
  set g₂ : koszulRel a s →ₗ[A] (A ⧸ Ideal.span {a}) :=
    (Ideal.span {a}).mkQ ∘ₗ (LinearMap.snd A A A) ∘ₗ (koszulRel a s).subtype with hg₂
  have hg₁app : ∀ p : koszulRel a s, g₁ p = Submodule.Quotient.mk (p : A × A).1 := fun _ ↦ rfl
  have hg₂app : ∀ p : koszulRel a s, g₂ p = Submodule.Quotient.mk (p : A × A).2 := fun _ ↦ rfl
  have hker : LinearMap.ker g₁ = LinearMap.ker g₂ := by
    ext p
    obtain ⟨⟨x, y⟩, hp⟩ := p
    rw [mem_koszulRel] at hp
    simp only [LinearMap.mem_ker, hg₁app, hg₂app, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      refine mul_left_cancel₀ hs ?_
      rw [← hp]
      ring
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      refine mul_left_cancel₀ ha ?_
      rw [hp]
      ring
  have hr₁ : LinearMap.range g₁ = LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {s}) a) := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      obtain ⟨⟨x, y⟩, hp⟩ := p
      rw [mem_koszulRel] at hp
      rw [LinearMap.mem_ker, hg₁app, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ⟨y, hp⟩)
    · intro z hz
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hz
      obtain ⟨y, hy⟩ := hz
      exact ⟨⟨(x, y), mem_koszulRel.2 hy⟩, rfl⟩
  have hr₂ : LinearMap.range g₂ = LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) s) := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      obtain ⟨⟨x, y⟩, hp⟩ := p
      rw [mem_koszulRel] at hp
      rw [LinearMap.mem_ker, hg₂app, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul]
      exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ⟨x, hp.symm⟩)
    · intro z hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hz
      obtain ⟨x, hx⟩ := hz
      exact ⟨⟨(x, y), mem_koszulRel.2 hx.symm⟩, rfl⟩
  have e : (LinearMap.range g₁) ≃ₗ[A] (LinearMap.range g₂) :=
    (LinearMap.quotKerEquivRange g₁).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivRange g₂))
  rw [chiKer, chiKer, ← hr₁, ← hr₂]
  exact LinearEquiv.length_eq e

end Koszul

section LocalKey

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The `b`-torsion of `A ⧸ q` vanishes for a prime `q` not containing `b`. -/
theorem chiKer_quotient_prime_eq_zero (q : Ideal A) [hq : q.IsPrime] {b : A} (hb : b ∉ q) :
    chiKer b (A ⧸ q) = 0 := by
  have hker : LinearMap.ker (LinearMap.lsmul A (A ⧸ q) b) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective q m
    rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero] at hm
    exact (Submodule.Quotient.mk_eq_zero q).2 ((hq.mem_or_mem hm).resolve_left hb)
  rw [chiKer, hker, Module.length_bot]

/-- If the only prime of `A` containing `I` is a maximal ideal `m`, then `A ⧸ I` is an Artinian
`A`-module. -/
theorem isArtinian_quotient_of_unique_prime (m : Ideal A) [m.IsMaximal] (I : Ideal A)
    (hIm : I ≤ m) (hI : ∀ P : Ideal A, P.IsPrime → I ≤ P → P = m) : IsArtinian A (A ⧸ I) := by
  have hkd : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun P hP ↦ ?_
    have hcp : (P.comap (Ideal.Quotient.mk I)).IsPrime := hP.comap _
    have hIle : I ≤ P.comap (Ideal.Quotient.mk I) := fun x hx ↦ by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact P.zero_mem
    have heq : P.comap (Ideal.Quotient.mk I) = m := hI _ hcp hIle
    have hPeq : P = m.map (Ideal.Quotient.mk I) := by
      rw [← heq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hfield : IsField (A ⧸ m) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 ‹m.IsMaximal›
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient, hPeq]
    exact (DoubleQuot.quotQuotEquivQuotOfLE hIm).toMulEquiv.isField hfield
  have _ : IsArtinianRing (A ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact isArtinian_of_surjective_algebraMap (R := A ⧸ I) (M := A ⧸ I)
    (Ideal.Quotient.mk_surjective (I := I))

/-- Fulton's local formula (*Intersection Theory*, A.3) in a Noetherian local domain `A` with
maximal ideal `m` in which there is no chain `⊥ < q' < q < m` of primes: the length of
`A ⧸ (a, s)` is the length of the `a`-torsion of `A ⧸ (s)` plus the sum, over the minimal primes
`q` of `(s)`, of `ord_q(s)` times the order of `a` on `A ⧸ q`. -/
theorem local_key [IsDomain A] (m : Ideal A) [m.IsMaximal]
    (hlocal : ∀ P : Ideal A, P.IsPrime → P ≤ m) (a s : A) (hs : s ≠ 0) (ham : a ∈ m) (hsm : s ∈ m)
    (hchain : ∀ q q' : Ideal A, q.IsPrime → q'.IsPrime → ⊥ < q' → q' < q → q < m → False)
    (hgood : ∀ q : Ideal A, q.IsPrime → a ∈ q → s ∈ q → q = m)
    (hmnot : m ∉ (Ideal.span {s}).minimalPrimes)
    (T : Finset (PrimeSpectrum A))
    (hT : ∀ q : PrimeSpectrum A, q ∈ T ↔ q.asIdeal ∈ (Ideal.span {s}).minimalPrimes) :
    Module.length A (A ⧸ (Ideal.span {s} ⊔ Ideal.span {a}))
      = chiKer a (A ⧸ Ideal.span {s})
        + ∑ q ∈ T, lengthAt q.asIdeal (A ⧸ Ideal.span {s}) * chiCoker a (A ⧸ q.asIdeal) := by
  have hart : IsArtinian A (A ⧸ (Ideal.span {s} ⊔ Ideal.span {a})) := by
    refine isArtinian_quotient_of_unique_prime m _ ?_ ?_
    · exact sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 hsm))
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 ham))
    · intro P hP hle
      exact hgood P hP (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
        (hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self s)))
  have hdim : ∀ q : Ideal A, q.IsPrime → Ideal.span {s} ≤ q →
      q ∈ (Ideal.span {s}).minimalPrimes ∨ q.IsMaximal := by
    intro q hq hsq
    by_cases hqm : q = m
    · exact Or.inr (hqm ▸ ‹m.IsMaximal›)
    · refine Or.inl ⟨⟨hq, hsq⟩, fun p hp hpq ↦ ?_⟩
      by_contra hcon
      have hplt : p < q := lt_of_le_of_ne hpq fun h ↦ hcon (h ▸ le_rfl)
      have hpbot : ⊥ < p := by
        refine bot_lt_iff_ne_bot.2 fun h ↦ hs ?_
        have hsp := hp.2 (Ideal.mem_span_singleton_self s)
        rw [h, Ideal.mem_bot] at hsp
        exact hsp
      exact hchain q p hq hp.1 hpbot hplt (lt_of_le_of_ne (hlocal q hq) hqm)
  have hdev := devissage a (Ideal.span {s}) hart T (fun q h ↦ (hT q).2 h) (fun q h ↦ (hT q).1 h)
    hdim (Ideal.span {s}) le_rfl
  have hzero : ∀ q ∈ T,
      lengthAt q.asIdeal (A ⧸ Ideal.span {s}) * chiKer a (A ⧸ q.asIdeal) = 0 := by
    intro q hq
    have hmin := (hT q).1 hq
    have hqm : q.asIdeal ≠ m := fun h ↦ hmnot (h ▸ hmin)
    have hanq : a ∉ q.asIdeal := fun h ↦
      hqm (hgood _ q.isPrime h (hmin.1.2 (Ideal.mem_span_singleton_self s)))
    rw [chiKer_quotient_prime_eq_zero q.asIdeal hanq, mul_zero]
  rw [Finset.sum_eq_zero hzero, add_zero] at hdev
  rw [← chiCoker_quotient]
  exact hdev

end LocalKey

section Assembly

/-- Iterated localization: the localization of `D_Q` at a prime `P` is the localization of `D`
at the contraction of `P`, so the orders of vanishing of an element of `D` agree. -/
theorem ord_comap_eq {D : Type*} [CommRing D] (Q : Ideal D) [Q.IsPrime]
    (P : Ideal (Localization.AtPrime Q)) [P.IsPrime] (x : D) :
    Ring.ord (Localization.AtPrime P)
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)
          (algebraMap D (Localization.AtPrime Q) x))
      = Ring.ord (Localization.AtPrime (P.comap (algebraMap D (Localization.AtPrime Q))))
          (algebraMap D _ x) := by
  have e : Localization.AtPrime (P.comap (algebraMap D (Localization.AtPrime Q)))
      ≃ₐ[D] Localization.AtPrime P :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl P
  rw [← IsScalarTower.algebraMap_apply D (Localization.AtPrime Q) (Localization.AtPrime P) x,
    ← e.commutes x]
  exact ord_ringEquiv e.toRingEquiv _

/-- Changing the ideal in an order of vanishing on a quotient ring. -/
theorem ord_quotient_congr {A : Type*} [CommRing A] {J J' : Ideal A} (h : J = J') (x : A) :
    Ring.ord (A ⧸ J) (Ideal.Quotient.mk J x) = Ring.ord (A ⧸ J') (Ideal.Quotient.mk J' x) := by
  subst h
  rfl

open Classical in
/-- One half of Fulton's symmetric identity, computed in the local ring `D_Q`: the sum over the
primes `q < Q` containing `s` of `ord_q(s) · ord_Q(a on V(q))`, plus the length of the
`a`-torsion of `D_Q ⧸ (s)`, is the length of `D_Q ⧸ (a, s)`. -/
theorem finsum_ord_add_chiKer {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    (Q : Ideal D) [Q.IsPrime] (a s : D) (hs : s ≠ 0) (haQ : a ∈ Q) (hsQ : s ∈ Q)
    (hchain : ∀ q q' : Ideal D, q.IsPrime → q'.IsPrime → ⊥ < q' → q' < q → q < Q → False)
    (hgood : ∀ q : Ideal D, q.IsPrime → q ≤ Q → a ∈ q → s ∈ q → q = Q)
    (q₀ : Ideal D) (hq₀p : q₀.IsPrime) (hq₀b : ⊥ < q₀) (hq₀Q : q₀ < Q) :
    (∑ᶠ q : PrimeSpectrum D, (if q.asIdeal < Q ∧ s ∈ q.asIdeal then
          Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ s) *
            Ring.ord (Localization.AtPrime Q ⧸
                q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
              (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) a))
        else 0))
      + chiKer (algebraMap D (Localization.AtPrime Q) a)
          (Localization.AtPrime Q ⧸ Ideal.span {algebraMap D (Localization.AtPrime Q) s})
      = Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          (Ideal.span {algebraMap D (Localization.AtPrime Q) s} ⊔
            Ideal.span {algebraMap D (Localization.AtPrime Q) a}))
      ∧ Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          (Ideal.span {algebraMap D (Localization.AtPrime Q) s} ⊔
            Ideal.span {algebraMap D (Localization.AtPrime Q) a})) ≠ ⊤ := by
  have hnzd : Q.primeCompl ≤ nonZeroDivisors D := Q.primeCompl_le_nonZeroDivisors
  have hdom : IsDomain (Localization.AtPrime Q) := IsLocalization.isDomain_localization hnzd
  have hnoeth : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hinj : Function.Injective (algebraMap D (Localization.AtPrime Q)) :=
    IsLocalization.injective _ hnzd
  have hmax : Q.map (algebraMap D (Localization.AtPrime Q))
      = IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hcomapmax : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap D (Localization.AtPrime Q)) = Q := Localization.AtPrime.under_maximalIdeal
  have hmapcomap : ∀ J : Ideal (Localization.AtPrime Q),
      (J.comap (algebraMap D (Localization.AtPrime Q))).map
        (algebraMap D (Localization.AtPrime Q)) = J :=
    fun J ↦ IsLocalization.map_under Q.primeCompl _ J
  have hrefl : ∀ J K : Ideal (Localization.AtPrime Q),
      J.comap (algebraMap D (Localization.AtPrime Q))
        ≤ K.comap (algebraMap D (Localization.AtPrime Q)) → J ≤ K := by
    intro J K h
    rw [← hmapcomap J, ← hmapcomap K]
    exact Ideal.map_mono h
  have hltcomap : ∀ J K : Ideal (Localization.AtPrime Q), J < K →
      J.comap (algebraMap D (Localization.AtPrime Q))
        < K.comap (algebraMap D (Localization.AtPrime Q)) := by
    intro J K h
    refine lt_of_le_of_ne (Ideal.comap_mono h.le) fun he ↦ h.ne ?_
    rw [← hmapcomap J, ← hmapcomap K, he]
  have hcomaplt : ∀ P : Ideal (Localization.AtPrime Q),
      P < IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
      P.comap (algebraMap D (Localization.AtPrime Q)) < Q := by
    intro P h
    have h2 := hltcomap _ _ h
    rwa [hcomapmax] at h2
  have hcomaple : ∀ P : Ideal (Localization.AtPrime Q),
      P ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
      P.comap (algebraMap D (Localization.AtPrime Q)) ≤ Q := by
    intro P h
    have h2 := Ideal.comap_mono (f := algebraMap D (Localization.AtPrime Q)) h
    rwa [hcomapmax] at h2
  have hdisj : ∀ q : Ideal D, q ≤ Q → Disjoint (Q.primeCompl : Set D) (q : Set D) :=
    fun q hqQ ↦ Set.disjoint_left.2 fun x hx hx' ↦ hx (hqQ hx')
  have hprimemap : ∀ q : Ideal D, q.IsPrime → q ≤ Q →
      (q.map (algebraMap D (Localization.AtPrime Q))).IsPrime := fun q hq hqQ ↦
    IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ q hq (hdisj q hqQ)
  have hcomapmapq : ∀ q : Ideal D, q.IsPrime → q ≤ Q →
      (q.map (algebraMap D (Localization.AtPrime Q))).comap
        (algebraMap D (Localization.AtPrime Q)) = q := fun q hq hqQ ↦
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl _ hq (hdisj q hqQ)
  have hlocalA : ∀ P : Ideal (Localization.AtPrime Q), P.IsPrime →
      P ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    fun _ hP ↦ IsLocalRing.le_maximalIdeal hP.ne_top
  have hbotcomap : (⊥ : Ideal (Localization.AtPrime Q)).comap
      (algebraMap D (Localization.AtPrime Q)) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hchainA : ∀ P P' : Ideal (Localization.AtPrime Q), P.IsPrime → P'.IsPrime → ⊥ < P' →
      P' < P → P < IsLocalRing.maximalIdeal (Localization.AtPrime Q) → False := by
    intro P P' hP hP' hbot hlt hltm
    refine hchain (P.comap (algebraMap D (Localization.AtPrime Q)))
      (P'.comap (algebraMap D (Localization.AtPrime Q))) (hP.comap _) (hP'.comap _) ?_
      (hltcomap _ _ hlt) ?_
    · rw [← hbotcomap]; exact hltcomap _ _ hbot
    · exact hcomaplt _ hltm
  have hgoodA : ∀ P : Ideal (Localization.AtPrime Q), P.IsPrime →
      algebraMap D (Localization.AtPrime Q) a ∈ P →
      algebraMap D (Localization.AtPrime Q) s ∈ P →
      P = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro P hP haP hsP
    have h1 : P.comap (algebraMap D (Localization.AtPrime Q)) = Q :=
      hgood _ (hP.comap _) (hcomaple _ (hlocalA P hP)) haP hsP
    rw [← hmapcomap P, h1, hmax]
  have hs' : algebraMap D (Localization.AtPrime Q) s ≠ 0 := fun h ↦ hs (hinj (by rw [h, map_zero]))
  have ham' : algebraMap D (Localization.AtPrime Q) a
      ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← hmax]; exact Ideal.mem_map_of_mem _ haQ
  have hsm' : algebraMap D (Localization.AtPrime Q) s
      ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← hmax]; exact Ideal.mem_map_of_mem _ hsQ
  -- Krull's principal ideal theorem rules out that the maximal ideal is minimal over `(s)`
  have hP₀ : (q₀.map (algebraMap D (Localization.AtPrime Q))).IsPrime :=
    hprimemap q₀ hq₀p hq₀Q.le
  have hP₀lt : q₀.map (algebraMap D (Localization.AtPrime Q))
      < IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    refine lt_of_le_of_ne (by rw [← hmax]; exact Ideal.map_mono hq₀Q.le) fun h ↦ hq₀Q.ne ?_
    rw [← hcomapmapq _ hq₀p hq₀Q.le, h, hcomapmax]
  have hP₀bot : ⊥ < q₀.map (algebraMap D (Localization.AtPrime Q)) := by
    refine bot_lt_iff_ne_bot.2 fun h ↦ hq₀b.ne ?_
    rw [← hcomapmapq _ hq₀p hq₀Q.le, h, hbotcomap]
  have hmnotA : IsLocalRing.maximalIdeal (Localization.AtPrime Q)
      ∉ (Ideal.span {algebraMap D (Localization.AtPrime Q) s}).minimalPrimes := by
    intro hcon
    have hprin : Submodule.IsPrincipal
        (Ideal.span {algebraMap D (Localization.AtPrime Q) s}) := ⟨⟨_, rfl⟩⟩
    have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hcon
    have h1 : (q₀.map (algebraMap D (Localization.AtPrime Q))).height < (1 : ℕ) :=
      Ideal.height_le_iff.1 hh _ hP₀ hP₀lt
    have h1' : (q₀.map (algebraMap D (Localization.AtPrime Q))).height ≤ (0 : ℕ) := by
      rw [Nat.cast_one] at h1
      rw [Nat.cast_zero]
      exact le_of_eq (Order.lt_one_iff.1 h1)
    have h2 := Ideal.height_le_iff.1 h1' ⊥ Ideal.isPrime_bot hP₀bot
    exact absurd h2 (by simp)
  -- the set of minimal primes of `(s)` in the local ring
  have hminiff : ∀ P : Ideal (Localization.AtPrime Q), P.IsPrime →
      (P ∈ (Ideal.span {algebraMap D (Localization.AtPrime Q) s}).minimalPrimes ↔
        (P < IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∧
          algebraMap D (Localization.AtPrime Q) s ∈ P)) := by
    intro P hP
    constructor
    · intro hmin
      exact ⟨lt_of_le_of_ne (hlocalA P hP) fun h ↦ hmnotA (h ▸ hmin),
        hmin.1.2 (Ideal.mem_span_singleton_self _)⟩
    · rintro ⟨hPm, hsP⟩
      refine ⟨⟨hP, Ideal.span_le.2 (Set.singleton_subset_iff.2 hsP)⟩, fun p hp hpP ↦ ?_⟩
      by_contra hcon
      have hplt : p < P := lt_of_le_of_ne hpP fun h ↦ hcon (h ▸ le_rfl)
      have hpbot : ⊥ < p := by
        refine bot_lt_iff_ne_bot.2 fun h ↦ hs' ?_
        have hsp := hp.2 (Ideal.mem_span_singleton_self _)
        rw [h, Ideal.mem_bot] at hsp
        exact hsp
      exact hchainA P p hP hp.1 hpbot hplt hPm
  have hfin : (PrimeSpectrum.asIdeal ⁻¹'
      (Ideal.span {algebraMap D (Localization.AtPrime Q) s}).minimalPrimes).Finite :=
    Set.Finite.preimage (fun x _ y _ h ↦ PrimeSpectrum.ext h)
      (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)
  have hT : ∀ P : PrimeSpectrum (Localization.AtPrime Q),
      P ∈ hfin.toFinset ↔
        P.asIdeal ∈ (Ideal.span {algebraMap D (Localization.AtPrime Q) s}).minimalPrimes :=
    fun P ↦ Set.Finite.mem_toFinset hfin
  have hkey := local_key (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) hlocalA
    (algebraMap D (Localization.AtPrime Q) a) (algebraMap D (Localization.AtPrime Q) s)
    hs' ham' hsm' hchainA hgoodA hmnotA hfin.toFinset hT
  have hlesup : Ideal.span {algebraMap D (Localization.AtPrime Q) s} ⊔
      Ideal.span {algebraMap D (Localization.AtPrime Q) a}
      ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    sup_le (Ideal.span_le.2 (Set.singleton_subset_iff.2 hsm'))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 ham'))
  have hartsup := isArtinian_quotient_of_unique_prime
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) _ hlesup fun P hP hPle ↦
      hgoodA P hP (hPle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
        (hPle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)))
  refine ⟨?_, Module.length_ne_top⟩
  rw [hkey, add_comm (chiKer _ _)]
  congr 1
  -- translate the `finsum` over `PrimeSpectrum D` into the sum over the local minimal primes
  have hmapinj : ∀ P ∈ hfin.toFinset, ∀ P' ∈ hfin.toFinset,
      (⟨P.asIdeal.comap (algebraMap D (Localization.AtPrime Q)), P.isPrime.comap _⟩ :
        PrimeSpectrum D)
        = ⟨P'.asIdeal.comap (algebraMap D (Localization.AtPrime Q)), P'.isPrime.comap _⟩ →
        P = P' := by
    intro P _ P' _ h
    have h' : P.asIdeal.comap (algebraMap D (Localization.AtPrime Q))
        = P'.asIdeal.comap (algebraMap D (Localization.AtPrime Q)) :=
      congrArg PrimeSpectrum.asIdeal h
    exact PrimeSpectrum.ext (le_antisymm (hrefl _ _ h'.le) (hrefl _ _ h'.ge))
  have hsupp : (Function.support fun q : PrimeSpectrum D ↦
      (if q.asIdeal < Q ∧ s ∈ q.asIdeal then
          Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ s) *
            Ring.ord (Localization.AtPrime Q ⧸
                q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
              (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) a))
        else 0))
      ⊆ ↑(hfin.toFinset.image fun P : PrimeSpectrum (Localization.AtPrime Q) ↦
          (⟨P.asIdeal.comap (algebraMap D (Localization.AtPrime Q)), P.isPrime.comap _⟩ :
            PrimeSpectrum D)) := by
    intro q hq
    by_cases hcond : q.asIdeal < Q ∧ s ∈ q.asIdeal
    · have hPq : (q.asIdeal.map (algebraMap D (Localization.AtPrime Q))).IsPrime :=
        hprimemap _ q.isPrime hcond.1.le
      refine Finset.mem_coe.2 (Finset.mem_image.2
        ⟨⟨q.asIdeal.map (algebraMap D (Localization.AtPrime Q)), hPq⟩, ?_, ?_⟩)
      · refine (hT _).2 ((hminiff _ hPq).2 ⟨?_, Ideal.mem_map_of_mem _ hcond.2⟩)
        refine lt_of_le_of_ne (by rw [← hmax]; exact Ideal.map_mono hcond.1.le) fun h ↦
          hcond.1.ne ?_
        rw [← hcomapmapq _ q.isPrime hcond.1.le, h, hcomapmax]
      · exact PrimeSpectrum.ext (hcomapmapq _ q.isPrime hcond.1.le)
    · exact absurd (if_neg hcond) (Function.mem_support.1 hq)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_image hmapinj]
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  have hmin := (hT P).1 hP
  obtain ⟨hPm, hsP⟩ := (hminiff _ P.isPrime).1 hmin
  have hcond : P.asIdeal.comap (algebraMap D (Localization.AtPrime Q)) < Q ∧
      s ∈ P.asIdeal.comap (algebraMap D (Localization.AtPrime Q)) := by
    exact ⟨hcomaplt _ hPm, hsP⟩
  rw [if_pos hcond, ord_quotient_congr (hmapcomap P.asIdeal)
      (algebraMap D (Localization.AtPrime Q) a),
    ← chiCoker_quotient_ord, ← ord_comap_eq Q P.asIdeal s, ← lengthAt_quotient_span]

/-- The order of vanishing of a unit is zero. -/
theorem ord_eq_zero_of_isUnit {R : Type*} [CommRing R] {x : R} (hx : IsUnit x) :
    Ring.ord R x = 0 := by
  have h : Ideal.span {x} = ⊤ := Ideal.span_singleton_eq_top.2 hx
  have hsub : Subsingleton (R ⧸ (⊤ : Ideal R)) := by
    constructor
    intro y z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.eq _).2 Submodule.mem_top
  rw [Ring.ord, h]
  exact Module.length_eq_zero

end Assembly


end LocalOrdSymmetry

open Classical in
/-- Fulton's symmetric local identity (Intersection Theory, Appendix A.2–A.3). -/
def VectorBundle.LocalOrdSymmetry : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] (Q : Ideal D) [Q.IsPrime]
    (a s : D), a ≠ 0 → s ≠ 0 →
    (∀ q q' : Ideal D, q.IsPrime → q'.IsPrime → ⊥ < q' → q' < q → q < Q → False) →
    (∀ q : Ideal D, q.IsPrime → q ≤ Q → a ∈ q → s ∈ q → q = Q) →
    ∑ᶠ q : PrimeSpectrum D,
        (if q.asIdeal < Q ∧ s ∈ q.asIdeal then
          Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ s) *
            Ring.ord (Localization.AtPrime Q ⧸
                q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
              (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) a))
        else 0) =
      ∑ᶠ q : PrimeSpectrum D,
        (if q.asIdeal < Q ∧ a ∈ q.asIdeal then
          Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap D _ a) *
            Ring.ord (Localization.AtPrime Q ⧸
                q.asIdeal.map (algebraMap D (Localization.AtPrime Q)))
              (Ideal.Quotient.mk _ (algebraMap D (Localization.AtPrime Q) s))
        else 0)

open Classical in
/-- Fulton's symmetric local identity, *Intersection Theory*, Appendix A.2–A.3. -/
theorem VectorBundle.localOrdSymmetry : VectorBundle.LocalOrdSymmetry.{u} := by
  intro D _ _ _ Q _ a s ha hs hchain hgood
  have hunit : ∀ x : D, x ∉ Q → ∀ J : Ideal (Localization.AtPrime Q),
      Ring.ord (Localization.AtPrime Q ⧸ J)
        (Ideal.Quotient.mk J (algebraMap D (Localization.AtPrime Q) x)) = 0 := fun x hx J ↦
    LocalOrdSymmetry.ord_eq_zero_of_isUnit
      (((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q x).2 hx).map
        (Ideal.Quotient.mk J))
  by_cases hsQ : s ∈ Q
  · by_cases haQ : a ∈ Q
    · by_cases hq₀ : ∃ q₀ : Ideal D, q₀.IsPrime ∧ ⊥ < q₀ ∧ q₀ < Q
      · obtain ⟨q₀, hq₀p, hq₀b, hq₀Q⟩ := hq₀
        obtain ⟨h1e, h1n⟩ :=
          LocalOrdSymmetry.finsum_ord_add_chiKer Q a s hs haQ hsQ hchain hgood q₀ hq₀p hq₀b hq₀Q
        obtain ⟨h2e, h2n⟩ :=
          LocalOrdSymmetry.finsum_ord_add_chiKer Q s a ha hsQ haQ hchain
            (fun q hq hqQ h h' ↦ hgood q hq hqQ h' h) q₀ hq₀p hq₀b hq₀Q
        have hinj : Function.Injective (algebraMap D (Localization.AtPrime Q)) :=
          IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors
        have hdom : IsDomain (Localization.AtPrime Q) :=
          IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
        have ha' : algebraMap D (Localization.AtPrime Q) a ≠ 0 := fun h ↦
          ha (hinj (by rw [h, map_zero]))
        have hs' : algebraMap D (Localization.AtPrime Q) s ≠ 0 := fun h ↦
          hs (hinj (by rw [h, map_zero]))
        rw [LocalOrdSymmetry.chiKer_quotient_comm (algebraMap D (Localization.AtPrime Q) a)
          (algebraMap D (Localization.AtPrime Q) s) ha' hs'] at h1e
        have hL : Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
            (Ideal.span {algebraMap D (Localization.AtPrime Q) s} ⊔
              Ideal.span {algebraMap D (Localization.AtPrime Q) a}))
            = Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
            (Ideal.span {algebraMap D (Localization.AtPrime Q) a} ⊔
              Ideal.span {algebraMap D (Localization.AtPrime Q) s})) := by
          rw [sup_comm]
        rw [hL] at h1e
        have hK : LocalOrdSymmetry.chiKer (algebraMap D (Localization.AtPrime Q) s)
            (Localization.AtPrime Q ⧸
              Ideal.span {algebraMap D (Localization.AtPrime Q) a}) ≠ ⊤ :=
          fun h ↦ h2n (by rw [← h2e, h, add_top])
        exact LocalOrdSymmetry.enat_add_right_cancel hK (h1e.trans h2e.symm)
      · have hLz : ∀ q : PrimeSpectrum D, ¬(q.asIdeal < Q ∧ s ∈ q.asIdeal) := by
          rintro q ⟨hlt, hmem⟩
          refine hq₀ ⟨q.asIdeal, q.isPrime, bot_lt_iff_ne_bot.2 fun h ↦ hs ?_, hlt⟩
          rw [h, Ideal.mem_bot] at hmem
          exact hmem
        have hRz : ∀ q : PrimeSpectrum D, ¬(q.asIdeal < Q ∧ a ∈ q.asIdeal) := by
          rintro q ⟨hlt, hmem⟩
          refine hq₀ ⟨q.asIdeal, q.isPrime, bot_lt_iff_ne_bot.2 fun h ↦ ha ?_, hlt⟩
          rw [h, Ideal.mem_bot] at hmem
          exact hmem
        simp only [hLz, hRz, if_false, finsum_zero]
    · have hRz : ∀ q : PrimeSpectrum D, ¬(q.asIdeal < Q ∧ a ∈ q.asIdeal) :=
        fun q h ↦ haQ (h.1.le h.2)
      simp only [hRz, if_false, hunit a haQ, mul_zero, ite_self, finsum_zero]
  · have hLz : ∀ q : PrimeSpectrum D, ¬(q.asIdeal < Q ∧ s ∈ q.asIdeal) :=
      fun q h ↦ hsQ (h.1.le h.2)
    simp only [hLz, if_false, hunit s hsQ, mul_zero, ite_self, finsum_zero]


end GromovWitten.AlgebraicGeometry.IntersectionTheory
