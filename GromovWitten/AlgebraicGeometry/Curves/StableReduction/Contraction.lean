/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.StableReduction.ArithmeticSurface

/-!
# Geometric contractions and termination of the surface minimal-model program

A contraction in this file contains a genuine morphism of models.  It also contains open
subschemes of its source and target, an isomorphism between them, and carrier equalities saying
that these opens are precisely the complements of the contracted loci.  Thus the assertion that
the morphism is an isomorphism away from its exceptional locus is not represented by a Boolean
or by unrelated numerical data.

An exceptional contraction ties its source locus to an actual irreducible component of the
scheme-theoretic special fibre and strictly decreases the number of such components.  The last
section uses that decrease to prove termination of any supplied geometric contraction engine.
The engine is a construction interface: its output at every nonminimal surface is an actual
regular target model and an actual contraction.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves.StableReduction

universe u

noncomputable section

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The carrier of a special-fibre component inside the total space of a model. -/
def ArithmeticSurface.componentCarrierInTotal (M : Model R K C toK)
    (i : ArithmeticSurface.Component M) : Set M.total :=
  specialFiberι R M.toBase '' (i : Set M.specialFiberScheme)

/-- A proper birational morphism of models which is an isomorphism off displayed closed loci.

The two open immersions and their carrier equalities make the complement isomorphism fully
scheme-theoretic.  `contracts` records that the exceptional source locus maps into the target
locus. -/
structure GeometricContraction (M N : Model R K C toK) where
  modification : ModelModification M N
  sourceLocus : Set M.total
  targetLocus : Set N.total
  sourceLocus_isClosed : IsClosed sourceLocus
  targetLocus_isClosed : IsClosed targetLocus
  sourceComplement : Scheme.{u}
  targetComplement : Scheme.{u}
  sourceOpen : sourceComplement ⟶ M.total
  targetOpen : targetComplement ⟶ N.total
  sourceOpen_isOpen : IsOpenImmersion sourceOpen
  targetOpen_isOpen : IsOpenImmersion targetOpen
  sourceOpen_range : Set.range sourceOpen = sourceLocusᶜ
  targetOpen_range : Set.range targetOpen = targetLocusᶜ
  complementIso : sourceComplement ≅ targetComplement
  complement_commutes : complementIso.hom ≫ targetOpen =
    sourceOpen ≫ modification.hom.hom
  contracts : Set.MapsTo modification.hom.hom sourceLocus targetLocus

namespace GeometricContraction

variable {M N : Model R K C toK} (c : GeometricContraction M N)

/-- The underlying contraction map of total schemes. -/
abbrev hom : M.total ⟶ N.total := c.modification.hom.hom

/-- The underlying model morphism is generically an isomorphism. -/
instance generic_isIso :
    IsIso (Model.baseChangeHom (R := R) (K := K)
      c.hom c.modification.hom.over_base) :=
  c.modification.genericIsIso

/-- A point outside the exceptional locus is represented by the displayed source open. -/
theorem exists_sourceComplement_point {x : M.total} (hx : x ∉ c.sourceLocus) :
    ∃ u : c.sourceComplement, c.sourceOpen u = x := by
  rw [← Set.mem_range, c.sourceOpen_range]
  exact hx

/-- A point outside the target locus is represented by the displayed target open. -/
theorem exists_targetComplement_point {y : N.total} (hy : y ∉ c.targetLocus) :
    ∃ v : c.targetComplement, c.targetOpen v = y := by
  rw [← Set.mem_range, c.targetOpen_range]
  exact hy

/-- On complement points the contraction is exactly the displayed scheme isomorphism. -/
theorem hom_sourceOpen (u : c.sourceComplement) :
    c.hom (c.sourceOpen u) = c.targetOpen (c.complementIso.hom u) := by
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply,
    ← _root_.AlgebraicGeometry.Scheme.Hom.comp_apply, c.complement_commutes]

end GeometricContraction

/-- Compatibility of a contraction with every selected finite extension of DVRs.  The loci on
the pulled-back total spaces are the inverse images of the original loci and the new contraction
map is the canonical pullback of the old one. -/
structure GeometricContraction.BaseChangeStable {M N : Model R K C toK}
    (c : GeometricContraction M N) : Type (u + 1) where
  pullback : ∀ (E : FiniteDVRExtension R K),
    GeometricContraction (Model.baseChangeObj E M) (Model.baseChangeObj E N)
  hom_eq : ∀ (E : FiniteDVRExtension R K),
    (pullback E).modification.hom = Model.baseChangeMap E c.modification.hom
  sourceLocus_eq : ∀ (E : FiniteDVRExtension R K),
    (pullback E).sourceLocus =
      (CategoryTheory.Limits.pullback.fst M.toBase
        (FiniteDVRExtension.baseSpecMap R K E)) ⁻¹'
        c.sourceLocus
  targetLocus_eq : ∀ (E : FiniteDVRExtension R K),
    (pullback E).targetLocus =
      (CategoryTheory.Limits.pullback.fst N.toBase
        (FiniteDVRExtension.baseSpecMap R K E)) ⁻¹'
        c.targetLocus

/-- Contraction of an actual exceptional special-fibre component.  The target remains a regular
proper arithmetic surface, carries intersection data on its actual special-fibre components,
and has strictly fewer components. -/
structure ExceptionalContraction {M : Model R K C toK}
    (sourceSurface : ArithmeticSurface M)
    (sourceData : ArithmeticSurface.SpecialFiberIntersectionData M)
    (exceptional : ArithmeticSurface.Component M)
    (N : Model R K C toK) where
  exceptional_signature : sourceData.IsExceptionalComponent exceptional
  contraction : GeometricContraction M N
  sourceLocus_eq : contraction.sourceLocus =
    ArithmeticSurface.componentCarrierInTotal M exceptional
  target_is_point : ∃ center : N.total, contraction.targetLocus = {center}
  targetSurface : ArithmeticSurface N
  targetData : ArithmeticSurface.SpecialFiberIntersectionData N
  componentCard_lt :
    @Fintype.card (ArithmeticSurface.Component N) targetData.componentFintype <
      @Fintype.card (ArithmeticSurface.Component M) sourceData.componentFintype

namespace ExceptionalContraction

variable {M N : Model R K C toK}
variable {sourceSurface : ArithmeticSurface M}
variable {sourceData : ArithmeticSurface.SpecialFiberIntersectionData M}
variable {exceptional : ArithmeticSurface.Component M}

/-- Every point of the exceptional component maps to the unique contraction centre. -/
theorem maps_exceptional_to_center
    (c : ExceptionalContraction sourceSurface sourceData exceptional N) :
    ∃ center : N.total, ∀ x : M.specialFiberScheme, x ∈ (exceptional : Set _ ) →
      c.contraction.hom (specialFiberι R M.toBase x) = center := by
  obtain ⟨center, hcenter⟩ := c.target_is_point
  refine ⟨center, ?_⟩
  intro x hx
  have hsource : specialFiberι R M.toBase x ∈ c.contraction.sourceLocus := by
    rw [c.sourceLocus_eq]
    exact ⟨x, hx, rfl⟩
  have htarget := c.contraction.contracts hsource
  rw [hcenter, Set.mem_singleton_iff] at htarget
  exact htarget

end ExceptionalContraction

/-- A geometric contraction engine for regular arithmetic surfaces.  At each nonminimal input it
constructs a regular proper target and a contraction of an exceptional component. -/
structure SurfaceContractionEngine : Type (u + 1) where
  contract : ∀ (M : Model R K C toK) (surface : ArithmeticSurface M)
    (data : ArithmeticSurface.SpecialFiberIntersectionData M),
    ¬ data.IsRelativelyMinimal →
      Σ exceptional : ArithmeticSurface.Component M,
        Σ N : Model R K C toK,
          ExceptionalContraction surface data exceptional N

/-- A finite chain of actual exceptional contractions. -/
inductive ContractionChain :
    (M N : Model R K C toK) → Type (u + 1)
  | refl (M : Model R K C toK) : ContractionChain M M
  | step {M N P : Model R K C toK}
      {surface : ArithmeticSurface M}
      {data : ArithmeticSurface.SpecialFiberIntersectionData M}
      {exceptional : ArithmeticSurface.Component M}
      (head : ExceptionalContraction surface data exceptional N)
      (tail : ContractionChain N P) : ContractionChain M P

namespace ContractionChain

variable {M N P Q : Model R K C toK}

/-- Number of exceptional contractions in a contraction chain. -/
def length {M N : Model R K C toK} : ContractionChain M N → ℕ
  | .refl _ => 0
  | .step _ tail => tail.length + 1

/-- Concatenation of finite contraction chains. -/
def comp {M N P : Model R K C toK} :
    ContractionChain M N → ContractionChain N P → ContractionChain M P
  | .refl _, tail => tail
  | .step head tail, rest => .step head (tail.comp rest)

@[simp]
theorem comp_refl (chain : ContractionChain M N) :
    chain.comp (.refl N) = chain := by
  induction chain with
  | refl => rfl
  | step head tail ih => simp [comp, ih]

theorem comp_assoc (first : ContractionChain M N) (second : ContractionChain N P)
    (third : ContractionChain P Q) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  induction first with
  | refl => rfl
  | step head tail ih => simp [comp, ih]

theorem length_comp (first : ContractionChain M N) (second : ContractionChain N P) :
    (first.comp second).length = first.length + second.length := by
  induction first with
  | refl => simp [comp, length]
  | step head tail ih => simp [comp, length, ih, Nat.add_assoc, Nat.add_comm]

/-- The proper generic-isomorphism modification obtained by composing every contraction in a
chain. -/
def modification {M N : Model R K C toK} :
    ContractionChain M N → ModelModification M N
  | .refl M => ModelModification.refl M
  | .step head tail => head.contraction.modification.comp tail.modification

@[simp]
theorem modification_refl (M : Model R K C toK) :
    (ContractionChain.refl M).modification = ModelModification.refl M := rfl

end ContractionChain

/-- A relatively minimal regular proper model obtained by contracting actual exceptional
components. -/
structure RelativelyMinimalModel : Type (u + 1) where
  model : Model R K C toK
  surface : ArithmeticSurface model
  intersectionData : ArithmeticSurface.SpecialFiberIntersectionData model
  minimal : intersectionData.IsRelativelyMinimal

/-- A relatively minimal model together with the finite contraction chain which produces it. -/
structure Minimalization (M : Model R K C toK) extends
    RelativelyMinimalModel (R := R) (K := K) (C := C) (toK := toK) where
  chain : ContractionChain M model

/-- A regular-resolution supplier.  Its output is an actual proper modification whose source is
regular, together with intersection data on the source's genuine special-fibre components. -/
structure SurfaceResolutionEngine : Type (u + 1) where
  resolve : ∀ (M : Model R K C toK), M.IsProper →
    Σ resolution : RegularResolution M,
      ArithmeticSurface.SpecialFiberIntersectionData resolution.resolved

/-- Resolution followed by a finite chain of exceptional contractions. -/
structure ResolvedMinimalization (M : Model R K C toK) : Type (u + 1) where
  resolution : RegularResolution M
  minimalization : Minimalization resolution.resolved

namespace SurfaceContractionEngine

/-- Strict component decrease makes every geometric contraction engine produce a finite chain
ending at a relatively minimal regular proper model. -/
theorem exists_minimalization
    (engine : SurfaceContractionEngine (R := R) (K := K) (C := C) (toK := toK))
    (M : Model R K C toK)
    (surface : ArithmeticSurface M)
    (data : ArithmeticSurface.SpecialFiberIntersectionData M) :
    Nonempty (Minimalization M) := by
  classical
  let _ := data.componentFintype
  generalize hmeasure : Fintype.card (ArithmeticSurface.Component M) = measure
  induction measure using Nat.strong_induction_on generalizing M surface data with
  | h measure ih =>
      by_cases hminimal : data.IsRelativelyMinimal
      · exact ⟨⟨⟨M, surface, data, hminimal⟩, .refl M⟩⟩
      · obtain ⟨exceptional, N, contraction⟩ :=
          SurfaceContractionEngine.contract engine M surface data hminimal
        let _ := contraction.targetData.componentFintype
        obtain ⟨tail⟩ := ih (Fintype.card (ArithmeticSurface.Component N))
          (by rw [← hmeasure]; exact contraction.componentCard_lt)
          N contraction.targetSurface contraction.targetData rfl
        exact ⟨⟨tail.toRelativelyMinimalModel, .step contraction tail.chain⟩⟩

/-- Forgetting the contraction chain gives existence of a relatively minimal model. -/
theorem exists_relativelyMinimalModel
    (engine : SurfaceContractionEngine (R := R) (K := K) (C := C) (toK := toK))
    (M : Model R K C toK)
    (surface : ArithmeticSurface M)
    (data : ArithmeticSurface.SpecialFiberIntersectionData M) :
    Nonempty (RelativelyMinimalModel (R := R) (K := K) (C := C) (toK := toK)) := by
  obtain ⟨result⟩ := engine.exists_minimalization M surface data
  exact ⟨result.toRelativelyMinimalModel⟩

end SurfaceContractionEngine

namespace SurfaceResolutionEngine

/-- Resolving a proper model and running the contraction engine constructs a minimalization
connected to the original model by an actual resolution modification and contraction chain. -/
theorem minimalize (resolver : SurfaceResolutionEngine (R := R) (K := K) (C := C) (toK := toK))
    (contractor : SurfaceContractionEngine (R := R) (K := K) (C := C) (toK := toK))
    (M : Model R K C toK) (proper : M.IsProper) :
    Nonempty (ResolvedMinimalization M) := by
  obtain ⟨resolution, data⟩ := resolver.resolve M proper
  let surface : ArithmeticSurface resolution.resolved :=
    ⟨resolution.resolvedProper, resolution.resolvedRegular⟩
  exact (contractor.exists_minimalization resolution.resolved surface data).map
    fun minimalization ↦ ⟨resolution, minimalization⟩

end SurfaceResolutionEngine

end

end GromovWitten.AlgebraicGeometry.Curves.StableReduction
