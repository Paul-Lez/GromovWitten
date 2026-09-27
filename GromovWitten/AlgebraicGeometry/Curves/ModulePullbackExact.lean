import GromovWitten.AlgebraicGeometry.Curves.ModuleBaseChange
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped ZeroObject

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-- Flat extension of scalars preserves homology of module short complexes. -/
lemma moduleExtendScalars_preservesHomology_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    (ModuleCat.extendScalars.{u,u,u} f).PreservesHomology := by
  let hlim : PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let hcol : PreservesFiniteColimits (ModuleCat.extendScalars.{u,u,u} f) := by
    exact inferInstance
  exact {
    preservesKernels := fun {X Y} q =>
      (hlim.preservesFiniteLimits WalkingParallelPair).preservesLimit
    preservesCokernels := fun {X Y} q =>
      (hcol.preservesFiniteColimits WalkingParallelPair).preservesColimit }

/- The finite-limit argument above is the categorical affine shadow of the
stalkwise argument needed for scheme pullback.  The colimit half is supplied
by the fact that extension of scalars is a left adjoint. -/

/-- In the affine flat case, extension of scalars carries monomorphisms to
monomorphisms. -/
lemma moduleExtendScalars_preservesMonomorphisms_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    : Functor.PreservesMonomorphisms (ModuleCat.extendScalars.{u,u,u} f) := by
  let hlim : PreservesFiniteLimits (ModuleCat.extendScalars.{u,u,u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let hmono : Functor.PreservesMonomorphisms (ModuleCat.extendScalars.{u,u,u} f) := by
    refine ⟨fun {X Y} q hq => ?_⟩
    let hqpres : PreservesLimit (cospan q q) (ModuleCat.extendScalars.{u,u,u} f) :=
      (hlim.preservesFiniteLimits WalkingCospan).preservesLimit
    exact @preserves_mono_of_preservesLimit _ _ _ _
      (ModuleCat.extendScalars.{u,u,u} f) X Y q hqpres hq
  exact hmono

/-- Pointwise form of
`moduleExtendScalars_preservesMonomorphisms_of_flat`. -/
lemma moduleExtendScalars_map_mono_of_flat
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    {M N : ModuleCat R} (φ : M ⟶ N) [Mono φ] :
    Mono ((ModuleCat.extendScalars.{u,u,u} f).map φ) :=
  (moduleExtendScalars_preservesMonomorphisms_of_flat f hf).preserves φ

end
end GromovWitten.AlgebraicGeometry.Curves
