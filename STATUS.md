# Project status

This Lean library develops theorem-backed foundations for the Tau Ceti roadmap on stable
reduction of curves and stable maps.  The implementation follows the roadmap's separation
between scheme-theoretic curve families, models over discrete valuation rings, dual-graph
stability, arithmetic-surface numerical types, and map-decorated graphs.

It also contains the Behrend--Fantechi virtual-fundamental-class development specified by the
[Tau Ceti roadmap comparison](https://github.com/TauCetiProject/TauCetiRoadmap/compare/main...Paul-Lez:TauCetiRoadmap:agent/behrend-fantechi-roadmap).
That development supplies groundwork in groupoid-valued fppf stacks, bicategorical pullbacks,
distinct stack sites with canonical regular-function sheaves, rational Chow gradings, and
derived obstruction theories.  It currently exports the fully constructed virtual class only
for the proper-point acceptance test; the general intrinsic-normal-cone, absolute/relative
virtual-class, and functoriality layers remain under construction.  Its exact layer map and
public entry points are recorded in
[VIRTUAL_FUNDAMENTAL_CLASS_STATUS.md](VIRTUAL_FUNDAMENTAL_CLASS_STATUS.md).

Implemented APIs include:

- a scheme-level `Unramified` morphism class, agreeing on affine spectra with Mathlib's
  ring-theoretic `Algebra.Unramified`, local on source and target, stable under composition and
  arbitrary base change, and satisfied by every immersion;
- fibrewise and field-valued geometric relative-dimension predicates, source and target
  locality, arbitrary base-change stability, and the basic `FamilyOfCurves` package;
- generic and special fibres over a DVR, faithfully flat finite DVR extensions, and models
  with a chosen natural generic-fibre identification and properness-preserving faithful base
  change;
- the local-node algebra `R[x,y]/(xy-πⁿ)`, including its universal property, unique
  axis-supported normal form, its defining equation as a regular singleton sequence over a
  domain, flatness over a DVR, arbitrary coefficient-ring base change
  with its affine fibre-product isomorphism, preservation of affineness, quasi-compactness,
  local finite presentation, and DVR-flatness under that base change, exact dimension one for
  every field-valued node,
  including the two minimal primes and irreducible affine-line components of a positive special
  fibre, and consequently relative dimension at most one and pure relative dimension one for the
  full structural morphism; Laurent-polynomial and standard-smooth
  relative-dimension-one generic fibre for every thickness, and the equation `xy = 0` on
  positive-exponent special fibres; the exact relative Jacobian ideal `(x,y)`, its quotient
  `R/(πⁿ)`, its closed structural immersion with unramified coordinate algebra, an unramified
  structural scheme map with open diagonal, an explicit arbitrary coefficient-base-change
  equivalence for the quotient and an isomorphism over the new base, and empty generic carrier;
  explicit Laurent-polynomial
  descriptions of both coordinate principal opens, each standard smooth of relative dimension
  one, proving that the nonsmooth locus is contained in the Jacobian zero locus; the exact
  tangent-order boundary `xy-πⁿ ∈ (x,y,π)² ↔ 2 ≤ n` for an irreducible parameter; and two
  closed affine-line branches with exact ideals, scheme-theoretic common-origin intersection,
  and transported smooth branch covers after coefficient base change; plus the three
  explicit over-base chart substitutions: the central substitution lowers thickness
  from `k+2` to `k`, while the two side substitutions land in thickness one by scaling one
  coordinate by `π^(k+1)`; all three have proved inverses wherever `π` is invertible and
  commute with arbitrary coefficient base change; the central substitution's `m`-fold
  composite does as well, has its own explicit generic inverse, and is also exposed directly
  as an over-base map from thickness `n` to parity thickness `n%2≤1` after `n/2`
  reductions; plus the graded Rees algebra and Proj blowup, its degree-one affine cover and
  universal principalization maps, and genuine scheme isomorphisms identifying all three node
  charts with Rees charts compatibly with the blowup projection;
- regular proper arithmetic surfaces whose numerical data is indexed by the actual irreducible
  components of the scheme-theoretic special fibre, with vertical-divisor intersection,
  resolutions, proper geometric contractions, open-complement isomorphisms, strict component
  decrease, finite contraction chains, and termination at a relatively minimal model;
- finite connected dual multigraphs with loops, valence, arithmetic genus, unpointed
  stability, and relabelling invariance;
- weighted numerical Picard groups, their comparison with the raw intersection cokernel,
  parity and signed-genus formulae, connectedness criteria, the rank-one theorem, and
  finite prime-torsion calculations, together with specialization of genuine relative
  line-bundle classes and prime-to-characteristic Jacobian torsion control;
- conditional semistable- and stable-reduction result types containing actual finite DVR
  extensions and models together with caller-supplied numerical/genus, dualizing-line-bundle,
  graph, and stability witnesses; the resulting genus split and comparison deductions are not
  constructions of semistable reduction, duality, or geometric stability;
- marked maps, target-changing isomorphisms with groupoid laws, functorial marking restriction
  and target postcomposition with identity/composition coherence, base change, evaluation,
  decorated graphs, stability
  inequalities, numerical clutching, evaluation-gated gluing data, and descent of target
  maps through supplied external pushouts and self-coequalizers; plus proper nodal prestable
  families and base-change-stable transport of supplied numerical stability data.  Finiteness of
  the geometric automorphism group scheme is absent, while stabilization, forgetting, and
  geometric nodal gluing remain conditional outputs of caller-supplied engines;
- executable worked examples for the combinatorial acceptance cases.

Some classical existence results beyond the pinned Mathlib snapshot currently appear only as
typed caller-supplied construction engines.  Their outputs contain actual schemes, morphisms,
line bundles, colimits, and isomorphisms, but supplying an engine is a dependency boundary—not a
formalization of the existence or geometry it assumes.  Results depending on such engines are
conditional and do not count as completed roadmap items.  No placeholder proofs or custom axioms
are used; see [ROADMAP_STATUS.md](ROADMAP_STATUS.md) for the exact construction boundary and audit
result.

The specification is [TauCetiRoadmap PR #142](https://github.com/TauCetiProject/TauCetiRoadmap/pull/142).

## Build

Install the Lean toolchain selected by `lean-toolchain`, then run:

```console
lake update
lake build
```

Project warnings are treated as errors, so placeholder proofs and linter regressions fail this
build.
