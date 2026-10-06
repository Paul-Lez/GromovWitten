# Issue 48: dimension-graded Chow operations

Upstream: https://github.com/Paul-Lez/GromovWitten/issues/48

This branch is based on `d31abfc6a80148596ca5b1300d06396626aabb7f`.

## Verified construction

- `ProperPushforward.lean` proves a norm-order/quotient-length formula for finite
  free domain algebras over a one-dimensional Noetherian PID, using Smith normal
  form, and the local residue-length specialization. Its Galois formulas keep
  their order-invariance hypotheses explicit.
- `FlatPullbackMultiplicity.lean` proves local flat base-change formulas for
  element orders and nonzero fraction-field orders, multiplicativity of fibre
  lengths, and the unramified multiplicity-one formula.
- `FiniteFlatPullback.lean` constructs ramification-weighted inverse images of
  locally finite rational cycles along finite affine maps, with linearity.
- `FiniteFlatCycleOperations.lean` proves preservation of certified dimensions
  and constructs the corresponding dimension-graded linear map. These raw
  weighted constructions already make sense for finite algebras; flat
  functoriality and Chow descent require additional theorems.

- `FiniteFlatResidueDegree.lean` identifies the actual scheme residue degree
  with the algebraic inertia degree. For finite flat algebras over a domain,
  it proves that dimension-graded proper pushforward after finite pullback
  equals multiplication by the module rank. No degree-compatibility witness
  is assumed; the residue-field square and fibre-sum reindexing are proved.

## Remaining scope

General proper pushforward of principal divisors requires semilocal norm
formulas and the dimension-drop cancellation argument. General flat pullback
on Chow groups, exterior products, and their full compatibilities are not
claimed by the local formulas or by the cycle-level constructions above.

## Review

Four distinct `gpt-5.6-luna` agents at `xhigh` were assigned norm/divisor,
local-flat, dimension-grading, and residue-degree/rank tasks. The orchestrator
reviews hypotheses and kernel dependencies independently. All Lean/Lake
commands use a shared build lock and two Lean threads.

## Validation

The complete default `/tmp/gw-issue-build build` passed with warnings treated
as errors (8,984 jobs). The public umbrella imports all five new modules.
Central construction and proof declarations were audited with `#print axioms`;
they use only `propext`, `Classical.choice`, and `Quot.sound`. No new
`sorry`, `admit`, custom axioms, `native_decide`, or warning suppression is used.
