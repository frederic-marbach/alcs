# Continuity of solutions to abstract linear control systems

Lean formalization of the main theorem and corollary in
*Continuity of solutions to abstract linear control systems* (unpublished
manuscript, version supplied on 3 October 2026).

For real or complex Banach spaces `X` and `U`, let `T` be a strongly continuous
semigroup on `X`, and let `Φ_t : L∞([0,∞); U) → X` be bounded linear maps satisfying
the usual input-concatenation identity. The formalization proves:

1. **Zero-class property:** `‖Φ_t‖ → 0` as `t → 0` through nonnegative times.
2. **Continuity:** for every input `u ∈ L∞([0,∞); U)`, the response `t ↦ Φ_t u`
   is continuous on `[0,∞)`.

Neither result assumes that the input maps have a semigroup-convolution or other
integral representation. The intended research audience is infinite-dimensional
control theory and operator semigroups. The second result addresses the endpoint
continuity question identified as Problem 2.4 in George Weiss, *Admissibility of
unbounded control operators*, SIAM J. Control Optim. 27 (1989), 527–545,
[doi:10.1137/0327028](https://doi.org/10.1137/0327028).

## Auditable statements and proof files

| Paper claim | Comparator declaration | Underlying proof |
| --- | --- | --- |
| Main theorem, `thm:zero-class` (Theorem 1.5) | `PalomarALCS.zero_class` | `ALCS.zero_class` |
| Corollary, `cor:Phi-continuous` (Corollary 1.6) | `PalomarALCS.continuousOn_Phi` | `ALCS.continuousOn_Phi` |

Start with [Challenge.lean](Challenge.lean). It imports only Mathlib, contains no
project-specific definitions, and explicitly states every hypothesis of the two
results. Its two intentional `sorry` terms are statement placeholders for
Comparator. [Solution.lean](Solution.lean) proves the same declarations by
bundling these hypotheses into the control-system structure.

The substantive proof development is contained in:

- [Semigroup.lean](Semigroup.lean): strongly continuous semigroups, their
  exponential bound, and continuity of their orbits.
- [Phillips.lean](Phillips.lean): the diagonal consequence of Phillips' lemma,
  proved using finite sums and a recursive selection argument, and its
  operator-valued consequence.
- [ALCS.lean](ALCS.lean): input concatenation and shifts, elementary system
  identities, the zero-class theorem, and the continuity corollary.

The proof selects nearly extremal short input pulses and packs them into disjoint
intervals before a common final time. The resulting bounded operator from `ℓ∞`
lets Phillips' lemma control the semigroup motion of the selected states.
A doubling inequality then forces the limiting input-map norm to be zero.
Continuity follows from the concatenation identity and semigroup orbit continuity.

## Correspondence and scope

The formal statements use `RCLike` scalars, covering both real and complex Banach
spaces. Both spaces have explicit completeness hypotheses. There are no
finite-dimensionality, separability, reflexivity, or integral-representation
assumptions.

Inputs are Mathlib `Lp` almost-everywhere classes for Lebesgue measure restricted
to `[0,∞)`; thus their values at negative arguments do not matter. Operator
families are defined on `ℝ`, but only their nonnegative-time values occur in the
system axioms and conclusions. Strong continuity at zero, together with the
semigroup laws and completeness, yields orbit continuity on the half-line.

The composition axiom quantifies over an `Lp` element whose representative agrees
almost everywhere with the piecewise concatenation. This is the ordinary
concatenation identity on equivalence classes: `ALCS.ZeroClassProof.exists_concat`
constructs such an element at the endpoint exponent. The half-line limit includes
zero; the system identity implies `Φ_0 = 0`.

The packing argument uses disjoint intervals with zero padding before time 1,
instead of the manuscript's consecutive intervals before their accumulated final
time. This changes the proof organization, not either theorem statement.
`Phillips.lean` proves the diagonal consequence actually used; it does not claim
to formalize the full absolute-sum version of Phillips' lemma.

The manuscript's finite-`p` counterexamples, invariant-mean construction,
failure of integral representation, and failure of Orlicz-heart admissibility
are outside this formalization. The registered corollary concerns `Φ_t u`;
continuity of the full state also uses the proved semigroup-orbit continuity.

The manuscript acknowledges independent related work by Arora, Preußler and
Schwenninger, [*ISS and integral ISS coincide for linear systems with bounded
inputs*, arXiv:2609.40348v1](https://arxiv.org/abs/2609.40348v1),
for systems with a control-operator representation. Their Orlicz-admissibility
conclusion is stronger for that represented class. The present
development concerns abstract input maps. No independent priority or exhaustive
novelty assessment is claimed here. The source manuscript has no public identifier
at the time of preparation; its authorship, date and theorem labels identify the
source, and the complete claims being submitted are reproduced in Challenge.
No earlier substantive formalization was identified in the materials supplied
for this submission; this repository contains the proof development.

## Authorship, automation and review

Frédéric Marbach is the sole human contributor and responsible maintainer. He reports
that GPT-6 Pro and Opus 5.5 wrote parts of the Lean formalization. The manuscript
reports that GPT-6 Pro supplied the main informal argument from his previous
notes, and that he revised the exposition with assistance from Opus 5.5.

GPT-6 in Codex prepared the Palomar packaging, ported the module interfaces,
updated dependencies, and compared the exposed statements with the supplied
manuscript. This is an agent review; no independent human review has been
reported. Costs, prompt logs and the original formalization effort were not
tracked for this metadata. See [formalization.yaml](formalization.yaml).

## Build and verification

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

The toolchain is pinned in `lean-toolchain`, Mathlib is pinned to a full Git commit
in `lakefile.toml`, and all resolved dependencies are recorded in
`lake-manifest.json`. No dependency points outside the repository checkout.

`comparator.json` selects the two `PalomarALCS` declarations. The proof development
has no `sorry`, custom axioms or `native_decide`; the permitted axioms are
`propext`, `Classical.choice` and `Quot.sound`. `AxiomCheck.lean` prints the axiom
dependencies of the actual Solution declarations.

The **Palomar mechanical preflight** GitHub Actions workflow calls Palomar's
complete verifier, pinned at an immutable revision, with `mode: full` and the
standard GitHub runner profile. It checks the exact pushed commit using
Comparator and NanoDa as well as Palomar's metadata and source requirements.
A successful local build is not a substitute for this workflow's passing report.

Follow [SUBMISSION.md](SUBMISSION.md) to publish and submit manually at
<https://submit.palomar-registry.org/>. A preflight pass does not itself submit or
register the result.

## License

The repository is licensed under [Apache-2.0](LICENSE). This does not relicense
the cited literature or dependencies.
