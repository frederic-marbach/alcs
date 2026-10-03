# Continuity of solutions to abstract linear control systems — Lean formalization

Lean 4 / Mathlib formalization of the numbered statements of

> F. Marbach, *Continuity of solutions to abstract linear control systems* (2026),
> <https://hexagonmath.org/2610.00022>.

For abstract linear control systems in the sense of Weiss (a strongly continuous semigroup
`𝕋` on a Banach space `X` and input maps `Φ_t : L^p(ℝ₊; U) → X` satisfying the
concatenation identity), the paper proves that, for `p = ∞`, every system is of the
*zero-class* (`‖Φ_t‖ → 0` as `t → 0`) and that `t ↦ Φ_t u` is continuous for every
`u ∈ L^∞`, answering Weiss' 1989 Problem 2.4. No integral representation of `Φ` is
assumed; the key tool is Phillips' lemma. Section 3 gives examples: failure of the
zero-class property for `p < ∞`, and a system with `p = ∞` that has no integral
representation and is not Orlicz-admissible.

## Where to find each statement

| Paper | LaTeX label | Lean declaration | File |
| --- | --- | --- | --- |
| Definition 1.1 | — | `ALCS` | [ALCS/Definitions.lean](ALCS/Definitions.lean) |
| Proposition 1.2 | `prop:pazy-semigroup-solution-continuous` | `C0Semigroup.continuousOn_orbit` | [ALCS/Background/Semigroup.lean](ALCS/Background/Semigroup.lean) |
| Proposition 1.3 | `prop:finite-p-solution-continuous` | `ALCS.continuousOn_Phi_of_ne_top` | [ALCS/ContinuityFiniteP.lean](ALCS/ContinuityFiniteP.lean) |
| Definition 1.4 | — | `ALCS.IsZeroClass` | [ALCS/Definitions.lean](ALCS/Definitions.lean) |
| **Theorem 1.5** | `thm:p-infty-zero-class` | `ALCS.zero_class` | [ALCS/ZeroClass.lean](ALCS/ZeroClass.lean) |
| **Corollary 1.6** | `cor:p-infty-solution-continuous` | `ALCS.continuousOn_Phi` | [ALCS/ContinuityLinfty.lean](ALCS/ContinuityLinfty.lean) |
| Lemma 2.1 | `lem:Phi-properties` | `ALCS.causality`, `ALCS.delay`, `ALCS.free` | [ALCS/Definitions.lean](ALCS/Definitions.lean) |
| Lemma 2.2 (Phillips) | `lem:Phillips` | `Phillips.full` | [ALCS/Background/Phillips.lean](ALCS/Background/Phillips.lean) |
| Lemma 2.3 | `lem:cor-Phillips` | `Phillips.uniform` | [ALCS/Background/Phillips.lean](ALCS/Background/Phillips.lean) |
| Proposition 3.1 | `prop:example-finite-p-not-zero-class` | `exists_system_norm_Phi_eq_one` | [ALCS/Examples/FinitePNotZeroClass.lean](ALCS/Examples/FinitePNotZeroClass.lean) |
| Lemma 3.2 | `lem:exotic-mean` | `ExoticMean.exotic_mean` | [ALCS/Examples/ExoticMean.lean](ALCS/Examples/ExoticMean.lean) |
| Proposition 3.3 | `prop:no-representation` | `ExoticMean.Counterexample.no_representation` | [ALCS/Examples/NoRepresentation.lean](ALCS/Examples/NoRepresentation.lean) |

Each Lean file starts with the statements it contains (number and LaTeX label);
[formalization.yaml](formalization.yaml) records the divergences from the paper.

[Challenge.lean](Challenge.lean) states Theorem 1.5 and Corollary 1.6 with Mathlib only, and
[Solution.lean](Solution.lean) proves them (checked by Comparator, see
[comparator.json](comparator.json)). Build with `lake exe cache get && lake build`;
there is no `sorry` outside `Challenge.lean`, and `lake env lean AxiomCheck.lean` prints
the axioms of each statement.

## License

[Apache-2.0](LICENSE).
