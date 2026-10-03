module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# Abstract linear control systems with `L^∞` inputs: zero-class property and continuity

Statements (with deliberate `sorry`s, for Comparator) of the two main results of
F. Marbach, *Continuity of solutions to abstract linear control systems* (2026),
<https://hexagonmath.org/2610.00022>: Theorem 1.5 and Corollary 1.6.
They are proved in `Solution.lean`. Only Mathlib definitions are used, and every axiom
of the systems is an explicit hypothesis.

## Setting

Let `X` (states) and `U` (controls) be Banach spaces. Following G. Weiss (1989), an
*abstract linear control system* with inputs in `L^p(ℝ₊; U)` is a pair `(T, Φ)` where
* `T` is a strongly continuous semigroup on `X` (hypotheses `hT_zero`, `hT_semigroup`,
  `hT_cont`);
* `Φ_t : L^p(ℝ₊; U) → X` (`t ≥ 0`) are bounded linear *input maps* satisfying the
  concatenation identity (hypothesis `hΦ_concat`)

      Φ_{τ+t} (u ◇_τ v) = T_t (Φ_τ u) + Φ_t v,

  where `u ◇_τ v` plays `u` on `[0, τ)`, then `v` (shifted by `τ`).

The state at time `t` from the initial state `x₀` with control `u` is `T_t x₀ + Φ_t u`.
The model case is `Φ_t u = ∫₀ᵗ T_{t-s} B u(s) ds`, but no such integral representation is
assumed; for `p = ∞` it does not always exist.

## Interest

For `p < ∞`, `t ↦ Φ_t u` is continuous (Weiss 1989, Proposition 2.3). The case `p = ∞`
was left open as Problem 2.4 in G. Weiss, *Admissibility of unbounded control operators*,
SIAM J. Control Optim. 27 (1989), 527–545. The two results below settle it:
* `zero_class` (Theorem 1.5): for `p = ∞`, every system is *zero-class*, i.e.
  `‖Φ_t‖ → 0` as `t → 0⁺`. This fails for `p < ∞` (e.g. the right shift on `L^p(ℝ₊)`).
* `continuousOn_Phi` (Corollary 1.6): for `p = ∞` and every `u`, `t ↦ Φ_t u` is continuous
  on `[0, ∞)`: a positive answer to Weiss' Problem 2.4.

## Proof

The proof of Theorem 1.5 is a direct semigroup argument: with `ℓ = lim_{t→0⁺} ‖Φ_t‖`,
playing a nearly extremal control twice gives `2ℓ ≤ ℓ`, provided the semigroup barely moves
the corresponding states. This uniformity comes from Phillips' lemma on `(ℓ^∞)*`, applied
after packing infinitely many controls into one bounded operator `ℓ^∞ → X`. Corollary 1.6
then follows from the concatenation identity. The informal proof was produced by GPT-6 Pro
from the author's notes and rewritten by the author; see the paper.

## Lean conventions

* Scalars `𝕜` are `ℝ` or `ℂ` (`RCLike 𝕜`); a Banach space is a complete normed space.
* `L∞(ℝ₊; U)` is local notation for Mathlib's `Lp U ∞ (volume.restrict (Set.Ici 0))`:
  a.e. classes of essentially bounded functions `ℝ → U` for Lebesgue measure on `[0, ∞)`;
  `u s` denotes the value of a representative.
* `T` and `Φ` are defined on `ℝ`, but only nonnegative times occur in the hypotheses and
  conclusions: `𝓝[≥] 0` means `t → 0` with `t ≥ 0`.
* The concatenation identity is required for every `w` a.e. equal on `[0, ∞)` to
  `s ↦ if s < τ then u s else v (s - τ)`. Since this concatenation is again in `L^∞` and
  a.e. classes are unique, this is exactly the identity above.
* Non-vacuity: `X = U = ℝ`, `T_t = Id`, `Φ_t u = ∫₀ᵗ u(s) ds` satisfies the hypotheses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

-- `L∞(ℝ₊; U)`: pure notation for Mathlib's `Lp U ∞` with Lebesgue measure on `[0, ∞)`.
local notation "L∞(ℝ₊; " U ")" => Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ)))

/-- **Theorem 1.5** (`thm:p-infty-zero-class`, zero-class property).
For an abstract linear control system `(T, Φ)` with inputs in `L^∞(ℝ₊; U)`,
`‖Φ_t‖ → 0` as `t → 0⁺` (operator norm of `Φ_t : L^∞(ℝ₊; U) → X`). -/
theorem zero_class
    (T : ℝ → X →L[𝕜] X)
    (Φ : ℝ → L∞(ℝ₊; U) →L[𝕜] X)
    -- `T` is a strongly continuous semigroup on `X`:
    (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hT_semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
    (hT_cont : ∀ x : X, Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x))
    -- concatenation identity `Φ_{τ+t} (u ◇_τ v) = T_t (Φ_τ u) + Φ_t v`,
    -- where `w` represents the concatenation `u ◇_τ v`:
    (hΦ_concat : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : L∞(ℝ₊; U),
      (⇑w =ᵐ[volume.restrict (Set.Ici (0 : ℝ))]
        (fun s => if s < τ then u s else v (s - τ))) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v) :
    Tendsto (fun t => ‖Φ t‖) (𝓝[≥] 0) (𝓝 0) := by
  sorry

/-- **Corollary 1.6** (`cor:p-infty-solution-continuous`), answering Weiss' Problem 2.4.
Under the same hypotheses, for every input `u ∈ L^∞(ℝ₊; U)`, `t ↦ Φ_t u` is continuous on
`[0, ∞)`, including at `t = 0`. -/
theorem continuousOn_Phi
    (T : ℝ → X →L[𝕜] X)
    (Φ : ℝ → L∞(ℝ₊; U) →L[𝕜] X)
    -- `T` is a strongly continuous semigroup on `X`:
    (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hT_semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
    (hT_cont : ∀ x : X, Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x))
    -- concatenation identity `Φ_{τ+t} (u ◇_τ v) = T_t (Φ_τ u) + Φ_t v`,
    -- where `w` represents the concatenation `u ◇_τ v`:
    (hΦ_concat : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : L∞(ℝ₊; U),
      (⇑w =ᵐ[volume.restrict (Set.Ici (0 : ℝ))]
        (fun s => if s < τ then u s else v (s - τ))) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v)
    (u : L∞(ℝ₊; U)) :
    ContinuousOn (fun t => Φ t u) (Set.Ici 0) := by
  sorry

end PalomarALCS
