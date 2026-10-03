module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# Abstract linear control systems with `L∞` inputs: zero-class property and continuity

This file contains the *statements* (with deliberate `sorry`s) of the two main results of
F. Marbach, *Continuity of solutions to abstract linear control systems* (2026).
`Solution.lean` proves exactly the same declarations. The deliberate `sorry` terms belong
only to this independent statement module.

The statements use standard Mathlib notions only, and every axiom of the systems under
consideration is spelled out as an explicit hypothesis: nothing is hidden behind a custom
definition. The only shorthand is the purely syntactic notation `L∞(ℝ₊; U)` below.

## Abstract linear control systems (Weiss, 1989)

Let `X` (the *state space*) and `U` (the *input space*) be Banach spaces and fix
`p ∈ [1, ∞]`. Following G. Weiss [W89], an *abstract linear control system* is a pair
`(T, Φ)` where

* `T = (T_t)_{t ≥ 0}` is a strongly continuous semigroup of bounded operators on `X`:
  `T_0 = Id`, `T_{t+s} = T_t T_s` for `t, s ≥ 0`, and `T_t x → x` as `t → 0⁺` for every
  `x ∈ X`;
* `Φ = (Φ_t)_{t ≥ 0}` is a family of bounded linear operators `L^p(ℝ₊; U) → X`
  (the *input maps*) satisfying the *concatenation identity*: for all `τ, t ≥ 0` and all
  inputs `u, v`,

      Φ_{τ+t} (u ◇_τ v) = T_t (Φ_τ u) + Φ_t v,

  where `u ◇_τ v` is the input equal to `u(s)` for `s < τ` and to `v(s - τ)` for `s ≥ τ`
  ("play `u` on `[0, τ)`, then play `v`").

One thinks of `x(t) := T_t x₀ + Φ_t u` as the state at time `t` of a linear control system
started from `x₀ ∈ X` and driven by the control `u`. The typical example is
`Φ_t u = ∫₀ᵗ T_{t-s} B u(s) ds` for a (possibly unbounded) control operator `B`, but the
definition does *not* require such an integral representation. For `p < ∞` every system
has one [W89, Thm. 3.9]; for `p = ∞` this fails in general (Weiss, 1991).

## The question: Weiss' Problem 2.4 [W89]

The free part `t ↦ T_t x₀` is always continuous (standard semigroup theory).
For `p < ∞`, Weiss proved [W89, Prop. 2.3] that the controlled part `t ↦ Φ_t u` is
continuous as well; his argument uses `p < ∞` in an essential way (the `L^p` norm of `u` on
`(0, t)` tends to `0` as `t → 0`, and translations are continuous in `L^p`).
He left the endpoint case open as [W89, Problem 2.4]:

  *for `p = ∞`, is `t ↦ Φ_t u` continuous for every `u ∈ L^∞(ℝ₊; U)`?*

This was known for some classes of systems (e.g. systems with an integral representation
that are zero-class, see below), but not in general. Independently, Arora, Preußler and
Schwenninger (2026) obtained the result for systems given by a control operator `B` as
above; the statements below assume no such representation.

## The results formalized here (with `p = ∞` and arbitrary Banach spaces `X`, `U`)

* `zero_class`: every abstract linear control system with `p = ∞` is *zero-class*, i.e.
  `‖Φ_t‖ → 0` as `t → 0⁺` (operator norm from `L^∞(ℝ₊; U)` to `X`).
  This is false in general for `p < ∞` (e.g. the right shift on `X = L^p(ℝ₊)`, `U = ℝ`,
  for which `‖Φ_t‖ = 1` for every `t > 0`).
* `continuousOn_Phi`: for every `u ∈ L^∞(ℝ₊; U)`, the map `t ↦ Φ_t u` is continuous on
  `[0, ∞)`. Together with the continuity of `t ↦ T_t x₀`, this says that all state
  trajectories `t ↦ T_t x₀ + Φ_t u` are continuous: a positive answer to
  [W89, Problem 2.4].

No integral representation, control operator or extrapolation space is assumed: only the
axioms listed above.

[W89] G. Weiss, *Admissibility of unbounded control operators*,
      SIAM J. Control Optim. 27 (1989), 527–545.

## Dictionary between the mathematics and the Lean statements

* Scalars: `𝕜` is `ℝ` or `ℂ` (`RCLike 𝕜`). A Banach space over `𝕜` is a type with
  `[NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]`.
* `L∞(ℝ₊; U)` is local notation (defined below) for Mathlib's
  `Lp U ∞ (volume.restrict (Set.Ici 0))`: almost-everywhere classes of essentially bounded,
  (a.e. strongly) measurable functions `ℝ → U`, for Lebesgue measure restricted to
  `ℝ₊ = [0, ∞)`, with the essential-supremum norm. For `u` in this space, `u s` is the value
  at `s` of a representative of `u` (coercion `⇑u : ℝ → U`).
* Times: for convenience, `T` and `Φ` are functions defined on all of `ℝ`, but their values
  at negative times play no role. Every hypothesis only involves nonnegative times, and so
  do the conclusions: `𝓝[≥] 0` is the filter "`t → 0` with `t ≥ 0`", and
  `ContinuousOn f (Set.Ici 0)` is the continuity of the restriction of `f` to `[0, ∞)`.
* `X →L[𝕜] X` and `L∞(ℝ₊; U) →L[𝕜] X` are spaces of bounded linear operators, and
  `‖Φ t‖` is Mathlib's operator norm.
* Semigroup: hypotheses `hT_zero`, `hT_semigroup`, `hT_cont`. Strong continuity is only
  required at `0⁺`, which is the usual definition; no bound on `‖T_t‖` is assumed.
* Concatenation identity: hypothesis `hΦ_concat`. Instead of building `u ◇_τ v` as an
  element of `L∞(ℝ₊; U)`, it quantifies over every `w ∈ L∞(ℝ₊; U)` that is a.e. equal on
  `[0, ∞)` to `s ↦ if s < τ then u s else v (s - τ)`. Since the concatenation of two `L^∞`
  inputs is always an `L^∞` input, and since a.e. classes are unique, this is exactly the
  identity above (neither weaker nor stronger). It does not depend on the chosen
  representatives of `u` and `v`, because translations preserve Lebesgue-null sets.
* Non-vacuity: the hypotheses are satisfied by non-trivial systems, e.g. `X = U = ℝ`,
  `T_t = Id` and `Φ_t u = ∫₀ᵗ u(s) ds`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

-- `L∞(ℝ₊; U)`: the input space `L^∞(ℝ₊; U)`, i.e. Mathlib's `Lp U ∞` for Lebesgue measure
-- restricted to `[0, ∞)`. This is pure notation: it is expanded syntactically and does not
-- introduce any new definition.
local notation "L∞(ℝ₊; " U ")" => Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ)))

/-- **Zero-class property** (main theorem of the paper).

Let `(T, Φ)` be an abstract linear control system with state space `X`, input space `U`
and inputs in `L^∞(ℝ₊; U)`. Then `‖Φ_t‖ → 0` as `t → 0⁺`, where `‖Φ_t‖` is the operator
norm of `Φ_t : L^∞(ℝ₊; U) → X`. -/
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

/-- **Continuity of the input response** (main corollary of the paper), i.e. a positive
answer to Weiss' 1989 Problem 2.4.

Under the same assumptions, for every input `u ∈ L^∞(ℝ₊; U)`, the map `t ↦ Φ_t u` is
continuous on the whole nonnegative time axis `[0, ∞)`, including at `t = 0`. -/
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
