module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# Zero-class property and continuity of abstract linear control systems

These are the main theorem (`thm:zero-class`) and corollary (`cor:Phi-continuous`)
of Frédéric Marbach, *Continuity of solutions to abstract linear control systems*.
Both statements use ordinary Mathlib notions and spell out all system axioms.

The scalar field is real or complex (`RCLike`), and `X` and `U` are Banach spaces.
Inputs are almost-everywhere classes in `L∞` for Lebesgue measure restricted to
`[0, ∞)`. Times are real numbers; hypotheses and conclusions concern only
nonnegative times. `T` is a strongly continuous semigroup and `Φ` is a family
of bounded linear input maps. The last hypothesis is the concatenation identity:
the input `w` agrees almost everywhere with `u` before `τ`, and with the shifted
input `v` afterwards. No integral representation is assumed.

The deliberate `sorry` terms belong only to this independent statement module.
`Solution.lean` proves the same declarations from the substantive development.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

/-- Every abstract `L∞` control system is zero-class: the operator norm of its
input map tends to zero as nonnegative time tends to zero. -/
theorem zero_class
    (T : ℝ → X →L[𝕜] X)
    (Φ : ℝ → Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ))) →L[𝕜] X)
    (hzero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hadd : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
    (hcont : ∀ x : X, Tendsto (fun t => T t x) (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (hcomp : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ))),
      (⇑w =ᵐ[volume.restrict (Set.Ici (0 : ℝ))]
        (fun s => if s < τ then u s else v (s - τ))) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v) :
    Tendsto (fun t => ‖Φ t‖) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
  sorry

/-- For every `L∞` input, the input response of an abstract linear control
system is continuous on the entire nonnegative time axis, including time zero. -/
theorem continuousOn_Phi
    (T : ℝ → X →L[𝕜] X)
    (Φ : ℝ → Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ))) →L[𝕜] X)
    (hzero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hadd : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
    (hcont : ∀ x : X, Tendsto (fun t => T t x) (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (hcomp : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ))),
      (⇑w =ᵐ[volume.restrict (Set.Ici (0 : ℝ))]
        (fun s => if s < τ then u s else v (s - τ))) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v)
    (u : Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ)))) :
    ContinuousOn (fun t => Φ t u) (Set.Ici 0) := by
  sorry

end PalomarALCS
