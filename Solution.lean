module

public import ALCS

public section

/-! # Proved Palomar statements
The hypotheses below are bundled into the existing ALCS structure.
Comparator checks these declarations against the independent Challenge.
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
  let S : ALCS 𝕜 X U ∞ :=
    { T := T, T_zero := hzero, T_add := hadd, T_cont := hcont,
      Φ := Φ, composition := hcomp }
  exact S.zero_class

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
  let S : ALCS 𝕜 X U ∞ :=
    { T := T, T_zero := hzero, T_add := hadd, T_cont := hcont,
      Φ := Φ, composition := hcomp }
  exact S.continuousOn_Phi u

end PalomarALCS
