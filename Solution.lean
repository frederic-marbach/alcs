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

local notation "L∞(ℝ₊; " U ")" => Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ)))

/-- Every abstract `L∞` control system is zero-class: the operator norm of its
input map tends to zero as nonnegative time tends to zero. -/
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
  let S : ALCS 𝕜 X U ∞ :=
    { T := T, T_zero := hT_zero, T_add := hT_semigroup, T_cont := hT_cont,
      Φ := Φ, composition := hΦ_concat }
  exact S.zero_class

/-- For every `L∞` input, the input response of an abstract linear control
system is continuous on the entire nonnegative time axis, including time zero. -/
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
  let S : ALCS 𝕜 X U ∞ :=
    { T := T, T_zero := hT_zero, T_add := hT_semigroup, T_cont := hT_cont,
      Φ := Φ, composition := hΦ_concat }
  exact S.continuousOn_Phi u

end PalomarALCS
