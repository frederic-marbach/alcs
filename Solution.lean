module

public import ALCS.ContinuityLinfty

public section

/-!
# Proofs of the statements of `Challenge.lean`

The two declarations below have exactly the statements of `Challenge.lean` (Comparator
checks this). Their hypotheses are bundled into the structure `ALCS` (Definition 1.1,
`ALCS/Definitions.lean`) and the proofs are those of the development:

* `PalomarALCS.zero_class` : Theorem 1.5 (`thm:p-infty-zero-class`), from
  `ALCS.zero_class` in `ALCS/ZeroClass.lean`;
* `PalomarALCS.continuousOn_Phi` : Corollary 1.6 (`cor:p-infty-solution-continuous`),
  from `ALCS.continuousOn_Phi` in `ALCS/ContinuityLinfty.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

local notation "L∞(ℝ₊; " U ")" => Lp U ∞ (volume.restrict (Set.Ici (0 : ℝ)))

/-- **Theorem 1.5** (`thm:p-infty-zero-class`): every abstract linear control system with
`p = ∞` is zero-class, `‖Φ t‖ → 0` as `t → 0⁺`. -/
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

/-- **Corollary 1.6** (`cor:p-infty-solution-continuous`): for `p = ∞` and every input
`u ∈ L^∞(ℝ₊; U)`, `t ↦ Φ t u` is continuous on `[0, ∞)`. -/
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
