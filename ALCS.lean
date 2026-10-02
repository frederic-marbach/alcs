module

public import Semigroup
public import Phillips
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Abstract linear control systems

* `concat τ u v` : the `τ`-concatenation `u ⋄_τ v` of two functions `ℝ → U`.
* `ALCS 𝕜 X U p` : an abstract linear control system `(𝕋, Φ)`.
* `ALCS.Phi_zero` : `Φ 0 = 0`.
* `ALCS.causality`, `ALCS.delay`, `ALCS.free` : Lemma (elementary).
* `exists_shift` : the shifted input `u₁ = u (a + ·)`, with `‖u₁‖ ≤ ‖u‖` and `u = u ⋄_a u₁`.
* `ALCS.zero_class` : Theorem (zero-class), over real/complex scalars.
* `ALCS.continuousOn_Phi` : Corollary (Phi-continuous), proved from the theorem.

Design choices.
* `L^p(ℝ₊; U)` is `Lp U p muPlus`, where `muPlus` is Lebesgue measure restricted
  to `[0, ∞)`. Its elements are a.e.-classes; `⇑u : ℝ → U` is a representative.
* As for `T`, the input maps are a function `Φ : ℝ → (L^p →L X)`;
  only nonnegative times play a role.
* The concatenation is defined on functions. Instead of building `u ⋄_τ v` as an
  element of `L^p`, the composition property is stated for every `w ∈ L^p` whose
  representative is a.e. equal to `u ⋄_τ v`. Since `u ⋄_τ v ∈ L^p`, this is the
  same as the definition in the paper.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Lebesgue measure on `ℝ₊ = [0, ∞)`. -/
noncomputable abbrev muPlus : Measure ℝ := volume.restrict (Set.Ici 0)

/-- The `τ`-concatenation `u ⋄_τ v`: equal to `u s` for `s < τ`
and to `v (s - τ)` for `s ≥ τ`. -/
noncomputable def concat (τ : ℝ) (u v : ℝ → U) : ℝ → U :=
  fun s => if s < τ then u s else v (s - τ)

/-! ## Shifted inputs -/

/-- `s ↦ a + s` sends `ℝ₊` to `[a, ∞)`, preserving Lebesgue measure. -/
theorem measurePreserving_shift (a : ℝ) :
    MeasurePreserving (fun s => a + s) muPlus (volume.restrict (Set.Ici a)) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) a).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici a))
  rwa [Set.preimage_const_add_Ici, sub_self] at h

/-- `s ↦ -a + s` sends `[a, ∞)` to `ℝ₊`, preserving Lebesgue measure. -/
theorem measurePreserving_unshift (a : ℝ) :
    MeasurePreserving (fun s => -a + s) (volume.restrict (Set.Ici a)) muPlus := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) (-a)).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
  rwa [Set.preimage_const_add_Ici, zero_sub, neg_neg] at h

/-- For `a ≥ 0` and `u ∈ L^p(ℝ₊; U)`, the shifted input `u₁ := u (a + ·)` is in
`L^p(ℝ₊; U)`, with `‖u₁‖ ≤ ‖u‖` and `u = u ⋄_a u₁` a.e. -/
theorem exists_shift {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : ℝ) (ha : 0 ≤ a)
    (u : Lp U p muPlus) :
    ∃ u₁ : Lp U p muPlus, ‖u₁‖ ≤ ‖u‖ ∧ ⇑u =ᵐ[muPlus] concat a ⇑u ⇑u₁ := by
  have hmp := measurePreserving_shift a
  have hle : volume.restrict (Set.Ici a) ≤ muPlus :=
    Measure.restrict_mono (Set.Ici_subset_Ici.2 ha) le_rfl
  -- `u (a + ·)` is in `L^p`
  have hmem : MemLp (⇑u ∘ fun s => a + s) p muPlus :=
    ((Lp.memLp u).mono_measure hle).comp_measurePreserving hmp
  refine ⟨hmem.toLp _, ?_, ?_⟩
  · -- `‖u₁‖ = ‖u‖_{L^p(a, ∞)} ≤ ‖u‖_{L^p(0, ∞)}`
    rw [Lp.norm_toLp, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    rw [eLpNorm_comp_measurePreserving ((Lp.aestronglyMeasurable u).mono_measure hle) hmp]
    exact eLpNorm_mono_measure _ hle
  · -- `u₁ r = u (a + r)` for a.e. `r ≥ 0`
    have h0 := hmem.coeFn_toLp
    -- hence `u₁ (s - a) = u s` for a.e. `s ≥ a`
    have h1 := (measurePreserving_unshift a).quasiMeasurePreserving.ae h0
    have h2 := (ae_restrict_iff' (measurableSet_Ici : MeasurableSet (Set.Ici a))).1 h1
    filter_upwards [ae_restrict_of_ae h2] with s hs
    by_cases hsa : s < a
    · simp [concat, hsa]
    · simpa [concat, hsa, sub_eq_neg_add] using (hs (Set.mem_Ici.2 (not_lt.1 hsa))).symm

/-- `‖(a + b) - (c + d)‖ ≤ ‖a - c‖ + ‖b‖ + ‖d‖` -/
theorem norm_three_terms_le (a b c d : X) :
    ‖a + b - (c + d)‖ ≤ ‖a - c‖ + ‖b‖ + ‖d‖ := by
  have key : a + b - (c + d) = (a - c + b) - d := by abel
  rw [key]
  have k1 := norm_sub_le (a - c + b) d
  have k2 := norm_add_le (a - c) b
  linarith

/-- An abstract linear control system with state space `X`, input space `U`
and exponent `p`. The semigroup `T` comes from `C0Semigroup`. -/
structure ALCS (𝕜 : Type*) (X : Type*) (U : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] extends C0Semigroup 𝕜 X where
  /-- the input maps `Φ t : L^p(ℝ₊; U) → X` -/
  Φ : ℝ → Lp U p muPlus →L[𝕜] X
  /-- composition property: `Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v` -/
  composition : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → ∀ u v w : Lp U p muPlus,
    (⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) → Φ (τ + t) w = T t (Φ τ u) + Φ t v

namespace ALCS

section Elementary

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : ALCS 𝕜 X U p)

/-- `Φ 0 = 0`: composition with `τ = t = 0` and `u = v`, since `u ⋄_0 u = u`. -/
theorem Phi_zero : S.Φ 0 = 0 := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  -- `u ⋄_0 u = u` everywhere
  have hw : ⇑u =ᵐ[muPlus] concat 0 ⇑u ⇑u :=
    Filter.Eventually.of_forall (fun s => by simp [concat])
  -- `Φ 0 u = T 0 (Φ 0 u) + Φ 0 u = Φ 0 u + Φ 0 u`
  have h := S.composition 0 0 le_rfl le_rfl u u u hw
  simpa [S.T_zero] using h

/-- Causality: `Φ τ (u ⋄_τ v) = Φ τ u`, i.e. `Φ τ u` only depends on `u` on `[0, τ)`.
(Composition with `t = 0`.) -/
theorem causality (τ : ℝ) (hτ : 0 ≤ τ) (u v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) :
    S.Φ τ w = S.Φ τ u := by
  have h := S.composition τ 0 hτ le_rfl u v w hw
  simpa [S.T_zero, S.Phi_zero] using h

/-- Delay: `Φ (s + t) (0 ⋄_s v) = Φ t v`, an initial period of zero input has no effect.
(Composition with `u = 0`.) -/
theorem delay (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat s ⇑(0 : Lp U p muPlus) ⇑v) :
    S.Φ (s + t) w = S.Φ t v := by
  have h := S.composition s t hs ht 0 v w hw
  simpa using h

/-- Free evolution: `Φ (τ + t) (u ⋄_τ 0) = T t (Φ τ u)`, once the input is switched off
the state evolves freely. (Composition with `v = 0`.) -/
theorem free (τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t) (u w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑(0 : Lp U p muPlus)) :
    S.Φ (τ + t) w = S.T t (S.Φ τ u) := by
  have h := S.composition τ t hτ ht u 0 w hw
  simpa using h

end Elementary


end ALCS

end General

/-!
## Endpoint proof

The endpoint argument uses real/complex scalars.  The preceding definitions and
composition lemmas are still stated over an arbitrary nontrivially normed field.
In particular, there is only one scalar-field instance in each section.

The packing below uses disjoint intervals in `[0,1)` with zero input in the gaps.
If the n-th control has length `h n` and its chosen free-evolution time is `r n`,
its interval is `[1 - r n - h n, 1 - r n)`.  This is the manuscript's packing
argument with zero padding: its image at time 1 is exactly `T (r n) x_n`.
-/

noncomputable section

section Endpoint

open scoped BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS
namespace ZeroClassProof

/-! ### Representatives and concatenation in L-infinity -/

/-- A pointwise bound gives membership in L-infinity, without a finite-measure
assumption. -/
lemma memLp_of_bound {f : ℝ → U} (hf : StronglyMeasurable f)
    {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C) : MemLp f ∞ muPlus := by
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)

/-- The real-valued L-infinity norm is bounded by any nonnegative a.e. bound. -/
lemma lp_norm_le {u : Lp U ∞ muPlus} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ C) : ‖u‖ ≤ C := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus := by
    exact eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  rw [Lp.norm_def, htop]
  calc
    (eLpNormEssSup (⇑u) muPlus).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hb)
    _ = C := ENNReal.toReal_ofReal hC

/-- The representative of an L-infinity class obeys its norm bound a.e. -/
lemma ae_norm_le (u : Lp U ∞ muPlus) :
    ∀ᵐ t ∂muPlus, ‖u t‖ ≤ ‖u‖ := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus := by
    exact eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  have hfinite : eLpNormEssSup (⇑u) muPlus ≠ ∞ := by
    rw [← htop]
    exact Lp.eLpNorm_ne_top u
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑u) muPlus] with t ht
  have ht' := ENNReal.toReal_mono hfinite ht
  simpa only [Lp.norm_def, htop, toReal_enorm] using ht'

/-- Choose an everywhere bounded, strongly measurable representative.  The
modification takes place only where the original representative exceeds `C`. -/
lemma exists_bounded_rep (u : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ∃ f : ℝ → U, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ C) ∧
      ⇑u =ᵐ[muPlus] f := by
  let f : ℝ → U := fun t => if ‖u t‖ ≤ C then u t else 0
  have hf : StronglyMeasurable f := by
    apply StronglyMeasurable.ite
      ((Lp.stronglyMeasurable u).norm.measurableSet_le stronglyMeasurable_const)
      (Lp.stronglyMeasurable u) stronglyMeasurable_const
  refine ⟨f, hf, ?_, ?_⟩
  · intro t
    by_cases ht : ‖u t‖ ≤ C
    · simp [f, ht]
    · simpa [f, ht] using hC
  · filter_upwards [ae_norm_le u] with t ht
    simp [f, ht.trans hu]

omit [NormedAddCommGroup U] in
/-- A.e. equality can be substituted in either argument of concatenation.
The second argument requires transporting the null set under translation. -/
lemma concat_congr {f f' g g' : ℝ → U} (a : ℝ)
    (hf : f =ᵐ[muPlus] f') (hg : g =ᵐ[muPlus] g') :
    concat a f g =ᵐ[muPlus] concat a f' g' := by
  have hg₁ := (measurePreserving_unshift a).quasiMeasurePreserving.ae hg
  have hg₂ := (ae_restrict_iff'
    (measurableSet_Ici : MeasurableSet (Set.Ici a))).1 hg₁
  filter_upwards [hf, ae_restrict_of_ae hg₂] with t hft hgt
  by_cases ht : t < a
  · simp [concat, ht, hft]
  · simpa only [concat, ite_eq_right ht, sub_eq_neg_add] using
      hgt (Set.mem_Ici.2 (not_lt.1 ht))

lemma concat_stronglyMeasurable {f g : ℝ → U}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (a : ℝ) :
    StronglyMeasurable (concat a f g) := by
  exact StronglyMeasurable.ite measurableSet_Iio hf
    (hg.comp_measurable (measurable_id.sub_const a))

/-- Concatenation is a contraction on a common L-infinity ball. -/
lemma exists_concat (a : ℝ) (u v : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ C ∧
      ⇑w =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u hC hu
  obtain ⟨g, hg, hgb, hvg⟩ := exists_bounded_rep v hC hv
  have hb : ∀ t, ‖concat a f g t‖ ≤ C := by
    intro t
    by_cases ht : t < a
    · simpa [concat, ht] using hfb t
    · simpa [concat, ht] using hgb (t - a)
  have hm := memLp_of_bound (concat_stronglyMeasurable hf hg a) hb
  refine ⟨hm.toLp _, ?_, ?_⟩
  · apply lp_norm_le hC
    filter_upwards [hm.coeFn_toLp] with t ht
    rw [ht]
    exact hb t
  · exact hm.coeFn_toLp.trans (concat_congr a huf hvg).symm

/-- The Lp representative of a bounded raw function has the same bound. -/
lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) :
    ‖hf.toLp f‖ ≤ C := by
  apply lp_norm_le hC
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]
  exact hb t

/-! ### Monotonicity and the doubling estimate -/

variable (S : ALCS 𝕜 X U ∞)

lemma norm_Phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖S.Φ s‖ ≤ ‖S.Φ t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  obtain ⟨w, hw, hcat⟩ := exists_concat (t - s) (0 : Lp U ∞ muPlus) u
    (norm_nonneg u) (by simp) le_rfl
  have heq := S.delay (t - s) s (sub_nonneg.2 hst) hs u w hcat
  rw [sub_add_cancel] at heq
  calc
    ‖S.Φ s u‖ = ‖S.Φ t w‖ := congrArg norm heq.symm
    _ ≤ ‖S.Φ t‖ * ‖w‖ := (S.Φ t).le_opNorm w
    _ ≤ ‖S.Φ t‖ * ‖u‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)

lemma doubling {h : ℝ} (hh : 0 ≤ h) (u : Lp U ∞ muPlus)
    (hu : ‖u‖ ≤ 1) :
    2 * ‖S.Φ h u‖ ≤ ‖S.Φ (2 * h)‖ +
      ‖S.T h (S.Φ h u) - S.Φ h u‖ := by
  obtain ⟨w, hw, hcat⟩ := exists_concat h u u (by norm_num) hu hu
  have hcomp := S.composition h h hh hh u u w hcat
  have hnorm : ‖S.Φ (2 * h) w‖ ≤ ‖S.Φ (2 * h)‖ := by
    exact ((S.Φ (2 * h)).le_opNorm w).trans
      (by simpa using mul_le_mul_of_nonneg_left hw (norm_nonneg (S.Φ (2 * h))))
  let x := S.Φ h u
  have hid : x + x = S.Φ (2 * h) w - (S.T h x - x) := by
    rw [show 2 * h = h + h by ring, hcomp]
    dsimp [x]
    abel
  have htwo : ‖x + x‖ = 2 * ‖x‖ := by
    calc
      ‖x + x‖ = ‖(2 : 𝕜) • x‖ := by rw [two_smul]
      _ = ‖(2 : 𝕜)‖ * ‖x‖ := norm_smul _ _
      _ = 2 * ‖x‖ := by rw [show ‖(2 : 𝕜)‖ = 2 from RCLike.norm_natCast 2]
  calc
    2 * ‖S.Φ h u‖ = ‖x + x‖ := htwo.symm
    _ ≤ ‖S.Φ (2 * h) w‖ + ‖S.T h x - x‖ := by
      rw [hid]
      exact norm_sub_le _ _
    _ ≤ ‖S.Φ (2 * h)‖ + ‖S.T h x - x‖ := add_le_add hnorm le_rfl

/-! ### Nearly extremal pulses and rapidly decreasing time scales -/

lemma exists_near_extremal (h ε : ℝ) (hε : 0 < ε) :
    ∃ u : Lp U ∞ muPlus, ‖u‖ ≤ 1 ∧ ‖S.Φ h‖ - ε ≤ ‖S.Φ h u‖ := by
  by_cases hc : ‖S.Φ h‖ - ε ≤ 0
  · exact ⟨0, by simp, by simpa using hc⟩
  · by_contra hn
    have hbound : ‖S.Φ h‖ ≤ ‖S.Φ h‖ - ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (lt_of_not_ge hc))
      intro u hu
      exact (lt_of_not_ge (fun h => hn ⟨u, hu.le, h⟩)).le
    linarith

/-- A unit-ball control, with an actual representative supported in `[0,h)`. -/
structure Pulse (U : Type*) [NormedAddCommGroup U] (h : ℝ) where
  f : ℝ → U
  measurable : StronglyMeasurable f
  bound : ∀ t, ‖f t‖ ≤ 1
  off : ∀ t, t < 0 ∨ h ≤ t → f t = 0

namespace Pulse

variable {h : ℝ} (P : Pulse U h)

def input : Lp U ∞ muPlus :=
  (memLp_of_bound P.measurable P.bound).toLp P.f

lemma coe_input : ⇑P.input =ᵐ[muPlus] P.f :=
  (memLp_of_bound P.measurable P.bound).coeFn_toLp

lemma norm_input : ‖P.input‖ ≤ 1 :=
  norm_toLp_le _ (by norm_num) P.bound

lemma free_rep : ⇑P.input =ᵐ[muPlus]
    concat h ⇑P.input ⇑(0 : Lp U ∞ muPlus) := by
  have hraw : P.f = concat h P.f (fun _ => (0 : U)) := by
    funext t
    by_cases ht : t < h
    · simp [concat, ht]
    · simp [concat, ht, P.off t (Or.inr (not_lt.1 ht))]
  exact P.coe_input.trans
    ((Filter.EventuallyEq.of_eq hraw).trans
      (concat_congr h P.coe_input (Lp.coeFn_zero U ∞ muPlus)).symm)

end Pulse

lemma exists_pulse (h : ℝ) (hh : 0 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Pulse U h, ‖S.Φ h‖ - ε ≤ ‖S.Φ h P.input‖ := by
  obtain ⟨u, hu, hnear⟩ := exists_near_extremal S h ε hε
  obtain ⟨g, hg, hgb, hug⟩ := exists_bounded_rep u (by norm_num) hu
  let f := (Set.Ico 0 h).indicator g
  have hf : StronglyMeasurable f := hg.indicator measurableSet_Ico
  have hb : ∀ t, ‖f t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ Set.Ico 0 h
    · simpa [f, Set.indicator_of_mem ht] using hgb t
    · simp [f, Set.indicator_of_notMem ht]
  have hoff : ∀ t, t < 0 ∨ h ≤ t → f t = 0 := by
    intro t ht
    have hnot : t ∉ Set.Ico 0 h := by
      intro hin
      rcases ht with ht | ht
      · exact (not_lt_of_ge hin.1) ht
      · exact (not_lt_of_ge ht) hin.2
    exact Set.indicator_of_notMem hnot g
  let P : Pulse U h := ⟨f, hf, hb, hoff⟩
  have hraw : f =ᵐ[muPlus] concat h g (fun _ => (0 : U)) := by
    have hpos : ∀ᵐ t ∂muPlus, t ∈ Set.Ici (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ici
    filter_upwards [hpos] with t ht
    have ht0 : 0 ≤ t := ht
    by_cases hth : t < h
    · simp [f, concat, hth, Set.mem_Ico, ht0]
    · simp [f, concat, hth, Set.mem_Ico]
  have hcat : ⇑P.input =ᵐ[muPlus] concat h ⇑u ⇑(0 : Lp U ∞ muPlus) :=
    P.coe_input.trans (hraw.trans (concat_congr h hug (Lp.coeFn_zero U ∞ muPlus)).symm)
  refine ⟨P, ?_⟩
  rwa [S.causality h hh u 0 P.input hcat]

/-- The accuracy in the n-th selection. -/
def err (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma err_pos (n : ℕ) : 0 < err n := by
  unfold err
  positivity

lemma err_tendsto : Tendsto err atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- One nearly extremal control and a short free-evolution time for its state. -/
structure FrozenPulse (S : ALCS 𝕜 X U ∞) (n : ℕ) (h : ℝ) where
  pulse : Pulse U h
  near : ‖S.Φ h‖ - err n ≤ ‖S.Φ h pulse.input‖
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ h
  close : ‖S.T r (S.Φ h pulse.input) - S.Φ h pulse.input‖ ≤ err n

lemma frozenPulse_nonempty (n : ℕ) (h : ℝ) (hh : 0 < h) :
    Nonempty (FrozenPulse S n h) := by
  obtain ⟨P, hP⟩ := exists_pulse S h hh.le (err n) (err_pos n)
  obtain ⟨δ, hδ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.1
    (S.T_cont (S.Φ h P.input)) (err n) (err_pos n)
  let r := min h (δ / 2)
  have hr : 0 < r := lt_min hh (by positivity)
  have hrh : r ≤ h := min_le_left _ _
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨⟨P, hP, r, hr, hrh, ?_⟩⟩
  have hc' := hc (Set.mem_Ici.2 hr.le)
    (show dist r 0 < δ by simpa [Real.dist_eq, abs_of_pos hr] using hrδ)
  have hclose : ‖S.T r (S.Φ h P.input) - S.Φ h P.input‖ < err n := by
    simpa only [dist_eq_norm] using hc'
  exact hclose.le

/-- Classical choice is used only to choose actual witnesses to proved existences. -/
def choosePulse (n : ℕ) (h : ℝ) (hh : 0 < h) : FrozenPulse S n h :=
  Classical.choice (frozenPulse_nonempty S n h hh)

/-- The next pulse fits strictly inside the remaining free-evolution interval. -/
def positiveTimes : ℕ → {h : ℝ // 0 < h} :=
  Nat.rec ⟨1 / 4, by norm_num⟩
    (fun n h =>
      ⟨(choosePulse S n h.1 h.2).r / 4,
        div_pos (choosePulse S n h.1 h.2).r_pos (by norm_num)⟩)

def h (n : ℕ) : ℝ := (positiveTimes S n).1

def data (n : ℕ) : FrozenPulse S n (h S n) :=
  choosePulse S n (h S n) (positiveTimes S n).2

def r (n : ℕ) : ℝ := (data S n).r

def x (n : ℕ) : X := S.Φ (h S n) (data S n).pulse.input

lemma h_pos (n : ℕ) : 0 < h S n := (positiveTimes S n).2
lemma r_pos (n : ℕ) : 0 < r S n := (data S n).r_pos
lemma r_le_h (n : ℕ) : r S n ≤ h S n := (data S n).r_le
lemma h_zero : h S 0 = 1 / 4 := rfl
lemma h_succ (n : ℕ) : h S (n + 1) = r S n / 4 := rfl

lemma h_succ_le (n : ℕ) : h S (n + 1) ≤ h S n / 2 := by
  rw [h_succ]
  have := r_le_h S n
  have := (h_pos S n).le
  linarith

lemma h_le_quarter (n : ℕ) : h S n ≤ 1 / 4 := by
  induction n with
  | zero => simp [h_zero]
  | succ n ih =>
    have := h_succ_le S n
    linarith

lemma h_geometric (n : ℕ) : h S n ≤ err n / 4 := by
  induction n with
  | zero => simp [h_zero, err]
  | succ n ih =>
    have := h_succ_le S n
    dsimp [err] at ih ⊢
    rw [pow_succ]
    linarith

lemma h_tendsto : Tendsto (h S) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => (h_pos S n).le) (h_geometric S)
    (by simpa using err_tendsto.div_const 4)

lemma x_near (n : ℕ) : ‖S.Φ (h S n)‖ - err n ≤ ‖x S n‖ :=
  (data S n).near

lemma x_le (n : ℕ) : ‖x S n‖ ≤ ‖S.Φ (h S n)‖ := by
  exact ((S.Φ (h S n)).le_opNorm _).trans
    (by simpa using
      mul_le_mul_of_nonneg_left (data S n).pulse.norm_input (norm_nonneg (S.Φ (h S n))))

lemma x_frozen (n : ℕ) : ‖S.T (r S n) (x S n) - x S n‖ ≤ err n :=
  (data S n).close

/-! ### Packing the pulses in one bounded operator -/

def start (n : ℕ) : ℝ := 1 - r S n - h S n

def window (n : ℕ) : Set ℝ := Set.Ico (start S n) (start S n + h S n)

def block (n : ℕ) (t : ℝ) : U := (data S n).pulse.f (t - start S n)

lemma start_nonneg (n : ℕ) : 0 ≤ start S n := by
  have := r_le_h S n
  have := h_le_quarter S n
  dsimp [start]
  linarith

lemma finish_le_next (n : ℕ) : start S n + h S n ≤ start S (n + 1) := by
  have h₁ := r_le_h S (n + 1)
  have h₂ := h_succ S n
  have h₃ := (r_pos S n).le
  dsimp [start]
  linarith

lemma start_mono : Monotone (start S) := by
  apply monotone_nat_of_le_succ
  intro n
  have := finish_le_next S n
  have := (h_pos S n).le
  linarith

lemma finish_le_start {i j : ℕ} (hij : i < j) :
    start S i + h S i ≤ start S j :=
  (finish_le_next S i).trans (start_mono S (Nat.succ_le_of_lt hij))

lemma window_unique {i j : ℕ} {t : ℝ}
    (hi : t ∈ window S i) (hj : t ∈ window S j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have := finish_le_start S hij
    have hi' := hi.2
    have hj' := hj.1
    linarith
  · exact hij
  · have := finish_le_start S hji
    have hj' := hj.2
    have hi' := hi.1
    linarith

lemma block_measurable (n : ℕ) : StronglyMeasurable (block S n) :=
  (data S n).pulse.measurable.comp_measurable (measurable_id.sub_const _)

lemma block_bound (n : ℕ) (t : ℝ) : ‖block S n t‖ ≤ 1 :=
  (data S n).pulse.bound _

lemma block_off (n : ℕ) {t : ℝ} (ht : t ∉ window S n) : block S n t = 0 := by
  apply (data S n).pulse.off
  by_cases hs : t < start S n
  · left
    linarith
  · right
    by_contra hh
    apply ht
    constructor
    · exact not_lt.1 hs
    · change t < start S n + h S n
      linarith

/-- Pointwise gluing.  The selected interval depends on the time, not on the
coefficient sequence, so additivity and scalar compatibility are pointwise. -/
def packRaw (a : Phillips.Linfty 𝕜) : ℝ → U := by
  classical
  exact fun t => if ht : ∃ n, t ∈ window S n then
    a (Classical.choose ht) • block S (Classical.choose ht) t else 0

lemma packRaw_on (a : Phillips.Linfty 𝕜) {n : ℕ} {t : ℝ}
    (ht : t ∈ window S n) : packRaw S a t = a n • block S n t := by
  classical
  have hex : ∃ j, t ∈ window S j := ⟨n, ht⟩
  have heq : Classical.choose hex = n :=
    window_unique S (Classical.choose_spec hex) ht
  simp only [packRaw, dite_eq_left hex, heq]

lemma packRaw_off (a : Phillips.Linfty 𝕜) {t : ℝ}
    (ht : ¬ ∃ n, t ∈ window S n) : packRaw S a t = 0 := by
  classical
  simp [packRaw, ht]

lemma packRaw_add (a b : Phillips.Linfty 𝕜) (t : ℝ) :
    packRaw S (a + b) t = packRaw S a t + packRaw S b t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S (a + b) hn, packRaw_on S a hn, packRaw_on S b hn]
    simp only [BoundedContinuousFunction.add_apply, add_smul]
  · simp only [packRaw_off S (a + b) ht, packRaw_off S a ht,
      packRaw_off S b ht, add_zero]

lemma packRaw_smul (c : 𝕜) (a : Phillips.Linfty 𝕜) (t : ℝ) :
    packRaw S (c • a) t = c • packRaw S a t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S (c • a) hn, packRaw_on S a hn]
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_smul]
  · simp only [packRaw_off S (c • a) ht, packRaw_off S a ht, smul_zero]

lemma packRaw_bound (a : Phillips.Linfty 𝕜) (t : ℝ) :
    ‖packRaw S a t‖ ≤ ‖a‖ := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S a hn, norm_smul]
    have ha : ‖a n‖ ≤ ‖a‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg a)).1 le_rfl n
    calc
      ‖a n‖ * ‖block S n t‖ ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left (block_bound S n t) (norm_nonneg _)
      _ ≤ ‖a‖ := by simpa using ha
  · rw [packRaw_off S a ht, norm_zero]
    exact norm_nonneg _

/-- At every time the partial sums eventually equal the glued function.  This
uses pointwise disjointness, not convergence of a series in the L-infinity norm. -/
lemma partial_sums_eventually (a : Phillips.Linfty 𝕜) (t : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, a n • block S n t) = packRaw S a t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    rw [packRaw_on S a hn]
    apply Finset.sum_eq_single n
    · intro j _ hjn
      have hj : t ∉ window S j :=
        fun hj => hjn (window_unique S hj hn)
      simp [block_off S j hj]
    · intro hnN
      exact (hnN (Finset.mem_range.2 (by omega))).elim
  · filter_upwards [] with N
    rw [packRaw_off S a ht]
    apply Finset.sum_eq_zero
    intro n _
    have hn : t ∉ window S n := fun hn => ht ⟨n, hn⟩
    simp [block_off S n hn]

lemma packRaw_measurable (a : Phillips.Linfty 𝕜) :
    StronglyMeasurable (packRaw S a) := by
  classical
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun N t => ∑ n ∈ Finset.range N, a n • block S n t)
  · intro N
    exact Finset.stronglyMeasurable_fun_sum (Finset.range N)
      (fun n _ => (block_measurable S n).const_smul (a n))
  · apply tendsto_pi_nhds.2
    intro t
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (partial_sums_eventually S a t))

lemma packRaw_memLp (a : Phillips.Linfty 𝕜) : MemLp (packRaw S a) ∞ muPlus :=
  memLp_of_bound (packRaw_measurable S a) (packRaw_bound S a)

def packedInput (a : Phillips.Linfty 𝕜) : Lp U ∞ muPlus :=
  (packRaw_memLp S a).toLp (packRaw S a)

lemma packedInput_ae (a : Phillips.Linfty 𝕜) :
    ⇑(packedInput S a) =ᵐ[muPlus] packRaw S a :=
  (packRaw_memLp S a).coeFn_toLp

lemma packedInput_norm (a : Phillips.Linfty 𝕜) : ‖packedInput S a‖ ≤ ‖a‖ :=
  norm_toLp_le _ (norm_nonneg _) (packRaw_bound S a)

lemma packedInput_add (a b : Phillips.Linfty 𝕜) :
    packedInput S (a + b) = packedInput S a + packedInput S b := by
  apply Lp.ext
  filter_upwards [packedInput_ae S (a + b), packedInput_ae S a,
    packedInput_ae S b, Lp.coeFn_add (packedInput S a) (packedInput S b)]
      with t hab ha hb hsum
  rw [hab, hsum]
  simpa only [Pi.add_apply, ha, hb] using packRaw_add S a b t

lemma packedInput_smul (c : 𝕜) (a : Phillips.Linfty 𝕜) :
    packedInput S (c • a) = c • packedInput S a := by
  apply Lp.ext
  filter_upwards [packedInput_ae S (c • a), packedInput_ae S a,
    Lp.coeFn_smul c (packedInput S a)] with t hca ha hsmul
  rw [hca, hsmul]
  simpa only [Pi.smul_apply, ha] using packRaw_smul S c a t

/-- The contraction from bounded scalar sequences to packed controls. -/
def packing : Phillips.Linfty 𝕜 →L[𝕜] Lp U ∞ muPlus :=
  LinearMap.mkContinuous
    { toFun := packedInput S
      map_add' := packedInput_add S
      map_smul' := fun c a => by
        simpa using packedInput_smul S c a }
    1 (fun a => by simpa using packedInput_norm S a)

lemma packing_ae (a : Phillips.Linfty 𝕜) :
    ⇑(packing S a) =ᵐ[muPlus] packRaw S a := packedInput_ae S a

lemma packRaw_e (n : ℕ) (t : ℝ) :
    packRaw S (Phillips.e n) t = block S n t := by
  classical
  by_cases hn : t ∈ window S n
  · rw [packRaw_on S _ hn]
    simp
  · rw [block_off S n hn]
    by_cases ht : ∃ j, t ∈ window S j
    · obtain ⟨j, hj⟩ := ht
      have hjn : j ≠ n := by
        intro heq
        subst j
        exact hn hj
      rw [packRaw_on S _ hj]
      simp [Phillips.e_apply, hjn]
    · exact packRaw_off S _ ht

/-- Apply the input map at the common final time. -/
def packedOperator : Phillips.Linfty 𝕜 →L[𝕜] X :=
  (S.Φ 1).comp (packing S)

lemma packedOperator_e (n : ℕ) :
    packedOperator S (Phillips.e n) = S.T (r S n) (x S n) := by
  let P := (data S n).pulse
  have hraw : packRaw S (Phillips.e n) =
      concat (start S n) (fun _ => (0 : U)) P.f := by
    funext t
    rw [packRaw_e]
    by_cases ht : t < start S n
    · have hoff : P.f (t - start S n) = 0 :=
        P.off _ (Or.inl (by linarith))
      simpa [concat, ht, block, P] using hoff
    · simp [concat, ht, block, P]
  have hw : ⇑(packing S (Phillips.e n)) =ᵐ[muPlus]
      concat (start S n) ⇑(0 : Lp U ∞ muPlus) ⇑P.input :=
    (packing_ae S _).trans
      ((Filter.EventuallyEq.of_eq hraw).trans
        (concat_congr (start S n) (Lp.coeFn_zero U ∞ muPlus) P.coe_input).symm)
  have hsum : start S n + (h S n + r S n) = 1 := by
    unfold start
    ring
  change S.Φ 1 (packing S (Phillips.e n)) = _
  rw [← hsum]
  rw [S.delay (start S n) (h S n + r S n) (start_nonneg S n)
    (add_nonneg (h_pos S n).le (r_pos S n).le) P.input _ hw]
  exact S.free (h S n) (r S n) (h_pos S n).le (r_pos S n).le
    P.input P.input P.free_rep

lemma packedOperator_close (n : ℕ) :
    ‖packedOperator S (Phillips.e n) - x S n‖ ≤ err n := by
  rw [packedOperator_e]
  exact x_frozen S n

/-! ### The right-hand limit of the input-map norms -/

/-- The possible input-map norms at strictly positive times. -/
def normRange : Set ℝ := (fun t : ℝ => ‖S.Φ t‖) '' Set.Ioi 0

lemma normRange_nonempty : (normRange S).Nonempty :=
  ⟨‖S.Φ 1‖, 1, by norm_num, rfl⟩

lemma normRange_bddBelow : BddBelow (normRange S) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, _, rfl⟩
  exact norm_nonneg _

/-- The limit denoted by `ℓ` in the manuscript. -/
def ell : ℝ := sInf (normRange S)

lemma ell_nonneg : 0 ≤ ell S := by
  apply le_csInf (normRange_nonempty S)
  rintro y ⟨t, _, rfl⟩
  exact norm_nonneg _

lemma ell_le (t : ℝ) (ht : 0 < t) : ell S ≤ ‖S.Φ t‖ :=
  csInf_le (normRange_bddBelow S) ⟨t, ht, rfl⟩

lemma exists_norm_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖S.Φ t‖ < ell S + ε := by
  by_contra hn
  have hbad : ell S + ε ≤ ell S := by
    apply le_csInf (normRange_nonempty S)
    rintro y ⟨t, ht, rfl⟩
    exact le_of_not_gt (fun hlt => hn ⟨t, ht, hlt⟩)
  linarith

/-- Monotonicity identifies the norm limit along every positive null sequence. -/
lemma norm_Phi_tendsto (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖S.Φ (t n)‖) atTop (𝓝 (ell S)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨τ, hτ, hτnorm⟩ := exists_norm_lt S ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht τ hτ
  refine ⟨N, fun n hn => ?_⟩
  have htn : t n < τ := by
    have hdist := hN n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (htpos n)] using hdist
  have hupper := norm_Phi_mono S (htpos n).le htn.le
  have hlower := ell_le S (t n) (htpos n)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hlower)]
  linarith

lemma x_norm_tendsto : Tendsto (fun n => ‖x S n‖) atTop (𝓝 (ell S)) := by
  have hk := norm_Phi_tendsto S (h S) (h_pos S) (h_tendsto S)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hk ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 err_tendsto ε hε
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hkdist := hN₁ n (le_trans (le_max_left _ _) hn)
  have hedist := hN₂ n (le_trans (le_max_right _ _) hn)
  have hkabs : |‖S.Φ (h S n)‖ - ell S| < ε := by
    simpa only [Real.dist_eq] using hkdist
  have he : err n < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (err_pos n)] using hedist
  have hupper := x_le S n
  have hnear := x_near S n
  have hlower := ell_le S (h S n) (h_pos S n)
  rw [Real.dist_eq]
  obtain ⟨_, hkright⟩ := abs_lt.1 hkabs
  exact abs_lt.2 ⟨by linarith, by linarith⟩

/-! ### Phillips uniformity and transfer from packed columns to the states -/

lemma x_moves_tendsto [CompleteSpace X] :
    Tendsto (fun n => ‖S.T (h S n) (x S n) - x S n‖) atTop (𝓝 0) := by
  obtain ⟨ω, hω, M, hM, hbound⟩ := S.toC0Semigroup.exists_exp_bound
  let K : ℝ := M * Real.exp ω
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hK : 0 ≤ K := mul_nonneg hM0 (Real.exp_pos _).le
  have hTbound : ∀ n, ‖S.T (h S n)‖ ≤ K := by
    intro n
    calc
      ‖S.T (h S n)‖ ≤ M * Real.exp (ω * h S n) :=
        hbound _ (h_pos S n).le
      _ ≤ M * Real.exp ω := by
        apply mul_le_mul_of_nonneg_left _ hM0
        apply Real.exp_le_exp.2
        have hn : h S n ≤ 1 := le_trans (h_le_quarter S n) (by norm_num)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hω
      _ = K := rfl
  let A : ℕ → X →L[𝕜] X :=
    fun n => S.T (h S n) - ContinuousLinearMap.id 𝕜 X
  have hAbound : ∀ n, ‖A n‖ ≤ K + 1 := by
    intro n
    calc
      ‖A n‖ ≤ ‖S.T (h S n)‖ + ‖ContinuousLinearMap.id 𝕜 X‖ := norm_sub_le _ _
      _ ≤ K + 1 := add_le_add (hTbound n) (ContinuousLinearMap.norm_id_le)
  have hPhillips : Tendsto
      (fun n => ‖A n (packedOperator S (Phillips.e n))‖) atTop (𝓝 0) := by
    exact Phillips.uniform (packedOperator S) S.T S.T_cont
      (h S) (fun n => (h_pos S n).le) (h_tendsto S)
  have herror : ∀ n, ‖S.T (h S n) (x S n) - x S n‖ ≤
      ‖A n (packedOperator S (Phillips.e n))‖ + (K + 1) * err n := by
    intro n
    let y := packedOperator S (Phillips.e n)
    have hxy : ‖x S n - y‖ ≤ err n := by
      rw [norm_sub_rev]
      exact packedOperator_close S n
    have hsplit : A n (x S n) = A n y + A n (x S n - y) := by
      rw [map_sub]
      abel
    calc
      ‖S.T (h S n) (x S n) - x S n‖ = ‖A n (x S n)‖ := rfl
      _ = ‖A n y + A n (x S n - y)‖ := congrArg norm hsplit
      _ ≤ ‖A n y‖ + ‖A n (x S n - y)‖ := norm_add_le _ _
      _ ≤ ‖A n y‖ + ‖A n‖ * ‖x S n - y‖ :=
        add_le_add le_rfl ((A n).le_opNorm _)
      _ ≤ ‖A n y‖ + (K + 1) * err n := by
        apply add_le_add le_rfl
        exact mul_le_mul (hAbound n) hxy (norm_nonneg _) (by linarith)
  apply squeeze_zero (fun n => norm_nonneg _) herror
  simpa only [mul_zero, add_zero] using
    hPhillips.add (err_tendsto.const_mul (K + 1))

end ZeroClassProof

open ZeroClassProof

/-- Theorem (zero-class), for real or complex Banach spaces: all abstract
L-infinity control systems have input-map norm tending to zero at time zero.

No integral representation or continuity of translations in L-infinity is used.
The key external functional-analytic input is `Phillips.uniform` from the supplied
`Phillips.lean`. -/
theorem zero_class [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞) :
    Tendsto (fun t => ‖S.Φ t‖) (nhdsWithin 0 (Set.Ici 0)) (𝓝 0) := by
  have hx := x_norm_tendsto S
  have hm := x_moves_tendsto S
  have htwo : Tendsto (fun n => ‖S.Φ (2 * h S n)‖) atTop (𝓝 (ell S)) :=
    norm_Phi_tendsto S (fun n => 2 * h S n)
      (fun n => mul_pos (by norm_num) (h_pos S n))
      (by simpa only [mul_zero] using (h_tendsto S).const_mul 2)
  have hineq : ∀ n, 2 * ‖x S n‖ ≤ ‖S.Φ (2 * h S n)‖ +
      ‖S.T (h S n) (x S n) - x S n‖ := by
    intro n
    exact doubling S (h_pos S n).le (data S n).pulse.input
      (data S n).pulse.norm_input
  have hlimit : 2 * ell S ≤ ell S := by
    have hleft := hx.const_mul 2
    have hright := htwo.add hm
    have hle := le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall hineq)
    simpa only [add_zero] using hle
  have hell : ell S = 0 := by
    have := ell_nonneg S
    linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨τ, hτ, hnormτ⟩ := exists_norm_lt S ε hε
  rw [hell, zero_add] at hnormτ
  refine ⟨τ, hτ, fun t ht hdist => ?_⟩
  have ht0 : 0 ≤ t := ht
  have htτ : t < τ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht0] using hdist
  have hsmall : ‖S.Φ t‖ < ε :=
    lt_of_le_of_lt (norm_Phi_mono S ht0 htτ.le) hnormτ
  simpa using hsmall

/-- Consequence of the zero-class property: for `ε > 0` there is `η > 0` such that
`‖Φ r v‖ < ε` for all `r ∈ [0, η)` and all `v` with `‖v‖ ≤ ‖u‖`. -/
theorem small_Phi [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ r, 0 ≤ r → r < η → ∀ v : Lp U ∞ muPlus, ‖v‖ ≤ ‖u‖ → ‖S.Φ r v‖ < ε := by
  -- `κ(r) = ‖Φ r‖ < ε / (‖u‖ + 1)` for `r ∈ [0, η)`
  obtain ⟨η, hη, hκ⟩ :=
    Metric.tendsto_nhdsWithin_nhds.1 S.zero_class (ε / (‖u‖ + 1)) (by positivity)
  refine ⟨η, hη, fun r hr hrη v hv => ?_⟩
  have h1 := hκ (Set.mem_Ici.2 hr)
    (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr]; exact hrη)
  have h2 : ‖S.Φ r‖ < ε / (‖u‖ + 1) := by simpa using h1
  have h3 : ‖S.Φ r‖ * (‖u‖ + 1) < ε := (lt_div_iff₀ (by positivity)).1 h2
  -- `‖Φ r v‖ ≤ κ(r) ‖v‖`
  calc ‖S.Φ r v‖ ≤ ‖S.Φ r‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖S.Φ r‖ * (‖u‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ < ε := h3

/-- Corollary (Phi-continuous): for `p = ∞` and every `u`, `t ↦ Φ t u` is continuous
on `[0, ∞)`. -/
theorem continuousOn_Phi [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞)
    (u : Lp U ∞ muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  rw [Set.mem_Ici] at ht₀
  rcases ht₀.eq_or_lt with h0 | hpos
  · -- continuity at `t₀ = 0`: `‖Φ t u‖ ≤ κ(t) ‖u‖ → 0`
    subst h0
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u ε hε
    refine ⟨η, hη, fun t ht hdist => ?_⟩
    rw [Set.mem_Ici] at ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht] at hdist
    show dist (S.Φ t u) (S.Φ 0 u) < ε
    rw [S.Phi_zero, zero_apply, dist_zero_right]
    exact hsmall t ht hdist u le_rfl
  · -- continuity at `t₀ > 0`
    -- `‖Φ r v‖ < ε / 4` for `r ∈ [0, η)` and `‖v‖ ≤ ‖u‖`
    obtain ⟨η, hη, hsmall⟩ := S.small_Phi u (ε / 4) (by positivity)
    -- `0 < δ < t₀` and `2 δ < η`
    obtain ⟨δ, hδpos, hδt, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ t₀ / 2 ∧ δ ≤ η / 3 :=
      ⟨min (t₀ / 2) (η / 3), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    -- `t₁ := t₀ - δ`, `u₁ := u (t₁ + ·)` and `y := Φ t₁ u`
    have ht₁ : 0 ≤ t₀ - δ := by linarith
    obtain ⟨u₁, hu₁, hcat⟩ := exists_shift (t₀ - δ) ht₁ u
    obtain ⟨y, hy⟩ : ∃ y : X, y = S.Φ (t₀ - δ) u := ⟨_, rfl⟩
    -- composition: `Φ (t₁ + r) u = T r y + Φ r u₁`
    have hcomp : ∀ r, 0 ≤ r → S.Φ (t₀ - δ + r) u = S.T r y + S.Φ r u₁ := by
      intro r hr
      rw [hy]
      exact S.composition (t₀ - δ) r ht₁ hr u u₁ u hcat
    -- in particular `Φ t₀ u = T δ y + Φ δ u₁`
    have e₀ : S.Φ t₀ u = S.T δ y + S.Φ δ u₁ := by
      have h := hcomp δ hδpos.le
      rwa [sub_add_cancel] at h
    -- continuity of `s ↦ T s y` at `s = δ`
    obtain ⟨δ', hδ', horbit⟩ := Metric.continuousOn_iff.1
      (S.toC0Semigroup.continuousOn_orbit y) δ (Set.mem_Ici.2 hδpos.le) (ε / 2) (by positivity)
    refine ⟨min δ δ', lt_min hδpos hδ', fun t _ hdist => ?_⟩
    -- write `t = t₁ + r`, with `|r - δ| = |t - t₀|`
    obtain ⟨r, rfl⟩ : ∃ r, t = t₀ - δ + r := ⟨t - (t₀ - δ), by ring⟩
    rw [Real.dist_eq, show t₀ - δ + r - t₀ = r - δ by ring] at hdist
    have hd1 : |r - δ| < δ := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 : |r - δ| < δ' := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨hr1, hr2⟩ := abs_lt.1 hd1
    have hr : 0 ≤ r := by linarith
    -- the three terms
    have h1 : ‖S.T r y - S.T δ y‖ < ε / 2 := by
      have h := horbit r (Set.mem_Ici.2 hr) (by rw [Real.dist_eq]; exact hd2)
      rwa [dist_eq_norm] at h
    have h2 : ‖S.Φ r u₁‖ < ε / 4 := hsmall r hr (by linarith) u₁ hu₁
    have h3 : ‖S.Φ δ u₁‖ < ε / 4 := hsmall δ hδpos.le (by linarith) u₁ hu₁
    -- conclusion
    show dist (S.Φ (t₀ - δ + r) u) (S.Φ t₀ u) < ε
    rw [dist_eq_norm, hcomp r hr, e₀]
    have h4 := norm_three_terms_le (S.T r y) (S.Φ r u₁) (S.T δ y) (S.Φ δ u₁)
    linarith

end ALCS

end Endpoint

end
