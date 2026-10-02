module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Lemmas

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# The diagonal consequence of Phillips' lemma

`Linfty 𝕜` is the space of bounded sequences with values in `𝕜`, represented
as bounded continuous functions on the discrete space `ℕ`.

The main result is `Phillips.diagonal_tendsto_zero`.  The argument uses only
finite sums: first thin an infinite set for one continuous functional,
then perform a recursive selection.

-/

noncomputable section

open Filter
open scoped BigOperators Topology

set_option maxHeartbeats 800000

namespace Phillips

attribute [local instance] Classical.propDecidable

/-- Bounded scalar sequences, with the supremum norm. -/
abbrev Linfty (𝕜 : Type*) [RCLike 𝕜] := BoundedContinuousFunction ℕ 𝕜

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The characteristic sequence of a set of natural numbers. -/
def chi (S : Set ℕ) : Linfty 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => if k ∈ S then (1 : 𝕜) else 0) 1
    (by
      intro k
      by_cases hk : k ∈ S <;> simp [hk])

@[simp] theorem chi_apply (S : Set ℕ) (k : ℕ) :
    chi (𝕜 := 𝕜) S k = if k ∈ S then 1 else 0 := rfl

/-- The `k`th canonical vector of `ℓ∞`. -/
def e (k : ℕ) : Linfty 𝕜 := chi {k}

@[simp] theorem e_apply (k j : ℕ) :
    e (𝕜 := 𝕜) k j = if j = k then 1 else 0 := by
  simp [e]

/-- An infinite set can be thinned so that a given functional is small on
all characteristic sequences supported in the remaining set. -/
private theorem small_on_subsets
    (φ : Linfty 𝕜 →L[𝕜] 𝕜) (S : Set ℕ) (hS : S.Infinite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧
      ∀ B : Set ℕ, B ⊆ T → ‖φ (chi B)‖ ≤ δ := by
  classical
  -- Partition an infinite subset of S into infinitely many infinite sets.
  let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hS
  let g : ℕ × ℕ → ℕ := fun p => (emb (Nat.pair p.1 p.2)).val
  have hg : Function.Injective g := by
    intro p q hpq
    have hpq' : Nat.pair p.1 p.2 = Nat.pair q.1 q.2 :=
      emb.injective (Subtype.ext hpq)
    exact Nat.pairEquiv.injective hpq'
  let A : ℕ → Set ℕ := fun i => Set.range (fun j => g (i, j))
  have hAinf (i : ℕ) : (A i).Infinite := by
    apply Set.infinite_range_of_injective
    intro j k hjk
    exact congrArg Prod.snd (hg hjk)
  have hAS (i : ℕ) : A i ⊆ S := by
    rintro x ⟨j, rfl⟩
    exact (emb (Nat.pair i j)).property
  by_contra h
  have hbad : ∀ i : ℕ, ∃ B : Set ℕ, B ⊆ A i ∧ δ < ‖φ (chi B)‖ := by
    intro i
    by_contra hi
    apply h
    refine ⟨A i, hAS i, hAinf i, ?_⟩
    intro B hBA
    by_contra hle
    exact hi ⟨B, hBA, lt_of_not_ge hle⟩
  choose B hBA hBδ using hbad
  have hdisj {i j x : ℕ} (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
    obtain ⟨a, ha⟩ := hBA i hi
    obtain ⟨b, hb⟩ := hBA j hj
    exact congrArg Prod.fst (hg (ha.trans hb.symm))
  have hz (i : ℕ) : φ (chi (B i)) ≠ 0 :=
    norm_pos_iff.mp (hδ.trans (hBδ i))
  -- Normalize each witness so that its image under φ is exactly 1.
  let v : ℕ → Linfty 𝕜 := fun i => (φ (chi (B i)))⁻¹ • chi (B i)
  have hv (i : ℕ) : φ (v i) = 1 := by
    simp [v, map_smul, smul_eq_mul, hz i]
  have hcoef (i : ℕ) : ‖(φ (chi (B i)))⁻¹‖ ≤ δ⁻¹ := by
    simpa only [norm_inv, one_div] using
      (one_div_le_one_div_of_le hδ (le_of_lt (hBδ i)))
  -- Disjoint supports give a norm bound independent of the number of terms.
  have hsum (s : Finset ℕ) : ‖∑ i ∈ s, v i‖ ≤ δ⁻¹ := by
    apply (BoundedContinuousFunction.norm_le (show 0 ≤ δ⁻¹ by positivity)).2
    intro x
    rw [BoundedContinuousFunction.sum_apply]
    by_cases hx : ∃ i ∈ s, x ∈ B i
    · obtain ⟨i, hi, hxi⟩ := hx
      have heq : (∑ j ∈ s, (v j) x) = (v i) x := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hxj : x ∉ B j := fun hxj => hji (hdisj hxj hxi)
          simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxj]
        · intro hnot
          exact (hnot hi).elim
      rw [heq]
      simpa [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi] using hcoef i
    · have hzero : ∀ i ∈ s, (v i) x = 0 := by
        intro i hi
        have hxi : x ∉ B i := fun hxi => hx ⟨i, hi, hxi⟩
        simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi]
      rw [Finset.sum_eq_zero hzero, norm_zero]
      positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ * δ⁻¹)
  have hval : φ (∑ i ∈ Finset.range N, v i) = (N : 𝕜) := by
    simp [map_sum, hv]
  have hup : ‖φ (∑ i ∈ Finset.range N, v i)‖ ≤ ‖φ‖ * δ⁻¹ :=
    (φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hsum _) (norm_nonneg φ))
  rw [hval, RCLike.norm_natCast] at hup
  exact (not_le_of_gt hN) hup

/-- It is enough to assume convergence on characteristic sequences. -/
theorem diagonal_of_indicator_tendsto
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ S : Set ℕ, Tendsto (fun n => μ n (chi S)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (e n)) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ ‖μ n (e n)‖ := by
    push Not at hnot
    simpa only [dist_zero_right] using hnot
  let D : Set ℕ := {n | ε ≤ ‖μ n (e n)‖}
  have hD : D.Infinite := by
    intro hfin
    obtain ⟨N, hN⟩ := Set.exists_upper_bound_image D (fun n : ℕ => n) hfin
    obtain ⟨n, hn, hbn⟩ := hbad (N + 1)
    have hle : n ≤ N := hN n hbn
    omega
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  -- A reservoir is an infinite subset of the bad indices.
  let X := {S : Set ℕ // S.Infinite ∧ S ⊆ D}
  have hstep : ∀ (F : Set ℕ) (S : X), ∃ (n : ℕ) (T : X),
      n ∈ S.val ∧
      ‖μ n (chi F)‖ < δ ∧
      T.val ⊆ S.val ∧
      (∀ m ∈ T.val, n < m) ∧
      (∀ B : Set ℕ, B ⊆ T.val → ‖μ n (chi B)‖ ≤ δ) := by
    intro F S
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ F)) δ hδ
    obtain ⟨n, hnS, hnN⟩ :=
      S.property.1.exists_notMem_finite (Set.finite_lt_nat N)
    have hNn : N ≤ n := by
      simpa only [Set.mem_ofPred_eq, not_lt] using hnN
    have hnsmall : ‖μ n (chi F)‖ < δ := by
      simpa only [dist_zero_right] using hN n hNn
    have hSinfinite : (S.val \ {m : ℕ | m ≤ n}).Infinite :=
      S.property.1.sdiff (Set.finite_le_nat n)
    obtain ⟨T, hTS, hTinf, hTsmall⟩ :=
      small_on_subsets (μ n) (S.val \ {m : ℕ | m ≤ n}) hSinfinite δ hδ
    have hTsub : T ⊆ S.val := fun m hm => (hTS hm).1
    have hTD : T ⊆ D := fun m hm => S.property.2 (hTsub hm)
    refine ⟨n, ⟨T, hTinf, hTD⟩, hnS, hnsmall, hTsub, ?_, hTsmall⟩
    intro m hm
    exact lt_of_not_ge (hTS hm).2
  choose pick tail hpick hhead hsub hgt hsmall using hstep
  -- State = (already selected indices, current infinite reservoir).
  let state : ℕ → Set ℕ × X :=
    Nat.rec (∅, ⟨D, hD, fun _ h => h⟩)
      (fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2))
  let n : ℕ → ℕ := fun i => pick (state i).1 (state i).2
  let F : ℕ → Set ℕ := fun i => (state i).1
  let R : ℕ → Set ℕ := fun i => ((state i).2).val
  have hF0 : F 0 = ∅ := rfl
  have hFs (i : ℕ) : F (i + 1) = insert (n i) (F i) := rfl
  have hnmem (i : ℕ) : n i ∈ R i := hpick (state i).1 (state i).2
  have hRsub (i : ℕ) : R (i + 1) ⊆ R i := hsub (state i).1 (state i).2
  have hRgt (i : ℕ) : ∀ m ∈ R (i + 1), n i < m :=
    hgt (state i).1 (state i).2
  have hhead' (i : ℕ) : ‖μ (n i) (chi (F i))‖ < δ :=
    hhead (state i).1 (state i).2
  have hsmall' (i : ℕ) :
      ∀ B : Set ℕ, B ⊆ R (i + 1) → ‖μ (n i) (chi B)‖ ≤ δ :=
    hsmall (state i).1 (state i).2
  have hnD (i : ℕ) : ε ≤ ‖μ (n i) (e (n i))‖ :=
    (state i).2.property.2 (hnmem i)
  have hnstep (i : ℕ) : n i < n (i + 1) := hRgt i _ (hnmem (i + 1))
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ hnstep
  have hRanti : Antitone R := antitone_nat_of_succ_le hRsub
  have hin : ∀ i : ℕ, i ≤ n i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
        have hi := hnstep i
        omega
  have hFmem : ∀ (i x : ℕ), x ∈ F i ↔ ∃ j < i, n j = x := by
    intro i
    induction i with
    | zero =>
        intro x
        simp [hF0]
    | succ i ih =>
        intro x
        rw [hFs, Set.mem_insert_iff, ih]
        constructor
        · rintro (hxi | ⟨j, hj, hjx⟩)
          · exact ⟨i, Nat.lt_succ_self i, hxi.symm⟩
          · exact ⟨j, by omega, hjx⟩
        · rintro ⟨j, hj, hjx⟩
          by_cases hji : j = i
          · left
            simpa [hji] using hjx.symm
          · right
            exact ⟨j, by omega, hjx⟩
  let A : Set ℕ := Set.range n
  let B : ℕ → Set ℕ := fun i => {x | ∃ j, i < j ∧ n j = x}
  have hBsub (i : ℕ) : B i ⊆ R (i + 1) := by
    rintro x ⟨j, hij, rfl⟩
    exact hRanti (Nat.succ_le_of_lt hij) (hnmem j)
  have hsplit (i : ℕ) :
      chi (𝕜 := 𝕜) A = chi (F i) + e (n i) + chi (B i) := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [BoundedContinuousFunction.add_apply, chi_apply, e_apply]
    by_cases hx : x ∈ A
    · obtain ⟨j, rfl⟩ := hx
      have hA : n j ∈ A := ⟨j, rfl⟩
      have hF : n j ∈ F i ↔ j < i := by
        rw [hFmem]
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact hnmono.injective hkj ▸ hk
        · intro hji
          exact ⟨j, hji, rfl⟩
      have hB : n j ∈ B i ↔ i < j := by
        change (∃ k, i < k ∧ n k = n j) ↔ i < j
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact hnmono.injective hkj ▸ hk
        · intro hij
          exact ⟨j, hij, rfl⟩
      have heq : n j = n i ↔ j = i :=
        ⟨fun h => hnmono.injective h, fun h => congrArg n h⟩
      rcases lt_trichotomy j i with hji | hji | hij
      · simp [hA, hF, hB, heq, hji, ne_of_lt hji, not_lt_of_ge (le_of_lt hji)]
      · subst j
        simp [hA, hF, hB]
      · simp [hA, hF, hB, heq, hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
    · have hxF : x ∉ F i := by
        intro hxF
        obtain ⟨j, hj, hjx⟩ := (hFmem i x).1 hxF
        exact hx ⟨j, hjx⟩
      have hxB : x ∉ B i := by
        rintro ⟨j, hj, hjx⟩
        exact hx ⟨j, hjx⟩
      have hxn : x ≠ n i := by
        intro hxn
        exact hx ⟨i, hxn.symm⟩
      simp [hx, hxF, hxB, hxn]
  -- The characteristic sequence of all selected indices contradicts hμ.
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ A)) δ hδ
  have hA_small : ‖μ (n N) (chi A)‖ < δ := by
    simpa only [dist_zero_right] using hN (n N) (hin N)
  have hF_small := hhead' N
  have hB_small := hsmall' N (B N) (hBsub N)
  have hidentity : μ (n N) (chi A) =
      μ (n N) (chi (F N)) + μ (n N) (e (n N)) + μ (n N) (chi (B N)) := by
    rw [hsplit N, map_add, map_add]
  have hdiag : μ (n N) (e (n N)) =
      μ (n N) (chi A) - μ (n N) (chi (F N)) - μ (n N) (chi (B N)) := by
    rw [hidentity]
    abel
  have hnorm : ‖μ (n N) (e (n N))‖ ≤
      ‖μ (n N) (chi A)‖ + ‖μ (n N) (chi (F N))‖ +
        ‖μ (n N) (chi (B N))‖ := by
    rw [hdiag]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hlarge := hnD N
  dsimp [δ] at hA_small hF_small hB_small
  linarith only [hε, hA_small, hF_small, hB_small, hnorm, hlarge]

/-- Phillips' lemma: its diagonal consequence, over either `ℝ` or `ℂ`. -/
theorem diagonal_tendsto_zero
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (e n)) atTop (𝓝 0) :=
  diagonal_of_indicator_tendsto μ (fun S => hμ (chi S))

end Phillips

namespace Phillips

open Filter
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Vector-valued diagonal consequence of Phillips' lemma. -/
theorem norm_diagonal_tendsto_zero
    (A : ℕ → (Linfty 𝕜 →L[𝕜] X))
    (hA : ∀ a : Linfty 𝕜,
      Tendsto (fun n => A n a) atTop (𝓝 0)) :
    Tendsto (fun n => ‖A n (e n)‖) atTop (𝓝 0) := by
  classical

  -- Choose a norming functional for each diagonal vector.
  choose φ hφnorm hφeval using
    (fun n : ℕ => exists_dual_vector'' 𝕜 (A n (e n)))

  let μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜) :=
    fun n => (φ n).comp (A n)

  -- The scalar functionals converge pointwise to zero.
  have hμ : ∀ a : Linfty 𝕜,
      Tendsto (fun n => μ n a) atTop (𝓝 0) := by
    intro a
    refine squeeze_zero_norm (a := fun n => ‖A n a‖) ?_ ?_
    · intro n
      change ‖φ n (A n a)‖ ≤ ‖A n a‖
      calc
        ‖φ n (A n a)‖ ≤ ‖φ n‖ * ‖A n a‖ :=
          (φ n).le_opNorm _
        _ ≤ 1 * ‖A n a‖ :=
          mul_le_mul_of_nonneg_right (hφnorm n) (norm_nonneg _)
        _ = ‖A n a‖ := one_mul _
    · simpa only [norm_zero] using (hA a).norm

  -- Taking norms recovers the norms of the diagonal vectors.
  have hnorm (n : ℕ) : ‖μ n (e n)‖ = ‖A n (e n)‖ := by
    change ‖φ n (A n (e n))‖ = ‖A n (e n)‖
    rw [hφeval n]
    exact RCLike.norm_of_nonneg (norm_nonneg _)

  simpa only [hnorm, norm_zero] using
    (diagonal_tendsto_zero μ hμ).norm

/-- For a strongly continuous family at zero and nonnegative times
`t n → 0`, the vectors `(T (t n) - id) (S (e n))` tend to zero in norm.

Only strong right-continuity at zero is required; the semigroup law
and completeness of `X` are not used. -/
theorem uniform
    (S : Linfty 𝕜 →L[𝕜] X)
    (T : ℝ → (X →L[𝕜] X))
    (hT : ∀ x : X,
      Tendsto (fun s : ℝ => T s x)
        (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (t : ℕ → ℝ)
    (ht_nonneg : ∀ n : ℕ, 0 ≤ t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        ‖(T (t n) - ContinuousLinearMap.id 𝕜 X) (S (e n))‖)
      atTop (𝓝 0) := by
  have htWithin :
      Tendsto t atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) :=
    tendsto_nhdsWithin_iff.2
      ⟨ht, Filter.Eventually.of_forall (fun n => ht_nonneg n)⟩

  refine norm_diagonal_tendsto_zero
    (fun n => (T (t n) - ContinuousLinearMap.id 𝕜 X).comp S) ?_
  intro a

  have hTa :
      Tendsto (fun n => T (t n) (S a)) atTop (𝓝 (S a)) :=
    (hT (S a)).comp htWithin

  change Tendsto (fun n => T (t n) (S a) - S a) atTop (𝓝 0)
  simpa only [sub_self] using
    (hTa.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => S a) atTop (𝓝 (S a))))

end Phillips
