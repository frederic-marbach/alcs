module

-- Background
public import ALCS.Background.Semigroup
public import ALCS.Background.Lp
public import ALCS.Background.Phillips
public import ALCS.Background.InvariantHahnBanach
-- Definitions 1.1 and 1.4, Lemma 2.1
public import ALCS.Definitions
-- Proposition 1.3
public import ALCS.ContinuityFiniteP
-- Theorem 1.5
public import ALCS.ZeroClass
-- Corollary 1.6
public import ALCS.ContinuityLinfty
-- Section 3: examples
public import ALCS.Examples.FinitePNotZeroClass
public import ALCS.Examples.ExoticMean
public import ALCS.Examples.Periodization
public import ALCS.Examples.NoRepresentation

/-!
# Continuity of solutions to abstract linear control systems

Lean formalization of the numbered statements of
F. Marbach, *Continuity of solutions to abstract linear control systems* (2026),
<https://hexagonmath.org/2610.00022>. See `README.md` for the correspondence between the
statements of the paper and the Lean declarations.
-/
