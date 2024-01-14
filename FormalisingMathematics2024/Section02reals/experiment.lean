import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet6 -- import a bunch of previous stuff

namespace experiment
open Section2sheet3solutions Section2sheet5solutions Finset BigOperators

-- initial definition of a partial sum
def partial_sum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i in range (n + 1), a i

-- evals to `Real.ofCauchy (sorry /- 55, ...` which is not what we want
#eval partial_sum (fun k ↦ k) 10
-- this is what we want (?) i think
#eval ∑ i in range (11), i

-- initial definition os a convergent sequence
def converges (a : ℕ → ℝ) : Prop :=
  ∃ L, ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |L - a n| < ε

-- sum of 0's
def zero_sum (n : ℕ) : ℝ :=
  ∑ i in range (n + 1), 0

lemma zero_sum_def (n : ℕ) : zero_sum n = ∑ i in range (n + 1), 0 := by rfl

-- sum of zeros converges
example : converges zero_sum := by
  use 0
  intro ε hε
  use 1
  intro n hn
  simp
  rw [zero_sum_def]
  norm_num
  linarith

/-
**Plan for Coursework 1**
Convergence of series

DEFINITIONS
  - Partial sum of sequence
  - Sum converges iff the sequence of partial sums converges
  - Absolute Convergence
  - Diverges

THEOREMS
  - Sum convergent implies sequence converges to zero
  - Comparison Test
  - Algebra of Limits for series
  - Absoloutley convergent => Convergent
  - Sandwich Test
  - Comparison Test III: an/bn → L and bn abs.conv => an abs conv
  - Alternatig Series Test
  - Ratio Test
  - Root Test
  -


-/
