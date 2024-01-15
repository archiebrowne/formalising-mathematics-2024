import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet6 -- import a bunch of previous stuff

namespace experiment
open Section2sheet3solutions Section2sheet5solutions Finset BigOperators

-- initial definition of a partial sum
def partial_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range (n + 1), a i
def partial_abs_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range (n + 1), |a i|

@[simp]
lemma partial_sum_def (a : ℕ → ℝ) (n : ℕ) : partial_sum a n = ∑ i in range (n + 1), a i := by rfl

-- evals to `Real.ofCauchy (sorry /- 55, ...` which is not what we want
#eval partial_sum (fun k ↦ k) 10
-- this is what we want (?) i think
#eval ∑ i in range (11), i

-- initial definition of a convergent sequence
def sum_converges (a : ℕ → ℝ) : Prop :=
  ∃ L, TendsTo (partial_sum a) L

def sum_abs_converges (a : ℕ → ℝ) : Prop :=
  ∃ L, TendsTo (partial_abs_sum a) L

def Bounded (a : ℕ → ℝ) : Prop := ∃ M, ∀ n, a n ≤ M

lemma mono_bounded_conv (a : ℕ → ℝ) : Monotone a ∧ Bounded a → ∃ L ,TendsTo a L := by sorry

lemma abs_conv : ∀ (a : ℕ → ℝ), sum_abs_converges a → sum_converges a := by sorry



/- if the sequence of partial sums converges, then an → 0 -/
lemma sum_conv_zero : ∀ (a : ℕ → ℝ), sum_converges a → TendsTo a 0 := by
  rintro a ⟨L, ha⟩ ε hε
  obtain ⟨N, hN⟩ := ha (ε / 3) (by linarith)
  use (N + 1)
  intro n hn
  rw [sub_zero]
  calc |a n| = |partial_sum a n - partial_sum a (n - 1)| := by {
    refine abs_eq_abs.mpr ?_
    left
    refine eq_sub_of_add_eq ?h.h
    rw [partial_sum_def]
    rw [partial_sum_def]
    rw [show (n - 1) + 1 = n by sorry]
    exact (sum_range_succ_comm (fun x => a x) n).symm
  }
          _  = |(partial_sum a n - L) + (L - partial_sum a (n - 1))| := by ring_nf
          _  ≤ |(partial_sum a n - L)| + |(L - partial_sum a (n - 1))| := by exact abs_add (partial_sum a n - L) (L - partial_sum a (n - 1))
          _  < ε / 3 + ε / 3 := by {
            gcongr
            · exact hN n (by linarith)
            · rw [abs_sub_comm]
              exact hN (n - 1) (by exact Nat.le_sub_one_of_lt hn)
          }
  linarith
  done

/- a n is nonnegative for all n iff the sequence of partial sums is monotone increasing -/
lemma partial_monotone (a : ℕ → ℝ) : (∀ (n : ℕ), a n ≥ 0) ↔ Monotone (partial_sum a) := by
  constructor
  · intro h r s hrs
    dsimp
    have : ∑ i in range (s + 1), a i = ∑ i in range (r + 1), a i + ∑ i in range (s - r), a i := by sorry
    rw [this, le_add_iff_nonneg_right]
    exact sum_nonneg' h
  · intro h n
    unfold Monotone at h
    specialize h (show n - 1 ≤ n by exact Nat.sub_le n 1)
    dsimp at h
    rw [show n - 1 + 1 = n by sorry] at h
    rw [sum_range_succ_comm] at h
    exact nonneg_of_le_add_left h
  done

theorem comparison_test (a b : ℕ → ℝ) (hab : ∀ n, a n ≤ b n) (hb : sum_converges b) : sum_converges a := by

  sorry






/-
**Plan for Coursework 1**
Convergence of series

DEFINITIONS
  * Partial sum of sequence
  * Sum converges iff the sequence of partial sums converges
  * Absolute Convergence
  * Diverges
  * need a way to thinkn about the limit of a series

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
