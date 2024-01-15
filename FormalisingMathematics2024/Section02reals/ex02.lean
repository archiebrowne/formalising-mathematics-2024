import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet6 -- import a bunch of previous stuff

namespace experiment
open Section2sheet3solutions Section2sheet5solutions Finset BigOperators

/- partial sum of a sequence of real numbers -/
def sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range (n + 1), a i
def abs_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range (n + 1), |a i|

@[simp]
lemma sum_def (a : ℕ → ℝ) (n : ℕ) : sum a n = ∑ i in range (n + 1), a i := by rfl

/- a sequence of real numbers converges if it has a limit -/
def converges (a : ℕ → ℝ) : Prop := ∃ L, TendsTo a L
/- a sum converges if the sequence of partial sums converges -/
def sum_conv (a : ℕ → ℝ) : Prop := ∃ L, TendsTo (sum a) L
/- a sum converges *absolutley* is the sequence of absolute sums converges -/
def sum_abs_conv (a : ℕ → ℝ) : Prop := ∃ L, TendsTo (abs_sum a) L

def Bounded (a : ℕ → ℝ) : Prop := ∃ M, ∀ n, a n ≤ M

/- a sequence converges if it is monotone and bounded -/
lemma mono_bounded_conv (a : ℕ → ℝ) : Monotone a ∧ Bounded a → converges a := by sorry
/- absolute convergence implies convergence -/
lemma abs_conv : ∀ (a : ℕ → ℝ), sum_abs_conv a → sum_conv a := by sorry
/- if a sum converges its terms must tend to zero -/
lemma sum_conv_zero : ∀ (a : ℕ → ℝ), sum_conv a → TendsTo a 0 := by sorry
/- a n nonnegative iff the partial sums are monotone increasing -/
lemma partial_monotone (a : ℕ → ℝ) : (∀ (n : ℕ), a n ≥ 0) ↔ Monotone (sum a) := by sorry
/- The Comparison Test: if an ≤ bn and the sum of bn's converges, then the same is true for an -/
theorem comparison_test (a b : ℕ → ℝ) (hab : ∀ n, a n ≤ b n) (hb : sum_conv b) : sum_conv a := by sorry
-- algebra of limits ??
/- The Sandwich Test: if cn ≤ an ≤ bn and the sums of both the cn and bn converges, then the same
is true for an  -/
theorem sandwich_test (a b c : ℕ → ℝ) (hca : ∀ n, c n ≤ a n) (hab : ∀ n, a n ≤ b n) (hc : sum_conv c)
  (hb : sum_conv b) : sum_conv a := by sorry
/- if the an/bn converges to L, and the sum of the bn converges, then so does the sum of the an -/
theorem limit_test (a b : ℕ → ℝ) (h : ∃ L, TendsTo (fun i ↦ (a i / b i)) L) (hb : sum_conv b) : sum_conv a := by
  sorry
-- alternating series test: need definition of alternating
-- ratio test
-- root test
