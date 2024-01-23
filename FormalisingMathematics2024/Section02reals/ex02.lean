import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet6 -- import a bunch of previous stuff

namespace experiment
open Section2sheet3solutions Section2sheet5solutions Finset BigOperators

/- partial sum of a sequence of real numbers a₀ + a₁ + ⋯ + aₙ₋₁ -/
def sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, a i
def abs_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, |a i|
/- a sequence of real numbers converges if it has a limit -/
def converges (a : ℕ → ℝ) : Prop := ∃ L, TendsTo a L
def cauchy (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ (N : ℕ), ∀ (n m : ℕ), (n ≥ N ∧ m ≥ N → |a n - a m| < ε)
/- a sum converges if the sequence of partial sums converges -/
def sum_conv (a : ℕ → ℝ) : Prop := converges (sum a)
/- a sum converges *absolutley* if the sequence of absolute sums converges -/
def sum_abs_conv (a : ℕ → ℝ) : Prop := converges (abs_sum a)
/- a sequence is bounded if we can find M such that |a n| ≤ M ∀ n -/
def Bounded (a : ℕ → ℝ) : Prop := ∃ M, ∀ n, |a n| ≤ M

#eval sum (fun n ↦ n) 10 -- `Real.ofCauchy (sorry /- 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, ... -/)` ??
#eval ∑ i in range 11, i -- `55`
-- **Outcome** : this is fine (eval command is not used for this)

@[simp]
lemma sum_def (a : ℕ → ℝ) (n : ℕ) : sum a n = ∑ i in range n, a i := by rfl
lemma converges_def (a : ℕ → ℝ) : converges a ↔ ∃ L, TendsTo a L := by rfl
lemma sum_conv_def (a : ℕ → ℝ) : sum_conv a ↔ converges (sum a) := by rfl
lemma sum_abs_conv_def (a : ℕ → ℝ) : sum_abs_conv a ↔ converges (abs_sum a) := by rfl
lemma cauchy_def (a : ℕ → ℝ) : cauchy a ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ (n m : ℕ), (n ≥ N ∧ m ≥ N → |a n - a m| < ε) := by rfl

/- if a sequence is cauchy, then it is bounded -/
theorem cauchy_bounded (a : ℕ → ℝ) : cauchy a → Bounded a := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  specialize hN N
  let M := max' (image (fun i ↦ |a i|) (range (N + 1))) (by norm_num)
  have hM (r : ℕ) (hr : r < N + 1) : |a r| ≤ M := by {
    apply le_max'
    rw [mem_image]
    use r
    rw [mem_range]
    exact ⟨hr, rfl⟩}
  use M + 1
  intro n
  cases' (lt_or_ge n N) with _ _
  · calc |a n| ≤ M := by {
    apply hM
    exact Nat.lt_add_right 1 (by assumption)}
    _ ≤ M + 1 := by linarith
  · calc |a n| = |a N + (a n - a N)| := by ring_nf
    _ ≤ |a N| + |a n - a N| := by exact abs_add _ _
    _ ≤ |a N| + 1 := by {
      gcongr
      specialize hN n ⟨le_refl N, by assumption⟩
      apply le_of_lt
      rw [abs_sub_comm]
      exact hN}
    _ ≤ M + 1 := by {
      gcongr
      apply hM
      exact Nat.lt.base N}

theorem cauchy_iff_convergent (a : ℕ → ℝ) : converges a ↔ cauchy a := by
  constructor
  <;> intro h
  · intro ε hε
    obtain ⟨L, hL⟩ := h
    obtain ⟨B, hB⟩ := hL (ε / 2) (by linarith)
    use B
    rintro n m ⟨hn, hm⟩
    calc |a n - a m| = |(a n - L) + (L - a m)| := by ring_nf
    _ ≤ |a n - L| + |L - a m| := abs_add (a n - L) (L - a m)
    _ < ε / 2 + ε / 2 := by {
      gcongr
      · exact hB n hn
      · rw [abs_sub_comm]
        exact hB m hm}
    _ = ε := by ring_nf
  · let b (n : ℕ) := sSup {a i | i ≥ n}
    have bMon : Monotone b := by sorry
    let L := sInf {b i | i : ℕ}
    use L
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)

    sorry

#check sSup
/- a sequence converges if it is monotone and bounded -/
lemma mono_bounded_conv (a : ℕ → ℝ) : Monotone a ∧ Bounded a → converges a := by
  intro ⟨hM, hB⟩
  by_contra h
  have : ¬ Bounded a := by {
    intro ⟨R, hR⟩
    rw [converges_def] at h
    push_neg at h
    specialize h R

    sorry
  }
  contradiction

/- absolute convergence implies convergence -/
lemma abs_conv : ∀ (a : ℕ → ℝ), sum_abs_conv a → sum_conv a := by
  intros a ha
  rw [sum_conv_def, cauchy_iff_convergent]
  rw [sum_abs_conv_def, cauchy_iff_convergent] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro m n ⟨hm, hn⟩ -- remove `⟨hm, hn⟩` replace with `hmn` if unused individually
  specialize hN m n ⟨hm, hn⟩
  wlog h : m ≤ n generalizing m n
  · specialize this n m hn hm (by rwa [abs_sub_comm] at hN) (by (rw [Nat.le_iff_lt_or_eq]; left; exact Nat.not_le.mp h))
    simpa [abs_sub_comm] using this
  rw [abs_sub_comm]
  calc |sum a n - sum a m| = |∑ i in range (n - m), a (i + m)| := by sorry
  _ ≤ ∑ i in range (n - m), |a (i + m)| := abs_sum_le_sum_abs _ _
  _ < ε := by {

    sorry
  }

example (m n : ℕ) (h : m ≤ n) (f : ℕ → ℝ) :
  ∑ i in range n, f i - ∑ i in range m, f i = ∑ i in range (n - m - 1), f (i + m) := by
  refine tsub_eq_of_eq_add_rev ?h
  induction' n with d hd generalizing m
  | zero => have : m = 0 := by sorry

            rw [this]
            exact self_eq_add_left.mpr rfl
  | succ n hn => rw [Nat.succ_eq_add_one] at *

                 specialize hn (m - 1) (by ())
  sorry

#check positivity
#check peel
/- if a sum converges its terms must tend to zero -/
lemma sum_conv_zero : ∀ (a : ℕ → ℝ), sum_conv a → TendsTo a 0 := by
  intro a ⟨L, hL⟩ ε hε
  obtain ⟨N, hN⟩ := hL (ε / 2) (by linarith)
  use N
  intro n hn
  rw [sub_zero]
  have : a n = sum a (n + 1) - sum a n := by { -- TURN INTO LEMMA?
    dsimp [sum_def]
    rw [eq_sub_iff_add_eq]
    exact (sum_range_succ_comm a n).symm
  }
  rw [this]
  calc |sum a (n + 1) - sum a n| = |(sum a (n + 1) - L) - (sum a n - L)| := by ring_nf
  _ ≤ |sum a (n + 1) - L| + |sum a n - L| := by exact abs_sub (sum a (n + 1) - L) (sum a n - L)
  _ < ε / 2 + ε / 2 := by {
    gcongr
    exact hN (n + 1) (by linarith)
    exact hN n hn
  }
  _ = ε := by linarith

/- a n nonnegative iff the partial sums are monotone increasing -/
lemma partial_monotone (a : ℕ → ℝ) : (∀ (n : ℕ), a n ≥ 0) ↔ Monotone (sum a) := by
  constructor
  · intro h x y hxy
    dsimp [sum_def]
  -- need a way to split the range of summation :
    -- have : ∀ (r s : ℕ), (r ≤ s) → ∑ i in range r, a i + ∑ i in range (r - s, s), a i = ∑ i in range s, a i := by sorry OR:
    -- have : ∀ (r s : ℕ), (r ≤ s) → ∑ i in range r, a i + ∑ i in range (r - s), a (i + r) = ∑ i in range s, a i := by sorry
    sorry
  sorry
/- The Comparison Test: if an ≤ bn and the sum of bn's converges, then the same is true for an -/
theorem comparison_test (a b : ℕ → ℝ) (ha : ∀ n, a n ≥ 0) (hab : ∀ n, a n ≤ b n) (hb : sum_conv b) : sum_conv a := by
  rw [sum_conv_def]
  apply mono_bounded_conv
  constructor
  · exact (partial_monotone a).mp ha
  · obtain ⟨M, hM⟩ := hb
    use M
    intro n
    have hbM : sum b n ≤ M := by {
      -- ASK ABOUT IN CLASS
      by_contra hc
      obtain ⟨B, hB⟩ := hM (|(M + (sum b n)) / 2 - M|) (by (
        refine abs_pos.mpr ?_
        intro hf
        linarith))
      specialize hB (B + n) (by linarith)
      have hbMono : Monotone (sum b) := by {
        rw [← partial_monotone b]
        intro m
        exact le_trans (ha m) (hab m)}
      have : sum b (B + n) < sum b n := by {
        sorry}
      unfold Monotone at hbMono
      specialize hbMono (Nat.le_add_right n B)
      rw [lt_iff_not_le, add_comm] at this
      contradiction}
    rw [sum_def] at *
    calc
      |∑ i in range n, a i| = ∑ i in range n, a i := abs_sum_of_nonneg' ha
      _ ≤ ∑ i in range n, b i := by {
        gcongr with r hr
        · exact hab r}
      _ ≤ M := hbM
#check Monotone
#check sum_range
example (a b : ℕ) : a < b ↔ ¬ b ≤ a := by exact lt_iff_not_le
sorry
-- algebra of limits ??
/- The Sandwich Test: if cn ≤ an ≤ bn and the sums of both the cn and bn converges, then the same
is true for an  -/
theorem sandwich_test (a b c : ℕ → ℝ) (hca : ∀ n, c n ≤ a n) (hab : ∀ n, a n ≤ b n) (hc : sum_conv c)
  (hb : sum_conv b) : sum_conv a := by sorry
/- if the an/bn converges to L, and the sum of the bn converges, then so does the sum of the an -/
theorem limit_test (a b : ℕ → ℝ) (h : converges (fun i ↦ (a i / b i))) (hb : sum_conv b) : sum_conv a := by
  sorry
-- alternating series test: need definition of alternating
-- ratio test
theorem ratio_test (a : ℕ → ℝ) (h : ∃ r < 1, TendsTo (fun i ↦ |(a (i + 1) / a i)|) r) : sum_abs_conv a := by sorry
-- root test
theorem root_test (a : ℕ → ℝ) (h : ∃ r < 1, TendsTo (fun i ↦ |a i|^(1 / i)) r) : sum_abs_conv a := by sorry
#lint
