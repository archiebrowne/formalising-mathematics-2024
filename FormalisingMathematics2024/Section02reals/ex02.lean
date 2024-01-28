import Mathlib.Tactic

namespace ProjectOne
open Finset BigOperators

/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop := -- **From K.Buzzard**
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
/- partial sum of a sequence of real numbers a₀ + a₁ + ⋯ + aₙ₋₁ -/
def sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, a i
def abs_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, |a i|
/- a sequence of real numbers converges if it has a limit -/
def converges (a : ℕ → ℝ) : Prop := ∃ L, TendsTo a L
/- a sequence of real numbers is cauchy if its terms become, and remain, arbitrarily close -/
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

@[simp] -- tell these definitions to the simplifier
lemma tendsTo_def {a : ℕ → ℝ} {t : ℝ} : -- **From K.Buzzard**
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by rfl
lemma sum_def (a : ℕ → ℝ) (n : ℕ) : sum a n = ∑ i in range n, a i := by rfl
lemma abs_sum_def (a : ℕ → ℝ) (n : ℕ) : abs_sum a n = ∑ i in range n, |a i| := by rfl
lemma converges_def (a : ℕ → ℝ) : converges a ↔ ∃ L, TendsTo a L := by rfl
lemma sum_conv_def (a : ℕ → ℝ) : sum_conv a ↔ converges (sum a) := by rfl
lemma sum_abs_conv_def (a : ℕ → ℝ) : sum_abs_conv a ↔ converges (abs_sum a) := by rfl
lemma cauchy_def (a : ℕ → ℝ) : cauchy a ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ (n m : ℕ), (n ≥ N ∧ m ≥ N → |a n - a m| < ε) := by rfl

/- any term in a sequence can be represented as a telescoping sum -/
lemma sum_range_succ_sub (a : ℕ → ℝ) (n : ℕ) : a n = sum a (n + 1) - sum a n := by
/- this lemma is easily deducible from the library, but is use a ocuple of times,
so it is useful to give it in a lemma -/
  dsimp [sum_def]
/- once lean knows `sum` is just a finite `∑`, the proof is short -/
  rw [eq_sub_iff_add_eq]
  exact (sum_range_succ_comm a n).symm

/- if a sequence is cauchy, then it is bounded -/
theorem cauchy_bounded (a : ℕ → ℝ) : cauchy a → Bounded a := by
  intro h
/- we can bound the distance between terms by 1 after a certain `N` -/
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  specialize hN N
/- `max'` of a set in `ℝ` gives the maximum as an element of `ℝ` when provided
with a proof that the set is non empty  -/
  let M := max' (image (fun i ↦ |a i|) (range (N + 1))) (by norm_num)
/- `M` is the maximum of {a₁, ⋯, aₙ}, so for any of these elements, `M` is greater -/
  have hM (r : ℕ) (hr : r < N + 1) : |a r| ≤ M := by
    · apply le_max'
      rw [mem_image]
      use r
      rw [mem_range]
      exact ⟨hr, rfl⟩
/- we would now like to bound aₙ for all n. `M + 1` should work, since after `N`
the distance between terms is less than 1, and before it, all terms are less than `M` -/
  use M + 1
  intro n
/- `n` is either smaller than `N`, or at least `N`, we split into the two cases -/
  cases' (lt_or_ge n N) with _ _
/- when `n < N`, `hM` provides a proof that `|a n| < M` -/
  · calc |a n| ≤ M := by
          · apply hM
            exact Nat.lt_add_right 1 (by assumption)
    _ ≤ M + 1 := by linarith
/- when `n ≥ N`, we use the triangle inequality with `a N` which we know is bounded by `M` -/
  · calc |a n| = |a N + (a n - a N)| := by ring_nf
    _ ≤ |a N| + |a n - a N| := by exact abs_add _ _
    _ ≤ |a N| + 1 := by
/- `x ≤ y → z + x ≤ z + y` and so we can apply this fact -/
      · apply add_le_add_left
        specialize hN n ⟨le_refl N, by assumption⟩
        apply le_of_lt
        rw [abs_sub_comm]
        exact hN
    _ ≤ M + 1 := by
/- similarly, `x ≤ y → x + z ≤ y + z`, so it is enough to prove that `x ≤ y` -/
      · apply add_le_add_right
        apply hM
        exact Nat.lt.base N


/- a sequence converges if it is monotone and bounded -/
lemma mono_bounded_conv (a : ℕ → ℝ) : Monotone a ∧ Bounded a → converges a := by
  intro ⟨hM, hB⟩
/- if a sequence is monotone and bounded, then it converges to the supremum of its terms -/
  let L := sSup {a i | i : ℕ}
  use L
  intro ε hε
/- by definition of `L`, the supremum, if we take any number smaller than it,
we can find an element of the set larger than this new value -/
  have : ∃ N, a N > L - ε := by
/- to prove this, we of course need that the set is non empty, which is easily verifiable -/
    · have : {x | ∃ i, a i = x}.Nonempty := by
        · use (a 1); use 1
/- `Real.add_neg_lt_sSup` provides almost exactly what we need with a little adjustment. -/
      obtain ⟨aN, ⟨⟨N, hN⟩, _⟩⟩ := Real.add_neg_lt_sSup (this) (show -ε < 0 by linarith)
      use N
/- using just `dsimp` works here, but restricting to `only [L]` avoids searching through
irrelevant definitional equality lemmas. this is used later aswell -/
      dsimp only [L]
      linarith
  obtain ⟨N, hN⟩ := this
/- now that we have `a N > L - ε`, we know that for any `n ≥ N`, `L - ε < a n ≤ L`, and
so we can show convergence -/
  use N
  intro n hn
/- an absolute value `|x|` is bounded iff both `-x` and `x` are bounded -/
  rw [abs_sub_lt_iff]
  constructor
  · dsimp only [L]
/- more lemmas involve expressions using only `+`'s and not `-`'s so it is
helpful to change the goal to this form -/
    rw [sub_lt_iff_lt_add]
/- proving the following fact is obvious in normal mathematics, but lean does
not know anything about the set in question. we have not told it that it is
bounded or non empty, so a supremum may not exist -/
    calc a n ≤ sSup {x | ∃ i, a i = x} := by
          · specialize hM (Nat.le_add_right n 1)
            let s := {x | ∃ i, a i = x}
            have hsbound : BddAbove s := by
              · obtain ⟨R, hR⟩ := hB
                use R
                intro i ⟨k, hk⟩
                rw [← hk]
                exact le_of_abs_le (hR k)
/- whilst `ℝ` is not a `CompleteLattice` (every non empty set has a supremum + infimum),
it is a `ConditionallyCompleteLattice`, (non empty sets have suprema/imfima if they are
bounded above/bellow) and lean infers this. `le_csSup_of_le` requires a proof that the
set is bounded above in order to say anything useful about the `sSup` -/
            exact le_csSup_of_le hsbound (by use n + 1) hM
    _ < ε + sSup {x | ∃ i, a i = x} := by exact lt_add_of_pos_left (sSup {x | ∃ i, a i = x}) hε
/- the next goal is much more abvious as it just relies on the fact that `a` is monotone -/
  · rw [sub_lt_comm]
    calc L - ε < a N := by exact hN
    _ ≤ a n := by exact hM hn

/- for real numbers, cauchy and convergence criterion are equivalent -/
theorem cauchy_iff_convergent (a : ℕ → ℝ) : converges a ↔ cauchy a := by
/- `constructor` allows us to split the goal into the two directions -/
  constructor
/- for both goals, we need to introduce a hypothesis, and this can be done
using the `<;>` notation -/
  <;> intro h
  · intro ε hε
    obtain ⟨L, hL⟩ := h
    obtain ⟨B, hB⟩ := hL (ε / 2) (by linarith)
    use B
    rintro n m ⟨hn, hm⟩
    calc |a n - a m| = |(a n - L) + (L - a m)| := by ring_nf
    _ ≤ |a n - L| + |L - a m| := abs_add (a n - L) (L - a m)
    _ < ε / 2 + ε / 2 := by
      · gcongr
        · exact hB n hn
        · rw [abs_sub_comm]
          exact hB m hm
    _ = ε := by ring_nf
  · obtain ⟨A, hA⟩ := cauchy_bounded a h -- maybe don't need this direction, just stick with one way.
    let b (n : ℕ) := - sSup {a i | i ≥ n}
    have bMon : Monotone b := by sorry
    have bBounded : Bounded b := by sorry
    obtain ⟨L, hL⟩ := mono_bounded_conv b ⟨bMon, bBounded⟩
    use L
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
    use N
    intro n hn
    sorry

/- two sums of the same terms can be subtracted and represented as one sum -/
lemma sum_sub_range_sub (m n : ℕ) (h : m ≤ n) (f : ℕ → ℝ) :
  ∑ x in range n, f x - ∑ x in range m, f x = ∑ x in range (n - m), f (m + x) := by
  refine tsub_eq_of_eq_add ?h
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
  rw [ht, Nat.add_sub_self_left m t, sum_range_add f m t]
  ring

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
  calc |sum a n - sum a m| = |∑ x in range (n - m), a (m + x)| := by
        · rw [← sum_sub_range_sub m n h a]
          simp only [← sum_def a]
  _ ≤ ∑ x in range (n - m), |a (m + x)| := abs_sum_le_sum_abs _ _
  _ < ε := by
    · rw [← sum_sub_range_sub m n h (fun x ↦ |a x|)]
      simp only [← abs_sum_def]
      apply lt_of_abs_lt
      rw [abs_sub_comm]
      exact hN

/- if a sum converges its terms must tend to zero -/
lemma sum_conv_zero : ∀ (a : ℕ → ℝ), sum_conv a → TendsTo a 0 := by
  intro a ⟨L, hL⟩ ε hε
  obtain ⟨N, hN⟩ := hL (ε / 2) (by linarith)
  use N
  intro n hn
  rw [sub_zero, sum_range_succ_sub a n]
  calc |sum a (n + 1) - sum a n| = |(sum a (n + 1) - L) - (sum a n - L)| := by ring_nf
  _ ≤ |sum a (n + 1) - L| + |sum a n - L| := by exact abs_sub (sum a (n + 1) - L) (sum a n - L)
  _ < ε / 2 + ε / 2 := by
    · gcongr
      · exact hN (n + 1) (by linarith)
      · exact hN n hn
  _ = ε := by linarith

/- a sequence is nonnegative iff the partial sums are monotone increasing -/
lemma partial_monotone (a : ℕ → ℝ) : (∀ (n : ℕ), a n ≥ 0) ↔ Monotone (sum a) := by
  constructor
  · intro h x y hxy
    dsimp [sum_def]
    refine sub_nonneg.mp ?_
    rw [sum_sub_range_sub x y hxy a]
    refine sum_nonneg ?_
    intro i _
    exact h (x + i)
  · intro h n
    specialize h (Nat.le_add_right n 1)
    rw [sum_range_succ_sub a n]
    linarith

/- The Comparison Test: if an ≤ bn and the sum of bn's converges, then the same is true for an -/
theorem Comparison_Test (a b : ℕ → ℝ) (ha : ∀ n, a n ≥ 0) (hab : ∀ n, a n ≤ b n) (hb : sum_conv b) : sum_conv a := by
  rw [sum_conv_def]
  apply mono_bounded_conv
  constructor
  · exact (partial_monotone a).mp ha
  · have : Monotone (sum b) := by
      · rw [← partial_monotone b]
        intro n
        obtain ha' := ha n
        obtain hb' := hab n
        linarith
    rw [sum_conv_def, cauchy_iff_convergent] at hb
    obtain ⟨M, hM⟩ := cauchy_bounded (sum b) hb
    use M
    intro n
    calc |sum a n| ≤ |sum b n| := by
          · simp only [sum_def]
            rw [abs_sum_of_nonneg' ha, le_abs]
            left
            apply sum_le_sum
            intro i _
            exact hab i
    _ ≤ M := by exact hM n

/- The Sandwich Test: if cn ≤ an ≤ bn and the sums of both the cn and bn converges, then the same
is true for an  -/
theorem Sandwich_Test (a b c : ℕ → ℝ) (hca : ∀ n, c n ≤ a n) (hab : ∀ n, a n ≤ b n) (hc : sum_conv c)
  (hb : sum_conv b) : sum_conv a := by
  rw [sum_conv_def, cauchy_iff_convergent, cauchy_def] at *
  intros ε hε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  obtain ⟨Nb, hNb⟩ := hb ε hε
  use max Nc Nb
  intros n m hnm
  specialize hNb n m ⟨le_of_max_le_right hnm.1, le_of_max_le_right hnm.2⟩
  specialize hNc n m ⟨le_of_max_le_left hnm.1, le_of_max_le_left hnm.2⟩
  rw [abs_sub_lt_iff] at *
  wlog h : m ≤ n generalizing n m
  · exact (this m n hnm.symm hNb.symm hNc.symm (Nat.le_of_not_ge h)).symm
  constructor
  · calc
    sum a n - sum a m ≤ sum b n - sum b m := by
      · simp only [sum_def]
        rw [sum_sub_range_sub m n h a, sum_sub_range_sub m n h b]
        refine sum_le_sum ?_
        intro i _
        exact hab (m + i)
    _ < ε := by exact hNb.1
  · rw [← neg_sub, neg_lt]
    calc
    -ε < sum c n - sum c m := by
      · rw[← neg_sub, neg_lt]
        simp only [neg_sub]
        exact hNc.2
    _  ≤ sum a n - sum a m := by
      · simp only [sum_def]
        rw [sum_sub_range_sub m n h a, sum_sub_range_sub m n h c]
        refine sum_le_sum ?_
        intro i _
        exact hca (m + i)

-- spent ages proving / trying to find this only to realise the addition of n + x was flipped in the library
example (n t : ℕ) (f : ℕ → ℝ) :
  ∑ x in range (n + t), f x = ∑ x in range n, f x + ∑ x in range t, f (n + x) := by
  exact sum_range_add f n t

/- if the an/bn converges to L, and the sum of the bn converges, then so does the sum of the an -/
theorem limit_test (a b : ℕ → ℝ) (h : converges (fun i ↦ (a i / b i))) (hb : sum_conv b) : sum_conv a := by
  sorry
-- alternating series test: need definition of alternating
-- ratio test
theorem ratio_test (a : ℕ → ℝ) (h : ∃ r < 1, TendsTo (fun i ↦ |(a (i + 1) / a i)|) r) : sum_abs_conv a := by sorry
-- root test
theorem root_test (a : ℕ → ℝ) (h : ∃ r < 1, TendsTo (fun i ↦ |a i|^(1 / i)) r) : sum_abs_conv a := by sorry
-- #lint
