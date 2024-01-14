/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions Finset BigOperators

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  obtain ⟨B, hB⟩ := h (ε / 37) (by linarith)
  use B
  intro n hn
  specialize hB n hn
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;>
  linarith
  done


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  obtain ⟨B, hB⟩ := h (ε / c) (by exact div_pos hε hc)
  use B
  intro n hn
  rw [← mul_sub, abs_mul, abs_of_nonneg]
  ·exact (lt_div_iff' hc).mp (hB n hn)
  ·linarith
  done

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
-- we know by the previous that when the constant is positive, the result holds
  obtain h' := @tendsTo_pos_const_mul a t h (-c) (by linarith)
-- switch signs of h', simplify it, and then observe it is exactly the goal
  simpa using tendsTo_neg h'
  done

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  cases' (lt_or_ge c 0) with h1 h2
  ·exact tendsTo_neg_const_mul h (by linarith)
  ·cases' (LE.le.eq_or_gt h2) with h3 h4
   · rw [h3, tendsTo_def]
     intro ε hε
     use 1
     intro n hn
     simpa
   ·exact tendsTo_pos_const_mul h (by linarith)
  done

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  rw [show (fun n => a n * c) = (fun n => c * a n) by (refine funext ?h; intro x; ring_nf)]
  rw [mul_comm]
  exact tendsTo_const_mul c h
  done

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
-- an = (an - bn) + bn, and we know that sums of limits are limits of sums
  simpa using tendsTo_add h1 h2
  done

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  <;> intro h
  · simpa using tendsTo_sub h (tendsTo_const t)
  · simpa using tendsTo_add h (tendsTo_const t)
  done

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha ε hε
  obtain ⟨Nb, hNb⟩ := hb 1 zero_lt_one
  use max Na Nb
  intro n hn
  simp
  rw [abs_mul, show ε = ε * 1 by ring_nf]
  specialize hNa n (by exact le_of_max_le_left hn)
  specialize hNb n (by exact le_of_max_le_right hn)
  rw [sub_zero] at hNa hNb
  refine mul_lt_mul'' hNa hNb (by norm_num) (by norm_num)
  done

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_sub_lim_iff] at ha hb
  intro ε hε
  obtain ⟨Na, hNa⟩ := ha (min 1 ε) (by simpa using hε)
  obtain ⟨Nb, hNb⟩ := hb (min 1 ε) (by simpa using hε)
  use max Na Nb
  intro n hn
  dsimp
  rw [show a n = t + (a n - t) by ring,
      show b n = u + (b n - u) by ring]
  -- need simple way to do this
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  rw [show s = t ↔ ∀ ε > 0, |s - t| < ε by sorry]
  intro ε hε
  obtain ⟨N1, hN1⟩ := hs (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := ht (ε / 2) (by linarith)
  rw [show s - t = (s - a (max N1 N2)) + (a (max N1 N2) - t) by ring]
  --calc |s - a (max N1 N2) + (a (max N1 N2) - t)| ≤ |s - a (max N1 N2)| + |a (max N1 N2) - t| := by sorry
-- need a simple way to do this
-- try by contradiction
  sorry



end Section2sheet6
