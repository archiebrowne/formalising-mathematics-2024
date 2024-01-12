/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3solutions

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw [tendsTo_def] at *
  intro ε hε
  obtain ⟨B, hB⟩ := ha ε hε
  use B
  intro n
  specialize hB n
-- Is there a way to do this with exact things?
  rw [
    show |-a n - -t| = |-(a n - t)| by (norm_num; ring_nf),
    abs_neg _
  ]
  exact hB

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def] at *
-- let ε be arbitrary
  intro ε hε
-- find Na, Nb such that |a n - t|, |b n - u| < ε / 2 for n > Na, Nb resp
  obtain ⟨Na, hNa⟩ := ha (ε / 2) (by linarith)
  obtain ⟨Nb, hNb⟩ := hb (ε / 2) (by linarith)
-- use the maximum of these n values, so that both inequalities are satisfied
  use max Na Nb
  intro n hn
-- final calcluation, using the triangle inequality
  calc
    |a n + b n - (t + u)| = |(a n - t) + (b n - u)| := by ring_nf
    _ ≤ |a n - t| + |b n - u| := by exact abs_add (a n - t) (b n - u)
    _ < ε / 2 + ε / 2 := by refine add_lt_add ?_ ?_
                            exact hNa n (by exact le_of_max_le_left hn)
                            exact hNb n (by exact le_of_max_le_right hn)
    _ = ε := by norm_num

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  sorry

end Section2sheet5
