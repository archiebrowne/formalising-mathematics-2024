import Mathlib.Tactic

namespace ProjectOne
open Finset BigOperators

/-
In this file, I prove both the Comparison Test and the Sandwich Test for infinite sums
of real numbers. Before this, some auxillary definitions and lemmas are made / proven.

I have used the definition of `TendsTo` from the formalising mathematics course sheets.
Additionally I written my own definitions of sums, absolute sums, cauchy sequences and
bounded sequences as well has what it means for a sum to converge.
-/

/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop := -- **From K.Buzzard**
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
/-- partial sum of a sequence of real numbers `a₀ + a₁ + ⋯ + aₙ₋₁` -/
def sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, a i
/-- partial absolute sum of a sequence of real numbers `|a₀| + |a₁| + ⋯ + |aₙ₋₁|`-/
def abs_sum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i in range n, |a i|
/-- a sequence of real numbers converges if it has a limit -/
def converges (a : ℕ → ℝ) : Prop := ∃ L, TendsTo a L
/-- a sequence of real numbers is cauchy if its terms become, and remain, arbitrarily close -/
def cauchy (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ (N : ℕ), ∀ (n m : ℕ), (n ≥ N ∧ m ≥ N → |a n - a m| < ε)
/-- a sum converges if the sequence of partial sums converges -/
def sum_conv (a : ℕ → ℝ) : Prop := converges (sum a)
/-- a sum converges *absolutley* if the sequence of absolute sums converges -/
def sum_abs_conv (a : ℕ → ℝ) : Prop := converges (abs_sum a)
/-- a sequence is bounded if we can find M such that |a n| ≤ M ∀ n -/
def Bounded (a : ℕ → ℝ) : Prop := ∃ M, ∀ n, |a n| ≤ M

@[simp] -- tell these definitions to the simplifier
lemma tendsTo_def {a : ℕ → ℝ} {t : ℝ} : -- **From K.Buzzard**
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by rfl
lemma sum_def (a : ℕ → ℝ) (n : ℕ) : sum a n = ∑ i in range n, a i := by rfl
lemma abs_sum_def (a : ℕ → ℝ) (n : ℕ) : abs_sum a n = ∑ i in range n, |a i| := by rfl
lemma converges_def (a : ℕ → ℝ) : converges a ↔ ∃ L, TendsTo a L := by rfl
lemma sum_conv_def (a : ℕ → ℝ) : sum_conv a ↔ converges (sum a) := by rfl
lemma sum_abs_conv_def (a : ℕ → ℝ) : sum_abs_conv a ↔ converges (abs_sum a) := by rfl
lemma cauchy_def (a : ℕ → ℝ) : cauchy a ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ (n m : ℕ), (n ≥ N ∧ m ≥ N → |a n - a m| < ε) := by rfl

/-- any term in a sequence can be represented as the difference of two sums -/
lemma sum_range_succ_sub (a : ℕ → ℝ) (n : ℕ) : a n = sum a (n + 1) - sum a n := by
/- this lemma is easily deducible from the library, but is uses a couple of times,
so it is useful to give it in a lemma -/
  dsimp only [sum_def]
/- once lean knows `sum` is just a `∑`, the proof is short -/
  rw [eq_sub_iff_add_eq]
  exact (sum_range_succ_comm a n).symm

/-- if a sequence is cauchy, then it is bounded -/
lemma cauchy_bounded (a : ℕ → ℝ) : cauchy a → Bounded a := by
  intro h
/- we can bound the distance between terms by 1 after a certain `N` -/
  obtain ⟨N, hN⟩ := h 1 (by positivity)
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


/-- a sequence converges if it is monotone and bounded -/
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
set is bounded above in order to say anything useful about the `sSup`. thanks to
**K.Buzzard** for pointing this out in the discord. -/
            exact le_csSup_of_le hsbound (by use n + 1) hM
    _ < ε + sSup {x | ∃ i, a i = x} := by exact lt_add_of_pos_left (sSup {x | ∃ i, a i = x}) hε
/- the next goal is much more abvious as it just relies on the fact that `a` is monotone -/
  · rw [sub_lt_comm]
    calc L - ε < a N := by exact hN
    _ ≤ a n := by exact hM hn

/-- for real numbers, cauchy and convergence criterion are equivalent -/
lemma cauchy_iff_convergent (a : ℕ → ℝ) : converges a ↔ cauchy a := by
/- `constructor` allows us to split the goal into the two directions -/
  constructor
/- for both goals, we need to introduce a hypothesis, and this can be done
using the `<;>` notation -/
  <;> intro h
  · intro ε hε
/- proving `converges a → cauchy a` is the easy direction. since we can eventually
bound `|a n - L|` where `L` is the limit, we can use a triangle inequality to
bound `|a n - a m|`-/
    obtain ⟨L, hL⟩ := h
    obtain ⟨B, hB⟩ := hL (ε / 2) (by positivity)
    use B
    rintro n m ⟨hn, hm⟩
/- this is the triangle inequality we would like to prove -/
    calc |a n - a m| = |(a n - L) + (L - a m)| := by ring_nf
/- if the proof of a `calc` step is a one liner, we often don't need to enter
tactic mode using `by` -/
    _ ≤ |a n - L| + |L - a m| := abs_add (a n - L) (L - a m)
    _ < ε / 2 + ε / 2 := by
/- `gcongr` usefully splits up `a + b < c + d` into two goals `a < c` and `b + d` -/
      · gcongr
        · exact hB n hn
        · rw [abs_sub_comm]
          exact hB m hm
    _ = ε := add_halves ε
/- the next direction seems a lot harder, at least with the proof I wa attempting.
my strategy was to show that the sequence of `bₙ = -sSup {a i | i ≥ n}` was monotone
increasing, and bounded therefore convergent. Then show that `aₙ` converges to
this limit multiplied by -1. The reason i tried with all the negatives was because
`mono_bounded_conv` only allows for monotone increasing, not monotone decreasing.
perhaps I should have allowed for both but at this point the project was getting
quite long! A lesson I guess is to prove things in the correct generality from the start -/
  · obtain ⟨A, hA⟩ := cauchy_bounded a h
    let b (n : ℕ) := - sSup {a i | i ≥ n}
    have bMon : Monotone b := by sorry
    have bBounded : Bounded b := by sorry
    obtain ⟨L, hL⟩ := mono_bounded_conv b ⟨bMon, bBounded⟩
    use L
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
    use N
    intro n hn
/- this inequality seems difficult to prove, I would need to find `a m` which is
within `ε / 2` of the limit of the sequence `bₙ` using the fact is is defined
by an `sSup` -/
    sorry

/-- two sums of the same terms can be subtracted and represented as one sum -/
lemma sum_sub_range_sub (m n : ℕ) (h : m ≤ n) (f : ℕ → ℝ) :
  ∑ x in range n, f x - ∑ x in range m, f x = ∑ x in range (n - m), f (m + x) := by
/- this lemma is *almost* in the library, this is just a rearrangement, since it
occurs a couple of times in the proofs bellow -/
  refine tsub_eq_of_eq_add ?h
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
/- `sum_range_add` is the key lemma, everythiing else is just rearangement -/
  rw [ht, Nat.add_sub_self_left m t, sum_range_add f m t]
  ring

/-- absolute convergence implies convergence -/
lemma abs_conv : ∀ (a : ℕ → ℝ), sum_abs_conv a → sum_conv a := by
  intros a ha
/- the proof of the lemma becomes much clearer when we unpack
that `converges` is the same as `cauchy` -/
  rw [sum_conv_def, sum_abs_conv_def, cauchy_iff_convergent] at *
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro m n ⟨hm, hn⟩
  specialize hN m n ⟨hm, hn⟩
/- we need to be able to assume that one of `m`, `n` is less than or
equal to the other. the `wlog` tactic allows us to do this. once
used, we must supply a proof that we can reach the same goal using
this neq assumption -/
  wlog h : m ≤ n generalizing m n
  · specialize this n m hn hm (by rwa [abs_sub_comm] at hN)
                              (by (rw [Nat.le_iff_lt_or_eq]; left; exact Nat.not_le.mp h))
    simpa [abs_sub_comm] using this
  rw [abs_sub_comm]
  calc |sum a n - sum a m| = |∑ x in range (n - m), a (m + x)| := by
/- assuming `m ≤ n` is useful at this stage, since `n - m` appears in the
range of a sum. additionally, we find the first use of our lemma
`sum_sub_range_sub` -/
        · rw [← sum_sub_range_sub m n h a]
          simp only [← sum_def a]
/- this is the triangle inequality for sums -/
  _ ≤ ∑ x in range (n - m), |a (m + x)| := abs_sum_le_sum_abs _ _
  _ < ε := by
/- `sum_sub_range_sub` takes in a function `ℕ → ℝ`, and we would like to
apply it to the sequence `|aₙ|`, so we give it a function describing this
sequence `fun x ↦ |a x|` -/
    · rw [← sum_sub_range_sub m n h (fun x ↦ |a x|)]
/- the rest of this part is proving that the goal is equivalent to `hN` -/
      simp only [← abs_sum_def]
      apply lt_of_abs_lt
      rw [abs_sub_comm]
      exact hN

/-- if a sum converges its terms must tend to zero -/
lemma sum_conv_zero : ∀ (a : ℕ → ℝ), sum_conv a → TendsTo a 0 := by
  intro a ⟨L, hL⟩ ε hε
  obtain ⟨N, hN⟩ := hL (ε / 2) (by positivity)
  use N
  intro n hn
/- since we know the sum converges, it is helpful to write `a n` as
the difference of two sums, and this is what our lemma `sum_range_succ_sub`
allos us to do -/
  rw [sub_zero, sum_range_succ_sub a n]
/- now we have `a n` in this form, we can use the triangle inequality
aswell as the fact that `sum a → L` to prove the inequality -/
  calc |sum a (n + 1) - sum a n| = |(sum a (n + 1) - L) - (sum a n - L)| := by ring_nf
  _ ≤ |sum a (n + 1) - L| + |sum a n - L| := abs_sub (sum a (n + 1) - L) (sum a n - L)
  _ < ε / 2 + ε / 2 := by
/- `gcongr` is again helpful in proving inequalities involving sums -/
    · gcongr
      · exact hN (n + 1) (by linarith)
      · exact hN n hn
  _ = ε := add_halves ε

/-- a sequence is nonnegative iff the partial sums are monotone increasing -/
lemma partial_monotone (a : ℕ → ℝ) : (∀ (n : ℕ), a n ≥ 0) ↔ Monotone (sum a) := by
  constructor
  · intro h x y hxy
/- proving the sum of non negative values up to `x` is less than the
sum up to `y` where `x ≤ y` is not too tricky, and made easier by the
`sum_sub_range_sub` lemma we proved earlier -/
    dsimp [sum_def]
    refine sub_nonneg.mp ?_
    rw [sum_sub_range_sub x y hxy a]
    refine sum_nonneg ?_
    intro i _
    exact h (x + i)
/- the next direction is easier, and it is again useful to
write `a n` as the difference of two sums, using `sum_range_succ_sub` -/
  · intro h n
    specialize h (Nat.le_add_right n 1)
    rw [sum_range_succ_sub a n]
    linarith

/-- The Comparison Test: if an ≤ bn and the sum of bn's converges,
then the same is true for an -/
theorem Comparison_Test (a b : ℕ → ℝ) (ha : ∀ n, a n ≥ 0) (hab : ∀ n, a n ≤ b n)
(hb : sum_conv b) : sum_conv a := by
/- finally, we arrive at the first main theorem, the sandwich test. the strategy of
the proof is to prove that `sum a` is both bounded and monotone, and then by
`mono_bounded_conv` we will be done -/
  rw [sum_conv_def]
  apply mono_bounded_conv
  constructor
/- `sum a ` is monotone: this simple using `partial_monotone` which we proved earlier -/
  · exact (partial_monotone a).mp ha
/- `sum a` is bounded: this is true because since `sum b` converges, it is
cauchy, and hence bounded via `cauchy_bounded`. the rest of the proof
is showing that this same upper bound works for `sum a` -/
  · rw [sum_conv_def, cauchy_iff_convergent] at hb
    obtain ⟨M, hM⟩ := cauchy_bounded (sum b) hb
    use M
    intro n
/- this next inequality is simple mathematically, but requires some
justification since we need to tell lean that both the sums are
of nonnegative values -/
    calc |sum a n| ≤ |sum b n| := by
          · simp only [sum_def]
            rw [abs_sum_of_nonneg' ha, le_abs]
            left
            apply sum_le_sum
            intro i _
            exact hab i
    _ ≤ M := by exact hM n

/-- The Sandwich Test: if cn ≤ an ≤ bn and the sums of both the cn and bn converges, then the same
is true for an  -/
theorem Sandwich_Test (a b c : ℕ → ℝ) (hca : ∀ n, c n ≤ a n) (hab : ∀ n, a n ≤ b n) (hc : sum_conv c)
  (hb : sum_conv b) : sum_conv a := by
/- the strategy here was to convert all mentions of `converges` to `cauchy`,
and show that `sum a` is cauchy -/
  rw [sum_conv_def, cauchy_iff_convergent, cauchy_def] at *
  intros ε hε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  obtain ⟨Nb, hNb⟩ := hb ε hε
  use max Nc Nb
  intros n m hnm
  specialize hNb n m ⟨le_of_max_le_right hnm.1, le_of_max_le_right hnm.2⟩
  specialize hNc n m ⟨le_of_max_le_left hnm.1, le_of_max_le_left hnm.2⟩
/- `|x| < ε ↔ x < ε ∧ -x < ε`, and each of the conjuncts are easier to prove
than `|x| < ε` on its own. so we split up both the goal and `hNb`, `hNc` into this
form -/
  rw [abs_sub_lt_iff] at *
/- again, we use `wlog` to assume the order of `m`, `n`. this is
helpful when we use `sum_sub_range_sub` later -/
  wlog h : m ≤ n generalizing n m
  · exact (this m n hnm.symm hNb.symm hNc.symm (Nat.le_of_not_ge h)).symm
  constructor
/- `sum a n - sum a m < ε` since `sum b n - sum b m < ε` by assumption -/
  · calc
    sum a n - sum a m ≤ sum b n - sum b m := by
      · simp only [sum_def]
/- once we tell lean that `sum` quantities are just `∑`'s and convert them into
single sums, things become easier. here we need to make use of `h`, the assumption
that `m ≤ n` -/
        rw [sum_sub_range_sub m n h a, sum_sub_range_sub m n h b]
        refine sum_le_sum ?_
        intro i _
        exact hab (m + i)
    _ < ε := hNb.1
/- `sum a m - sum a n < ε` since `-ε < sum c n - sum c m` by assumption, although
this is a slightly different form to what our assumption says, so
a little justification is required -/
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

/- finally, a small remark: I spent quite a while trying to prove this example when proving
`sum_sub_range_sub`, only to realise that it was already in the library as `sum_range_add`.
the reason `exact?` did not work was because I had written `x + n` and not `n + x` in the
second sum in the statment. perhaps seeing beyone these intricacies is something
that lean needs to improve upon in order to become more accessible for more people -/
example (n t : ℕ) (f : ℕ → ℝ) :
  ∑ x in range (n + t), f x = ∑ x in range n, f x + ∑ x in range t, f (n + x) :=
  sum_range_add f n t

/-
Well, that was rather long - bellow is a few things I had originally aimed at proving,
but realised that they would take a lot more time.
-/

/-- The Limit Test: if the `a n / b n` converges to `L`, and the sum of the `b n`
converges, then so does the sum of the `a n` -/
theorem Limit_Test (a b : ℕ → ℝ) (h : converges (fun i ↦ (a i / b i)))
(hb : sum_conv b) : sum_conv a := by sorry
/-- The Ratio Test: if `a (n + 1) / a n` converges to `r < 1`, then the sum of the `a n`
converges absoloutley -/
theorem Ratio_Test (a : ℕ → ℝ)
(h : ∃ r < 1, TendsTo (fun i ↦ |(a (i + 1) / a i)|) r) : sum_abs_conv a := by sorry
/-- The Root Test: if `|a n|^(1 / n)` converges to `r < 1`, the the sum of the `a n`
convrges absoloutley -/
theorem Root_Test (a : ℕ → ℝ)
(h : ∃ r < 1, TendsTo (fun i ↦ |a i|^(1 / i)) r) : sum_abs_conv a := by sorry
#lint
