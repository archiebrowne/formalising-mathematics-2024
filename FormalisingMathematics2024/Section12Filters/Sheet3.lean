/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.Order.Filter.Basic

/-!

# Examples of filters

## `at_top` filter on a totally ordered set

Let `L` be a non-empty totally ordered set. Let's say that a subset `X` of `L` is
"big" if there exists `x : L` such for all `y ≥ x`, `y ∈ X`.

I claim that the big subsets are a filter. Check this. The mathematical idea
is that the "big subsets" are the neighbourhoods of `∞`, so the corresponding
filter is some representation of an infinitesimal neighbourhood of `∞`.

Implementation notes: `LinearOrder L` is the type of linear orders on `L`.
`e : L` is just an easy way of saying that `L` is nonempty.

Recall that `max x y` is the max of x and y in a `LinearOrder`, and
`le_max_left a b : a ≤ max a b` and similarly `le_max_right`.
-/

namespace Section12sheet3

open Set

def atTop (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    use e
    intro y hy
    triv
  sets_of_superset := by
    rintro P Q ⟨x, hx⟩ hPQ
    use x
    intro y hy
    specialize hx y hy
    exact hPQ hx
  inter_sets := by
    intro P Q ⟨a, ha⟩ ⟨b, hb⟩
    use max a b
    intro y hy
    constructor
    · exact ha y (le_of_max_le_left hy)
    · exact hb y (le_of_max_le_right hy)

/-

## the cofinite filter

The _cofinite filter_ on a type `α` has as its sets the subsets `S : set α`
with the property that `Sᶜ`, the complement of `S`, is finite.
Let's show that these are a filter.

Things you might find helpful:

`compl_univ : univᶜ = ∅`
`finite_empty : Finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`Finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.Finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`Finite.union : S.finite → T.finite → (S ∪ T).Finite`

NB if you are thinking "I could never use Lean by myself, I don't know
the names of all the lemmas so I have to rely on Kevin telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/
def cofinite (α : Type) : Filter α where
  sets := {S : Set α | Sᶜ.Finite}
  univ_sets := by
    dsimp
    rw [compl_univ]
    exact finite_empty
  sets_of_superset := by
    intro P Q hP hPQ
    dsimp
    apply (Finite.subset hP)
    exact compl_subset_compl.mpr hPQ
  inter_sets := by
    intro P Q hP hQ
    dsimp at hP hQ ⊢
    rw [compl_inter]
    exact Finite.union hP hQ

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `atTop` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `atTop` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

open scoped Filter

/-- cofinite filter on a finite type is the entire power set `⊥`. -/
example (α : Type) : cofinite (Fintype α) = ⊥ := by
  ext X
  constructor <;>
  intro _
  · triv
  · exact toFinite Xᶜ
example (p q : Prop) : (p → q) ↔ (¬ q → ¬ p) := by exact Iff.symm not_imp_not


/-- the cofinite filter on `ℕ` is the `atTop` filter. -/
example : cofinite ℕ = atTop ℕ 0 := by
  ext X
  constructor <;>
  intro h
  · have : Xᶜ.Finite := by exact h
    rw [finite_iff_bddAbove] at this
    obtain ⟨L, hL⟩ := this
    use L + 1
    intro y hy
    by_contra h'
    specialize hL h'
    linarith
  · obtain ⟨L, hL⟩ := h
    refine finite_iff_bddAbove.mpr ?_
    use L
    intro r hr
    by_contra hr'
    specialize hL r (by linarith)
    contradiction

/-- the cofinite filter on `ℤ` is not equal to the `atTop` fliter. -/
example : cofinite ℤ ≠ atTop ℤ 0 := by sorry

/-- the cofinite filter on `ℕ` is not principal. -/
example : ∀ (X : Set ℕ), cofinite ℕ ≠ 𝓟 X := by sorry


end Section12sheet3
