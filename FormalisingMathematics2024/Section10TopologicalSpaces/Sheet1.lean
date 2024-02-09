/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
    · dsimp
      right
      triv -- use `dsimp`
  isOpen_inter := by
    · rintro s t (rfl | rfl) (rfl | rfl)
      · left; simp
      · left; simp
      · left; simp
      · right; simp
            -- use `cases'`
  isOpen_sUnion := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      aesop
    · left
      have : ∀ s ∈ F, s = ∅ := by
        · intro s hs
          by_contra! h2
          rcases h2 with ⟨a, b⟩
          specialize hF s hs
          cases' hF with x y
          · simp_all only [Set.mem_empty_iff_false]
          · rw [y] at hs
            contradiction
      exact Set.sUnion_eq_empty.mpr this
    -- do cases on whether Set.univ ∈ F


-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  convert isOpen_sUnion (s := ∅) ?_ <;> simp

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 1
  norm_num

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  obtain ⟨δ1, ⟨h1l, h1r⟩⟩ := hs x hx.1
  obtain ⟨δ2, ⟨h2l, h2r⟩⟩ := ht x hx.2
  use min δ1 δ2
  constructor
  · exact lt_min h1l h2l
  · intro y
    intro ⟨l, r⟩
    refine ⟨(h1r y ⟨?_, ?_⟩), (h2r y ⟨?_, ?_⟩)⟩
    all_goals linarith [min_le_left δ1 δ2, min_le_right δ1 δ2]


lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  obtain ⟨s, ⟨hsF, hxs⟩⟩ := hx
  obtain ⟨δ, ⟨hδ1, hδ2⟩⟩ := hF s hsF x hxs
  use δ
  refine ⟨hδ1, ?_⟩
  intro y hy
  use s
  exact ⟨hsF, hδ2 y hy⟩


-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
