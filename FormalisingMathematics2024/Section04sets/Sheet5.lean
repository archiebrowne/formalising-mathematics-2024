/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext w
  constructor
  · rintro (_ | _)
    <;> assumption
  · intro h
    left
    assumption

example : A ∩ A = A := by
  ext w
  constructor
  · rintro ⟨_, _⟩
    assumption
  · intro h
    exact ⟨h, h⟩

example : A ∩ ∅ = ∅ := by
  ext w
  constructor
  · rintro ⟨_, _⟩
    assumption
  · intro h
    cases h

example : A ∪ univ = univ := by
  ext w
  constructor
  · rintro (_ | _)
    <;> triv
  · intro _
    right
    triv

example : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext w
  constructor
  <;> intro h3
  · exact h1 h3
  · exact h2 h3

example : A ∩ B = B ∩ A := by
  ext w
  constructor
  <;> rintro ⟨h, h'⟩
  <;> exact ⟨h', h⟩

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext w
  constructor
  · rintro ⟨ha, ⟨hb, hc⟩⟩
    exact ⟨⟨ha, hb⟩, hc⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, ⟨hb, hc⟩⟩

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext w
  constructor
  · rintro (ha | (hb | hc))
    · left; left; exact ha
    · left; right; exact hb
    · right; exact hc
  · rintro ((ha | hb) | hc)
    · left; exact ha
    · right; left; exact hb
    · right; right; exact hc

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext w
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · exact ⟨mem_union_left B ha, mem_union_left C ha⟩
    · exact ⟨mem_union_right A hb, mem_union_right A hc⟩
  · rintro ⟨(ha | hb), (ha' | hc)⟩
    all_goals try (left; assumption)
    right; exact ⟨hb, hc⟩


example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext w
  constructor
  · rintro ⟨ha, (hb | hc)⟩
    · left; exact ⟨ha, hb⟩
    · right; exact ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha', hc⟩)
    · exact ⟨ha, mem_union_left C hb⟩
    · exact ⟨ha', mem_union_right B hc⟩
