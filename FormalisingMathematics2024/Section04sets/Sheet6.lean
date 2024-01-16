/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)


example : S ⊆ f ⁻¹' (f '' S) := by
exact Set.subset_preimage_image f S


example : f '' (f ⁻¹' T) ⊆ T := by
  rintro x ⟨y, ⟨hy, h⟩⟩
  have : f y ∈ T := by exact hy
  rwa [h] at this

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h x hx
    specialize h (by use x)
    assumption
  · rintro h1 x ⟨y, ⟨hy, h2⟩⟩
    specialize h1 hy
    have : f y ∈ T := by exact h1
    rwa [h2] at this

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext w
  constructor
  <;> intro
  <;> assumption

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext w
  constructor
  · intro ⟨k, ⟨hk1, hk2⟩⟩
    dsimp at hk2
    simpa [hk2] using hk1
  · intro h
    use w
    exact ⟨h, rfl⟩

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext w
  constructor
  <;> intro
  <;> assumption

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext w
  constructor
  · intro ⟨r, ⟨hr1, hr2⟩⟩
    use (f r)
    exact ⟨by (use r), hr2⟩
  · intro ⟨r, ⟨⟨k, ⟨hr2, hr3⟩⟩, hr4⟩⟩
    use k
    constructor
    · exact hr2
    · dsimp
      rw [hr3, hr4]
