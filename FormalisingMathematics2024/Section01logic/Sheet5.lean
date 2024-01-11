/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  intro h <;>
  rw [h]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intros hPQ hQR
  rw [hPQ, hQR]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
  intro h <;>
  cases' h with h1 h2 <;>
  constructor
  exact h2
  exact h1
  exact h2
  exact h1
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor <;>
  intro h
  rcases h with ⟨⟨h1, h2⟩, h3⟩
  refine ⟨?_, ?_, ?_⟩
  exact h1
  exact h2
  exact h3
  rcases h with ⟨h1, ⟨h2, h3⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  exact h1
  exact h2
  exact h3
  done

example : P ↔ P ∧ True := by
  constructor <;>
  intro h
  constructor
  exact h
  triv
  cases' h with hP hT
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor <;>
  intro h
  constructor
  exfalso
  exact h
  exact h
  cases' h with hP hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intros hPQ hRS
  rw [hRS, hPQ]
  done

example : ¬(P ↔ ¬P) := by
-- Is there an easier way to do this?
  intro h
  cases' h with h1 h2
  apply h1
  apply h2
  intro hP
  apply h1
  exact hP
  exact hP
  apply h2
  intro hP
  apply h1
  exact hP
  exact hP
  done
