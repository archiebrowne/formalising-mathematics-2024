/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intros hPQ hPR hQR
  cases' hPQ with hP hQ
  apply hPR
  exact hP
  apply hQR
  exact hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPQ
  cases' hPQ with hP hQ
  right
  exact hP
  left
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
-- Is there a simpler way to do this?
  constructor <;>
  intro h
  cases' h with hPQ hR
  cases' hPQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR
  cases' h with hP hQR
  left
  left
  exact hP
  cases' hQR with hQ hR
  left
  right
  exact hQ
  right
  exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intros hPR hQS hPQ
  cases' hPQ with hP hQ
  left
  apply hPR
  exact hP
  right
  apply hQS
  exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intros hPQ hPR
  cases' hPR with hP hR
  left
  apply hPQ
  exact hP
  right
  exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intros hPR hQS
  rw [hPR, hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
-- Is there a simpler way to do this?
  constructor <;>
  intro h
  constructor
  intro hP
  apply h
  left
  exact hP
  intro hQ
  apply h
  right
  exact hQ
  intro hPQ
  cases' hPQ with h1 h2 <;>
  cases' h with hnP hnQ
  apply hnP
  exact h1
  apply hnQ
  exact h2
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
-- Is there a simpler way to do this?
  constructor <;>
  intro h
  by_cases hP : P
  right
  intro hQ
  apply h
  constructor
  exact hP
  exact hQ
  left
  exact hP
  cases' h with hnP hnQ
  intro ⟨hP, hQ⟩
  apply hnP
  exact hP
  intro ⟨hP, hQ⟩
  apply hnQ
  exact hQ
  done
