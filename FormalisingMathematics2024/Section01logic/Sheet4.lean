/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro hPQ
  cases' hPQ with hP hQ
  exact hP
  done

example : P ∧ Q → Q := by
  intro hPQ
  cases' hPQ with hP hQ
  exact hQ
  done

example : (P → Q → R) → P ∧ Q → R := by
  intros hPQR hPQ
  apply hPQR <;>
  cases' hPQ with hP hQ
  exact hP
  exact hQ
  done

example : P → Q → P ∧ Q := by
  intros hP hQ
  constructor
  exact hP
  exact hQ
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro hPQ
  constructor <;>
  cases' hPQ with hP hQ
  exact hQ
  exact hP
  done

example : P → P ∧ True := by
  intro hP
  constructor
  exact hP
  triv
  done

example : False → P ∧ False := by
  intro hf
  constructor
  exfalso
  exact hf
  exact hf
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intros hPQ hQR
  constructor
  cases' hPQ with hP hQ
  exact hP
  cases' hQR with hQ hR
  exact hR
  done

example : (P ∧ Q → R) → P → Q → R := by
  intros hPQR hP hQ
  apply hPQR
  constructor
  exact hP
  exact hQ
  done
