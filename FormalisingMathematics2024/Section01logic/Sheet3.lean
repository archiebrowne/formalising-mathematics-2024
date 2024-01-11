/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  triv
  done

example : False → ¬True := by
  intros hf ht
  exact hf
  done

example : ¬False → True := by
  intro h1
  by_contra h2
  apply h2
  triv
  done

example : True → ¬False := by
  intros h1 h2
  by_contra h3
  exact h2
  done

example : False → ¬P := by
  intros h hP
  exact h
  done

example : P → ¬P → False := by
  intros hP hnP
  apply hnP
  exact hP
  done

example : P → ¬¬P := by
  intros hP hnP
  apply hnP
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intros hPQ hnQ hP
  apply hnQ
  apply hPQ
  exact hP
  done

example : ¬¬False → False := by
  intro hf
  apply hf
  intro hf'
  exact hf'
  done

example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  apply hnnP
  exact hnP
  done

example : (¬Q → ¬P) → P → Q := by
  intros hQP hP
  by_contra hnQ
  apply hQP
  exact hnQ
  exact hP
  done
