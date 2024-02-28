import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn
-- style: indent 4 lines for theorem statments, proof indent 2 lines.
-- do #lint
-- use `→` instead of `∧`
-- Types e.g theorem stements, sets have capital letters
-- terms (elements of sets, proofs) have small letters
-- include module description
-- put variables in sections when only used for a short part, use capital letters for names
-- cut down on number of variables, they appear in theorem statments unnecesarily
-- try to remove a lot of the have statments, break statments into smaller lemmas

/-!

# Project 2: Results About Filters Including Tychonoff's Theorem

## Section One: ExerciseSheet

This file provides a formalisation of various results regarding filters. The first four
are those at the bottom of *Section12Filters.Sheet3* in the course repository. These use
the user defined definitions for the `atTop` and `cofinite` filters in that sheet.

The main results in this section are the following:
* `exercise_01_proof`
* `exercise_02_proof`
* `exercise_03_proof`
* `exercise_04_proof`


## Section Two: Ultrafilter Lemma + Tychonoff

After these I have formalised Tychonoff's Theorem along with some preliminary
results to help with the proof. This uses Lean's filters.  Tychonoff's Theorem
says that if each member of an arbitrary collection of topological spaces is
compact, then so is their product.

Tychonoff's theorem is in fact equivalent to the axiom of choice, and almost all
proofs use AC. Mine is no different and here it appears as the 'Ultrafilter Lemma'.
Although used implicitly in my proof (Lean's version is used), I have proven my own
version of the ultrafilter lemma for completness.

THe main results in this seciton are the following:
* `isAtomic_filter` - The lattice of filters is atomic
* `my_exists_le` - My implementation of the ultrafilter lemma
* `my_tychonoff`- Tychonoff's Theorem

-/

namespace ProjectTwo
open Filter Set
open scoped Filter Topology

section ExerciseSheet

/-- **From Sheet 3** The `atTop` filter on a LinearOrder is the
collection of all sets with `{x | M ≤ x}` as a subset for some `M`.
It is the generalisation the `→ ∞` limit. -/
def atTop (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    use e
    intro y _
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

/-- **From Sheet 3** The `cofinite` filter is the collection
of sets with finite complement. -/
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

/-- **EX 01** The cofinite filter on a finite type `α` is the entire power set `⊥`.
Since the ordering `f ≤ g ↔ g.sets ⊆ f.sets` forms a `CompleteLattice` on filters,
`⊥` is indeed the whole power set of `α` since the power set of `α` forms a filter,
and no filter can be "smaller" with respect to `≤`. -/
theorem exercise_01_proof (α : Type) (h : Fintype α) : cofinite α = ⊥ := by
/- Writing `f = g` for filters `f`, `g` is notation for `f.sets = g.sets`.
Both of which are sets of sets, so `ext` is the tactic to be used. -/
  ext X
  constructor <;>
  intro _
/- `⊥` is the power set of `α`, so `X` is of course in it. -/
  · triv
/- `h` is a proof that `α` is finite. `toFinite` infers from this
that any subset must be finite also. Since `Xᶜ` is a subset, we get
the result.  -/
  · exact toFinite Xᶜ

/-- **EX 02** The cofinite filter on `ℕ` is the `atTop` filter. -/
theorem exercise_02_proof : cofinite ℕ = atTop ℕ 0 := by
  ext X
  constructor <;>
  intro h
/- Sets in `ℕ` are finite if and only if they are bounded above. Hence, because
we know `X ∈ cofinite ℕ` we have that there is some upper bound `L` for `Xᶜ`. -/
  · obtain ⟨L, hL⟩ := finite_iff_bddAbove.mp h
/- We wish to show that `X` is in the `atTop` filter on `ℕ`. So we need
a number for which all numbers greater are in `X`. `L + 1` works because
`L` is an upper bound for `Xᶜ`. -/
    use L + 1
/- The rest of this half of the proof ammounts to showing that if `L + 1 ≤ y`
then we must have `y ∈ X`, since `y` is not in `Xᶜ`. -/
    intro y hy
    by_contra h'
    specialize hL h'
    linarith
/- `h` says that `X` is in `atTop`. i.e there is an `L` such that `L ≤ y → y ∈ X`.
This can be deconstructed using `obtain`. -/
  · obtain ⟨L, hL⟩ := h
/- Sets of Naturals are finite if and only if they are bounded above, so
to show `Xᶜ` is finite (i.e `X ∈ cofinite ℕ`) it is enough to show it is
bounded. -/
    apply finite_iff_bddAbove.mpr
/- `BddAbove` is an "exists" statment, we have to provide an upper bound. `L`
is the correct choice. -/
    use L
    intro r hr
/- `r` must be less that `L` since `hL` says that if that were not the case,
we would have `r ∈ X`. But `hr` says `r ∈ Xᶜ`. -/
    by_contra hr'
    specialize hL r (by linarith)
    contradiction

/-
The next two exercises involved comming up with counterexamples, and involved using
a lot of `have` blocks. After one of Kevin's Lectures I understood that this was not
in good style. So for these two I thought I would try out a more "Mathlib-esque" style
and prove lots of small lemmas before providing the main proof.
-/

/-- **EX 03** The cofinite filter on `ℤ` is not equal to the `atTop` fliter. -/
def Exercise03 : Prop := cofinite ℤ ≠ atTop ℤ 0

/- The two filters are not equal as their collection of sets are different.
We need to provide a set which is in one but not the other. -/

/-- `A` is the set of nonnegative integers -/
def A : Set ℤ := {x | 0 ≤ x}
lemma A_def : A = {x | 0 ≤ x} := by rfl

/-- `A` is in the `atTop` filter on `ℤ`. -/
lemma A_in_atTop : A ∈ atTop ℤ 0 := by
  use 0
  intro y hy
  exact hy

/-- `Aᶜ` is not finite. -/
lemma A_compl_not_finite : ¬ Aᶜ.Finite := by
  rw [finite_iff_bddBelow_bddAbove]
  push_neg
  intro ⟨M, hM⟩ _
  have : -1 ∈ Aᶜ := by
    · rw [A_def, mem_compl_iff, nmem_setOf_iff]
      linarith
  obtain hM':= hM this
  have : M - 1 ∈ Aᶜ := by
    · rw [A_def, mem_compl_iff, nmem_setOf_iff]
      linarith
  specialize hM this
  linarith

/-- `Aᶜ` is not in the `cofinite` filter on `ℤ`. -/
lemma A_not_in_cofinite : ¬ A ∈ cofinite ℤ := by
  intro h
  absurd A_compl_not_finite
  assumption

/-- **Proof of Exercise03**, made short due to the auxillary lemmas. -/
theorem exercise_03_proof : Exercise03 := by
  intro h
  absurd A_not_in_cofinite
  simp only [h, A_in_atTop]

variable (X : Set ℕ) (l : ℕ)

/-- **EX 04** The cofinite filter on `ℕ` is not principal. -/
def Exercise04 : Prop := cofinite ℕ ≠ 𝓟 X

/- We assume the claim is true, and look for a contradiction. -/
variable (h : cofinite ℕ = 𝓟 X)

/-- `X` is in the cofinite filter. -/
lemma X_in_cofinite : X ∈ cofinite ℕ := by
  rw [h]
  exact Filter.mem_principal_self X

/-- The complement of `X` is bounded above. -/
lemma X_compl_bddAbove : BddAbove Xᶜ := by
  rw [← finite_iff_bddAbove]
  exact X_in_cofinite X h

/- We need to provide a set that is in `cofinite ℕ`, but not `𝓟 X`.
Here we define `Y`. -/

/-- `Y l` is the set of Naturals at least `l + 2`. The addition
of `2` gives us sufficient lee-way to reach a contradiction. -/
def Y : Set ℕ := {y | l + 2 ≤ y}
lemma Y_def : Y l = {y | l + 2 ≤ y} := by rfl

/-- `(Y l)ᶜ` is the set of Naturals less than `l + 2`. -/
lemma Y_compl_eq : (Y l)ᶜ = {y | y < l + 2} := by
  rw [Y_def]
  ext z
  simp only [mem_compl_iff, mem_setOf_eq, not_le]

/-- `(Y l)ᶜ` is finite. -/
lemma Y_compl_finite : Set.Finite (Y l)ᶜ := by
  rw [finite_iff_bddAbove]
  use l + 2
  intro z hz
  apply le_of_lt
  rw [Y_compl_eq] at hz
  exact hz

/-- `Y` is in `cofinite ℕ`. -/
lemma Y_in_cofinite : Y l ∈ cofinite ℕ := by
  exact Y_compl_finite l

/-- `X` is a subset of `Y`. -/
lemma X_subset_Y : X ⊆ Y l := by
  rw [← mem_principal, ← h]
  exact Y_in_cofinite l

/-- **Proof of Exercise04** The cofinite filter on `ℕ` is not principal. -/
theorem exercise_04_proof : Exercise04 X := by
  obtain ⟨L, hL⟩ := X_compl_bddAbove X h
  absurd (X_subset_Y X L h)
  intro h'
  have : L + 1 ∈ X := by
/- It turned out to be easier to prove that `L + 1 ∉ Xᶜ`, and
that is what these rewrites change the goal to. -/
    rw [← compl_compl X, mem_compl_iff]
    intro hL'
    specialize hL hL'
    linarith
/- We have that `L + 1` is in `Y L`, but this is a contradiction,
based on the definition of `Y L`. -/
  specialize h' this
  rw [Y_def, mem_setOf_eq] at h'
  linarith

end ExerciseSheet

section Tychonoff

variable {ι X : Type} {π : ι → Type} {H : Set X}
variable [∀ i, TopologicalSpace (π i)] [TopologicalSpace X]

/- In a Lattice, there is a notion of 'Atomic' elements. These are elements
with no elements between it and `⊥`. A Lattice `IsAtomic` if every element
has an atom bellow it. `Filter X` forms a Lattice, and since we can show that
an `Atom` is infact an ultrafilter, it is enough to show `IsAtomic (Filter X)`.
After this, we can unfold this in the context of Filters, and this is what we
do in `MyExists_le`, giving the usual interpretation of the ultrafilter lemma. -/

-- Credit to Kevin for getting me to type the line:

#synth IsAtomic (Filter X)

-- which pointed me in the correct direction.

/-- The lattice of filters on `X` is Atomic. -/
instance isAtomic_filter : IsAtomic (Filter X) := by
/- The orderind on filters is counterintuetive, if `f ≤ g` then
this means that `g.sets ⊆ f.sets`. For this reason we need a version of
Zorn's lemma which works for finding a 'least element'. i.e an ultrafilters
are 'small' with respect to `≤`. -/
  apply IsAtomic.of_isChain_bounded
  intro c hc hne hcnbot
/- We want to provide a lower bound on the chain `c` which is not `⊥`.
`sInf c` is the union of all of the filters in `c` and is the correct choice. -/
  use sInf c
/- We must prove that `sInf c` is not `⊥` and also that it is a lower bound
for `c`. -/
  constructor
  · intro U hU
/- Trivially, any element of `c` is greater than the infimum. -/
    exact sInf_le hU
  · rw [← neBot_iff]
/- The `sInf` of a set is not equal to `⊥` if the set is nonempty, the
partial order `≤` is 'directed' on the set, and `⊥` is not in the set.
'directed' means that for any pair of elements in the set, we can find a third
`≥` both. If the set were not directed, then the `sInf` may well be `⊥`.
consider for instance the case where `c` is the collection of
all principal filters generated by points in `X`. Then the smallest filter
(w.r.t `≤`) 'less' than all of them is the power set of `X`. i.e `⊥`. -/
    refine sInf_neBot_of_directed' hne ?_ hcnbot
/- It turns out that chains do indeed have this directed property since for any
`x y` in a chain we have `x ≤ y` or `y ≤ x`. So the maximum of `x y` is bigger than both. -/
    apply IsChain.directedOn
/- `hc` says that `c` is a chain, so the rest of the proof is just giving lean this information. -/
    intro F hF G hG hFG
    specialize hc hF hG hFG
    simp_rw [ge_iff_le] at hc ⊢
    exact Or.comm.mpr hc

/-- **The Ultrafilter Lemma** Any filter on `X` not equal to `⊥` is extensible to an ultrafilter. -/
theorem my_exists_le (f : Filter X) [h : NeBot f] : ∃ u : Ultrafilter X, ↑u ≤ f := by
/- In an atomic lattice, every emelent is either `⊥` or has an atom bellow it. -/
  cases' IsAtomic.eq_bot_or_exists_atom_le f with h1 h2
/- We have `h : NeBot f` so it is absurd that `f = ⊥`. -/
  · rw [neBot_iff] at h
    contradiction
/- `f` has an atom bellow it, and any atom is infact an ultrafilter. This is a pretty
simple check, and provided by `Ultrafilter.ofAtom`. This is the correct ultrafilter to
use for the claim. -/
  · obtain ⟨a, ha, haf⟩ := h2
    use (Ultrafilter.ofAtom a ha)
    exact haf

/-- The statment that `f(l₁) ≤ l₂ ↔ l₁ ≤ f⁻¹(l₂)` where `g(h)` is the image of the
filter `h` under the map `g`. The same statment as `tendsto_iff_comap` but with
my own proof. -/
theorem my_tendsto_iff_comap {α β : Type} {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f := by
  constructor
  · intro h s ⟨t, ht1, ht2⟩
    exact mem_of_superset (h ht1) ht2
  · intro h s hs
    exact h (preimage_mem_comap hs)

/-- **MyTychonoff** The product of arbitrary compact sets is compact. The statment
here is the same as `isCompact_pi_infinite` but the proof is my own. -/
theorem my_tychonoff {s : ∀ i, Set (π i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
-- this is where `of_le` is used
/- A space is compact if and only if all ultrafilters on the space converge to some point.
This lemma interprest "all ultrafilters on `s i` as "all filters on `∀ i, Set (π i)` less than
`𝓟 (s i)`." In this way we don't need to talk about the type of filters on one fo the factots,
which could get messy, since `s i` is not a Type, but a term. -/
  simp only [isCompact_iff_ultrafilter_le_nhds]
  intro h
  intro f hf
  rw [le_principal_iff] at hf
  have : ∀ i, ∃ xᵢ, xᵢ ∈ s i ∧ Tendsto (Function.eval i) f (𝓝 xᵢ) := by
    · intro i
      specialize h i
      apply h (f.map (Function.eval i))
      dsimp only [Ultrafilter.coe_map]
      intro y hy
      rw [mem_map]
      apply mem_of_superset hf
      intro x hx
      specialize hx i
      rw [mem_preimage, Function.eval]
      rw [mem_principal] at hy
      exact hy hx
  -- have : ∀ i, ∃ xᵢ, xᵢ ∈ s i ∧ f.map (Function.eval i) ≤ (𝓝 xᵢ) := by sorry -- this is actually `Tendsto`, explain differnece in report?
  -- have : ∀ i, ∃ xᵢ ∈ s i, f.map (fun r ↦ r i) ≤ 𝓝 xᵢ := by sorry
  choose x hx using this
  use x
  constructor
  · intro i
    exact (hx i).1
  · rw [nhds_pi, Filter.pi, le_iInf_iff]
    intro i
    obtain ⟨-, h'⟩ := hx i
    simpa [my_tendsto_iff_comap] using h'

end Tychonoff
end ProjectTwo
