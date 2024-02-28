import Mathlib.Tactic
import Mathlib.Order.Filter.Bases -- for filter bases
import Mathlib.Topology.Filter
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Compactness.Compact

#check Continuous.nhds
#check Filter.cocompact
#check Filter.coprodᵢ
#check isCompact_iff_ultrafilter_le_nhds
#check nhds_pi -- the `𝓝 x` filter on `x : ∀ i, π i` is just the product of the filters `𝓝 (x i)` (i.e Filter.pi)
#check Filter.pi -- Given filters on each factor, we can get a filter on the product of the factors.

/- two versions of Tychonoff in the library -/
#check isCompact_univ_pi -- for product of sets in topological spaces
#check isCompact_pi_infinite -- same thing but using `Set.pi` notation
#check Filter.coprodᵢ_cocompact -- complicated fliter version (don't understand yet)
-- **note** first two prove that each set is compact implies product is compact, not the other way around.

namespace MyTychonoff
open Filter Set -- means that I can write `𝓝 x` instead of `nhds x` for the neighbourhood filter of `x`
open scoped Filter Topology

-- should I add `*` after `Type` for `ι X`? what does this add?
variable {ι X : Type} {π : ι → Type} [∀ i, TopologicalSpace (π i)] [TopologicalSpace X] (H : Set X)
(x : X) (f : Filter X)
-- curly brackets means that for any new lemmas / results, these are added as implicit variables
-- state lemmas in terms of a `H : Set X` which is by coercion a topological space. This is mathematically
-- equivalent, since we could take `H = ⊤ : Set X`
#check FilterBasis

/- a set of sets is a cover if it covers the whole space ?-/
def isCover {α : Type} (U : α → Set X) : Prop := (∀ i, IsOpen (U i)) ∧ ⊤ ⊂ ⋃ i, U i
def has_finite_subcover {α : Type} (U : α → Set X) : Prop := ∃ t : Finset α, ⊤ ⊆ ⋃ i ∈ t, U i

def basis_of_collection {α : Type} (U : α → Set X) : FilterBasis X where
  sets := {⊤ \ ⋃ i ∈ t, U i | t : Finset α}
  nonempty := by
    · use ⊤
      use ∅
      aesop
  inter_sets := by
    · intro P Q ⟨t1, ht1⟩ ⟨t2, ht2⟩
      use P ∩ Q
      refine ⟨?_, by rfl⟩
-- need `classical` for doing `t1 ∪ t2` as it in non constructive
      classical
      dsimp
      use t1 ∪ t2
      aesop

def filter_of_collection {α : Type} [DecidableEq α] (U : α → Set X) : Filter X :=
  FilterBasis.filter (basis_of_collection U)

#check Decidable
#check IsCompact.finite_compact_cover
#check isCompact_iff_finite_subcover
lemma compact_iff_inter_ne_empty :
  IsCompact (⊤ : Set X) ↔  ∀ (f : Filter X), ⋂₀ {closure k | k ∈ f} ≠ ∅ := by
  constructor
  · sorry
  · intro h
    rw [isCompact_iff_finite_subcover]
    intro j
    by_contra h'
    push_neg at h'
    obtain ⟨h1, h2⟩ := h'
    specialize h (filter_of_collection h1)
-- make filter for sets with no finite subcover (ex 4.23), may need filter base

    sorry


lemma exists_le_converge_iff_in_inter :
  ∃ g, f ≤ g ∧ 𝓝 x ≤ g ↔ x ∈ ⋂₀ {closure k | k ∈ f} := by sorry

lemma compact_iff_exists_le_converge :
  IsCompact H ↔ ∀ (f : Filter X), ∃ g, f ≤ g ∧ 𝓝 x ≤ g := by sorry

-- this kind of makes sense?
/-- a filter `m` on a product of topological spaces converges iff
the projection of the filter onto each factor conerges -/
lemma converge_prod_iff_converge_factor {m : Filter (∀ i, (π i))} (x : ∀ i, π i) :
  𝓝 x ≤ m ↔ ∀ i, 𝓝 (x i) ≤ m.map (fun r => r i) := by sorry
-- the problem is that `MyTychonoff` is formulated in terms of sets. Is this even a problem?
-- come up with new formulation?

-- the ultrafilter lemma. Prove if get time??
#check Ultrafilter.exists_le
#check isCompact_iff_ultrafilter_le_nhds'
/-- the set `H` is compact if every ultrafilter converges -/
lemma ultrafilter_converge_compact : (∀ (u : Ultrafilter H), ∃ (x : H), 𝓝 x ≤ ↑u) → IsCompact H := by sorry
-- for any `q : Ultrafilter X` with `H : Set X`, if `H ∈ q` the `q` is an ultrafilter on `H`???
-- No, not true I think ??

/-- instance NOT NEEDED, pushforward of an ultrafilter is an ultrafilter -/
instance (G : Type) (h : Ultrafilter H) (φ : H → G) : Ultrafilter G := Ultrafilter.map φ h

/-- the same statment as `isCompact_pi_infinite` except I have added the
reverse direction. I will supply my own proof. -/
theorem MyTychonoff {s : ∀ i, Set (π i)} :
  (∀ i, IsCompact (s i)) ↔ IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
  constructor
  · intro h
    apply ultrafilter_converge_compact
    intro u

-- need to say that there is a point in each factor for which the projection converges?
    --have : ∀ i, ∃ (xi : π i), ↑(𝓝 xi) ≤ u.map (fun r => r i) -- ???
    sorry
  · sorry


end MyTychonoff

/--
**Overview**

I would like to prove Tychonoff's Theorem

- I need a way to talk about the product of topological spaces
- should I formulate it in terms of sets of a topological space, or the whole space?
- I need a way to talk about a filter on the whole product, and its projection onto each factor
- If `π : ι → H` for the product, where `ι : Type`, does adding `[DecidableEq ι]` change the generality?
  This comes up when defining `basis_of_collection`, I seem unable to define the union of two finsets otherwise



--/
