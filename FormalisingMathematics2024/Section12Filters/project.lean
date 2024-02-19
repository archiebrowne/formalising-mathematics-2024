import Mathlib.Tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Filter
import Mathlib.Topology.Compactness.Compact

#check Continuous.nhds
#check Filter.cocompact
#check Filter.coprodᵢ

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

lemma compact_iff_inter_ne_empty :
  IsCompact H ↔  ⋂₀ {closure k | k ∈ f} ≠ ∅ := by sorry

lemma exists_le_converge_iff_in_inter :
  ∃ g, f ≤ g ∧ 𝓝 x ≤ g ↔ x ∈ ⋂₀ {closure k | k ∈ f} := by sorry

lemma compact_iff_exists_le_converge :
  IsCompact H ↔ ∀ (f : Filter X), ∃ g, f ≤ g ∧ 𝓝 x ≤ g := by sorry

--- define projection of filter onto each factor ?????
def proj (x : ∀ i, π i) (i : ι) : π i := x i

-- this kind of makes sense?
/-- a filter `m` on a product of topological spaces converges iff
the projection of the filter onto each factor conerges -/
lemma converge_prod_iff_converge_factor {m : Filter (∀ i, (π i))} (x : ∀ i, π i) :
  𝓝 x ≤ m ↔ ∀ i, 𝓝 (x i) ≤ m.map (fun r => r i) := by sorry
-- the problem is that `MyTychonoff` is formulated in terms of sets. Is this even a problem?
-- come up with new formulation?

-- the ultrafilter lemma. Prove if get time??
#check Ultrafilter.exists_le

/-- the set `H` is compact if every ultrafilter converges -/
lemma ultrafiltter_converge_compact (u : Ultrafilter H) : ∃ (x : H), 𝓝 x ≤ ↑u → IsCompact H := by sorry

/-- instance NOT NEEDED, pushforward of an ultrafilter is an ultrafilter -/
instance (G : Type) (h : Ultrafilter H) (φ : H → G) : Ultrafilter G := Ultrafilter.map φ h

/-- the same statment as `isCompact_pi_infinite` except I have added the
reverse direction. I will supply my own proof. -/
theorem MyTychonoff {s : ∀ i, Set (π i)} :
  (∀ i, IsCompact (s i)) ↔ IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by sorry





end MyTychonoff
