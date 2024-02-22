import Mathlib.Tactic
--import Mathlib.Order.Filter.Bases
import Mathlib.Topology.Filter
--import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Compactness.Compact

namespace MyTychonoff
open Filter Set
open scoped Filter Topology


variable {ι : Type} {π : ι → Type} [∀ i, TopologicalSpace (π i)]

-- **Maybe this is the best one?** maybe need `↑u ≤ 𝓟 H` or not ???
-- saying `↑u ≤ 𝓟 H` is asserting that `u` is actucally a filter on `H` also (i think) (PUT IN REPORT)
-- maybe make this more general, change `Set (∀ i, π i)` to `Set X` for some topological space `X`? (bellow)
lemma ultrafilter_converge_compact'' (H : Set (∀ i, π i)) :
  (∀ (u : Ultrafilter (∀ i, π i)), ↑u ≤ 𝓟 H → ∃ x ∈ H, ↑u ≤ 𝓝 x) ↔ IsCompact H := by sorry

lemma converge_prod_iff_converge_factor {u : Filter (∀ i, (π i))} (x : ∀ i, π i) :
  u ≤ 𝓝 x ↔ ∀ i, u.map (fun r => r i) ≤ 𝓝 (x i) := by sorry


variable (X : Type) [TopologicalSpace X]
/-- A set `H : Set X` is compact if and only if every ultrafilter on `H` converges to
some point. -/
lemma ultrafilter_converge_compact''' (H : Set X) :
  (∀ (u : Ultrafilter X), ↑u ≤ 𝓟 H → ∃ x ∈ H, ↑u ≤ 𝓝 x) ↔ IsCompact H := by sorry

#check Set.pi
#check Filter.pi
#check map_mono
/- sanity check -/
example (X Y : Type) (f g : Filter X) (h : X → Y) : f ≤ g → f.map h ≤ g.map h := by
  intro r x hx
  simp_all only [mem_map]
  exact r hx
#check nhds_pi

theorem MyTychonoff {s : ∀ i, Set (π i)} :
  (∀ i, IsCompact (s i)) ↔ IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
  constructor
  · intro h
    rw [← ultrafilter_converge_compact'']
    intro u hu
    have : ∀ i, ∃ xₜ ∈ s i, u.map (fun r => r i) ≤ 𝓝 xₜ := by
      · intro i
        obtain ⟨-, h2⟩ := ultrafilter_converge_compact''' (π i) (s i)
        specialize h2 (h i) (u.map (fun r ↦ r i))
        have : u.map (fun r ↦ r i) ≤ 𝓟 (s i) := by
          · intro y hy
            simp only [Ultrafilter.coe_map, mem_map, Ultrafilter.mem_coe]
            apply hu
            simp only [mem_principal]
            intro z j
            aesop
        obtain ⟨x, ⟨hx1, hx2⟩⟩ := h2 this
        use x
    choose x hx using this
    use x
    constructor
    · intro i
      exact (hx i).1
    · rw [converge_prod_iff_converge_factor]
      intro i
      exact (hx i).2
  · sorry



end MyTychonoff
