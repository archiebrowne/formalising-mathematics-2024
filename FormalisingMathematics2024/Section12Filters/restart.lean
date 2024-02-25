import Mathlib.Tactic
import Mathlib.Topology.Filter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

/-!
# Project 2: Tychonoff's Theorem

This file provides a formalisation of Tychonoff's Theorem along with some preliminary
results to help with the proof. Tychonoff's Theorem says that if each member of an
arbitrary collection of topological spaces is compact, then so is their product.

Tychonoff's theorem is in fact equivalent to the axiom of choice, and almost all
proofs use AC. Mine is no different and here it appears as the 'Ultrafilter Lemma'.
-/

namespace MyTychonoff
open Filter Set
open scoped Filter Topology

variable {ι X : Type} {π : ι → Type} {H : Set X}
variable [∀ i, TopologicalSpace (π i)] [TopologicalSpace X]

#check zorn_subset
#check Ultrafilter.of_le

example (f g : Filter X) : f ≤ g ↔ g.sets ⊆ f.sets := Iff.rfl
#check Ultrafilter
#check Filter.exists_ultrafilter_le
#check exists_ultrafilter_iff

theorem exists_le' (f : Filter X) [h : NeBot f] : ∃ u : Ultrafilter X, ↑u ≤ f := by
  let Ω : Set (Filter X) := {g | g ≤ f}
  suffices : ∃ x ∈ Ω, ∀ y ∈ Ω, x ≤ y → y = x
  · obtain ⟨u, huo, huy⟩ := this


    have neBot' : NeBot u := by sorry
    have le_of_le : ∀ g, Filter.NeBot g → g ≤ u → u ≤ g := by sorry

    sorry
  apply zorn_partialOrder₀ Ω
  intro c hc hcc
  simp_all only [mem_setOf_eq]
-- I don't understand how this works
  apply Exists.intro
  apply And.intro
  on_goal 2 => intro z a
  on_goal 2 => apply hc
  on_goal 2 => simp_all only
  simp_all only [le_refl]

#check ClusterPt
#check cluster_point_of_compact
-- prove these
#check isCompact_iff_ultrafilter_le_nhds
theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact H ↔ ∀ f : Ultrafilter X, ↑f ≤ 𝓟 H → ∃ x ∈ H, ↑f ≤ 𝓝 x := by
    constructor
    <;> intro h
    · intro f hf
      sorry
    · sorry

#check le_principal_iff
theorem le_principal {s : Set (∀ i, π i)} {f : Filter (∀ i, π i)} : f ≤ 𝓟 s ↔ s ∈ f := by
  constructor
  <;> intro h
  · exact h (mem_principal_self s)
  · intro y hy
    apply mem_of_superset h
    exact hy

#check nhds_induced
#check nhds_iInf
#check nhds_pi
example (x : Set X) (a : X) : ∀ i : ι, x ∈ 𝓝 a → x ∈ ⨅ i : ι, 𝓝 a := fun i a_1 ↦ mem_iInf_of_mem i a_1
#check mem_iInf_of_mem
theorem nhds_pi' {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  ext x
  constructor
  · intro h
    simp [Filter.pi, ← nhds_induced]
    have h1 : ∀ i : ι, x ∈ 𝓝 a := by
      · intro i
        exact h
    have h2 : ∀ i : ι, x ∈ 𝓝 a → x ∈ ⨅ i : ι, 𝓝 a := fun i a_1 ↦ mem_iInf_of_mem i h
    have := @mem_iInf_of_mem (∀ i, π i) ι (fun i ↦ 𝓝 a)
    sorry
  · intro h
    sorry



#check tendsto_iff_comap
variable {α β : Type}
theorem tendsto_iff_comap' {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f := by
    constructor
    · intro h s ⟨t, ht1, ht2⟩
      exact mem_of_superset (h ht1) ht2
    · intro h s hs
      exact h (preimage_mem_comap hs)

#check isCompact_pi_infinite
theorem MyTychonoff {s : ∀ i, Set (π i)} :
  (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
-- this is where `of_le` is used
  simp only [isCompact_iff_ultrafilter_le_nhds]
  intro h
  intro f hf
  rw [le_principal] at hf
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
    simpa [tendsto_iff_comap] using h'

end MyTychonoff
