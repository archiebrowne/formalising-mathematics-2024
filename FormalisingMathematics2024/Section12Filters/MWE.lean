import Mathlib.Tactic
--import Mathlib.Order.Filter.Bases
import Mathlib.Topology.Filter
--import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Compactness.Compact

namespace MyTychonoff
open Filter Set
open scoped Filter Topology

variable {ι : Type} {π : ι → Type} [∀ i, TopologicalSpace (π i)] {X : Type} [TopologicalSpace X]

-- thm 4.6
lemma baz (H : Set X) : (∀ (f : Filter X), f ≤ 𝓟 H → ⋂₀ {closure k | k ∈ f} ≠ ∅) ↔ IsCompact H := by
  constructor
  · sorry
  · intro h f hf
    let u : Set (Set X) := {(closure k)ᶜ | k ∈ f}
    sorry

-- thm 4.9
lemma bar (f : Filter X) (x : X) :
  x ∈ ⋂₀ {closure k | k ∈ f} ↔ ∃ g ≥ f, g ≤ 𝓝 x := by

   sorry

lemma bar' (f : Filter X) (x : X) (H : Set X) (h : f ≤ 𝓟 H) :
  x ∈ ⋂₀ {closure k | k ∈ f} ↔ ∃ g ≥ f, g ≤ 𝓝 x := by

  sorry

--#check IsClosed.isCompact
--#check IsCompact.isClosed
--#check T2Space
-- example (H : Set X) (h : IsCompact H) : IsClosed H := by exact?
#check closure
-- thm 4.10

lemma compact_iff_exists_ge_converge (H : Set X) :
  (∀ (f : Filter X), f ≤ 𝓟 H → ∃ g ≥ f, ∃ x ∈ H, g ≤ 𝓝 x) ↔ IsCompact H := by
  constructor
  · intro h
    rw [← baz H]
    intro f hf
    obtain ⟨g, hg1, x, hxH, hxg⟩ := h f hf
    push_neg
    use x
    exact (bar f x).mpr (by use g)
  · intro h
    have h' := h
    rw [← baz H] at h
    intro f hf
    specialize h f hf
    have := nmem_singleton_empty.mp h
    rw [nonempty_def] at this
    obtain ⟨x, hx⟩ := this
    obtain ⟨h1, -⟩ := bar f x
    obtain ⟨g, hg1, hg2⟩ := h1 hx
    use g
    refine ⟨hg1, ?_⟩
    use x
    constructor
    · simp at hx
      specialize hx H (by exact le_principal_iff.mp hf)
      sorry
    · exact hg2

#check NeBot.mono
#check isCompact_iff_ultrafilter_le_nhds
#check ClusterPt
#check Ultrafilter.of_le
-- **Maybe this is the best one?** maybe need `↑u ≤ 𝓟 H` or not ???
-- saying `↑u ≤ 𝓟 H` is asserting that `u` is actucally a filter on `H` also (i think) (PUT IN REPORT)
-- maybe make this more general, change `Set (∀ i, π i)` to `Set X` for some topological space `X`? (bellow)
-- thm 4.14 (via 4.10) + thm 4.23
/-- A set `H : Set X` is compact if and only if every ultrafilter on `H` converges to
some point. -/ -- TRUE
lemma ultrafilter_converge_compact (H : Set X) :
  (∀ (u : Ultrafilter X), ↑u ≤ 𝓟 H → ∃ x ∈ H, ↑u ≤ 𝓝 x) ↔ IsCompact H := by
  constructor
  · intro h



    rw [← compact_iff_exists_ge_converge H]
    intro f hf
    have : NeBot f := by sorry
    specialize h (Ultrafilter.of f) (by
      trans f
      · exact Ultrafilter.of_le f
      · exact hf
    )
    use (Ultrafilter.of f)
    constructor
    · sorry
    · exact h
  · intro h u hu
    obtain ⟨g, ⟨hgu, ⟨x, ⟨hxH, hgN⟩⟩⟩⟩ := (compact_iff_exists_ge_converge H).mpr h u hu
    use x
    refine ⟨hxH, ?_⟩
    · intro y hy
      exact hgu (hgN hy)

lemma converge_prod_iff_converge_factor {u : Filter (∀ i, (π i))} (x : ∀ i, π i) :
  u ≤ 𝓝 x ↔ ∀ i, u.map (fun r => r i) ≤ 𝓝 (x i) := by
  constructor
/- this direction is unimportant for the final goal, and may not be true, disregard for now -/
  · sorry
  · intro h y hy
    have h1 : ∀ i, (fun r => r i)'' y ∈ u.map (fun r => r i) := by sorry
    have h2 : ∀ i, ∃ F ∈ u, (fun r => r i)'' F ⊂ (fun r => r i)'' y := by sorry
    have : ∀ i, (fun r => r i)⁻¹' ((fun r => r i)'' y) ∈ u := by
      · intro i
        obtain ⟨F, hF1, hF2⟩ := h2 i
        simp_all only [mem_map]
    have hInter : y = ⋂₀ {(fun r => r i)⁻¹' (fun r => r i)'' y | i : ι} := by sorry

    sorry

--#check Set.pi
--#check Filter.pi
--#check map_mono
/- sanity check -/
example (X Y : Type) (f g : Filter X) (h : X → Y) : f ≤ g → f.map h ≤ g.map h := by
  intro r x hx
  simp_all only [mem_map]
  exact r hx
#check nhds_pi
#check isCompact_pi_infinite
#check isCompact_iff_ultrafilter_le_nhds
#check exists_prop
#check mem_setOf_eq
#check le_principal_iff
#check Ultrafilter.clusterPt_iff

/-
isCompact_iff_ultrafilter_le_nhds, nhds_pi, Filter.pi, exists_prop, mem_setOf_eq,
    le_iInf_iff, le_principal_iff
-/
theorem MyTychonoff {s : ∀ i, Set (π i)} :
  (∀ i, IsCompact (s i)) ↔ IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
  constructor
  · intro h1
    rw [← ultrafilter_converge_compact]
    intro u hu
    have : ∀ i, ∃ xₜ ∈ s i, u.map (fun r => r i) ≤ 𝓝 xₜ := by
      · intro i
/- delete the reverse implication using `-`-/
        obtain ⟨-, h2⟩ := ultrafilter_converge_compact (s i)
        specialize h2 (h1 i) (u.map (fun r ↦ r i))
        have : u.map (fun r ↦ r i) ≤ 𝓟 (s i) := by
          · intro _ h3
            simp only [Ultrafilter.coe_map, mem_map, Ultrafilter.mem_coe]
            apply hu
            intro _ _
            simp_all only [le_principal_iff, Ultrafilter.mem_coe,
              Ultrafilter.coe_map, mem_map, mem_principal,
              mem_setOf_eq, mem_preimage]
            apply h3
            simp_all only
        obtain ⟨x, ⟨hx1, hx2⟩⟩ := h2 this
-- initially tried not introducing hx1, hx2, by `⟨-, -⟩` but this meant that after `use x`
-- did not close the goal. With these know in the local context, `use` tries to close the
-- goal. Lean does a lot under the hood.
        use x
    choose x hx using this
    use x
    constructor
    · intro i
      exact (hx i).1
    ·
      rw [converge_prod_iff_converge_factor]
      intro i
      exact (hx i).2
  · sorry



end MyTychonoff
