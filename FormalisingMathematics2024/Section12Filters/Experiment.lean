import Mathlib.Tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.StoneCech
import Mathlib.Data.Set.Constructions
import Mathlib.SetTheory.ZFC.Basic

open Set Filter
open scoped Filter
open scoped Topology
namespace experiment
#check IsOpen
#check ultrafilter_converges_iff
#check isOpen_iff_ultrafilter
#check StoneCech
#check Tendsto.comp
#check FiniteInter
#check IsCompact
#check Ultrafilter.exists_le -- the ultrafilter lemma bellow
#check ZFSet.powerset
#check Infinite
#check Infinite.set
#check Set.sUnion

variable (X : Type) (U : Set X)
/-- set of size `n` subsets of a type `α` -/
def finite_subsets (α : Type) (n : ℕ) : Set (Finset α) := {e : Finset α | e.card = n}





-- trying to state Ramsey
-- theorem (X : Type) (n r : ℕ) (hX : Infinite X)




example (α : Type) (X : Set α) (h : Infinite X) : ¬ Finite X := by sorry


/-- the ultrafilter lemma. every flter is extendable to an ultrafilter -/
lemma ultrafilter_lemma (α : Type) : ∀ (f : Filter α), ∃ (g : Ultrafilter α), f ≤ g := by
  intro f
  let s : Set (Filter α) := {q | ∃ (m : Ultrafilter α), q ≤ m}
  suffices : ∃ x ∈ s, ∀ y ∈ s, x ≤ y → y = x
  · sorry
  refine zorn_partialOrder₀ s ?this.ih
  intro c hcs hc
  obtain rfl | hcnemp := c.eq_empty_or_nonempty
  · sorry
  · sorry


-- #check 𝓝[≠]



theorem open_ultra_conv : IsOpen U ↔ ∀ x ∈ U, ∀ (f : Ultrafilter S), ↑f ≤ 𝓝 x → U ∈ f := by
  constructor
  · intro h
    rintro x h' f h''
    have : U ∈ nhds x := IsOpen.mem_nhds h h'
    exact h'' this
  · intro h
    by_contra hnopenU
    sorry







/-
instance myinst : PartialOrder (Filter ℕ) where
  le_antisymm := by
    · intros a b hab hba
      rw [le_def] at hab hba
      ext x
      exact ⟨hba x, hab x⟩

#check myinst
example : PartialOrder (Filter ℕ) := by infer_instance
-/
