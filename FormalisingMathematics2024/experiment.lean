import Mathlib.Tactic
import Mathlib.RingTheory.UniqueFactorizationDomain -- UFDs
import Mathlib.RingTheory.PrincipalIdealDomain      -- PIDs
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

namespace ProjectThree
open MvPolynomial
#check Geometry.SimplicialComplex
#check Ideal
#check Ideal.span
#check Set.toFinset
#check Set.singleton
#check Finset
#check Finsupp
#check monomial
#check Finsupp.single
#check monic_monomial_eq
#check Ideal.span
#check GaloisConnection
#check support_eq_empty
#check choose_spec
#check Finsupp.toMultiset

/-
Looking at this paper: https://math.okstate.edu/people/mermin/papers/A_survey_of_Stanley-Reisner_theory.pdf

QUESTIONS:
  * typeclass stuck on `mono_sup_is_sq_free'`, and other places, how to fix?
  * Really need to provide definition for `SuppOfMonomial`, why cannot use `cases`? -- MWE in file
    `mwe_choose.lean`.
  * Check Definition of squarefree monomial ideal

TODOS:
  * Definitions should have camelCase
  * lemmas/theorems should have snake_case
  * structures should have CapitalCase
-/

/-
structure GeometricSimplicialComplex (n : ℕ) where
  faces : Set (Finset ℝ)
  convex_faces : {convexHull f | f ∈ faces}
  inter_closed : ∀ {f g}, f ∈ faces → g ∈ faces → f ∩ g ∈ faces

#check convexHull
-/

/-
`E` : Type which vertices/polynomial variables belong to.
`K [CommSemiRing K]` : Coefficients for polynomials
 -/

open Classical
variable {X K : Type} [CommSemiring K]

structure AbstractSimplicialComplex where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

instance : Membership (Finset X) (@AbstractSimplicialComplex X) :=
  ⟨fun f Δ => f ∈ Δ.faces⟩

/-- Index for a finite squarefree monomial. `A` is the set describing
which varibales to include. E.g if `A = {1, 2, 3} ⊂ ℕ = X` then `s A` is
the indicator function on `A`. It corresponds to the monomial `xy²z³`. -/
noncomputable def s (A : Finset X) : X →₀ ℕ where
  support := A
  toFun := fun x ↦ if x ∈ A then 1 else 0
  mem_support_toFun := by
    intro a
    constructor
    <;> intro h
    · simpa [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    · by_contra h'
      have : (fun x ↦ if x ∈ A then 1 else 0) a = 0
      · simpa only [ite_eq_right_iff, one_ne_zero, imp_false]
      contradiction


-- some lemmas about the finsupp `s A`.
lemma s_eq_toFun (A : Finset X) : s A = (s A).toFun := by rfl
lemma s_to_fun_eq_fun (A : Finset X) : (s A).toFun = fun w ↦ if w ∈ A then 1 else 0 := by rfl
lemma s_eq_one_iff (A : Finset X) (x : X) : (s A) x = 1 ↔ x ∈ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
lemma s_eq_zero_iff (A : Finset X) (x : X) : (s A) x = 0 ↔ x ∉ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_right_iff, one_ne_zero, imp_false]
lemma s_eq_zero_or_one (A : Finset X) (x : X) : (s A) x = 0 ∨ (s A) x = 1 := by
  simp_rw [s_eq_one_iff, s_eq_zero_iff]
  exact em' (x ∈ A)


variable (K)
-- **one half of Def 2.1**
/-- The monomial *supported* on `A` is the monomial with variables
according to the elements of `A`. -/
noncomputable def monomial_supported_by_set (A : Finset X) :
  MvPolynomial X K := monomial (s A) 1

lemma monomial_supported_by_set_def (A : Finset X) :
    monomial_supported_by_set K A = monomial (s A) (1 : K) := by rfl

-- want to show that the support of a `monomial_supported_by_set` is `s A` in some sense.
example (A : Finset X) : (monomial_supported_by_set A).support = Set.toFinset {s A} := by sorry

-- David Helped
def IsSqFreeMonomial (m : MvPolynomial X K) : Prop :=
    ∃ f, support m ⊆ {f} ∧ ∀ x : X, f x = 0 ∨ f x = 1 -- chooese, choose_spec
-- this includes squarefree


-- Maybe try to prove this but seems very hard, may make project more rigorous.
example (m : MvPolynomial X K) :
    (Squarefree m ∧ ∃ s a, m = monomial s a) ↔ ∃ f, support m ⊆ {f} ∧ ∀ x : X, f x = 0 ∨ f x = 1 := by
  constructor
  · rintro ⟨hsq, ⟨s, a, hsa⟩⟩
    use s
    constructor
    · rw [@Finset.subset_singleton_iff, hsa]
      right
      sorry
    sorry
  sorry


/-- The monomial supported by a set is square free. -/
lemma mono_sup_is_sq_free (A : Finset X) : IsSqFreeMonomial _ (monomial_supported_by_set K A) := by
  use s A
  constructor
  · exact support_monomial_subset
  · intro x
    exact s_eq_zero_or_one A x

#check Finset.subset_singleton_iff.mp
#check Set.toFinset
#check Fintype
#check MvPolynomial.support_monomial
#check MvPolynomial.monomial_one_dvd_monomial_one


-- **second half of Def 2.1**
-- need stuff s.t f x = 1, and convert to finset.
noncomputable def SuppOfMonomial (m : MvPolynomial X K) (h : IsSqFreeMonomial m) : Finset X := by
  obtain ⟨-, -⟩ := choose_spec h
  exact if support m = {choose h} then (choose h).support else Finset.empty


-- **prop 2.2** TODO: Rename properly.
lemma prop22a (m : MvPolynomial X K) (hsq : IsSqFreeMonomial m) :
    monomial_supported_by_set (SuppOfMonomial m hsq) = m := by sorry
-- this is where I need `mono_sup_is_sq_free` to prove the monomial is sqfree
lemma prop22b (A : Finset X) : SuppOfMonomial (monomial_supported_by_set A) _ = A := by sorry
lemma prop22c (m m' : MvPolynomial X K) (hm : IsSqFreeMonomial m) (hm' : IsSqFreeMonomial m') :
    m ∣ m' ↔ SuppOfMonomial m hm = SuppOfMonomial m' hm' := by sorry

-- AFTER THIS, NEED DEFINITION OF SQUARE FREE MONOMIAL IDEAL


-- maybe do structure and define a membership, as in Filter, Maybe consider making a finset??
structure SqFreeMonomialIdeal'' where
  basis : Set (MvPolynomial X K)
  ideal : Ideal (MvPolynomial X K)
  ideal_eq_span : ideal = Ideal.span basis
  sq_free : ∀ m, m ∈ basis → IsSqFreeMonomial m
#check SqFreeMonomialIdeal''.ideal


instance : Membership (MvPolynomial X K) (@SqFreeMonomialIdeal'' X K _) :=
  ⟨fun m I => m ∈ I.ideal⟩


@[simp]
theorem mem_ideal (m : MvPolynomial X K) (I : SqFreeMonomialIdeal'') : m ∈ I ↔ m ∈ I.ideal :=
  Iff.rfl


example (m q : MvPolynomial X K) (J : Ideal (MvPolynomial X K)) (h : m ∈ J) : m * q ∈ J := by
  exact Ideal.mul_mem_right q J h
sorry


-- restating with new structure, much nicer
lemma mono_ideal_up_closed' (I : SqFreeMonomialIdeal'') (m m' : MvPolynomial X K) (h : m ∣ m')
    (hm : m ∈ I) : m' ∈ I := by
  obtain ⟨r, hr⟩ := h
  rw [mem_ideal] at hm ⊢
  simpa [hr] using (Ideal.mul_mem_right r I.ideal hm)


-- need to instantiate a preorder on monomials???
#check Preorder
#synth Preorder (MvPolynomial X K)
lemma Gal_Complex_Monomial : @GaloisConnection (Finset X) (MvPolynomial X K) _ _ monomial_supported_by_set SuppOfMonomial := by sorry

def stanleyReisnerComplex (I : SqFreeMonomialIdeal'') : AbstractSimplicialComplex := by sorry

#synth Membership K (Ideal K) -- `SetLike.instMembership`
-- Then can talk about Cor 2.5 etc

-- implement geometric k simplex, complex ?
-- dimension of a simplex?
-- monomial, polynomial ring
-- monomial ideal
-- squarefree monomial ideal
-- support of a monomial
--
end ProjectThree
