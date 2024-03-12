import Mathlib.Tactic
import Mathlib.RingTheory.UniqueFactorizationDomain -- UFDs
import Mathlib.RingTheory.PrincipalIdealDomain      -- PIDs
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic


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
  * typeclass stuck on `mono_sup_is_sq_free'`
  * Really need to provide definition for `SuppOfMonomial`
  * Need definition of "squre free monomial ideal"
  * Do I need GeometricSimplicialComplex? Probably not
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
variable {X K : Type*} [CommSemiring K]

structure AbstractSimplicialComplex where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces


instance : Membership (Finset X) (@AbstractSimplicialComplex X) :=
  ⟨fun f Δ => f ∈ Δ.faces⟩


-- noncomputable section

/-- Index for a finite squarefree monomial. `A` is the set describing
which varibales to include. E.g if `A = {1, 2, 3} ⊂ ℕ = E` then `s A` is
the indicatir function on `A`. -/
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

-- **one half of Def 2.1**
/-- The monomial *supported* on `A` is the monomial with variables
according to the elements of `A`. -/
noncomputable def monmoial_supported_by_set (A : Finset X) :
  MvPolynomial X K := monomial (s A) (1 : K)

-- David Helped
def IsSqFreeMonomial (m : MvPolynomial X K) : Prop :=
  ∃ f, support m ⊆ {f} ∧ ∀ x : X, f x = 0 ∨ f x = 1 -- chooese, choose_spec
-- this includes squarefree

-- Maybe try to prove this but seems very hard, may make project more rigorous.
example (m : MvPolynomial X K) :
  Squarefree m ↔ ∃ f, support m ⊆ {f} ∧ ∀ x : X, f x = 0 ∨ f x = 1 := by sorry

variable (A : Finset X)
#check IsSqFreeMonomial (monmoial_supported_by_set A)
#check @IsSqFreeMonomial X K _ (monmoial_supported_by_set A)

/-- The monomial supported by a set is square free. -/
lemma mono_sup_is_sq_free (A : Finset X) (m : MvPolynomial X K) (hm : ∃ A, m = monmoial_supported_by_set A):
    IsSqFreeMonomial m := by sorry
-- Actually want this, but don't know why it is stuck.
lemma mono_sup_is_sq_free' (A : Finset X) : IsSqFreeMonomial (monmoial_supported_by_set A) := by sorry

-- **second half of Def 2.1**
-- need stuff s.t f x = 1, and convert to finset
def SuppOfMonomial (m : MvPolynomial X K) (h : IsSqFreeMonomial m) : Finset X := by
  obtain ⟨h1, h2⟩ := choose_spec h
  set R := (choose h)
  let M := R⁻¹' {1}
  have : support m = ∅ ∨ support m = {R} := by
    · simp_all only [Finset.subset_singleton_iff]
  cases' this with h1 h2 -- Why is this not working??
  sorry

-- **prop 2.2** TODO: Rename properly.
lemma prop22a (m : MvPolynomial X K) (hsq : IsSqFreeMonomial m) :
    monmoial_supported_by_set (SuppOfMonomial m hsq) = m := by sorry
-- this is where I need `mono_sup_is_sq_free` to prove the monomial is sqfree
lemma prop22b (A : Finset X) : SuppOfMonomial (monmoial_supported_by_set A) _ = A := by sorry
lemma prop22c (m m' : MvPolynomial X K) (hm : IsSqFreeMonomial m) (hm' : IsSqFreeMonomial m') :
    m ∣ m' ↔ SuppOfMonomial m hm = SuppOfMonomial m' hm' := by sorry


-- AFTER THIS, NEED DEFINITION OF SQUARE FREE MONOMIAL IDEAL

#check Ideal.span
-- probably not this. Dont think this is span of the carrier
def SqFreeMonomialIdeal : Ideal (MvPolynomial X K) where
  carrier := {m | IsSqFreeMonomial m}
  add_mem' := _
  zero_mem' := _
  smul_mem' := _
-- probably this, but h is redundant:
#synth CommSemiring (MvPolynomial X K)
def SqFreeMonomialIdeal' (s : Set (MvPolynomial X K)) (h : ∀ m, m ∈ s → IsSqFreeMonomial m) :
    Ideal (MvPolynomial X K) := Ideal.span s

-- but then things look quite messy. Would rather say 'let I be a square free monomial ideal' etc and
-- not have to worry about providing s, h etc
lemma mono_ideal_up_closed (m m' : MvPolynomial X K) (hm : IsSqFreeMonomial m)
    (s : Set (MvPolynomial X K)) (h : ∀ m, m ∈ s → IsSqFreeMonomial m) :
    m ∣ m' → m ∈ SqFreeMonomialIdeal' s h → m' ∈ SqFreeMonomialIdeal' s h := by sorry

-- maybe do structure and define a membership, as in Filter
structure SqFreeMonomialIdeal'' where
  basis : Set (MvPolynomial X K)
  ideal : Ideal (MvPolynomial X K)
  ideal_eq_span : ideal = Ideal.span basis
  sq_free : ∀ m, m ∈ basis → IsSqFreeMonomial m


#check SqFreeMonomialIdeal''.ideal
instance : Membership (MvPolynomial X K) (@SqFreeMonomialIdeal'' X K _) :=
  ⟨fun m I => m ∈ I.ideal⟩

#synth Membership K (Ideal K) -- `SetLike.instMembership`
-- Then can talk about Cor 2.5 etc

-- implement geometric k simplex, complex ?
-- dimension of a simplex?
-- monomial, polynomial ring
-- monomial ideal
-- squarefree monomial ideal
-- support of a monomial
--
