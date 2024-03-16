import Mathlib.Tactic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic

open MvPolynomial Classical
variable {X K : Type} [CommSemiring K]


/-
attempt using a structure for square free monomials: `SqFreeMonomial`

* When I say sq free monomial, implicitly I mean it is monic.

PROBLEMS/QUESTIONS:
* why are do errors disappear when typing `noncomputable` and is it okay to use?
* Need to decide on wether `IsSqFreeMonomial` is a good definition or not
* Should I create a coercion from `m : SqFreeMonomial` to `MvPolynomial` by returning `m.poly`. What
  are the implications of this?
* Need to create more API in general for `s`.
* Create new clean document with progress so far.
* What is difference between `def` and `instance`? !!!!

-/

/-- An abstract simplicial complex is a collection of finite sets which is downward closed with
respect to set inclusion. -/
structure AbstractSimplicialComplex (X : Type) where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

instance : Membership (Finset X) (AbstractSimplicialComplex X) :=
  ⟨fun f Δ => f ∈ Δ.faces⟩

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

@[simp]
lemma s_eq_toFun (A : Finset X) : s A = (s A).toFun := by rfl
lemma s_to_fun_eq_fun (A : Finset X) : (s A).toFun = fun w ↦ if w ∈ A then 1 else 0 := by rfl
lemma s_eq_one_iff (A : Finset X) (x : X) : (s A) x = 1 ↔ x ∈ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
lemma s_eq_zero_iff (A : Finset X) (x : X) : (s A) x = 0 ↔ x ∉ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_right_iff, one_ne_zero, imp_false]
lemma s_eq_zero_or_one (A : Finset X) (x : X) : (s A) x = 0 ∨ (s A) x = 1 := by
  simp_rw [s_eq_one_iff, s_eq_zero_iff]
  exact em' (x ∈ A)



noncomputable def monomialSupportedByFinset (K : Type) (A : Finset X) [CommSemiring K] :
  MvPolynomial X K := monomial (s A) 1

@[simp]
lemma monomialSupportedByFinset_def (K : Type) (A : Finset X) [CommSemiring K] :
    monomialSupportedByFinset K A = monomial (s A) 1 := by rfl

structure SqFreeMonomial (X K : Type) [CommSemiring K] where
/- The variables to be included in the polynomial. Typically the `support` of an `MvPolynomial`
is a Finsupp telling you the exponents of each variable. `supp` is simply the domain of such
a function. -/
  supp : Finset X
/- The underlying polynomial. -/
  poly : MvPolynomial X K
/- `poly` is a monomial with coefficient `1 : K` and exponents all 1 on `supp`. This is done by
constructing the Finsupp `s supp`. -/
  eq_mono : poly = monomial (s supp) 1

-- define all instances for EQ, add etc

-- **Don't understand this error** adding `noncomputable` stops it.
instance SqFreeMonomialOfFinset (X K : Type) (A : Finset X) [CommSemiring K] : SqFreeMonomial X K where
  supp := A
  poly := monomialSupportedByFinset K A
  eq_mono := by simp

@[simp]
lemma sq_free_monomial_of_finset_poly (A : Finset X) : monomialSupportedByFinset K A =
    (SqFreeMonomialOfFinset X K A).poly := by rfl

-- **Don't understand this error** adding `noncomputable` stops it.
instance one_sq_free : SqFreeMonomial X K where
  supp := Finset.empty
  poly := 1
  eq_mono := rfl

#check monic_monomial_eq
#check monomial_eq_monomial_iff
#check monomial_eq
#check Finsupp.prod
-- have done `= m.poly` but could define equality one the structure to just write `= m`. Much easier
-- with structure than before.
lemma prop22a (m : SqFreeMonomial X K) : monomialSupportedByFinset K (m.supp) = m.poly := by
  rw [m.eq_mono, monomialSupportedByFinset_def]

lemma prop22b (A : Finset X) : (SqFreeMonomialOfFinset X K A).supp = A := rfl

lemma supp_add (a b : Finsupp X ℕ) (x : X) : (a + b) x = a x + b x := rfl

-- would be good to find a way to not include so much calculation, perhaps create more API
lemma prop22c (m m' : SqFreeMonomial X K) : m.poly ∣ m'.poly ↔ m.supp ⊆ m'.supp := by
  constructor
  <;> intro h
  · obtain ⟨r, hr⟩ := h
    sorry
  · use monomial (s (m'.supp \ m.supp : Finset X)) 1
    rw [m'.eq_mono, m.eq_mono, monomial_mul, mul_one, monomial_eq_monomial_iff]
    left
    constructor
    · ext x
      have : x ∈ m.supp ∨ x ∈ m'.supp \ m.supp ∨ x ∉ m'.supp := by sorry
      rcases this with (h1|h2|h3)
      · calc
          (s m'.supp) x = 1 := by exact (s_eq_one_iff m'.supp x).mpr h1
          _ = 1 + 0 := by linarith
          _ = 1 + s (m'.supp \ m.supp) x := by
            · rw [add_left_cancel_iff, eq_comm]
              exact (s_eq_zero_iff (m'.supp \ m.supp) x).mpr (by sorry)
          _ = s (m.supp) x + s (m'.supp \ m.supp) x := by
            · rwa [add_right_cancel_iff, eq_comm, s_eq_one_iff m.supp x]
          _ = (s m.supp + s (m'.supp \ m.supp)) x := by rfl
      · sorry
      · sorry
    · rfl

/-- An `MvPolynomial` is a square free monomial if we can find a-/
def IsSqFreeMonomial (m : MvPolynomial X K) : Prop := ∃ n : SqFreeMonomial X K, m = n.poly

/-- A squarefree monomial ideal is the ideal generated by a collection of squarefree monomials. -/
structure SqFreeMonomialIdeal (X K : Type) [CommSemiring K] where
  basis : Set (MvPolynomial X K)
  ideal : Ideal (MvPolynomial X K)
  ideal_eq_span : ideal = Ideal.span basis
  sq_free : ∀ m, m ∈ basis → IsSqFreeMonomial m

instance : Membership (MvPolynomial X K) (SqFreeMonomialIdeal X K) :=
  ⟨fun m I => m ∈ I.ideal⟩

def stanleyReisnerComplex (I : SqFreeMonomialIdeal X K) : AbstractSimplicialComplex X where
  faces := by
  -- given any `IsSqFreeMonomial m` we have `n : SqFreeMonomial X K` such that `m = n.poly`
  -- want to return `{n.supp for all n}`.
  {m.support | IsSqFreeMonomial m ∧ m ∉ I}
  empty_mem := _
  down_closed := _

/-- The `stanleyReisnerIdeal` is the ideal generated by the monomials described by the non-faces
of an abstract simplicial complex. -/
def stanleyReisnerIdeal (Δ : AbstractSimplicialComplex X) : SqFreeMonomialIdeal X K where
  basis := {monomialSupportedByFinset K f | f ∉ Δ.faces}
  ideal := Ideal.span {monomialSupportedByFinset K f | f ∉ Δ.faces}
  ideal_eq_span := rfl
  sq_free := by
    · rintro m ⟨f, -, hf⟩
      use SqFreeMonomialOfFinset X K f
      rwa [← sq_free_monomial_of_finset_poly f, eq_comm]

-- Define the face ring
-- Proposition 2.7
