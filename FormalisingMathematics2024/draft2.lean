import Mathlib.Tactic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic

/-!

# Questions / ToDo's

* What is a subtype, and is it relevant to me for creating Stanley Reisner Complex (need monomials
  *not* in a `SqFreeMonomialIdeal`)
* How shouuld I handle coercions
* How should I handle Membership instances etc
* What is difference between `def` and `instance`?
* How should I be using sections and variables?

-/

open MvPolynomial Classical
namespace ProjectThree

variable {X K : Type} [CommSemiring K]

/-- An abstract simplicial complex is a collection of finite sets which is downward closed with
respect to set inclusion. -/
structure AbstractSimplicialComplex (X : Type) where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

/-- Identify an `AbstractSimplicialComplex` with its `faces` field. -/
instance : Membership (Finset X) (AbstractSimplicialComplex X) :=
  ⟨fun f Δ => f ∈ Δ.faces⟩

/-- Finsupp used to index squarefree monomials. -/
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

/-- The monomial with variables according to a Finset. -/
noncomputable def monomialSupportedByFinset (K : Type) (A : Finset X) [CommSemiring K] :
  MvPolynomial X K := monomial (s A) 1

@[simp]
lemma monomialSupportedByFinset_def (K : Type) (A : Finset X) [CommSemiring K] :
    monomialSupportedByFinset K A = monomial (s A) 1 := by rfl

/-- The type of square free monomials. Here a monomial means a multivariate polynomial with a single
term. Squarefree means no variable has exponent greater than 1. -/
structure SqFreeMonomial (X K : Type) [CommSemiring K] where
/- The variables to be included in the polynomial. Typically the `support` of an `MvPolynomial`
is a Finsupp telling you the exponents of each variable. `supp` is simply the domain of such
a function. -/
  supp : Finset X
/- The underlying polynomial. -/
  poly : MvPolynomial X K -- **Don't need to include this** If I don't need this then I don't need the coercion!
/- `poly` is a monomial with coefficient `1 : K` and exponents all 1 on `supp`. This is done by
constructing the Finsupp `s supp`. -/
  eq_mono : poly = monomial (s supp) 1 -- **Don't need to include this**

/-- An `MvPolynomial`, `m` is a square free monomial if we can find an element of `SqFreeMonomial`
with `m` as the `poly` field. -/
def IsSqFreeMonomial (m : MvPolynomial X K) : Prop := ∃ n : SqFreeMonomial X K, m = n.poly

/-- Coercion instance identifying any `SqFreeMonomial` with its `poly`. -/
instance SqFreeMonomial.toMvPolynomial : Coe (SqFreeMonomial X K) (MvPolynomial X K) where
  coe := fun x ↦ x.poly

-- **Don't understand this error** adding `noncomputable` stops it.
/-- Given a finset view `monomialSupportedByFinset` as a `SqFreeMonomial`  -/
instance SqFreeMonomialOfFinset (X K : Type) (A : Finset X) [CommSemiring K] : SqFreeMonomial X K where
  supp := A
  poly := monomialSupportedByFinset K A
  eq_mono := monomialSupportedByFinset_def K A

@[simp]
lemma sq_free_monomial_of_finset_poly (A : Finset X) : monomialSupportedByFinset K A =
    (SqFreeMonomialOfFinset X K A).poly := by rfl
lemma support_supp_eq (m : SqFreeMonomial X K) : monomialSupportedByFinset K (m.supp) = m := by
  rw [m.eq_mono, monomialSupportedByFinset_def]

lemma supp_of_sq_free_eq_supp (A : Finset X) : (SqFreeMonomialOfFinset X K A).supp = A := rfl

-- would be good to find a way to not include so much calculation, perhaps create more API
/-- A square free monomial divides another if and only if all of its variables are included in the
other. For example `xy` divides `wxyz`. -/
lemma poly_dvd_iff_supp_sub (m m' : SqFreeMonomial X K) : m.poly ∣ m'.poly ↔ m.supp ⊆ m'.supp := by
  constructor
  · rintro ⟨r, hr⟩
    sorry
  · intro h
    use monomial (s (m'.supp \ m.supp : Finset X)) 1
    rw [m'.eq_mono, m.eq_mono, monomial_mul, mul_one, monomial_eq_monomial_iff]
    left
    constructor
    · ext x
      have : x ∈ m.supp ∨ x ∈ m'.supp \ m.supp ∨ x ∉ m'.supp := by sorry
      rcases this with (h1|h2|h3)
      · calc
          (s m'.supp) x = 1 := by exact (s_eq_one_iff m'.supp x).mpr (h h1)
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

/-- A squarefree monomial ideal is the ideal generated by a collection of squarefree monomials. -/
structure SqFreeMonomialIdeal (X K : Type) [CommSemiring K] where
  basis : Set (MvPolynomial X K)
  ideal : Ideal (MvPolynomial X K) -- **Don't need to include this**
  ideal_eq_span : ideal = Ideal.span basis -- **Don't need to include this**
  sq_free : ∀ m, m ∈ basis → IsSqFreeMonomial m

/-- Identify a `SqFreeMonomialIdeal` with its `ideal` field. -/
instance : Membership (MvPolynomial X K) (SqFreeMonomialIdeal X K) :=
  ⟨fun m I => m ∈ I.ideal⟩

-- Instantiate `GaloisConnection` by getting correct functions and types.
-- Define StanleyReisnerComplex
def stanleyReisnerComplex (I : SqFreeMonomialIdeal X K) : AbstractSimplicialComplex X where
  faces := {(m : SqFreeMonomial X K).supp | m ∉ I}
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

-- Define Face Ring as quotient of polynomial ring by `stanleyReisnerIdeal`


end ProjectThree
