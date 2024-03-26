import Mathlib.Tactic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Subtype

/-!
# The Stanley-Reisner Correspondence

The Stanley-Reisner Correspondence provides a link between abstract simplicial complexes and
squarefree monomial ideals. In this file, we introduce both of these concepts as well as introduce
the Stanley-Reisner face ring.

## Conventions

- When a "square free monomial" is mentioned, we mean a multivariate polynomial with a single term.
  The coefficient is `1` and the exponent of any variable is either `0` or `1`
- The `support` of a `MvPolynomial` is a Finset of Finsupp's specifying the exponents of each term.
- In the case of a monomial, the `support` is a singleton. We refer to the `supp` as the domain over
  which this single Finsupp is non zero. In other words, the set of variables included in the
  monomial

## Main definitions and results

- `AbstractSimplicialComplex`    : a set of `Finset`'s containing `∅` which is downwards closed.
- `sqFreeMonomial`               : subtype of `MvPolynomial` containing squaerfree monomials.
- `SqFreeMonomialIdeal`          : basis for an ideal of `sqFreeMonomial`'s not containing `1`.
- `stanleyReisnerComplex`        : `AbstractSimplicialComplex` formed by a `SqFreeMonomialIdeal`.
- `stanleyReisnerIdeal`          : `SqFreeMonomialIdeal` formed by an `AbstractSimplicialComplex`.
- `faceRing`                     : the Stanley-Reisner face ring.
- `src_of_sri_of_asc_eq_asc`     : composing `stanleyReisnerComplex`, `stanleyReisnerIdeal` is Id.
- `sri_of_asc_of_ideal_eq_ideal` : composing `stanleyReisnerIdeal`, `stanleyReisnerComplex` is Id.

## References

- See [*Combinatorics and Commutative Algebra - R.P.Stanley*] for the original source.
- This file follows [*A Survey of Stanley-Reisner Theory -  C.A.Francisco, J.Mermin, J.Schweig*] for
the formalisation.
-/

/-!

# ToDo's

* Documentation of proofs etc
* Module docstring
* review style guidelines
* lint

-/

open MvPolynomial Classical
noncomputable section
namespace ProjectThree

/- `X` is the type in which the polynomial variables are contained. `R` is the integral domain over
which the polynomials are defined. -/
variable {X R : Type} [CommRing R] [Nontrivial R] [NoZeroDivisors R]

/-- An `AbstractSimplicialComplex X` is a collection of finite sets of `X` which is downward closed
with respect to set inclusion. -/
structure AbstractSimplicialComplex (X : Type) where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

/-- A finset `f` is an element of an `AbstractSimplicialComplex` if it is a member of the `faces`
field.  -/
instance : Membership (Finset X) (AbstractSimplicialComplex X) :=
  ⟨fun f Δ => f ∈ Δ.faces⟩

/-- Indicator function on a `Finset`, implemented as a `Finsupp`. Used as the support for
squarefree monomials. -/
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

/- # Basic API for Monomials -/

@[simp]
lemma s_support_eq (A : Finset X) : (s A).support = A := rfl

lemma s_eq_toFun (A : Finset X) : s A = (s A).toFun := by rfl

lemma s_to_fun_eq_fun (A : Finset X) : (s A).toFun = fun w ↦ if w ∈ A then 1 else 0 := by rfl

lemma s_eq_one_iff (A : Finset X) (x : X) : (s A) x = 1 ↔ x ∈ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_left_iff, zero_ne_one, imp_false, not_not]

lemma s_eq_zero_iff (A : Finset X) (x : X) : (s A) x = 0 ↔ x ∉ A := by
  simp_all only [s_eq_toFun, s_to_fun_eq_fun, ite_eq_right_iff, one_ne_zero, imp_false]

lemma s_eq_zero_or_one (A : Finset X) (x : X) : (s A) x = 0 ∨ (s A) x = 1 := by
  simp_rw [s_eq_one_iff, s_eq_zero_iff]
  exact em' (x ∈ A)

lemma s_eq_elem_elem {A B : Finset X} {x : X} (h1 : s A = s B) (h2 : x ∈ A) : x ∈ B := by
  have : (s B) x = 1 := by
    · simpa [h1] using (s_eq_one_iff A x).mpr h2
  exact (s_eq_one_iff B x).mp this

lemma s_eq_iff_supp_eq (A B : Finset X) : s A = s B ↔ A = B := by
  constructor
  <;> intro h
  · ext x
    constructor
    <;> intro h'
    · exact s_eq_elem_elem h h'
    · exact s_eq_elem_elem h.symm h'
  · simp_all only

lemma mono_empty_eq_one : (monomial (s ∅)) 1 = (1 : MvPolynomial X R) := rfl

lemma s_mem_ne_zero (A : Finset X) (x : X) (h : x ∈ A) : (s A) x ≠ 0 := by
  simp_all [(s_eq_one_iff A x).mpr h]

/- # Square Free Monomials -/

/-- Subtype for square free monomials. A `MvPolynomial` is a `sqFreeMonomial` if it can be
written as a monomial with support an indicator function, and coefficient `1`. -/
def sqFreeMonomial (X R : Type) [CommRing R] [Nontrivial R] :=
    {m : MvPolynomial X R // ∃ (A : Finset X), m = monomial (s A) 1}

/-- There is a one element for the type `sqFreeMonomial`. -/
instance : One (sqFreeMonomial X R) where
  one := ⟨1, by use ∅; rfl⟩

lemma sqFreeMonomial.one_eq : (1 : sqFreeMonomial X R).val = monomial (s ∅) (1 : R) := rfl

/-- For `m : sqFreeMonomial X K`, `m.supp` is the set of variables included in `m`. -/
def sqFreeMonomial.supp (m : sqFreeMonomial X R) : Finset X := choose m.property

/-- We can rewrite a `sqFreeMonomial` as the underlying monomial. -/
lemma sqFreeMonomial.eq_mono (m : sqFreeMonomial X R) : m.val = monomial (s m.supp) (1 : R) :=
    m.property.choose_spec

/-- Two coeficient one monomials are equal if and only if they have matching support. -/
lemma mono_eq_iff_support_eq (A B : X →₀ ℕ) : monomial A (1 : R) = monomial B 1 ↔ A = B := by
  simp_all only [monomial_eq_monomial_iff, and_true, one_ne_zero, and_self, or_false]

/-- If two `sqFreeMonomial` subtypes are equal, then their underlying polynomials are also. -/
lemma mono_eq_val_eq {m m' : sqFreeMonomial X R} (h : m = m') : m.val = m'.val :=
    congrArg Subtype.val h

/-- Two coefficient one square free monomials are equal if and only if the contain the same
variables. -/
lemma mono_s_eq_iff_supp_eq (A B : Finset X) :
    monomial (s A) (1 : R) = monomial (s B) 1 ↔ A = B := by
  rw [mono_eq_iff_support_eq, s_eq_iff_supp_eq]

/-- The underlying polynomial of a `sqFreeMonomial` is equal to a monomial if and only if they have
the same variables. -/
lemma val_eq_mono_iff_supp_eq (A : Finset X) (m : sqFreeMonomial X R) :
    m.val = (monomial (s A)) 1 ↔ m.supp = A := by
  rw [← s_eq_iff_supp_eq, ← @mono_eq_iff_support_eq X R _, ← sqFreeMonomial.eq_mono]

/- Before the next result, we need a result about Finsets. -/

/-- For two Finsets `A, B`, an element is either in `A`, in `B \ A` or not in `B`. -/
lemma mem_or_mem_sdiff_or_nmem (A B : Finset X) (x : X) : x ∈ A ∨ x ∈ B \ A ∨ x ∉ B := by
  rcases (Classical.em (x ∈ A)) with (ha | hna) -- how to remove `Classical.em` from this, is there a simpler way?
  · left
    exact ha
  · rcases (Classical.em (x ∈ B)) with (hb | hnb)
    · right; left
      rw [Finset.mem_sdiff]
      exact ⟨hb, hna⟩
    · right; right
      exact hnb

/-- One `sqFreeMonomial` divides another if and only if its `supp` is contained in the others. -/
lemma poly_dvd_iff_supp_sub (m m' : sqFreeMonomial X R) : m.val ∣ m'.val ↔ m.supp ⊆ m'.supp := by
  constructor
  · rintro ⟨r, hr⟩
    intro i hi
    obtain ⟨A, hA⟩ := m.property
    obtain ⟨B, hB⟩ := m'.property
    have eq1 : m.supp = A := (val_eq_mono_iff_supp_eq A m).mp hA
    have eq2 : m'.supp = B := (val_eq_mono_iff_supp_eq B m').mp hB
    have coeff_eq : coeff (s m'.supp) (m'.val) = coeff (s m'.supp) (m.val * r)
    · rw [hr]
    simp only [hA, hB, coeff_monomial, ite_true, eq1, eq2] at coeff_eq ⊢
    rw [coeff_monomial_mul'] at coeff_eq
    have subset1 : s m.supp ≤ s m'.supp
    · by_contra H
      simp only [eq1, eq2] at H
      rw [if_neg H] at coeff_eq
      exact one_ne_zero coeff_eq
    rw [Finsupp.le_iff] at subset1
    specialize subset1 i hi
    simp only [s, Finsupp.coe_mk] at subset1
    rw [if_pos hi, eq2] at subset1
    by_contra H
    rw [if_neg H] at subset1
    linarith
  · -- this part is in previous file
    intro h
    use monomial (s (m'.supp \ m.supp)) 1
    rw [m'.eq_mono, m.eq_mono, monomial_mul, mul_one, monomial_eq_monomial_iff]
    left
    refine ⟨?_, rfl⟩
    ext x
    rcases mem_or_mem_sdiff_or_nmem m.supp m'.supp x with (h1 | h2 | h3)
    · sorry
    · sorry
    · sorry

variable (R)

/-- Construct the unique `sqFreeMonomial` given a Finset. -/
def mono_finset (A : Finset X) : sqFreeMonomial X R :=
  ⟨monomial (s A) (1 : R), by use A⟩

/-- Retrieve the underlying polynomial from `mono_finset`. -/
lemma mono_finset_val_def (A : Finset X) : (mono_finset R A).val = monomial (s A) (1 : R) := by rfl

/-- Retrieve the `supp` of `mono_finset`. -/
lemma mono_finset_supp_eq (A : Finset X) : (mono_finset R A).supp = A := by
  rw [← val_eq_mono_iff_supp_eq, mono_finset]

/-- Given two finsets satisfying `u ⊆ v`, the corresponding monomials divide eachother. -/
lemma subset_mono_dvd {u v : Finset X} (h : u ⊆ v) : monomial (s u) (1 : R) ∣ monomial (s v) 1 := by
  rw [← mono_finset_supp_eq R u, ← mono_finset_supp_eq R v] at h
  rw [← mono_finset_val_def R u, ← mono_finset_val_def R v]
  exact (poly_dvd_iff_supp_sub (mono_finset R u) (mono_finset R v)).mpr h

/-- Given a monomial divides another, its `supp` must be contained in the others.  -/
lemma dvd_mono_subset {u v : Finset X} (h : monomial (s u) (1 : R) ∣ monomial (s v) 1) : u ⊆ v := by
  rw [← mono_finset_supp_eq R u, ← mono_finset_supp_eq R v]
  rw [← mono_finset_val_def R u, ← mono_finset_val_def R v] at h
  exact (poly_dvd_iff_supp_sub (mono_finset R u) (mono_finset R v)).mp h

variable {R}

/- # Square Free Monomial Ideals -/

/-- A basis for an ideal of `sqFreeMonomial`'s which does not contain `1`. -/
structure SqFreeMonomialIdeal (X R : Type) [CommRing R] [Nontrivial R] where
  basis : Set (sqFreeMonomial X R)
  one_nelem : 1 ∉ basis

/-- The Ideal generated by a `SqFreeMonomialIdeal`. -/
def SqFreeMonomialIdeal.ideal (I : SqFreeMonomialIdeal X R) : Ideal (MvPolynomial X R) :=
    Ideal.span {m | ∃ M ∈ I.basis, M.val = m}

lemma SqFreeMonomialIdeal.ideal_eq (I : SqFreeMonomialIdeal X R) :
    I.ideal = Ideal.span {m | ∃ M ∈ I.basis, M.val = m} := by rfl

/-- For any monomial inside a `SqFreeMonomialIdeal`, if any other monomial has a larger `supp`,
it too must be contained in the ideal. -/
lemma mono_supp_sub_mem {u v : Finset X} {I : SqFreeMonomialIdeal X R}
    (h1 : monomial (s u) 1 ∈ I.ideal) (h2 : u ⊆ v) : monomial (s v) 1 ∈ I.ideal := by
  simp_rw [SqFreeMonomialIdeal.ideal_eq] at h1 ⊢
  obtain ⟨r, hr⟩ := subset_mono_dvd R h2
  simpa [hr] using Ideal.mul_mem_right r _ h1

/-- If `1` is not in the basis of a square free monomial ideal, then the ideal is
contained in the kernel of the evaluation map of `MvPolynomial`s at zero. -/
lemma one_nelem_basis_le_ker (I : SqFreeMonomialIdeal X R) (h : 1 ∉ I.basis) :
    I.ideal ≤ RingHom.ker ((eval (fun _ ↦ 0 : X → R) : MvPolynomial X R →+* R)) := by
  rw [SqFreeMonomialIdeal.ideal_eq, Ideal.span_le]
  intro m ⟨M, hM1, hM2⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, ← hM2, sqFreeMonomial.eq_mono, eval_monomial, one_mul]
  have : (sqFreeMonomial.supp M).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h'
    have hM2' := hM2
    rw [sqFreeMonomial.eq_mono, h', mono_empty_eq_one] at hM2'
    have : M = 1
    · apply Subtype.eq
      simpa [hM2] using hM2'.symm
    simp_all only [not_true_eq_false]
  rw [Finsupp.prod_eq_zero_iff, s_support_eq]
  obtain ⟨y, hy⟩ := this
  use y
  constructor
  · exact hy
  · apply zero_pow'
    exact s_mem_ne_zero (M.supp) y hy

/-- If `1` is not in the basis of a square free monomial ideal, then it is not in the ideal. -/
lemma one_nelem_basis_nelem_span (I : SqFreeMonomialIdeal X R) (h : 1 ∉ I.basis) : 1 ∉ I.ideal := by
  intro h'
  have := one_nelem_basis_le_ker I h h'
  simp_all only [RingHom.mem_ker, map_one, one_ne_zero]

/- # Stanley-Reisner Correspondence -/

/-- The Stanley-Reisner Complex of `I : SqFreeMonomialIdeal` is the `AbstractSimplicialComplex`
formed by the Finset's whose corresponding monomial is not contained in `I`. -/
def stanleyReisnerComplex (I : SqFreeMonomialIdeal X R) : AbstractSimplicialComplex X where
  faces := {A : Finset X | (monomial (s A) (1 : R)) ∉ I.ideal}
  empty_mem := by
    · intro h
      rw [mono_empty_eq_one, ← Ideal.span_singleton_le_iff_mem,
          Ideal.span_singleton_one, top_le_iff] at h
      absurd (Ideal.eq_top_iff_one (I.ideal)).mp h
      apply one_nelem_basis_nelem_span
      exact I.one_nelem
  down_closed := by
    · rintro s t hs hts ht
      dsimp at hs ht
      apply hs
      exact mono_supp_sub_mem ht hts

lemma src_faces_eq (I : SqFreeMonomialIdeal X R) :
    (stanleyReisnerComplex I).faces = {A : Finset X | (monomial (s A) (1 : R)) ∉ I.ideal} := by rfl

/- Before we define the `stanleyReisnerIdeal`, we need a result about its basis. -/

/-- `1` is not contained in the basis of the stanley reisner ideal. -/
lemma sri_one_nin_basis (Δ : AbstractSimplicialComplex X) :
    1 ∉ {mono_finset R f | f ∉ Δ.faces} := by
  intro h
  obtain ⟨f, hf1, hf2⟩ := h
  apply hf1
  have hf3 : (mono_finset R f).val = 1 ↔ f = ∅
  · rw [← mono_empty_eq_one, mono_finset_val_def]
    exact mono_s_eq_iff_supp_eq f ∅
  simpa [hf3.mp (mono_eq_val_eq hf2)] using Δ.empty_mem

/-- The `stanleyReisnerIdeal` is the ideal generated by the monomials described by the non-faces
of an abstract simplicial complex. -/
def stanleyReisnerIdeal (X R : Type) (Δ : AbstractSimplicialComplex X) [CommRing R] [Nontrivial R]
    [NoZeroDivisors R]: SqFreeMonomialIdeal X R where
  basis := {mono_finset R f | f ∉ Δ.faces}
  one_nelem := sri_one_nin_basis Δ

lemma sri_basis_eq (Δ : AbstractSimplicialComplex X) :
    (stanleyReisnerIdeal X R Δ).basis = {mono_finset R f | f ∉ Δ.faces} := by rfl

/-- `1` is not contained in the stanley reisner ideal. -/
lemma sri_one_nin_ideal (Δ : AbstractSimplicialComplex X) :
    (1 : MvPolynomial X R) ∉ (stanleyReisnerIdeal X R Δ).ideal :=
  one_nelem_basis_nelem_span (stanleyReisnerIdeal X R Δ) (sri_one_nin_basis Δ)

/-- The stanley reisner face ring of and abstract simplicial complex `Δ`. The are the monomials
corresponding to the faces of `Δ `. -/
def faceRing (Δ : AbstractSimplicialComplex X) :=
    (MvPolynomial X R) ⧸ (stanleyReisnerIdeal X R Δ).ideal


-- Prop 2.7 provides the bijection between abstract simplicial complexes and squarefree monomial ideals
section expr
variable {σ R : Type*}

variable [CommSemiring R] [NeZero (1 : R)]

lemma mem_span_exists_dvd_mem_basis {S : Set (σ →₀ ℕ)} (s : σ →₀ ℕ)
    (h : monomial s 1 ∈ Ideal.span ((fun s => monomial s (1 : R)) '' S)) :
    ∃ i ∈ S, monomial i (1 : R) ∣ monomial s 1 := by
 classical
 rcases mem_ideal_span_monomial_image_iff_dvd.1 h s (by
  simp only [support_monomial, if_neg one_ne_zero, Finset.mem_singleton_self]) with ⟨j, hS, hj⟩
 use j, hS
 simpa [coeff_monomial, if_pos] using hj
end expr

lemma SqFreeMonomialIdeal.basis_eq (I : SqFreeMonomialIdeal X R) : {m | ∃ M ∈ I.basis, M.val = m} =
    ((fun k => monomial k (1 : R)) '' {s (M.supp) | M ∈ I.basis}) := by
  ext y
  constructor
  · rintro ⟨M, hM1, hM2⟩
    use (s M.supp)
    constructor
    · use M
    · rw [← hM2]
      dsimp
      exact (sqFreeMonomial.eq_mono M).symm
  · rintro ⟨k, ⟨M, ⟨hM, hk1⟩⟩, hk2⟩
    dsimp at hk2
    use M
    constructor
    · exact hM
    · rw [← hk2, ← hk1]
      exact sqFreeMonomial.eq_mono M

lemma SqFreeMonomialIdeal.ideal_eq' (I : SqFreeMonomialIdeal X R) :
    I.ideal = Ideal.span ((fun k => monomial k (1 : R)) '' {s (M.supp) | M ∈ I.basis}) := by
  rw [SqFreeMonomialIdeal.ideal_eq, SqFreeMonomialIdeal.basis_eq]

lemma mem_faces_mono_nmem_sri_ideal (Δ : AbstractSimplicialComplex X) (y : Finset X) (h : y ∈ Δ.faces) :
    monomial (s y) 1 ∉ (stanleyReisnerIdeal X R Δ).ideal := by
  intro h'
  rw [SqFreeMonomialIdeal.ideal_eq'] at h'
  obtain ⟨i, ⟨M, ⟨f, hf1, hf2⟩, hM⟩, hdvd⟩ := mem_span_exists_dvd_mem_basis (s y) h'
  have sub1 : M.supp ⊆ y
  · rw [← hM] at hdvd
    exact dvd_mono_subset R hdvd
  have eq1 : M.supp = f
  · rw [mono_finset] at hf2
    rw [← @mono_s_eq_iff_supp_eq X R _ _ M.supp f]
    have := (mono_eq_val_eq hf2).symm
    dsimp only at this
    simpa [sqFreeMonomial.eq_mono M] using this
  rw [eq1] at sub1
  apply hf1
  exact Δ.down_closed h sub1

/-- For `Δ` an `AbstractSimplicialComplex`, taking the `stanleyReisnerIdeal` and then the
`stanleyReisnerComplex` gives `Δ`. -/
lemma src_of_sri_of_asc_eq_asc (Δ : AbstractSimplicialComplex X) :
    (stanleyReisnerComplex (stanleyReisnerIdeal X R Δ)).faces = Δ.faces := by
  rw [src_faces_eq]
  ext y
  constructor
  · intro h'
    rw [SqFreeMonomialIdeal.ideal_eq, sri_basis_eq] at h'
    dsimp at h'
    by_contra H
    apply h'
    have : monomial (s y) (1 : R) ∈ {m | ∃ M, (∃ f ∉ Δ.faces, mono_finset R f = M) ∧ M.val = m}
    · use (mono_finset R y)
      constructor
      · use y
      · simp_all only [ne_eq, exists_exists_and_eq_and]
        rfl
    exact Ideal.subset_span this
  · intro h'
    dsimp
    intro h''
    have := @mem_faces_mono_nmem_sri_ideal X R _ _ _ Δ y h'
    contradiction

/-- If a set `A` is contained in the span of another `B` then the span of `A` is also contained. -/
lemma sub_span_span_sub {A B : Set (MvPolynomial X R)} (h : A ⊆ Ideal.span B) :
    SetLike.coe (Ideal.span A) ⊆ Ideal.span B := by
  simp only [SetLike.coe_subset_coe, Ideal.span_le.mpr h]

/-- Spans of two sets `A`, `B` are equal if and only if each is contained in the span of the other-/
lemma span_eq_iff_basis_sub (A B : Set (MvPolynomial X R)) :
    Ideal.span A = Ideal.span B ↔ A ⊆ Ideal.span B ∧ B ⊆ Ideal.span A := by
  constructor
  · intro h
    constructor
    · have : A ⊆ Ideal.span A := Ideal.subset_span
      simp_all only
    · have : B ⊆ Ideal.span B := Ideal.subset_span
      simp_all only
  · intro ⟨hA, hB⟩
    rw [← SetLike.coe_set_eq, Set.Subset.antisymm_iff]
    exact ⟨sub_span_span_sub hA, sub_span_span_sub hB⟩

/-- For `I` a `SqFreeMonomialIdeal`, taking the `stanleyReisnerComplex` and then the
`stanleyReisnerIdeal` gives `I`. -/
lemma sri_of_asc_of_ideal_eq_ideal (I : SqFreeMonomialIdeal X R) :
    (stanleyReisnerIdeal X R (stanleyReisnerComplex I)).ideal = I.ideal := by
  simp_rw [SqFreeMonomialIdeal.ideal_eq, span_eq_iff_basis_sub]
  constructor
  · intro m ⟨M, hM1, hM2⟩
    rw [sri_basis_eq] at hM1
    obtain ⟨f, hf1, hf2⟩ := hM1
    rw [src_faces_eq] at hf1


    --rw [SqFreeMonomialIdeal.ideal_eq'] at h


  -- --intro h
  --   --rw [SqFreeMonomialIdeal.ideal_eq, sri_basis_eq] at h
  --   rintro ⟨f, hf1, hf2⟩
  --   by_contra H
  --   apply hf1
  --   intro h'
  --   have := mem_faces_mono_nmem_sri_ideal R (stanleyReisnerComplex I)
  --   rw [src_faces_eq] at this
  --   specialize this f (by sorry)
  --   rw [SqFreeMonomialIdeal.ideal_eq] at this
    -- this is the same issue as the previous lemma
    sorry
  · intro h'
    dsimp
    use x.supp
    constructor
    · push_neg
      rw [← sqFreeMonomial.eq_mono]
      have : x.val ∈ {m | ∃ M ∈ I.basis, M.val = m}
      · use x
      exact Ideal.subset_span this
    · apply Subtype.eq
      simpa [mono_finset] using (sqFreeMonomial.eq_mono x).symm


#check (MvPolynomial X R)ˣ
#check MvPolynomial.X
example (A : Finset X) : Squarefree (monomial (s A) (1 : R)) := by -- seems tough
  intro x ⟨r, hr⟩
  unfold IsUnit
  simp only [monomial_eq, map_one, one_mul] at hr
  sorry


-- THIS IS A MONOID, to prove would need to come up with a supp definition as above
def monomial_subtype (X R : Type) [CommRing R] := {m : MvPolynomial X R // ∃ (f : X →₀ ℕ), m = monomial f (1 : R)}









end ProjectThree
