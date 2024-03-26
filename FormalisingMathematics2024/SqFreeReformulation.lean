import Mathlib.Tactic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Basic

open MvPolynomial Classical
noncomputable section
namespace ProjectThree
variable {X K : Type} [CommRing K] [Nontrivial K]
/-!

# Problems / Questions

* What does `simp_all only` to compared to `simp_all`
-/

/-- An abstract simplicial complex is a collection of finite sets which is downward closed with
respect to set inclusion. -/
structure AbstractSimplicialComplex (X : Type) where
  faces : Set (Finset X)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

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
lemma mono_empty_eq_one : (monomial (s ∅)) 1 = (1 : MvPolynomial X K) := rfl

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

-- **ASK ABOUT THIS**
example (m m' : SqFreeMonomial X K) : m = m' ↔ m.supp = m'.supp := by
  constructor
  · intro h
    simp_all only
  · intro h
    sorry

-- any way to remove the part before the dot using namespaces etc?
def SqFreeMonomial.toPoly (m : SqFreeMonomial X K) : MvPolynomial X K := monomial (s m.supp) 1

lemma SqFreeMonomial.eq_mono (m : SqFreeMonomial X K) : m.toPoly = monomial (s m.supp) 1 := by rfl

-- Is this really needed?
instance SqFreeMonomialOfFinset (X K : Type) (A : Finset X) [CommSemiring K] : SqFreeMonomial X K where
  supp := A

@[simp]
lemma sq_free_monomial_of_finset_poly (A : Finset X) : monomialSupportedByFinset K A =
    (SqFreeMonomialOfFinset X K A).toPoly := by rfl
lemma support_supp_eq (m : SqFreeMonomial X K) : monomialSupportedByFinset K (m.supp) = m.toPoly := by
  rw [m.eq_mono, monomialSupportedByFinset_def]
lemma supp_of_sq_free_eq_supp (A : Finset X) : (SqFreeMonomialOfFinset X K A).supp = A := rfl

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

lemma mono_eq_iff_supp_eq (A B : X →₀ ℕ) : monomial A (1 : K) = monomial B 1 ↔ A = B := by
  constructor
  · intro h
    rw [monomial_eq_monomial_iff] at h
    rcases h with (⟨hAB, -⟩ | ⟨hf, -⟩)
    · exact hAB
    · simp_all only [one_ne_zero]
  · intro
    simp_all only

example (f g : X →₀ ℕ) (a b : K) :
    (MvPolynomial.monomial f a) * (MvPolynomial.monomial g b)
    = (MvPolynomial.monomial (f + g) (a * b)) := monomial_mul
#synth Monoid (MvPolynomial X K)


#check Subtype
instance : Submonoid (MvPolynomial X K) where
  carrier := {m | ∃ (f : X →₀ ℕ), ∃ (a : K), m = monomial f a}
  mul_mem' := by
    · intro x y ⟨fx, ax, hx⟩ ⟨fy, ay, hy⟩
      use (fx + fy), (ax * ay)
      simp [hx, hy]
  one_mem' := by
    · dsimp
      use 0, 1
      rfl

#check Monoid
#check MvPowerSeries.monomial_mul_monomial
instance : Dvd (SqFreeMonomial X K) := ⟨fun m m' ↦ m.toPoly ∣ m'.toPoly⟩
variable (m m' : SqFreeMonomial X K)
#check m ∣ m'
example (h : m' ∣ m) : ∃ r, m.toPoly = r * m'.toPoly := by
  obtain ⟨r, hr⟩ := h
  use r
  rw [hr, mul_comm]

-- would be good to find a way to not include so much calculation, perhaps create more API
/-- A square free monomial divides another if and only if all of its variables are included in the
other. For example `xy` divides `wxyz`. -/
lemma poly_dvd_iff_supp_sub (m m' : SqFreeMonomial X K) : m.toPoly ∣ m'.toPoly ↔ m.supp ⊆ m'.supp := by
  constructor
  · rintro ⟨r, hr⟩
    intro i hi
    have coeff_eq :
      coeff (s m'.supp) (SqFreeMonomial.toPoly m') =
      coeff (s m'.supp) (SqFreeMonomial.toPoly m * r) := by
      rw [hr]

    simp only [SqFreeMonomial.eq_mono, coeff_monomial, ite_true] at coeff_eq
    rw [coeff_monomial_mul'] at coeff_eq
    have subset1 : s m.supp ≤ s m'.supp := by
      by_contra H
      rw [if_neg H] at coeff_eq
      exact one_ne_zero coeff_eq
    rw [Finsupp.le_iff] at subset1
    specialize subset1 i hi
    simp only [s, Finsupp.coe_mk] at subset1
    rw [if_pos hi] at subset1
    by_contra H
    rw [if_neg H] at subset1
    linarith
  · intro h
    use monomial (s (m'.supp \ m.supp : Finset X)) 1
    rw [m'.eq_mono, m.eq_mono, monomial_mul, mul_one, monomial_eq_monomial_iff]
    left
    constructor
    · ext x
      rcases mem_or_mem_sdiff_or_nmem m.supp m'.supp x with (h1|h2|h3)
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

-- **Alternative**
  --   have : ∃ A, r = monomial (s A) 1 := by
  --     · simp_rw [SqFreeMonomial.eq_mono] at hr

  --       use (m'.supp \ m.supp)
  --       simp_all [ext_iff]
  --       intro a
  --       specialize hr a
  --       rw [mul_comm, coeff_mul_monomial'] at hr
  --       split_ifs at hr with h1 h2
  --       · have a_eq : a = s a.support := by
  --           ext i
  --           simp only [s, Finsupp.mem_support_iff, ne_eq, ite_not, Finsupp.coe_mk]
  --           rw [FunLike.ext_iff] at h1
  --           specialize h1 i
  --           simp only [s, Finsupp.coe_mk] at h1

  --           by_cases hi : i ∈ m'.supp
  --           · rw [if_pos hi] at h1
  --             rw [h1, if_neg]
  --             linarith
  --           · rw [if_neg hi] at h1
  --             rw [h1, if_pos]
  --             rfl
  --         have a_supp_eq : a.support = m'.supp := sorry

  --         have subset1 : m.supp ⊆ m'.supp := by
  --           intro i hi
  --           rw [Finsupp.le_iff] at h2
  --           specialize h2 i
  --           simp only [s, Finsupp.coe_mk] at h2
  --           specialize h2 hi
  --           rw [if_pos hi] at h2
  --           rw [a_eq, s] at h2
  --           dsimp at h2
  --           rw [a_supp_eq] at h2
  --           by_contra H
  --           rw [if_neg H] at h2
  --           linarith

  --         have eq0 : a - s m.supp = s (a.support \ m.supp) := sorry
  --         have eq1 : a - s m.supp = s (m'.supp \ m.supp) := sorry
  --         have hr' : coeff (s (m'.supp \ m.supp)) r = 1 := sorry
  --         -- simp only [mul_one] at hr
  --         -- have h0 : s (m'.supp \ m.supp) = a := by

  --         --   ext i
  --         rw [a_eq, a_supp_eq]
  --         simp only [s, Finset.mem_sdiff]
  --         --   split_ifs with h3
  --         --   ·
  --       -- rw [eq_ite_iff]
  --       -- rcases (Classical.em (s (m'.supp \ m.supp) = a)) with (h1 | h2)
  --       -- · left
  --       --   constructor
  --       --   · exact h1
  --       --   · sorry
  --       -- · right
  --       --   constructor
  --       --   · exact h2
  --       --   · sorry


  --   obtain ⟨A, hA⟩ := this
  --   simp_rw [hA, SqFreeMonomial.eq_mono] at hr
  --   simp only [monomial_mul, mul_one] at hr
  --   have := (mono_eq_iff_supp_eq (s m'.supp) (s m.supp + s A)).mp hr
  --   intro y hy
  --   rw [← s_eq_one_iff] at hy ⊢
  --   have hsA : (s A) y = 0 := by sorry -- Should be simple using `s_eq_zero_or_one`.
  --   simp_all only [s_eq_toFun, Finsupp.coe_add, Pi.add_apply, add_zero]

/-- A squarefree monomial ideal is the ideal generated by a collection of squarefree monomials. -/
structure SqFreeMonomialIdeal (X K : Type) [CommSemiring K] where
  basis : Set (SqFreeMonomial X K)

def SqFreeMonomialIdeal.ideal (I : SqFreeMonomialIdeal X K) : Ideal (MvPolynomial X K) :=
    Ideal.span {p | ∃ m ∈ I.basis, m.toPoly = p}


lemma SqFreeMonomial.ideal_eq (I : SqFreeMonomialIdeal X K) :
    I.ideal = Ideal.span {p | ∃ m ∈ I.basis, m.toPoly = p} := by rfl

/-- Identify a `SqFreeMonomialIdeal` with its `ideal` field. -/
instance : Membership (MvPolynomial X K) (SqFreeMonomialIdeal X K) :=
  ⟨fun m I => m ∈ I.ideal⟩

-- example (I : SqFreeMonomialIdeal X K) (h : ⟨∅⟩ ∉ I.basis) : 1 ∉ I.ideal := by
--   rw [SqFreeMonomial.ideal_eq]
-- sorry

@[simp]
lemma SqFreeMonomial.mem_ideal_iff (I : SqFreeMonomialIdeal X K) (m : MvPolynomial X K) :
    m ∈ I ↔ m ∈ I.ideal := Iff.rfl

variable (K) -- Need to work out a good solution for this.

lemma eq_cons_supp (A : Finset X) : A = (⟨A⟩ : SqFreeMonomial X K).supp := by rfl
lemma mono_eq_cons_to_poly (A : Finset X) :
    monomial (s A) (1 : K) = (⟨A⟩ : SqFreeMonomial X K).toPoly := by rfl

example (I : Ideal (MvPolynomial X K)) (a b : MvPolynomial X K) (h : a ∣ b) (ha : a ∈ I) : b ∈ I := by
  obtain ⟨r, hr⟩ := h
  rw [hr]
  exact Ideal.mul_mem_right r I ha

-- example (A : Finset X) : monomial (s A) 1 ≠ 1 := by sorry
lemma mono_supp_sub_mem {u v : Finset X} {I : SqFreeMonomialIdeal X K} (h1 : monomial (s u) 1 ∈ I )
    (h2 : u ⊆ v) : monomial (s v) 1 ∈ I := by
  rw [eq_cons_supp K u, eq_cons_supp K v, ← poly_dvd_iff_supp_sub] at h2
  rw [mono_eq_cons_to_poly, SqFreeMonomial.mem_ideal_iff, SqFreeMonomial.ideal_eq] at h1 ⊢
  obtain ⟨r, hr⟩ := h2
  simpa [hr] using Ideal.mul_mem_right r _ h1

-- Define StanleyReisnerComplex
-- Added in `h` because if not, we may have that `∅` is not a member. Since `⟨∅⟩` (the SqFreeMonomial) corresponds to
-- the monomial `1`, which could well be in our ideal.
def stanleyReisnerComplex (I : SqFreeMonomialIdeal X K) (h : I.ideal ≠ ⊤) : AbstractSimplicialComplex X where
  faces := {A : Finset X | (monomial (s A) (1 : K)) ∉ I}
  empty_mem := by
    · intro h
      rw [mono_empty_eq_one, SqFreeMonomial.mem_ideal_iff, ← Ideal.span_singleton_le_iff_mem,
          Ideal.span_singleton_one, top_le_iff] at h
      contradiction
  down_closed := by
    · rintro s t hs hts ht
      dsimp at hs ht
      apply hs
      exact mono_supp_sub_mem K ht hts

/-- The `stanleyReisnerIdeal` is the ideal generated by the monomials described by the non-faces
of an abstract simplicial complex. -/
def stanleyReisnerIdeal (Δ : AbstractSimplicialComplex X) : SqFreeMonomialIdeal X K where
  basis := {⟨f⟩ | f ∉ Δ.faces}

lemma src_faces_eq (I : SqFreeMonomialIdeal X K) (h : I.ideal ≠ ⊤) :
    (stanleyReisnerComplex K I h).faces = {A : Finset X | (monomial (s A) (1 : K)) ∉ I} := by rfl
lemma sri_basis_eq (Δ : AbstractSimplicialComplex X) :
    (stanleyReisnerIdeal K Δ).basis = {⟨f⟩ | f ∉ Δ.faces} := by rfl

-- Need to define the Stanley Reisner Ring
#synth Ring (MvPolynomial X K)
def faceRing (Δ : AbstractSimplicialComplex X) := (MvPolynomial X K) ⧸ (stanleyReisnerIdeal K Δ).ideal


-- **Prop 2.7 part 1**
example (Δ : AbstractSimplicialComplex X) : (stanleyReisnerComplex K (stanleyReisnerIdeal K Δ) (by sorry)).faces = Δ.faces := by sorry

-- **Prop 2.7 part 2**
example (I : SqFreeMonomialIdeal X K) (h : I.ideal ≠ ⊤) : (stanleyReisnerIdeal K (stanleyReisnerComplex K I h)).basis = I.basis := by
  · rw [sri_basis_eq, src_faces_eq]
    ext x
    constructor
    · intro h1
      simp only [SqFreeMonomial.mem_ideal_iff, Set.mem_setOf_eq,
      not_not, SqFreeMonomial.ideal_eq, SqFreeMonomial.toPoly] at h1
      obtain ⟨f, ⟨hf1, hf2⟩⟩ := h1
      sorry
    sorry
#check fun (m : MvPolynomial X K) ↦ eval m -- at zero, ring hom
example (I : SqFreeMonomialIdeal X K) (h : I.ideal ≠ ⊤): (stanleyReisnerIdeal K (stanleyReisnerComplex K I h)).ideal = I.ideal := by
  · simp_rw [SqFreeMonomial.ideal_eq, SqFreeMonomial.eq_mono]
    ext y
    constructor
    intro H
    sorry





-- **Ask About This** Does it even make sense??
@[simp]
lemma SqFreeMonoimal.eq_poly_iff (a b : SqFreeMonomial X K) : a = b ↔ a.toPoly = b.toPoly := by
  constructor
  <;> intro h
  · simp_all only
  · sorry

#check Nat.galoisConnection_mul_div
#check GaloisConnection
-- Do I even need this?
#check dvd_iff_exists_eq_mul_left
#check Associated
example (m m' : MvPolynomial X K) (h1 : m ∣ m') (h2 : m' ∣ m) : m = m' := by sorry
instance : Preorder (SqFreeMonomial X K) where
  le := fun m m' ↦ m.toPoly ∣ m'.toPoly
  lt := fun m m' ↦ m.toPoly ∣ m'.toPoly ∧ m.toPoly ≠ m'.toPoly
  le_refl := by
    · intro a
      use 1
      simp only [mul_one]
  le_trans := by
    · intro a b c hab hbc
      obtain ⟨x, hx⟩ := hab
      obtain ⟨y, hy⟩ := hbc
      use x * y
      rw [hy, hx, mul_assoc]
  lt_iff_le_not_le := by
    · intro a b
      constructor
      <;> rintro ⟨⟨x, hx⟩, h⟩
      · constructor
        · use x
        · rintro ⟨y, hy⟩
          apply h
          simp_rw [SqFreeMonomial.eq_mono] at *

          rw [hy, mul_assoc] at hx
          sorry
      · constructor
        · use x
        · intro hab
          apply h
          use 1
          simpa [mul_one, SqFreeMonoimal.eq_poly_iff] using hab

structure MonoSupp (X : Type) where
  fsupp : Finsupp X ℕ



def MonoSupp.toPoly (m : MonoSupp X) : MvPolynomial X K := monomial (m.fsupp) (1 : K)
#synth AddMonoid (Finsupp X ℕ) -- this is the




/- **Monomials Form a `Monoid`? Also a `Cancel Monoid`?** But not sq free monomials. -/
/- What I would like to say is that monomials are ordered by division? -/

#check CancelMonoid
-- actuclly this doesn't make sense. Mult of two sq free monomials may not be a sq free monomial
instance : CancelMonoid (SqFreeMonomial X K) where
  mul := fun m m' ↦ ⟨m.supp ∪ m.supp⟩
  mul_assoc := by
    · intro a b c
      sorry
  mul_left_cancel := _
  one := _
  one_mul := _
  mul_one := _
  npow := _
  npow_zero := _
  npow_succ := _
  mul_right_cancel := _



#synth IsDomain ℤ
example (a b : ℤ) (h : a * b = 1) : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h
/-
example : GaloisConnection (fun (m : SqFreeMonomial X K) ↦ m.supp) (fun (m : SqFreeMonomial X K) ↦ m.toPoly) := by sorry
example : GaloisConnection (fun A ↦ monomial (s A) (1 : K)) (fun (A : Finset X) ↦ A) := by sorry
-/





end ProjectThree
