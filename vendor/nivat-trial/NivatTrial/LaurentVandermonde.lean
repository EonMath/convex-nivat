import NivatTrial.LaurentDilation
import NivatTrial.AnnihilatorDilation
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Vandermonde annihilator extraction

The algebraic core is valid over any commutative coefficient ring. If the
first `n` moment sums of finite families `c_j,y_j` vanish modulo an ideal,
the Vandermonde determinant times every `c_j` lies in that ideal. The result
is derived by multiplying the moment matrix by its adjugate, without using a
Nullstellensatz or assuming the quotient is a domain.
-/

namespace NivatTrial.LaurentVandermonde

open NivatTrial.LaurentAction NivatTrial.LaurentDilation

open scoped Classical

noncomputable section

theorem det_mul_coeff_mem_ideal {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (y c : Fin n → R)
    (hmoment : ∀ i : Fin n, (∑ j : Fin n, c j * (y j) ^ (i : ℕ)) ∈ I)
    (j : Fin n) :
    (Matrix.vandermonde y).det * c j ∈ I := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  let v : Fin n → R ⧸ I := fun k => q (y k)
  let a : Fin n → R ⧸ I := fun k => q (c k)
  let V : Matrix (Fin n) (Fin n) (R ⧸ I) := (Matrix.vandermonde v).transpose
  have hrow (i : Fin n) : ∑ k : Fin n, a k * (v k) ^ (i : ℕ) = 0 := by
    have hi : q (∑ k : Fin n, c k * (y k) ^ (i : ℕ)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hmoment i)
    simpa only [map_sum, map_mul, map_pow, a, v] using hi
  have hvec : V.mulVec a = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum]
    change (∑ k : Fin n, V i k * a k) = 0
    calc
      (∑ k : Fin n, V i k * a k) =
          ∑ k : Fin n, a k * (v k) ^ (i : ℕ) := by
            apply Finset.sum_congr rfl
            intro k _
            simp [V, Matrix.vandermonde, mul_comm]
      _ = 0 := hrow i
  have hdet : (Matrix.vandermonde v).det * a j = 0 := by
    have hadj : V.adjugate.mulVec (V.mulVec a) = 0 := by
      rw [hvec, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hadj
    simpa only [Pi.smul_apply, smul_eq_mul, V, Matrix.det_transpose,
      Pi.zero_apply] using congrFun hadj j
  have hmatrix : q.mapMatrix (Matrix.vandermonde y) = Matrix.vandermonde v := by
    ext i j
    simp [Matrix.vandermonde, v]
  have hmap : q ((Matrix.vandermonde y).det * c j) = 0 := by
    rw [map_mul, q.map_det, hmatrix]
    exact hdet
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmap

/-- The ideal statement specialized to a Laurent annihilator. A nonzero
coefficient times a monomial can be cancelled from the action because the
coefficient ring is torsion-free and lattice translation is bijective. -/
theorem det_annihilates_of_moments (n : ℕ) (v : Fin n → Lattice)
    (c : Fin n → ℤ) (r : ℕ) (x : Lattice → ℤ)
    (hmoment : ∀ i : Fin n,
      act (∑ j : Fin n,
        AddMonoidAlgebra.single (v j) (c j) *
          (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ) ^ (i : ℕ)) x = 0)
    (j : Fin n) (hc : c j ≠ 0) :
    act (Matrix.vandermonde
      (fun j : Fin n =>
        (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ))).det x = 0 := by
  let y : Fin n → RingLaurent ℤ :=
    fun j => AddMonoidAlgebra.single (r • v j) 1
  let a : Fin n → RingLaurent ℤ :=
    fun j => AddMonoidAlgebra.single (v j) (c j)
  have hI : (Matrix.vandermonde y).det * a j ∈ annihilator x :=
    det_mul_coeff_mem_ideal (annihilator x) n y a
      (fun i => hmoment i) j
  change act ((Matrix.vandermonde y).det * a j) x = 0 at hI
  rw [mul_comm, act_mul] at hI
  funext z
  have hz := congrFun hI (z - v j)
  simp only [a, act_single, Pi.zero_apply] at hz
  have hzero : c j * act (Matrix.vandermonde y).det x z = 0 := by
    simpa only [sub_add_cancel] using hz
  exact (mul_eq_zero.mp hzero).resolve_left hc

private theorem single_mul_frequency (v : Lattice) (a : ℤ) (r i : ℕ) :
    AddMonoidAlgebra.single v a *
      (AddMonoidAlgebra.single (r • v) 1 : RingLaurent ℤ) ^ i =
    AddMonoidAlgebra.single ((1 + i * r) • v) a := by
  simp only [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
    one_pow, mul_one]
  congr 1
  simp only [add_smul, one_smul, smul_smul]

def sparsePolynomial (n : ℕ) (v : Fin n → Lattice) (c : Fin n → ℤ) :
    RingLaurent ℤ :=
  ∑ j : Fin n, AddMonoidAlgebra.single (v j) (c j)

theorem dilate_sparsePolynomial (n : ℕ) (v : Fin n → Lattice)
    (c : Fin n → ℤ) (r i : ℕ) :
    dilate (1 + i * r) (sparsePolynomial n v c) =
      ∑ j : Fin n, AddMonoidAlgebra.single (v j) (c j) *
        (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ) ^ i := by
  simp only [sparsePolynomial, map_sum, dilate_single]
  apply Finset.sum_congr rfl
  intro j _
  exact (single_mul_frequency (v j) (c j) r i).symm

theorem det_annihilates_of_dilation_progression (n : ℕ)
    (v : Fin n → Lattice) (c : Fin n → ℤ) (r : ℕ)
    (x : Lattice → ℤ)
    (hprogression : ∀ i : ℕ,
      act (dilate (1 + i * r) (sparsePolynomial n v c)) x = 0)
    (j : Fin n) (hc : c j ≠ 0) :
    act (Matrix.vandermonde
      (fun j : Fin n =>
        (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ))).det x = 0 := by
  apply det_annihilates_of_moments n v c r x (fun i => ?_) j hc
  rw [← dilate_sparsePolynomial]
  exact hprogression i

/-- Enumerate exactly the nonzero monomials of a Laurent polynomial. The
coefficients are nonzero and the exponents are distinct by construction. -/
theorem support_coordinates (f : RingLaurent ℤ) :
    ∃ (n : ℕ) (v : Fin n → Lattice) (c : Fin n → ℤ),
      Function.Injective v ∧ (∀ j, c j ≠ 0) ∧
      f = sparsePolynomial n v c ∧ (f ≠ 0 → 0 < n) := by
  let S : Finset Lattice := f.coeff.support
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let v : Fin (Fintype.card S) → Lattice := fun j => (e j).1
  let c : Fin (Fintype.card S) → ℤ := fun j => f.coeff (v j)
  refine ⟨Fintype.card S, v, c, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext hij
  · intro j
    exact Finsupp.mem_support_iff.mp (e j).2
  · dsimp [sparsePolynomial]
    calc
      f = f.coeff.sum AddMonoidAlgebra.single := (AddMonoidAlgebra.sum_coeff_single f).symm
      _ = ∑ s ∈ S, AddMonoidAlgebra.single s (f.coeff s) := rfl
      _ = ∑ s : S, AddMonoidAlgebra.single (s : Lattice) (f.coeff s) :=
        (Finset.sum_attach S (fun s => AddMonoidAlgebra.single s (f.coeff s))).symm
      _ = ∑ j : Fin (Fintype.card S),
          AddMonoidAlgebra.single (v j) (c j) := by
        exact (Fintype.sum_equiv e
          (fun j => AddMonoidAlgebra.single (v j) (c j))
          (fun s : S => AddMonoidAlgebra.single (s : Lattice) (f.coeff s))
          (fun _ => rfl)).symm
  · intro hf
    have hcoeff : f.coeff ≠ 0 := fun heq => hf (AddMonoidAlgebra.coeff_eq_zero.mp heq)
    have hS : S.Nonempty := Finsupp.support_nonempty_iff.mpr hcoeff
    exact Fintype.card_pos_iff.mpr ⟨⟨hS.choose, hS.choose_spec⟩⟩

/-- A nonzero integer Laurent annihilator of a finite-range field yields a
Vandermonde determinant annihilator with distinct exponent columns. -/
theorem exists_vandermonde_annihilator (f : RingLaurent ℤ) (x : Lattice → ℤ)
    (hf : f ≠ 0) (hx : (Set.range x).Finite) (hann : act f x = 0) :
    ∃ (n : ℕ) (v : Fin n → Lattice) (r : ℕ),
      0 < n ∧ 0 < r ∧ Function.Injective v ∧
        act (Matrix.vandermonde
          (fun j : Fin n =>
            (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ))).det x = 0 := by
  obtain ⟨n, v, c, hv, hc, hrepr, hn⟩ := support_coordinates f
  obtain ⟨r, hr, hprog⟩ :=
    NivatTrial.AnnihilatorDilation.exists_dilation_progression f x hx hann
  let j : Fin n := ⟨0, hn hf⟩
  refine ⟨n, v, r, hn hf, hr, hv, ?_⟩
  apply det_annihilates_of_dilation_progression n v c r x ?_ j (hc j)
  intro i
  rw [← hrepr]
  exact hprog i

end

end NivatTrial.LaurentVandermonde
