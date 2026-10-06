import NivatTrial.LaurentVandermonde
import NivatTrial.IntegerPowerReduction
import NivatTrial.ParallelCollapse

/-!
# Directional binomials from a Laurent Vandermonde determinant

Each Vandermonde difference of monomials is a unit monomial times a pure
translation difference. This module removes the unit, then records the finite
list of nonzero directions. Parallel factors can subsequently be collected
and their multiplicities removed for a finite-range integer field.
-/

namespace NivatTrial.BinomialDirections

open NivatTrial.LaurentAction NivatTrial.LaurentVandermonde
open NivatTrial.PeriodicDifference NivatTrial.OneSidedRecurrence
open NivatTrial.ParallelCollapse

open scoped Classical

noncomputable section

def binomial (h : Lattice) : RingLaurent ℤ :=
  AddMonoidAlgebra.single h 1 - 1

def pairBinomial (n : ℕ) (v : Fin n → Lattice) (r : ℕ)
    (i j : Fin n) : RingLaurent ℤ :=
  binomial (r • (v j - v i))

def pairBinomialProduct (n : ℕ) (v : Fin n → Lattice) (r : ℕ) :
    RingLaurent ℤ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, pairBinomial n v r i j

def pairUnitProduct (n : ℕ) (v : Fin n → Lattice) (r : ℕ) :
    RingLaurent ℤ :=
  ∏ i : Fin n, ∏ _j ∈ Finset.Ioi i,
    AddMonoidAlgebra.single (r • v i) (1 : ℤ)

def pairShift (n : ℕ) (v : Fin n → Lattice) (r : ℕ) : Lattice :=
  ∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, r • v i

private theorem product_single_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → Lattice) :
    (∏ i ∈ s, (AddMonoidAlgebra.single (u i) 1 : RingLaurent ℤ)) =
      AddMonoidAlgebra.single (∑ i ∈ s, u i) 1 := by
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih]
    simp [AddMonoidAlgebra.single_mul_single]

theorem pairUnitProduct_eq_single (n : ℕ) (v : Fin n → Lattice) (r : ℕ) :
    pairUnitProduct n v r = AddMonoidAlgebra.single (pairShift n v r) 1 := by
  simp only [pairUnitProduct, pairShift]
  simp_rw [product_single_one]

theorem pair_difference_factor (n : ℕ) (v : Fin n → Lattice) (r : ℕ)
    (i j : Fin n) :
    (AddMonoidAlgebra.single (r • v j) 1 : RingLaurent ℤ) -
      AddMonoidAlgebra.single (r • v i) 1 =
    AddMonoidAlgebra.single (r • v i) 1 * pairBinomial n v r i j := by
  simp only [pairBinomial, binomial, mul_sub, mul_one]
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [one_mul]
  congr 1
  simp only [smul_sub]
  abel

theorem vandermonde_det_factor (n : ℕ) (v : Fin n → Lattice) (r : ℕ) :
    (Matrix.vandermonde (fun i : Fin n =>
      (AddMonoidAlgebra.single (r • v i) 1 : RingLaurent ℤ))).det =
      pairUnitProduct n v r * pairBinomialProduct n v r := by
  rw [Matrix.det_vandermonde]
  simp_rw [pair_difference_factor n v r]
  simp only [Finset.prod_mul_distrib, pairUnitProduct, pairBinomialProduct]

theorem binomial_product_annihilates (n : ℕ) (v : Fin n → Lattice)
    (r : ℕ) (x : Lattice → ℤ)
    (hdet : act (Matrix.vandermonde (fun i : Fin n =>
      (AddMonoidAlgebra.single (r • v i) 1 : RingLaurent ℤ))).det x = 0) :
    act (pairBinomialProduct n v r) x = 0 := by
  let u := pairShift n v r
  have hmul : act (AddMonoidAlgebra.single u 1 * pairBinomialProduct n v r) x = 0 := by
    rw [← pairUnitProduct_eq_single]
    rw [← vandermonde_det_factor]
    exact hdet
  rw [act_mul] at hmul
  funext z
  have hz := congrFun hmul (z - u)
  simpa only [act_single, one_mul, sub_add_cancel, Pi.zero_apply] using hz

theorem exists_binomial_product_annihilator (f : RingLaurent ℤ) (x : Lattice → ℤ)
    (hf : f ≠ 0) (hx : (Set.range x).Finite) (hann : act f x = 0) :
    ∃ (n : ℕ) (v : Fin n → Lattice) (r : ℕ),
      0 < n ∧ 0 < r ∧ Function.Injective v ∧
        act (pairBinomialProduct n v r) x = 0 := by
  obtain ⟨n, v, r, hn, hr, hv, hdet⟩ :=
    exists_vandermonde_annihilator f x hf hx hann
  exact ⟨n, v, r, hn, hr, hv, binomial_product_annihilates n v r x hdet⟩

theorem act_binomial (h : Lattice) (x : Lattice → ℤ) :
    act (binomial h) x = increment x h := by
  funext z
  simp [binomial, act_sub, act_single, increment]

def binomialListProduct (hs : List Lattice) : RingLaurent ℤ :=
  (hs.map binomial).prod

theorem act_binomialListProduct (hs : List Lattice) (x : Lattice → ℤ) :
    act (binomialListProduct hs) x = iteratedIncrement hs x := by
  induction hs with
  | nil => simp [binomialListProduct]
  | cons h hs ih =>
    simp only [binomialListProduct, List.map_cons, List.prod_cons, act_mul,
      iteratedIncrement_cons]
    change act (binomial h) (act (binomialListProduct hs) x) =
      increment (iteratedIncrement hs x) h
    rw [ih, act_binomial]

def pairDirectionList (n : ℕ) (v : Fin n → Lattice) (r : ℕ) : List Lattice :=
  (Finset.univ.toList : List (Fin n)).flatMap fun i =>
    ((Finset.Ioi i).toList.map fun j => r • (v j - v i))

private theorem list_prod_toList {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → RingLaurent ℤ) :
    (s.toList.map F).prod = ∏ i ∈ s, F i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi]

private theorem list_prod_flatMap {ι κ : Type*} (s : List ι)
    (F : ι → List κ) (g : κ → RingLaurent ℤ) :
    ((s.flatMap F).map g).prod =
      (s.map (fun i => ((F i).map g).prod)).prod := by
  induction s with
  | nil => simp
  | cons i s ih => simp [ih, List.prod_append]

theorem pairBinomialProduct_eq_listProduct (n : ℕ) (v : Fin n → Lattice)
    (r : ℕ) :
    pairBinomialProduct n v r = binomialListProduct (pairDirectionList n v r) := by
  unfold pairBinomialProduct binomialListProduct pairDirectionList
  rw [list_prod_flatMap]
  simp only [List.map_map, Function.comp_def]
  simp_rw [list_prod_toList]
  rfl

theorem pairDirectionList_nonzero (n : ℕ) (v : Fin n → Lattice)
    (hv : Function.Injective v) (r : ℕ) (hr : 0 < r) :
    ∀ h ∈ pairDirectionList n v r, h ≠ 0 := by
  intro h hh
  rcases List.mem_flatMap.mp hh with ⟨i, _, hi⟩
  rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp (Finset.mem_toList.mp hj))
  have hdiff : v j - v i ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hij (hv heq.symm))
  exact fun heq => hdiff ((nsmul_eq_zero_iff_right (Nat.ne_of_gt hr)).mp heq)

theorem independent_difference_annihilator (f : RingLaurent ℤ)
    (x : Lattice → ℤ) (hf : f ≠ 0)
    (hx : (Set.range x).Finite) (hann : act f x = 0) :
    ∃ ks : List Lattice,
      ks.Pairwise (fun h k => NivatTrial.Geometry.det h k ≠ 0) ∧
      (∀ k ∈ ks, k ≠ 0) ∧ iteratedIncrement ks x = 0 := by
  obtain ⟨n, v, r, _, hr, hv, hpairs⟩ :=
    exists_binomial_product_annihilator f x hf hx hann
  have hlist : iteratedIncrement (pairDirectionList n v r) x = 0 := by
    rw [← act_binomialListProduct, ← pairBinomialProduct_eq_listProduct]
    exact hpairs
  exact independent_annihilator_of_list (pairDirectionList n v r)
    (pairDirectionList_nonzero n v hv r hr) x hx hlist

end

end NivatTrial.BinomialDirections
