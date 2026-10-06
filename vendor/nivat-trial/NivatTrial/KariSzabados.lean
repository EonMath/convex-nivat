import NivatTrial.BinomialDirections
import NivatTrial.IntegerAnnihilator
import NivatTrial.IntegerDecomposition

/-!
# The integer periodic decomposition from low pattern complexity

The constructive route is: a low-complexity finite-alphabet field has a
nonzero integer Laurent annihilator; arithmetic progression dilations give a
Vandermonde determinant annihilator; its factors are translation differences;
parallel factors collapse on finite-range integer fields; independent factors
then yield an integral periodic decomposition.
-/

namespace NivatTrial.KariSzabados

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.OneSidedRecurrence
open NivatTrial.IntegerDecomposition NivatTrial.BinomialDirections
open NivatTrial.LaurentAction NivatTrial.IntegerAnnihilator

open scoped Classical

noncomputable section

theorem decomposition_of_independent_list (ks : List Lattice)
    (hpair : ks.Pairwise (fun h k => det h k ≠ 0))
    (hnonzero : ∀ k ∈ ks, k ≠ 0)
    (x : Lattice → ℤ) (hann : iteratedIncrement ks x = 0) :
    ∃ (n : ℕ) (h : Fin n → Lattice) (F : Fin n → Lattice → ℤ),
      (∀ i, h i ≠ 0) ∧
      (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) ∧
      (∀ i, IsPeriod (F i) (h i)) ∧ (∑ i, F i) = x := by
  let n := ks.length
  let h : Fin n → Lattice := fun i => ks[i.val]
  have hFn : List.ofFn h = ks := by
    simpa only [h] using (List.ofFn_getElem (xs := ks))
  have hnonzero' : ∀ i, h i ≠ 0 := by
    intro i
    exact hnonzero (h i) (List.getElem_mem i.isLt)
  have hpair' : ∀ i j, i ≠ j → det (h i) (h j) ≠ 0 := by
    intro i j hij
    have hp : (List.ofFn h).Pairwise (fun a b => det a b ≠ 0) := by
      rwa [hFn]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact List.pairwise_ofFn.mp hp hlt
    · have ht := List.pairwise_ofFn.mp hp hgt
      rw [det_swap]
      exact neg_ne_zero.mpr ht
  have hindexPerm : (Finset.univ.toList : List (Fin n)).Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList Finset.univ)
      (List.nodup_finRange n)).mpr (by intro i; simp)
  have hfinRange : (List.finRange n).map h = ks := by
    simpa [List.finRange, List.map_ofFn, Function.comp_def] using hFn
  have hperm : (Finset.univ.toList.map h).Perm ks := by
    simpa only [hfinRange] using hindexPerm.map h
  have hann' : iteratedIncrement (Finset.univ.toList.map h) x = 0 := by
    rw [iteratedIncrement_perm hperm x]
    exact hann
  obtain ⟨F, hperiod, hsum⟩ :=
    IntegerDecomposition.product_decomposition n h hnonzero' hpair' x hann'
  exact ⟨n, h, F, hnonzero', hpair', hperiod, hsum⟩

theorem decomposition_of_integer_annihilator (x : Lattice → ℤ)
    (hx : (Set.range x).Finite)
    (f : RingLaurent ℤ) (hf : f ≠ 0) (hann : act f x = 0) :
    ∃ (n : ℕ) (h : Fin n → Lattice) (F : Fin n → Lattice → ℤ),
      (∀ i, h i ≠ 0) ∧
      (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) ∧
      (∀ i, IsPeriod (F i) (h i)) ∧ (∑ i, F i) = x := by
  obtain ⟨ks, hpair, hnonzero, hks⟩ :=
    independent_difference_annihilator f x hf hx hann
  exact decomposition_of_independent_list ks hpair hnonzero x hks

/-- Kari--Szabados's low-complexity periodic decomposition, specialized to
the positive integer coding of a finite alphabet. -/
theorem low_complexity_decomposition (M : ℕ) (θ : Lattice → Fin M)
    (S : Finset Lattice) (_hS : S.Nonempty)
    (hlow : patternComplexity θ S ≤ S.card) :
    ∃ (n : ℕ) (h : Fin n → Lattice) (F : Fin n → Lattice → ℤ),
      (∀ i, h i ≠ 0) ∧
      (∀ i j, i ≠ j → det (h i) (h j) ≠ 0) ∧
      (∀ i, IsPeriod (F i) (h i)) ∧
      (∑ i, F i) = fun z => ((θ z).val : ℤ) + 1 := by
  let w : Fin M → ℤ := fun a => (a.val : ℤ) + 1
  let x : Lattice → ℤ := fun z => w (θ z)
  have hx : (Set.range x).Finite := by
    apply (Set.finite_range w).subset
    rintro y ⟨z, rfl⟩
    exact ⟨θ z, rfl⟩
  obtain ⟨f, hf, hann⟩ := exists_integer_annihilator θ S w hlow
  obtain ⟨n, h, F, hnonzero, hpair, hperiod, hsum⟩ :=
    decomposition_of_integer_annihilator x hx f hf hann
  exact ⟨n, h, F, hnonzero, hpair, hperiod, hsum⟩

end

end NivatTrial.KariSzabados
