import ConvexNivat.ReductionDefinitions
import Nivat.Algebra.ProductDifferences
import Nivat.Core.BoundedDifferences

namespace ConvexNivat
open scoped BigOperators
open Nivat.Algebra

/-- Source 8.4(b), annihilator-factor selection. Same [11] provenance.
`mixedDifference` is the actual ∏(T^{hᵢ}−1) action, retaining subset multiplicity. -/
theorem external8_4b_factors_obligation (ξ : Configuration ℤ) (A : Finset ℤ)
    (hA : ∀ z, ξ z ∈ A) (hann : HasNontrivialIntegerAnnihilator ξ) :
    ∃ m : ℕ, ∃ h : Fin m → Lattice,
      (∀ i, h i ≠ 0) ∧ Pairwise (fun i j => Nonparallel (h i) (h j)) ∧
      ∀ z, mixedDifference h Finset.univ ξ z = 0 := by
  classical
  by_cases hzero : ξ = 0
  · refine ⟨0, Fin.elim0, by simp, by simp [Pairwise], ?_⟩
    intro z
    simp [mixedDifference, hzero]
  have hfinite : Nivat.FiniteRange ξ :=
    A.finite_toSet.subset (by rintro _ ⟨z, rfl⟩; exact hA z)
  obtain ⟨f, hfne, hf⟩ := hann
  let F : Nivat.Algebra.IntegerLaurent := AddMonoidAlgebra.ofCoeff f
  have hFne : F ≠ 0 := by
    intro he
    exact hfne (congrArg AddMonoidAlgebra.coeff he)
  have hF : coefficientAct F ξ = 0 := by
    funext z
    rw [coefficientAct_apply]
    exact hf z
  obtain ⟨ks, _, hknz, hka⟩ := exists_integer_product_differences hfinite hzero hFne hF
  let c : Nivat.Configuration ℚ := (Int.castRingHom ℚ) ∘ ξ
  have hc : Nivat.FiniteRange c := hfinite.map (Int.castRingHom ℚ)
  have hkaq : act ((ks.map (fun h => monomial h - 1)).prod) c = 0 := by
    have he := coefficientAct_map (Int.castRingHom ℚ)
      ((ks.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) ξ
    rw [hka] at he
    funext z
    simpa [coefficientAct_rat, map_list_prod, List.map_map, monomial, c,
      Function.comp_def] using congrFun he z
  let P (n : ℕ) : Prop := ∃ hs : List Lattice, hs.length = n ∧
    (∀ h ∈ hs, h ≠ 0) ∧ act ((hs.map (fun h => monomial h - 1)).prod) c = 0
  have hex : ∃ n, P n := ⟨ks.length, ks, rfl, hknz, hkaq⟩
  obtain ⟨hs, hlen, hsnz, hsa⟩ := Nat.find_spec hex
  have hmin (ls : List Lattice) (hlnz : ∀ h ∈ ls, h ≠ 0)
      (hla : act ((ls.map (fun h => monomial h - 1)).prod) c = 0) :
      hs.length ≤ ls.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨ls, rfl, hlnz, hla⟩
  have hpairs : hs.Pairwise Nonparallel := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro a b hab
    by_contra hpar
    have habpar : a.1 * b.2 = a.2 * b.1 := by
      simpa [Nonparallel, det, sub_eq_zero] using hpar
    obtain ⟨ls, hperm⟩ := hab.exists_perm_append
    have hperm' : hs.Perm (a :: b :: ls) := hperm
    have ha : a ≠ 0 := hsnz a (hperm'.mem_iff.mpr (by simp))
    have hb : b ≠ 0 := hsnz b (hperm'.mem_iff.mpr (by simp))
    let g : Nivat.Laurent := (ls.map (fun h => monomial h - 1)).prod
    have hmix : Nivat.difference a (Nivat.difference b (act g c)) = 0 := by
      have he := hsa
      rw [(hperm'.map (fun h => monomial h - 1)).prod_eq] at he
      simpa [List.map_cons, List.prod_cons, act_mul, act_difference, g] using he
    obtain ⟨q, hq, hpq⟩ := Nivat.periodic_of_parallel_mixed_difference
      (act g c) (finiteRange_act g hc) a b ha hb habpar hmix
    have hshort : hs.length ≤ (q :: ls).length := hmin (q :: ls)
      (by intro h hh; rcases List.mem_cons.mp hh with rfl | hh
          · exact hq
          · exact hsnz h (hperm'.mem_iff.mpr (by simp [hh])))
      (by simpa [List.map_cons, List.prod_cons, act_mul, act_difference, g] using
        (Nivat.difference_eq_zero_iff q (act g c)).mpr hpq)
    have hl := hperm'.length_eq
    simp only [List.length_cons] at hl hshort
    omega
  let h : Fin hs.length → Lattice := hs.get
  refine ⟨hs.length, h, fun i => hsnz _ (List.get_mem hs i), ?_, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact List.pairwise_iff_get.mp hpairs i j hlt
    · have he := List.pairwise_iff_get.mp hpairs j i hgt
      dsimp [Nonparallel, det, h] at he ⊢
      intro hz
      apply he
      nlinarith
  · intro z
    have hprod : act (∏ i, (monomial (h i) - 1)) c = 0 := by
      rw [← List.prod_ofFn, List.ofFn_comp' h (fun u => monomial u - 1)]
      change act ((List.ofFn hs.get).map (fun u => monomial u - 1)).prod c = 0
      rw [List.ofFn_get]
      exact hsa
    have hexpand : act (∏ i, (monomial (h i) - 1)) c z =
        mixedDifference h Finset.univ c z := by
      rw [← coefficientAct_rat]
      simp_rw [sub_eq_add_neg]
      rw [Finset.prod_add, coefficientAct_finset_sum]
      simp only [Finset.sum_apply, mixedDifference]
      apply Finset.sum_congr rfl
      intro C hC
      have hCI : C ⊆ Finset.univ := Finset.mem_powerset.mp hC
      have hprod : (∏ i ∈ C, monomial (h i)) = monomial (∑ i ∈ C, h i) := by
        simp [monomial, AddMonoidAlgebra.prod_single]
      rw [hprod, Finset.prod_const, Finset.card_sdiff_of_subset hCI]
      have hneg (n : ℕ) : (-1 : Nivat.Laurent) ^ n =
          AddMonoidAlgebra.single 0 ((-1 : ℚ) ^ n) := by
        change (-(AddMonoidAlgebra.single 0 (1 : ℚ))) ^ n = _
        rw [← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.single_pow, nsmul_zero]
      rw [hneg]
      simp [monomial, coefficientAct_single, Nivat.shift]
    have he : mixedDifference h Finset.univ c z = 0 := by
      rw [← hexpand, hprod]
      rfl
    have hcast : mixedDifference h Finset.univ c z =
        (mixedDifference h Finset.univ ξ z : ℤ) := by
      simp [mixedDifference, c, Int.cast_sum, Int.cast_mul, Int.cast_pow]
    exact Int.cast_eq_zero.mp (hcast.symm.trans he)

end ConvexNivat
