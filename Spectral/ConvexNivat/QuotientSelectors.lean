import ConvexNivat.QuotientFoundation
import ConvexNivat.QuotientComaximal

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private theorem unit_mod_pair {R : Type*} [CommRing R] (a b c : R)
    (h : Ideal.span ({a,b,c} : Set R) = ⊤) :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({a,b} : Set R)) c) := by
  let I := Ideal.span ({a,b} : Set R)
  let q := Ideal.Quotient.mk I
  have ha : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hb : q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.map q) h
  simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, ha, hb,
    Ideal.span_insert_zero,
    Ideal.map_top] at hm
  exact Ideal.span_singleton_eq_top.mp hm

theorem spectral_pair_selector_unit {m : ℕ} (family : FiniteSpectralFamily m)
    (i j : Fin m) (hij : i ≠ j) :
    IsUnit (Ideal.Quotient.mk (family.pairIdeal i j) (spectralPairSelector family i j)) := by
  classical
  let a := family.secondPointFactor
  let c := family.firstPointFactor
  let C := firstPointRecursionPolynomial family.polynomial
  have hC : C ∈ family.pairIdeal i j :=
    spectral_bi_ideal_le_pair family i j (Ideal.subset_span (by simp [biRecursionIdeal, C]))
  have ha : ∀ k, k ≠ i → IsUnit (Ideal.Quotient.mk (family.pairIdeal i j) (a k)) := by
    intro k hk
    apply unit_mod_pair
    apply top_unique
    rw [← spectral_two_second_point_factors_coprime family i k (Ne.symm hk)]
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp [a])
    · exact Ideal.subset_span (by simp [a])
    · exact (show family.pairIdeal i j ≤ Ideal.span {a i,c j,a k} from
        Ideal.span_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)) hC
  have hc : ∀ l, l ≠ j → IsUnit (Ideal.Quotient.mk (family.pairIdeal i j) (c l)) := by
    intro l hl
    exact unit_mod_pair _ _ _ (spectral_two_first_point_factors_coprime family i j l (Ne.symm hl))
  unfold spectralPairSelector
  rw [map_mul, map_prod, map_prod]
  apply IsUnit.mul
  · exact (IsUnit.prod_iff.mpr (fun k hk => ha k (Finset.mem_erase.mp hk).1))
  · exact (IsUnit.prod_iff.mpr (fun l hl => hc l (Finset.mem_erase.mp hl).1))

end
end ConvexNivat
