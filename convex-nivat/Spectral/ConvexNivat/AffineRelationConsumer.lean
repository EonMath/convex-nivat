import ConvexNivat.ExceptionalAnnihilation
import ConvexNivat.SpectralDivisibility
import ConvexNivat.SpectralNonassociation
import ConvexNivat.SpectralPrime
import ConvexNivat.OperatorAction

open scoped BigOperators Pointwise
namespace ConvexNivat
noncomputable section

private lemma product_primes_divides {ι : Type*} (s : Finset ι) (b : ι → LaurentPolynomial)
    (f : LaurentPolynomial) (hp : ∀ i ∈ s, Prime (b i))
    (hn : (s : Set ι).Pairwise (fun i j => ¬ Associated (b i) (b j)))
    (hd : ∀ i ∈ s, b i ∣ f) : (∏ i ∈ s, b i) ∣ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hpin := hp i (by simp)
      have hps : ∀ j ∈ s, Prime (b j) := fun j hj => hp j (Finset.mem_insert_of_mem hj)
      have hns : (s : Set ι).Pairwise (fun i j => ¬ Associated (b i) (b j)) :=
        hn.mono (by simp)
      have hds : ∀ j ∈ s, b j ∣ f := fun j hj => hd j (Finset.mem_insert_of_mem hj)
      obtain ⟨q, hq⟩ := ih hps hns hds
      have hnot : ¬ b i ∣ ∏ j ∈ s, b j := by
        rw [hpin.dvd_finsetProd_iff]
        rintro ⟨j, hj, hdij⟩
        apply hn (x := i) (y := j) (by simp) (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj)
        exact (hpin.dvd_prime_iff_associated (hps j hj)).mp hdij
      have hqdiv : b i ∣ q := (hpin.dvd_mul.mp (hq ▸ hd i (by simp))).resolve_left hnot
      obtain ⟨r, hr⟩ := hqdiv
      refine ⟨r, ?_⟩
      rw [Finset.prod_insert hi, hq, hr]
      ring

private lemma constant_on_orbit_closure {p : ℕ} (star : StarData p)
    (w : ZMod p → ℤ) (f : LaurentPolynomial) (c : ℂ)
    (hc : applyLaurent f (encodedStar star w) = fun _ => c)
    (χ : Configuration (ZMod p)) (hχ : χ ∈ OrbitClosure star.configuration) :
    applyLaurent f (fun z => (w (χ z) : ℂ)) = fun _ => c := by
  classical
  funext z
  obtain ⟨u, hu⟩ := hχ (f.coeff.support.image (fun q => z + q))
  have hh := congrFun hc (u + z)
  change (∑ q ∈ f.coeff.support, f.coeff q * (w (χ (z + q)) : ℂ)) = c
  change (∑ q ∈ f.coeff.support, f.coeff q *
    (w (star.configuration (u + z + q)) : ℂ)) = c at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hu (z + q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩), add_assoc]

private lemma encoded_difference_side {p : ℕ} (star : StarData p)
    (i : Fin star.m) (σ : RayOrientation) (side : TailSide) (w : ZMod p → ℤ) :
    ∃ b : ℤ, (∀ z, b < height (star.component i).direction z →
      encodedExceptionalDifference star i σ side w z = 0) ∨
      (∀ z, height (star.component i).direction z < b →
        encodedExceptionalDifference star i σ side w z = 0) := by
  cases side with
  | right =>
      refine ⟨(star.component i).upper, Or.inl ?_⟩
      intro z hz
      have he : isolatingConfiguration star i σ z = pureRayBackground star i σ .right z := by
        by_contra hne
        have hv := exceptional_difference_right_vanishes star i σ
          (isolatingConfiguration star i σ z) z hz
        simp [exceptionalDifference, colorIndicator, Ne.symm hne] at hv
      simp [encodedExceptionalDifference, he]
  | left =>
      refine ⟨(star.component i).lower, Or.inr ?_⟩
      intro z hz
      have he : isolatingConfiguration star i σ z = pureRayBackground star i σ .left z := by
        by_contra hne
        have hv := exceptional_difference_left_vanishes star i σ
          (isolatingConfiguration star i σ z) z hz
        simp [exceptionalDifference, colorIndicator, Ne.symm hne] at hv
      simp [encodedExceptionalDifference, he]

theorem affine_relation_divisible {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (hw : SpectrumPreservingEncoding star periods w)
    (f : LaurentPolynomial) (hf : f ≠ 0)
    (hconstant : ∃ c : ℂ, applyLaurent f (encodedStar star w) = fun _ => c) :
    exceptionalPolynomial star periods ∣ f := by
  classical
  obtain ⟨c, hc⟩ := hconstant
  let b (i : Fin star.m) (ζ : ℂ) : LaurentPolynomial :=
    translationMonomial (star.component i).direction - AddMonoidAlgebra.single 0 ζ
  have hnz (i : Fin star.m) (ζ : ℂ) (hζ : ζ ∈ exceptionalSpectrum star periods i) : ζ ≠ 0 :=
    Polynomial.ne_zero_of_mem_nthRootsFinset (by simp) (Finset.mem_filter.mp hζ).1
  have hprime (i : Fin star.m) (ζ : ℂ) (hζ : ζ ∈ exceptionalSpectrum star periods i) :
      Prime (b i ζ) := primitive_translation_binomial_prime _ (star.component i).primitive _
        (hnz i ζ hζ)
  have hdvd (i : Fin star.m) (ζ : ℂ) (hζ : ζ ∈ exceptionalSpectrum star periods i) :
      b i ζ ∣ f := by
    obtain ⟨σ, side, hocc⟩ := hw.2 i ζ hζ
    have hi := constant_on_orbit_closure star w f c hc _
      (isolating_configuration_mem_orbit_closure star periods i σ)
    have hg := constant_on_orbit_closure star w f c hc _
      (pure_ray_background_mem_orbit_closure star periods i σ side)
    have hann : applyLaurent f (encodedExceptionalDifference star i σ side w) = 0 := by
      change applyLaurent f ((fun z => (w (isolatingConfiguration star i σ z) : ℂ)) -
        (fun z => (w (pureRayBackground star i σ side z) : ℂ))) = 0
      rw [sub_eq_add_neg, ← neg_one_smul ℂ
        (fun z => (w (pureRayBackground star i σ side z) : ℂ)),
        applyLaurent_add_field, applyLaurent_smul_field, hi, hg]
      funext z
      simp
    have hperiod : HasPeriod (encodedExceptionalDifference star i σ side w) (periods.vector i) := by
      intro z
      simp only [encodedExceptionalDifference,
        isolating_configuration_period star periods i σ z,
        pure_ray_background_common_period star periods i i σ side z]
    exact one_sided_spectral_divisibility _ (star.component i).primitive _ (periods.positive i)
      ζ ((Polynomial.mem_nthRootsFinset (periods.positive i) 1).mp (Finset.mem_filter.mp hζ).1)
      _ hperiod (encoded_difference_side star i σ side w) hocc f hann
  let s : Finset (Σ _ : Fin star.m, ℂ) := Finset.univ.sigma (exceptionalSpectrum star periods)
  have hs (q : Σ _ : Fin star.m, ℂ) : q ∈ s ↔ q.2 ∈ exceptionalSpectrum star periods q.1 := by
    simp [s]
  have hprod : (∏ q ∈ s, b q.1 q.2) ∣ f := by
    apply product_primes_divides
    · intro q hq
      exact hprime q.1 q.2 ((hs q).mp hq)
    · intro q hq r hr hqr
      by_cases he : q.1 = r.1
      · have hroot : q.2 ≠ r.2 := by
          intro h
          apply hqr
          cases q
          cases r
          simp_all
        simpa [b, he] using distinct_root_translation_binomials_not_associated _
          (star.component r.1).primitive q.2 r.2 (hnz q.1 q.2 ((hs q).mp hq))
          (hnz r.1 r.2 ((hs r).mp hr)) hroot
      · exact nonparallel_translation_binomials_not_associated _ _
          (star.pairwise_nonparallel q.1 r.1 he) _ _ (hnz q.1 q.2 ((hs q).mp hq))
          (hnz r.1 r.2 ((hs r).mp hr))
    · intro q hq
      exact hdvd q.1 q.2 ((hs q).mp hq)
  simpa [s, exceptionalPolynomial, exceptionalDirectionPolynomial, Finset.prod_sigma, b] using hprod

end
end ConvexNivat
