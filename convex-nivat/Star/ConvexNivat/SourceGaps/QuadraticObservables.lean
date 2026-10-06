import ConvexNivat.AffineDimensionConsumer
import ConvexNivat.Geometry.Basic
import ConvexNivat.Geometry.ZonotopeBasic
import ConvexNivat.StarWitness
import ConvexNivat.OperatorWitness

/-!
Source-facing results for §7: actual quadratic observables, their classes
modulo the actual affine-observable space, and the dimension join.
Source: source.txt lines 1018–1060.
-/

namespace ConvexNivat

open scoped BigOperators Pointwise

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The actual source indexing set R_Z(S), as a subtype of lattice sites. -/
abbrev SpectralErosionSite {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (S : Finset Lattice) :=
  {r : Lattice // r ∈ erosion (spectralZonotope star periods).carrier S}

/-- Source Φ_r(γ)=w(γ(r+q))w(γ(r+q+d)). Both arguments belong to the
actual finite window by Lemma 7.1, and γ is an actual occurring pattern. -/
def quadraticObservable {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (r : SpectralErosionSite star periods S) : OccurringPattern star S → ℚ :=
  fun γ =>
    (w (γ.val ⟨r.val + q, (lemma7_1 (spectralZonotope star periods)
      hS hq hqd r.property).1⟩) : ℚ) *
    (w (γ.val ⟨r.val + q + d, (lemma7_1 (spectralZonotope star periods)
      hS hq hqd r.property).2⟩) : ℚ)

/-- The actual class of Φ_r in {L→ℚ}/U_S, using Mathlib's quotient linear map. -/
def quadraticObservableClass {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (r : SpectralErosionSite star periods S) :
    (OccurringPattern star S → ℚ) ⧸ affineObservableSpace star w S :=
  (affineObservableSpace star w S).mkQ
    (quadraticObservable star periods w S hS q d hq hqd r)

/-- The substitution identity preceding Lemma 7.2. This records the exact
translation convention and rational values of the source observable. -/
theorem quadraticObservable_on_translate {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (r : SpectralErosionSite star periods S) (u : Lattice) :
    quadraticObservable star periods w S hS q d hq hqd r
      ⟨pattern star.configuration S u, Set.mem_range_self u⟩ =
      (w (star.configuration (u + (r.val + q))) : ℚ) *
        (w (star.configuration (u + (r.val + q + d))) : ℚ) := by
  rfl

/-- Lemma 7.2. The hypotheses retain Case B and the actual nonzero quadratic
witness J=D(η(·)η(·+d)); its finite support is produced by Lemma 1.1.
Independence is in the genuine quotient by U_S, for every actual erosion site. -/
theorem lemma7_2 {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice) (hd : d ≠ 0)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (hJ : quadraticWitness (starDifferencePolynomial star periods)
      (encodedStar star w) d ≠ 0) :
    LinearIndependent ℚ
      (quadraticObservableClass star periods w S hS q d hq hqd) := by
  classical
  have : NeZero p := ⟨star.prime.ne_zero⟩
  let D := starDifferencePolynomial star periods
  let η := encodedStar star w
  let J := quadraticWitness D η d
  let P : StarPeriodData star :=
    { multiplier := periods.multiplier
      multiplier_pos := periods.positive
      component_period := periods.component_period
      all_tail_periods := fun i j => ⟨periods.left_period i j, periods.right_period i j⟩ }
  have hJfin : ScalarHasFiniteSupport J :=
    quadraticWitness_finite_support star P w d
  have hDη : applyLaurent D η = 0 :=
    indicators_killed_encoding_killed star.configuration D hB (fun a => (w a : ℂ))
  let pull : (OccurringPattern star S → ℚ) →ₗ[ℚ] ScalarField :=
    { toFun := fun ψ u => (ψ ⟨pattern star.configuration S u, Set.mem_range_self u⟩ : ℂ)
      map_add' := by intro ψ χ; ext u; simp
      map_smul' := by intro c ψ; ext u; simp [Algebra.smul_def] }
  have hkill : ∀ ψ ∈ affineObservableSpace star w S, applyLaurent D (pull ψ) = 0 := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      rcases hx with hx | ⟨s, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hx
        have hp : pull (fun _ => 1) = (fun _ => (1 : ℂ)) := by ext u; simp [pull]
        rw [hp]
        exact differenceProduct_kills_constant Finset.univ
          ⟨⟨0, by have := star.two_le; omega⟩, Finset.mem_univ _⟩ periods.vector 1
      · change applyLaurent D (fun u => η (u + s.val)) = 0
        rw [applyLaurent_translate, hDη]
        rfl
    | zero => ext u; simp [pull, applyLaurent]
    | add x y hx hy ihx ihy =>
      rw [map_add, applyLaurent_add_field, ihx, ihy, add_zero]
    | smul c x hx ih =>
      rw [map_smul]
      change applyLaurent D ((c : ℂ) • pull x) = 0
      rw [applyLaurent_smul_field, ih, smul_zero]
  apply linearIndependent_iff'.mpr
  intro t c hrel r hr
  let Φ := quadraticObservable star periods w S hS q d hq hqd
  have hmem : (∑ x ∈ t, c x • Φ x) ∈ affineObservableSpace star w S := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (affineObservableSpace star w S).mkQ (∑ x ∈ t, c x • Φ x) = 0
    simpa only [map_sum, map_smul, Φ, quadraticObservableClass] using hrel
  have hk := hkill _ hmem
  have hpull : pull (∑ x ∈ t, c x • Φ x) =
      ∑ x ∈ t, (c x : ℂ) • (fun u => η (u + (x.val + q)) * η (u + (x.val + q) + d)) := by
    ext u
    simp [pull, Φ, quadraticObservable, pattern, η, encodedStar, Finset.sum_apply,
      Rat.cast_mul, Algebra.smul_def, add_assoc]
  have hsum (s : Finset (SpectralErosionSite star periods S))
      (f : SpectralErosionSite star periods S → ScalarField) :
      applyLaurent D (∑ x ∈ s, f x) = ∑ x ∈ s, applyLaurent D (f x) := by
    induction s using Finset.induction_on with
    | empty => ext u; simp [applyLaurent]
    | @insert x s hx ih =>
      rw [Finset.sum_insert hx, applyLaurent_add_field, ih, Finset.sum_insert hx]
  rw [hpull, hsum] at hk
  have hshift (x : SpectralErosionSite star periods S) :
      applyLaurent D ((c x : ℂ) •
        (fun u => η (u + (x.val + q)) * η (u + (x.val + q) + d))) =
      (c x : ℂ) • (fun u => J (u + (x.val + q))) := by
    rw [applyLaurent_smul_field]
    change (c x : ℂ) • applyLaurent D
      (fun u => (fun z => η z * η (z + d)) (u + (x.val + q))) = _
    have ht := applyLaurent_translate D (fun z => η z * η (z + d)) (x.val + q)
    rw [ht]
    rfl
  simp_rw [hshift] at hk
  let f : LaurentPolynomial := ∑ x ∈ t, AddMonoidAlgebra.single (x.val + q) (c x : ℂ)
  have hfJ : applyLaurent f J = 0 := by
    have hpoly (s : Finset (SpectralErosionSite star periods S)) :
        applyLaurent (∑ x ∈ s, AddMonoidAlgebra.single (x.val + q) (c x : ℂ)) J =
        ∑ x ∈ s, (c x : ℂ) • (fun u => J (u + (x.val + q))) := by
      induction s using Finset.induction_on with
      | empty => simp [applyLaurent_zero]
      | @insert x s hx ih =>
        rw [Finset.sum_insert hx, applyLaurent_add, ih, Finset.sum_insert hx]
        ext u
        simp [applyLaurent_single, smul_eq_mul]
    exact (hpoly t).trans hk
  have hfzero : f = 0 := by
    by_contra hf
    exact lemma_1_2 J hJfin hJ f hf hfJ
  have hc : (c r : ℂ) = 0 := by
    have he := congrArg (fun F : LaurentPolynomial => F.coeff (r.val + q)) hfzero
    simp only [f, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
      Finset.sum_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
    rw [Finset.sum_eq_single r] at he
    · simpa [AddMonoidAlgebra.coeff_single] using he
    · intro x hx hxr
      have hne : x.val + q ≠ r.val + q := fun h => hxr (Subtype.ext (add_right_cancel h))
      simp [AddMonoidAlgebra.coeff_single, hne]
    · intro hnot
      exact (hnot hr).elim
  exact_mod_cast hc

/-- Source V=U_S+span_Q{Φ_r : r∈R_Z(S)}, with the genuine pointwise function space. -/
def quadraticObservableSpace {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (w : ZMod p → ℤ)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier) :
    Submodule ℚ (OccurringPattern star S → ℚ) :=
  affineObservableSpace star w S ⊔ Submodule.span ℚ
    (Set.range (quadraticObservable star periods w S hS q d hq hqd))

/-- The exact dimension equality in the proof of Theorem 7.3, produced from
the actual Case-B witness rather than assumed as a certificate. -/
theorem quadraticObservableSpace_finrank {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice) (hd : d ≠ 0)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (hJ : quadraticWitness (starDifferencePolynomial star periods)
      (encodedStar star w) d ≠ 0) :
    Module.finrank ℚ (quadraticObservableSpace star periods w S hS q d hq hqd) =
      Module.finrank ℚ (affineObservableSpace star w S) +
        (erosion (spectralZonotope star periods).carrier S).ncard := by
  classical
  have : NeZero p := ⟨star.prime.ne_zero⟩
  let : Fintype (OccurringPattern star S) := Fintype.ofFinite _
  let : Fintype (SpectralErosionSite star periods S) :=
    (IntegralZonotope.erosion_finite (spectralZonotope star periods) hS).fintype
  let U := affineObservableSpace star w S
  let Φ := quadraticObservable star periods w S hS q d hq hqd
  let W := Submodule.span ℚ (Set.range Φ)
  have hli : LinearIndependent ℚ (U.mkQ ∘ Φ) :=
    lemma7_2 star periods hB w hw S hS q d hd hq hqd hJ
  have hΦ : LinearIndependent ℚ Φ := hli.of_comp U.mkQ
  have hdis : Disjoint U W := by
    rw [disjoint_iff_inf_le]
    intro x hx
    change x = 0
    obtain ⟨c, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx.2
    have hz : ∑ r, c r • (U.mkQ ∘ Φ) r = 0 := by
      simp only [Function.comp_apply, ← map_smul]
      rw [← map_sum]
      rw [he]
      exact (Submodule.Quotient.mk_eq_zero U).mpr hx.1
    have hc := Fintype.linearIndependent_iff.mp hli c hz
    rw [← he]
    simp [hc]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hinf : U ⊓ W = ⊥ := hdis.eq_bot
  rw [hinf] at hdim
  simp only [finrank_bot, add_zero] at hdim
  have hW : Module.finrank ℚ W = Fintype.card (SpectralErosionSite star periods S) :=
    finrank_span_eq_card hΦ
  rw [hW] at hdim
  have hcard : Fintype.card (SpectralErosionSite star periods S) =
      (erosion (spectralZonotope star periods).carrier S).ncard :=
    Set.fintypeCard_eq_ncard _
  rw [hcard] at hdim
  change Module.finrank ℚ ↥(U ⊔ W) = Module.finrank ℚ U +
    (erosion (spectralZonotope star periods).carrier S).ncard
  exact hdim

/-- Final dimension join in Theorem 7.3. The same erosion cardinal is subtracted
in Lemma 2.5 and added by Lemma 7.2, giving the exact source lower bound. -/
theorem quadraticObservableSpace_dimension_join {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice) (hd : d ≠ 0)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (hJ : quadraticWitness (starDifferencePolynomial star periods)
      (encodedStar star w) d ≠ 0) :
    S.card + 1 ≤
      Module.finrank ℚ (quadraticObservableSpace star periods w S hS q d hq hqd) ∧
    Module.finrank ℚ (quadraticObservableSpace star periods w S hS q d hq hqd) ≤
      complexity star.configuration S := by
  classical
  have : NeZero p := ⟨star.prime.ne_zero⟩
  let : Fintype (OccurringPattern star S) := Fintype.ofFinite _
  constructor
  · rw [quadraticObservableSpace_finrank star periods hB w hw S hS q d hd hq hqd hJ]
    exact affine_observable_dimension_budget star periods w hw S hS
  · calc
      _ ≤ Module.finrank ℚ (OccurringPattern star S → ℚ) := Submodule.finrank_le _
      _ = complexity star.configuration S := by
        rw [Module.finrank_fintype_fun_eq_card]
        exact Set.fintypeCard_eq_ncard _

/-- The Case-B witness branch of Theorem 7.3, including the resulting actual
pattern-complexity bound. No dimension statement is assumed as a premise. -/
theorem caseB_complexity_from_quadratic_witness {p : ℕ} (star : StarData p)
    (periods : StarCommonPeriods star) (hB : InCaseB star periods)
    (w : ZMod p → ℤ) (hw : SpectrumPreservingEncoding star periods w)
    (S : Finset Lattice) (hS : LatticeConvex S) (q d : Lattice) (hd : d ≠ 0)
    (hq : q ∈ latticePoints (spectralZonotope star periods).carrier)
    (hqd : q + d ∈ latticePoints (spectralZonotope star periods).carrier)
    (hJ : quadraticWitness (starDifferencePolynomial star periods)
      (encodedStar star w) d ≠ 0) :
    S.card + 1 ≤ complexity star.configuration S := by
  obtain ⟨hlower, hupper⟩ :=
    quadraticObservableSpace_dimension_join star periods hB w hw S hS q d hd hq hqd hJ
  exact hlower.trans hupper

end
end ConvexNivat
