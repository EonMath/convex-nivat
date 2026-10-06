import NivatTrial.QuotientFactors

/-! The ideals needed in §5.2 are proved to be the whole ring by passing to a
maximal-ideal quotient field and using the explicit split roots. -/

namespace NivatTrial.QuotientIdeals

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField
open NivatTrial.QuotientFactors
open scoped Classical

noncomputable section

theorem span_eq_top_of_no_field_zero (s : Set R)
    (h : ∀ (F : Type) [Field F] [Algebra K F] (rho : R →ₐ[K] F),
      (∀ r ∈ s, rho r = 0) → False) : Ideal.span s = ⊤ := by
  by_contra hproper
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hproper
  letI : M.IsMaximal := hM
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  apply h (R ⧸ M) (Ideal.Quotient.mkₐ K M)
  intro r hr
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hr))

theorem a_c_ideal_top (v : G) (hv : v ≠ 0) (S T : Finset ℂˣ) :
    Ideal.span {aFactor v S, cFactor v T} = ⊤ := by
  apply span_eq_top_of_no_field_zero
  intro F _ _ rho hzero
  exact a_c_no_common_root rho v hv S T
    (hzero _ (Set.mem_insert _ _))
    (hzero _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem a_a_c_ideal_top (v w u : G) (hdet : det v w ≠ 0) (hu : u ≠ 0)
    (S T U : Finset ℂˣ) : Ideal.span {aFactor v S, aFactor w T, cFactor u U} = ⊤ := by
  apply span_eq_top_of_no_field_zero
  intro F _ _ rho hzero
  exact a_a_c_no_common_root rho v w u hdet hu S T U
    (hzero _ (Set.mem_insert _ _))
    (hzero _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (hzero _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem c_c_a_ideal_top (v w u : G) (hdet : det v w ≠ 0) (hu : u ≠ 0)
    (S T U : Finset ℂˣ) : Ideal.span {cFactor v S, cFactor w T, aFactor u U} = ⊤ := by
  apply span_eq_top_of_no_field_zero
  intro F _ _ rho hzero
  exact c_c_a_no_common_root rho v w u hdet hu S T U
    (hzero _ (Set.mem_insert _ _))
    (hzero _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (hzero _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

variable {ι : Type*} [Fintype ι]

def aProduct (v : ι → G) (S : ι → Finset ℂˣ) : R := ∏ i, aFactor (v i) (S i)

def cProduct (v : ι → G) (S : ι → Finset ℂˣ) : R := ∏ i, cFactor (v i) (S i)

def aCofactor (v : ι → G) (S : ι → Finset ℂˣ) (i : ι) : R :=
  ∏ k ∈ Finset.univ.erase i, aFactor (v k) (S k)

def cCofactor (v : ι → G) (S : ι → Finset ℂˣ) (j : ι) : R :=
  ∏ l ∈ Finset.univ.erase j, cFactor (v l) (S l)

def projector (v : ι → G) (S : ι → Finset ℂˣ) (i j : ι) : R :=
  aCofactor v S i * cCofactor v S j

def relationIdeal (v : ι → G) (S : ι → Finset ℂˣ) : Ideal R :=
  Ideal.span {aProduct v S, cProduct v S}

abbrev relationQuotient (v : ι → G) (S : ι → Finset ℂˣ) := R ⧸ relationIdeal v S

def projection (v : ι → G) (S : ι → Finset ℂˣ) : R →ₐ[K] relationQuotient v S :=
  Ideal.Quotient.mkₐ K (relationIdeal v S)

abbrev OffDiagonal (ι : Type*) := {ij : ι × ι // ij.1 ≠ ij.2}

def globalGenerators (v : ι → G) (S : ι → Finset ℂˣ) : Set R :=
  {aProduct v S, cProduct v S} ∪
    Set.range (fun ij : OffDiagonal ι => projector v S ij.val.1 ij.val.2)

/-- The directional projectors and the two global relations generate the unit
ideal. This replaces the two CRT isomorphisms by the exact algebraic fact
needed for the spanning argument, with all coprimality inputs proved. -/
theorem globalGenerators_span_top (v : ι → G) (S : ι → Finset ℂˣ)
    (hv : ∀ i, v i ≠ 0)
    (hdet : ∀ i k, i ≠ k → det (v i) (v k) ≠ 0) :
    Ideal.span (globalGenerators v S) = ⊤ := by
  classical
  apply span_eq_top_of_no_field_zero
  intro F _ _ rho hzero
  have ha : rho (aProduct v S) = 0 := hzero _ (Or.inl (Set.mem_insert _ _))
  have hc : rho (cProduct v S) = 0 :=
    hzero _ (Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simp only [aProduct, map_prod] at ha
  simp only [cProduct, map_prod] at hc
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ha
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hc
  have hij : i ≠ j := by
    intro heq
    subst j
    exact a_c_no_common_root rho (v i) (hv i) (S i) (S i) hi hj
  have hprojector : rho (projector v S i j) = 0 :=
    hzero _ (Or.inr ⟨⟨(i, j), hij⟩, rfl⟩)
  rw [projector, map_mul] at hprojector
  rcases mul_eq_zero.mp hprojector with hleft | hright
  · simp only [aCofactor, map_prod] at hleft
    obtain ⟨k, hk, hzero'⟩ := Finset.prod_eq_zero_iff.mp hleft
    have hki := (Finset.mem_erase.mp hk).1
    exact a_a_c_no_common_root rho (v i) (v k) (v j)
      (hdet i k hki.symm) (hv j) (S i) (S k) (S j) hi hzero' hj
  · simp only [cCofactor, map_prod] at hright
    obtain ⟨l, hl, hzero'⟩ := Finset.prod_eq_zero_iff.mp hright
    have hlj := (Finset.mem_erase.mp hl).1
    exact c_c_a_no_common_root rho (v j) (v l) (v i)
      (hdet j l hlj.symm) (hv i) (S j) (S l) (S i) hj hzero' hi

end

end NivatTrial.QuotientIdeals
