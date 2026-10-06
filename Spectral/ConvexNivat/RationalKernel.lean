import Mathlib

open scoped BigOperators
namespace ConvexNivat
noncomputable section

def rationalSystemEquation {Row : Type*} {n : ℕ} (coeff : Row → Fin n → ℚ)
    (K : Type*) [Field K] [Algebra ℚ K] (r : Row) : (Fin n → K) →ₗ[K] K :=
  ∑ j : Fin n, (algebraMap ℚ K (coeff r j)) • LinearMap.proj j

def rationalSystemKernel {Row : Type*} {n : ℕ} (coeff : Row → Fin n → ℚ)
    (K : Type*) [Field K] [Algebra ℚ K] : Submodule K (Fin n → K) :=
  ⨅ r : Row, (rationalSystemEquation coeff K r).ker


private def rowForm {n : ℕ} (K : Type*) [Field K] :
    (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K) :=
  { toFun := fun v => ∑ j : Fin n, v j • LinearMap.proj j
    map_add' := by intro v w; simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by intro a v; simp [Pi.smul_apply, mul_smul, Finset.smul_sum] }

private lemma rowForm_apply {n : ℕ} (K : Type*) [Field K]
    (v x : Fin n → K) : rowForm K v x = ∑ j, v j * x j := by
  simp [rowForm]

private lemma rowForm_injective {n : ℕ} (K : Type*) [Field K] :
    Function.Injective (rowForm (n := n) K) := by
  classical
  intro v w h
  ext j
  have hh := congrArg (fun f : Module.Dual K (Fin n → K) => f (Pi.single j 1)) h
  simpa [rowForm_apply, Pi.single_apply] using hh

private lemma cast_mem_span {n : ℕ} (s : Set (Fin n → ℚ))
    (v : Fin n → ℚ) (hv : v ∈ Submodule.span ℚ s) :
    (fun j => algebraMap ℚ ℂ (v j)) ∈
      Submodule.span ℂ ((fun w : Fin n → ℚ => fun j => algebraMap ℚ ℂ (w j)) '' s) := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span ⟨v, hv, rfl⟩
  | zero =>
      change (fun j => algebraMap ℚ ℂ (0 : ℚ)) ∈ _
      simp only [map_zero]
      exact Submodule.zero_mem _
  | add v w hv hw ihv ihw =>
      convert Submodule.add_mem _ ihv ihw using 1
      ext j
      simp
  | smul a v hv ih =>
      convert Submodule.smul_mem _ (algebraMap ℚ ℂ a) ih using 1
      ext j
      simp [smul_eq_mul]

private lemma row_span_dimension {Row : Type*} {n : ℕ}
    (coeff : Row → Fin n → ℚ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun r j => algebraMap ℚ ℂ (coeff r j)))) =
      Module.finrank ℚ (Submodule.span ℚ (Set.range coeff)) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range coeff)
  have hfinite : Finite b := hli.finite
  let : Fintype b := Fintype.ofFinite b
  have hliC : LinearIndependent ℂ (fun v : b => fun j => algebraMap ℚ ℂ (v.val j)) :=
    linearIndependent_algebraMap_comp_iff.mpr hli
  have hrange : Set.range (fun v : b => fun j => algebraMap ℚ ℂ (v.val j)) =
      (fun v : Fin n → ℚ => fun j => algebraMap ℚ ℂ (v j)) '' b := by
    ext x; simp
  have hspanC : Submodule.span ℂ (Set.range
      (fun v : b => fun j => algebraMap ℚ ℂ (v.val j))) =
      Submodule.span ℂ (Set.range (fun r j => algebraMap ℚ ℂ (coeff r j))) := by
    rw [hrange]
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨r, rfl⟩ := hb hv
      exact Set.mem_range_self r
    · apply Submodule.span_le.mpr
      rintro _ ⟨r, rfl⟩
      exact cast_mem_span b _ (hspan.symm ▸ Submodule.subset_span (Set.mem_range_self r))
  rw [← hspanC, finrank_span_eq_card hliC, ← hspan]
  have hspQ : Submodule.span ℚ (Set.range (Subtype.val : b → Fin n → ℚ)) =
      Submodule.span ℚ b := by
    congr 1
    ext v
    simp
  rw [← hspQ]
  exact (finrank_span_eq_card hli).symm

private lemma equation_span_dimension {Row : Type*} {n : ℕ}
    (coeff : Row → Fin n → ℚ) (K : Type*) [Field K] [Algebra ℚ K] :
    Module.finrank K (Submodule.span K (Set.range (rationalSystemEquation coeff K))) =
      Module.finrank K (Submodule.span K (Set.range
        (fun r j => algebraMap ℚ K (coeff r j)))) := by
  let W := Submodule.span K (Set.range (fun r j => algebraMap ℚ K (coeff r j)))
  have hh : Submodule.map (rowForm K) W =
      Submodule.span K (Set.range (rationalSystemEquation coeff K)) := by
    change Submodule.map (rowForm K) (Submodule.span K _) = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hh]
  exact (Submodule.equivMapOfInjective (rowForm K) (rowForm_injective K) W).finrank_eq.symm

private lemma kernel_annihilator {Row : Type*} {n : ℕ}
    (coeff : Row → Fin n → ℚ) (K : Type*) [Field K] [Algebra ℚ K] :
    rationalSystemKernel coeff K =
      (Submodule.span K (Set.range (rationalSystemEquation coeff K))).dualCoannihilator := by
  ext x
  change x ∈ rationalSystemKernel coeff K ↔
    x ∈ ((Submodule.span K (Set.range (rationalSystemEquation coeff K))).dualCoannihilator :
      Set (Fin n → K))
  rw [Submodule.coe_dualCoannihilator_span]
  simp [rationalSystemKernel]

/-- The field-extension dimension equality explicitly used in Lemma 2.5,
including the source's potentially infinite family of rational equations. -/
theorem rational_system_kernel_dimension {Row : Type*} {n : ℕ}
    (coeff : Row → Fin n → ℚ) :
    Module.finrank ℂ (rationalSystemKernel coeff ℂ) =
      Module.finrank ℚ (rationalSystemKernel coeff ℚ) := by
  have hC := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℂ (Set.range (rationalSystemEquation coeff ℂ)))
  have hQ := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℚ (Set.range (rationalSystemEquation coeff ℚ)))
  rw [← kernel_annihilator, equation_span_dimension] at hC hQ
  simp only [Module.finrank_fin_fun, Algebra.algebraMap_self, RingHom.id_apply] at hC hQ
  rw [row_span_dimension] at hC
  change Module.finrank ℚ (Submodule.span ℚ (Set.range coeff)) +
    Module.finrank ℚ (rationalSystemKernel coeff ℚ) = n at hQ
  omega

end
end ConvexNivat
