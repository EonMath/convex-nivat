import NivatTrial.Divisibility
import Mathlib.RingTheory.Localization.FractionRing

/-! The rational coefficient field of §5.2, realized as the fraction field of
the already defined two-variable complex Laurent ring. -/

namespace NivatTrial.CoefficientField

open NivatTrial.Algebra NivatTrial.Divisibility

noncomputable section

abbrev K := FractionRing Laurent

abbrev R := AddMonoidAlgebra K G

def xUnit (u : G) : Kˣ :=
  Units.map (algebraMap Laurent K).toMonoidHom (monomialUnit u)

def constantUnit (c : ℂˣ) : Kˣ :=
  Units.map (algebraMap ℂ K).toMonoidHom c

def yUnit (u : G) : Rˣ := monomialUnitOver u

@[simp] theorem xUnit_val (u : G) :
    (xUnit u : K) = algebraMap Laurent K (monomial u) := rfl

@[simp] theorem constantUnit_val (c : ℂˣ) :
    (constantUnit c : K) = algebraMap ℂ K (c : ℂ) := rfl

@[simp] theorem yUnit_val (u : G) :
    (yUnit u : R) = AddMonoidAlgebra.single u 1 := rfl

@[simp] theorem xUnit_zero : xUnit 0 = 1 := by
  ext
  simp

@[simp] theorem yUnit_zero : yUnit 0 = 1 := by
  ext
  simp [AddMonoidAlgebra.one_def]

theorem xUnit_add (u v : G) : xUnit (u + v) = xUnit u * xUnit v := by
  ext
  simp [monomial_add]

theorem yUnit_add (u v : G) : yUnit (u + v) = yUnit u * yUnit v := by
  ext
  simp

theorem xUnit_zpow (u : G) (n : ℤ) : xUnit u ^ n = xUnit (n • u) := by
  unfold xUnit
  rw [← map_zpow]
  congr 1
  apply Units.ext
  exact monomialUnit_zpow u n

theorem yUnit_zpow (u : G) (n : ℤ) : yUnit u ^ n = yUnit (n • u) :=
  monomialUnitOver_zpow u n

/-- A nonconstant Laurent monomial cannot become a complex scalar in the
fraction field. This is the exact independence fact used by the maximal-ideal
argument; no algebraic-closure or Nullstellensatz premise is required. -/
theorem xUnit_ne_constantUnit {u : G} (hu : u ≠ 0) (c : ℂˣ) :
    xUnit u ≠ constantUnit c := by
  intro h
  have hv := congrArg (fun a : Kˣ => (a : K)) h
  have hs : monomial u = scalar (c : ℂ) := by
    apply IsFractionRing.injective Laurent K
    have hc : algebraMap Laurent K (scalar (c : ℂ)) = algebraMap ℂ K (c : ℂ) :=
      IsScalarTower.algebraMap_apply ℂ Laurent K _
    simpa only [xUnit_val, constantUnit_val, hc] using hv
  have hc := congrArg (fun f : Laurent => f.coeff u) hs
  simpa [monomial, scalar_apply, Finsupp.single_apply, hu, Ne.symm hu] using hc

def includeCoefficients : Laurent →ₐ[ℂ] R :=
  AddMonoidAlgebra.mapAlgHom G (Algebra.ofId ℂ K)

@[simp] theorem includeCoefficients_single (u : G) (c : ℂ) :
    includeCoefficients (AddMonoidAlgebra.single u c) =
      AddMonoidAlgebra.single u (algebraMap ℂ K c) := by
  simp [includeCoefficients]

end

end NivatTrial.CoefficientField
