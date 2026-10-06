import NivatTrial.CoefficientField
import Mathlib.Algebra.Group.Hom.Instances

/-! The completely split directional relations of §5.2 and their images in
maximal-ideal quotient fields. -/

namespace NivatTrial.QuotientFactors

open NivatTrial.Algebra NivatTrial.Divisibility NivatTrial.CoefficientField

noncomputable section

def xCharacter : Multiplicative G →* Kˣ where
  toFun u := xUnit u.toAdd
  map_one' := xUnit_zero
  map_mul' u v := xUnit_add u.toAdd v.toAdd

def yCharacter : Multiplicative G →* Rˣ where
  toFun u := yUnit u.toAdd
  map_one' := yUnit_zero
  map_mul' u v := yUnit_add u.toAdd v.toAdd

def wCharacter : Multiplicative G →* Rˣ where
  toFun u := Units.map (algebraMap K R).toMonoidHom (xCharacter u) * (yCharacter u)⁻¹
  map_one' := by simp
  map_mul' u v := by
    apply Units.ext
    simp only [map_mul, mul_inv_rev, Units.val_mul]
    ac_rfl

def rootPolynomial (S : Finset ℂˣ) : Polynomial K :=
  ∏ c ∈ S, (Polynomial.X - Polynomial.C (constantUnit c : K))

def aFactor (v : G) (S : Finset ℂˣ) : R :=
  Polynomial.aeval (yUnit v : R) (rootPolynomial S)

def cFactor (v : G) (S : Finset ℂˣ) : R :=
  Polynomial.aeval (wCharacter (.ofAdd v) : R) (rootPolynomial S)

theorem rootPolynomial_monic (S : Finset ℂˣ) : (rootPolynomial S).Monic := by
  classical
  exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)

@[simp] theorem rootPolynomial_natDegree (S : Finset ℂˣ) :
    (rootPolynomial S).natDegree = S.card := by
  classical
  rw [rootPolynomial, Polynomial.natDegree_prod_of_monic S _
    (fun c _ => Polynomial.monic_X_sub_C _)]
  simp

theorem rootPolynomial_constant_ne_zero (S : Finset ℂˣ) :
    (rootPolynomial S).coeff 0 ≠ 0 := by
  classical
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  exact Finset.prod_ne_zero_iff.mpr (fun c _ => neg_ne_zero.mpr (Units.ne_zero _))

section FieldImages

variable {F : Type*} [Field F] [Algebra K F]

def constantImage : ℂˣ →* Fˣ :=
  (Units.map (algebraMap K F).toMonoidHom).comp
    (Units.map (algebraMap ℂ K).toMonoidHom)

def xImage : Multiplicative G →* Fˣ :=
  (Units.map (algebraMap K F).toMonoidHom).comp xCharacter

def yImage (rho : R →ₐ[K] F) : Multiplicative G →* Fˣ :=
  (Units.map rho.toMonoidHom).comp yCharacter

def wImage (rho : R →ₐ[K] F) : Multiplicative G →* Fˣ :=
  (Units.map rho.toMonoidHom).comp wCharacter

@[simp] theorem constantImage_val (c : ℂˣ) :
    (constantImage (F := F) c : F) =
      algebraMap K F (algebraMap ℂ K (c : ℂ)) := rfl

@[simp] theorem yImage_val (rho : R →ₐ[K] F) (v : G) :
    (yImage rho (.ofAdd v) : F) = rho (yUnit v : R) := rfl

@[simp] theorem wImage_val (rho : R →ₐ[K] F) (v : G) :
    (wImage rho (.ofAdd v) : F) = rho (wCharacter (.ofAdd v) : R) := rfl

theorem xImage_ne_constantImage {u : G} (hu : u ≠ 0) (c : ℂˣ) :
    xImage (F := F) (.ofAdd u) ≠ constantImage c := by
  intro h
  apply xUnit_ne_constantUnit hu c
  apply Units.ext
  apply (algebraMap K F).injective
  exact congrArg (fun a : Fˣ => (a : F)) h

theorem wImage_eq (rho : R →ₐ[K] F) (v : G) :
    wImage rho (.ofAdd v) = xImage (.ofAdd v) * (yImage rho (.ofAdd v))⁻¹ := by
  change Units.map rho.toMonoidHom
      (Units.map (algebraMap K R).toMonoidHom (xCharacter (.ofAdd v)) *
        (yCharacter (.ofAdd v))⁻¹) =
    Units.map (algebraMap K F).toMonoidHom (xCharacter (.ofAdd v)) *
      (Units.map rho.toMonoidHom (yCharacter (.ofAdd v)))⁻¹
  rw [map_mul, map_inv]
  change Units.map rho.toMonoidHom
      (Units.map (algebraMap K R).toMonoidHom (xCharacter (.ofAdd v))) *
      (Units.map rho.toMonoidHom (yCharacter (.ofAdd v)))⁻¹ =
    Units.map (algebraMap K F).toMonoidHom (xCharacter (.ofAdd v)) *
      (Units.map rho.toMonoidHom (yCharacter (.ofAdd v)))⁻¹
  congr 1
  apply Units.ext
  exact rho.commutes _

theorem aFactor_zero_iff (rho : R →ₐ[K] F) (v : G) (S : Finset ℂˣ) :
    rho (aFactor v S) = 0 ↔
      ∃ c ∈ S, yImage rho (.ofAdd v) = constantImage c := by
  classical
  simp only [aFactor, Polynomial.aeval_algHom_apply, rootPolynomial,
    map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [Finset.prod_eq_zero_iff]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  rw [sub_eq_zero]
  rw [rho.commutes]
  change ((yImage rho (.ofAdd v) : F) = (constantImage (F := F) c : F)) ↔ _
  exact Units.ext_iff.symm

theorem cFactor_zero_iff (rho : R →ₐ[K] F) (v : G) (S : Finset ℂˣ) :
    rho (cFactor v S) = 0 ↔
      ∃ c ∈ S, wImage rho (.ofAdd v) = constantImage c := by
  classical
  simp only [cFactor, Polynomial.aeval_algHom_apply, rootPolynomial,
    map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [Finset.prod_eq_zero_iff]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  rw [sub_eq_zero]
  rw [rho.commutes]
  change ((wImage rho (.ofAdd v) : F) = (constantImage (F := F) c : F)) ↔ _
  exact Units.ext_iff.symm

end FieldImages

/-- Clearing the determinant denominator in the two rational coordinates. -/
theorem determinant_decomposition (v w u : G) :
    det v w • u = det u w • v + det v u • w := by
  apply Prod.ext <;> simp only [det, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, smul_eq_mul] <;> ring

theorem character_determinant_identity {H : Type*} [CommGroup H]
    (U : Multiplicative G →* H) (v w u : G) :
    U (.ofAdd u) ^ det v w =
      U (.ofAdd v) ^ det u w * U (.ofAdd w) ^ det v u := by
  rw [← map_zpow, ← ofAdd_zsmul, determinant_decomposition]
  simp only [ofAdd_add, map_mul, ofAdd_zsmul, map_zpow]

section CommonRoots

variable {F : Type*} [Field F] [Algebra K F]

theorem xImage_eq_y_mul_w (rho : R →ₐ[K] F) (v : G) :
    xImage (.ofAdd v) = yImage rho (.ofAdd v) * wImage rho (.ofAdd v) := by
  rw [wImage_eq]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem xImage_eq_w_mul_y (rho : R →ₐ[K] F) (v : G) :
    xImage (.ofAdd v) = wImage rho (.ofAdd v) * yImage rho (.ofAdd v) := by
  rw [mul_comm]
  exact xImage_eq_y_mul_w rho v

private theorem lattice_smul_ne_zero {n : ℤ} {u : G} (hn : n ≠ 0) (hu : u ≠ 0) :
    n • u ≠ 0 := by
  intro h
  apply hu
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  apply Prod.ext
  · exact (mul_eq_zero.mp hfst).resolve_left hn
  · exact (mul_eq_zero.mp hsnd).resolve_left hn

/-- Two independent constant character values force a determinant power in
every direction to be constant. The complementary character then contradicts
independence of the coefficient-field monomial. -/
theorem scalar_character_pair_impossible
    (U V : Multiplicative G →* Fˣ)
    (hX : ∀ z : G, xImage (F := F) (.ofAdd z) = U (.ofAdd z) * V (.ofAdd z))
    (v w u : G) (hdet : det v w ≠ 0) (hu : u ≠ 0)
    (a b c : ℂˣ)
    (hv : U (.ofAdd v) = constantImage a)
    (hw : U (.ofAdd w) = constantImage b)
    (hc : V (.ofAdd u) = constantImage c) : False := by
  have hU := character_determinant_identity U v w u
  rw [hv, hw] at hU
  have hx : xImage (F := F) (.ofAdd u) ^ det v w =
      constantImage (F := F) (a ^ det u w * b ^ det v u * c ^ det v w) := by
    rw [hX, mul_zpow, hU, hc]
    simp only [map_mul, map_zpow]
  have hx' : xImage (F := F) (.ofAdd (det v w • u)) =
      constantImage (F := F) (a ^ det u w * b ^ det v u * c ^ det v w) := by
    simpa only [ofAdd_zsmul, map_zpow] using hx
  exact xImage_ne_constantImage (lattice_smul_ne_zero hdet hu) _ hx'

theorem a_c_no_common_root (rho : R →ₐ[K] F) (v : G) (hv : v ≠ 0)
    (S T : Finset ℂˣ) (ha : rho (aFactor v S) = 0) (hc : rho (cFactor v T) = 0) :
    False := by
  obtain ⟨a, _, ha⟩ := (aFactor_zero_iff rho v S).mp ha
  obtain ⟨c, _, hc⟩ := (cFactor_zero_iff rho v T).mp hc
  apply xImage_ne_constantImage (F := F) hv (a * c)
  rw [xImage_eq_y_mul_w rho v, ha, hc, map_mul]

theorem a_a_c_no_common_root (rho : R →ₐ[K] F) (v w u : G)
    (hdet : det v w ≠ 0) (hu : u ≠ 0) (S T U : Finset ℂˣ)
    (hv : rho (aFactor v S) = 0) (hw : rho (aFactor w T) = 0)
    (hu' : rho (cFactor u U) = 0) : False := by
  obtain ⟨a, _, ha⟩ := (aFactor_zero_iff rho v S).mp hv
  obtain ⟨b, _, hb⟩ := (aFactor_zero_iff rho w T).mp hw
  obtain ⟨c, _, hc⟩ := (cFactor_zero_iff rho u U).mp hu'
  exact scalar_character_pair_impossible (yImage rho) (wImage rho)
    (xImage_eq_y_mul_w rho) v w u hdet hu a b c ha hb hc

theorem c_c_a_no_common_root (rho : R →ₐ[K] F) (v w u : G)
    (hdet : det v w ≠ 0) (hu : u ≠ 0) (S T U : Finset ℂˣ)
    (hv : rho (cFactor v S) = 0) (hw : rho (cFactor w T) = 0)
    (hu' : rho (aFactor u U) = 0) : False := by
  obtain ⟨a, _, ha⟩ := (cFactor_zero_iff rho v S).mp hv
  obtain ⟨b, _, hb⟩ := (cFactor_zero_iff rho w T).mp hw
  obtain ⟨c, _, hc⟩ := (aFactor_zero_iff rho u U).mp hu'
  exact scalar_character_pair_impossible (wImage rho) (yImage rho)
    (xImage_eq_w_mul_y rho) v w u hdet hu a b c ha hb hc

end CommonRoots

end

end NivatTrial.QuotientFactors
