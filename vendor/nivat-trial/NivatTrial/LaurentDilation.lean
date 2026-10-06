import NivatTrial.LaurentAction

/-! Coefficient changes and exponent dilations of Laurent actions. -/

namespace NivatTrial.LaurentDilation

open NivatTrial.LaurentAction
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def mapCoefficients (φ : R →+* S) : RingLaurent R →+* RingLaurent S :=
  AddMonoidAlgebra.mapRingHom Lattice φ

@[simp] theorem mapCoefficients_coeff (φ : R →+* S) (f : RingLaurent R) (v : Lattice) :
    (mapCoefficients φ f).coeff v=φ (f.coeff v) :=
  AddMonoidAlgebra.coeff_mapRingHom φ f v

@[simp] theorem mapCoefficients_single (φ : R →+* S) (v : Lattice) (c : R) :
    mapCoefficients φ (AddMonoidAlgebra.single v c) = AddMonoidAlgebra.single v (φ c) :=
  AddMonoidAlgebra.mapRingHom_single φ v c

theorem act_mapCoefficients (φ : R →+* S) (f : RingLaurent R) (x : Lattice → R) (z : Lattice) :
    act (mapCoefficients φ f) (fun u => φ (x u)) z = φ (act f x z) := by
  simp [act,mapCoefficients,AddMonoidAlgebra.mapRingHom,AddMonoidAlgebra.map,
    Finsupp.sum_mapRange_index,map_finsuppSum,map_mul]

theorem map_annihilates (φ : R →+* S) {f : RingLaurent R} {x : Lattice → R}
    (h : act f x=0) : act (mapCoefficients φ f) (fun z => φ (x z))=0 := by
  funext z
  rw [act_mapCoefficients]
  simp only [h,Pi.zero_apply,map_zero]

theorem reflect_annihilates (φ : R →+* S) (hφ : Function.Injective φ)
    {f : RingLaurent R} {x : Lattice → R}
    (h : act (mapCoefficients φ f) (fun z => φ (x z))=0) : act f x=0 := by
  funext z
  apply hφ
  have hz := congrFun h z
  simpa only [act_mapCoefficients,Pi.zero_apply,map_zero] using hz

def scaleExponent (n : ℕ) : Lattice →+ Lattice where
  toFun v := n • v
  map_zero' := smul_zero n
  map_add' x y := nsmul_add x y n

@[simp] theorem scaleExponent_apply (n : ℕ) (v : Lattice) : scaleExponent n v=n•v := rfl

def dilate (n : ℕ) : RingLaurent R →+* RingLaurent R :=
  AddMonoidAlgebra.mapDomainRingHom R (scaleExponent n)

@[simp] theorem dilate_single (n : ℕ) (v : Lattice) (c : R) :
    dilate n (AddMonoidAlgebra.single v c)=AddMonoidAlgebra.single (n•v) c := by
  simp [dilate]

theorem act_dilate (n : ℕ) (f : RingLaurent R) (x : Lattice → R) (z : Lattice) :
    act (dilate n f) x z = f.coeff.sum (fun u c => c*x (z+n•u)) := by
  simp [act,dilate,AddMonoidAlgebra.mapDomainRingHom,AddMonoidAlgebra.mapDomain,
    Finsupp.sum_mapDomain_index,scaleExponent,add_mul]

@[simp] theorem dilate_one (f : RingLaurent R) : dilate 1 f=f := by
  have hs : scaleExponent 1 = AddMonoidHom.id Lattice := by
    ext v : 1
    simp
  simp only [dilate,hs,AddMonoidAlgebra.mapDomainRingHom_id,RingHom.id_apply]

theorem dilate_comp (m n : ℕ) (f : RingLaurent R) : dilate m (dilate n f)=dilate (m*n) f := by
  have he : (scaleExponent m).comp (scaleExponent n)=scaleExponent (m*n) := by
    ext v : 1
    change m • (n • v) = (m*n) • v
    rw [smul_smul]
  have hh := congrArg (fun H : RingLaurent R →+* RingLaurent R => H f)
    (AddMonoidAlgebra.mapDomainRingHom_comp (R:=R) (scaleExponent m) (scaleExponent n))
  simpa only [he,RingHom.comp_apply,dilate] using hh.symm

theorem map_dilate (φ : R →+* S) (n : ℕ) (f : RingLaurent R) :
    mapCoefficients φ (dilate n f)=dilate n (mapCoefficients φ f) := by
  exact congrArg (fun H : RingLaurent R →+* RingLaurent S => H f)
    (AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom φ (scaleExponent n))

/-- Dilating exponents cannot increase the elementary absolute coefficient bound. -/
theorem abs_act_dilate_le (n : ℕ) (f : RingLaurent ℤ) (x : Lattice → ℤ) (B : ℤ)
    (hB : ∀ z, |x z| ≤ B) (z : Lattice) :
    |act (dilate n f) x z| ≤ (∑ u ∈ f.coeff.support, |f.coeff u|)*B := by
  rw [act_dilate,Finsupp.sum]
  calc
    |∑ u ∈ f.coeff.support, f.coeff u*x (z+n•u)| ≤
        ∑ u ∈ f.coeff.support, |f.coeff u*x (z+n•u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ f.coeff.support, |f.coeff u| * B := by
      apply Finset.sum_le_sum
      intro u hu
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
    _ = (∑ u ∈ f.coeff.support, |f.coeff u|)*B := (Finset.sum_mul ..).symm

end
end NivatTrial.LaurentDilation
