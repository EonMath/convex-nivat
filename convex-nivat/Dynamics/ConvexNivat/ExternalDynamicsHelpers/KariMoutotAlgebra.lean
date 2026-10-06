import ConvexNivat.ExternalDynamicsHelpers.KariMoutotCore

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem dot_add (a b u : Lattice) : latticeDot (a + b) u = latticeDot a u + latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_sub (a b u : Lattice) : latticeDot (a - b) u = latticeDot a u - latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_smul (k : ℤ) (a u : Lattice) : latticeDot (k • a) u = k * latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_neg_right (a u : Lattice) : latticeDot a (-u) = -latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_self_pos (u : Lattice) (hu : u ≠ 0) : 0 < latticeDot u u := by
  have hn : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h; push_neg at h; exact hu (Prod.ext h.1 h.2)
  unfold latticeDot
  rcases hn with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.1]

private theorem action_single (u : Lattice) (a : ℤ) (f : Configuration ℤ) (z : Lattice) :
    laurentAction (AddMonoidAlgebra.single u a).coeff f z = a * f (z - u) := by
  simp [laurentAction]
private theorem action_zero (f : Configuration ℤ) : laurentAction 0 f = 0 := by
  funext z; simp [laurentAction]
private theorem action_one (f : Configuration ℤ) :
    laurentAction (1 : AddMonoidAlgebra ℤ Lattice).coeff f = f := by
  rw [AddMonoidAlgebra.one_def]
  funext z
  rw [action_single]
  simp
private theorem action_add (P Q : AddMonoidAlgebra ℤ Lattice) (f : Configuration ℤ) :
    laurentAction (P + Q).coeff f = laurentAction P.coeff f + laurentAction Q.coeff f := by
  funext z; simp [laurentAction, Finsupp.sum_add_index, add_mul]
private theorem action_sub (P Q : AddMonoidAlgebra ℤ Lattice) (f : Configuration ℤ) :
    laurentAction (P - Q).coeff f = laurentAction P.coeff f - laurentAction Q.coeff f := by
  funext z; simp [laurentAction, Finsupp.sum_sub_index, sub_mul]
private theorem action_add_field (P : AddMonoidAlgebra ℤ Lattice) (f g : Configuration ℤ) :
    laurentAction P.coeff (f + g) = laurentAction P.coeff f + laurentAction P.coeff g := by
  funext z; simp [laurentAction, mul_add, Finsupp.sum_add]
private theorem action_sub_field (P : AddMonoidAlgebra ℤ Lattice) (f g : Configuration ℤ) :
    laurentAction P.coeff (f - g) = laurentAction P.coeff f - laurentAction P.coeff g := by
  funext z; simp [laurentAction, mul_sub, Finsupp.sum_sub]
private theorem action_mul (P Q : AddMonoidAlgebra ℤ Lattice) (f : Configuration ℤ) :
    laurentAction (P * Q).coeff f = laurentAction P.coeff (laurentAction Q.coeff f) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [action_zero]
  | add P Q hp hq => simp only [add_mul, action_add, hp, hq]
  | single u c =>
    induction Q using AddMonoidAlgebra.induction_linear with
    | zero =>
      simp only [mul_zero, AddMonoidAlgebra.coeff_zero, action_zero]
      funext z
      rw [action_single]
      simp
    | add P Q hp hq => simp only [mul_add, action_add, action_add_field, hp, hq]
    | single v d =>
      rw [AddMonoidAlgebra.single_mul_single]
      funext z
      rw [action_single, action_single, action_single]
      simp [sub_sub, mul_assoc]
private theorem action_difference (f : Configuration ℤ) (v : Lattice) :
    laurentAction (AddMonoidAlgebra.single v (1 : ℤ) - AddMonoidAlgebra.single 0 1).coeff f =
      periodDifference f v := by
  rw [action_sub]
  funext z
  simp only [Pi.sub_apply, action_single, one_mul, sub_zero, periodDifference]

private theorem periodic_zero (f : Configuration ℤ) (v u : Lattice)
    (hv : latticeDot v u ≠ 0) (hp : HasPeriod f v) (c : ℤ)
    (hc : ∀ z, latticeDot z u < c → f z = 0) : f = 0 := by
  funext z
  let S := |latticeDot z u| + |c| + 1
  let q := -(S * latticeDot v u)
  have hsq : 1 ≤ latticeDot v u * latticeDot v u := by
    have := sq_pos_of_ne_zero hv
    nlinarith
  have hS : 0 < S := by dsimp [S]; positivity
  have hm : S ≤ S * (latticeDot v u * latticeDot v u) := by nlinarith
  have hz : latticeDot (z + q • v) u < c := by
    rw [dot_add, dot_smul]
    dsimp [q, S] at *
    have h1 := le_abs_self (latticeDot z u)
    have h2 := neg_le_abs c
    nlinarith
  exact (hasPeriod_zsmul f v hp q z).symm.trans (hc _ hz)

private theorem action_half_zero (P : AddMonoidAlgebra ℤ Lattice) (f : Configuration ℤ)
    (u : Lattice) (hf : ∀ z ∈ strictHalf u, f z = 0) :
    ∃ c : ℤ, ∀ z, latticeDot z u < c → laurentAction P.coeff f z = 0 := by
  classical
  let M := P.coeff.support.sup (fun q => (latticeDot q u).natAbs)
  refine ⟨-(M : ℤ) - 1, fun z hz => ?_⟩
  apply Finset.sum_eq_zero
  intro q hq
  have hM : (latticeDot q u).natAbs ≤ M := Finset.le_sup (f := fun q => (latticeDot q u).natAbs) hq
  have hqneg := neg_le_abs (latticeDot q u)
  rw [← Int.natCast_natAbs] at hqneg
  have hzero := hf (z - q) (show latticeDot (z - q) u < 0 by rw [dot_sub]; omega)
  simp [hzero]

private theorem product_half_zero {ι : Type*} (s : Finset ι) (v : ι → Lattice)
    (f : Configuration ℤ) (u : Lattice)
    (hv : ∀ i ∈ s, latticeDot (v i) u ≠ 0)
    (hann : Annihilates (∏ i ∈ s,
      (AddMonoidAlgebra.single (v i) (1 : ℤ) - AddMonoidAlgebra.single 0 1)).coeff f)
    (hf : ∀ z ∈ strictHalf u, f z = 0) : f = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : laurentAction (1 : AddMonoidAlgebra ℤ Lattice).coeff f = 0 := by
      funext z; simpa using hann z
    simpa [action_one] using h
  | @insert i s hi ih =>
    let P : AddMonoidAlgebra ℤ Lattice := ∏ j ∈ s,
      (AddMonoidAlgebra.single (v j) (1 : ℤ) - AddMonoidAlgebra.single 0 1)
    have ha : periodDifference (laurentAction P.coeff f) (v i) = 0 := by
      have h : laurentAction ((AddMonoidAlgebra.single (v i) (1 : ℤ) -
          AddMonoidAlgebra.single 0 1) * P).coeff f = 0 := by
        funext z; simpa [Finset.prod_insert, hi, P] using hann z
      rwa [action_mul, action_difference] at h
    have hp : HasPeriod (laurentAction P.coeff f) (v i) := by
      intro z
      have h := congrFun ha (z + v i)
      simp [periodDifference] at h
      omega
    obtain ⟨c, hc⟩ := action_half_zero P f u hf
    have hzero := periodic_zero _ (v i) u (hv i (Finset.mem_insert_self _ _)) hp c hc
    apply ih (fun j hj => hv j (Finset.mem_insert_of_mem hj))
    intro z
    exact congrFun hzero z

theorem factor_image_remaining_annihilator (ξ : Configuration ℤ)
    (m : ℕ) (v : Fin m → Lattice)
    (hann : Annihilates (differenceFactors m v) ξ) (i : Fin m) :
    Annihilates (differenceWithout m v i) (periodDifference ξ (v i)) := by
  classical
  let P : AddMonoidAlgebra ℤ Lattice := ∏ j ∈ (Finset.univ.erase i),
    (AddMonoidAlgebra.single (v j) (1 : ℤ) - AddMonoidAlgebra.single 0 1)
  have hprod : P * (AddMonoidAlgebra.single (v i) (1 : ℤ) - AddMonoidAlgebra.single 0 1) =
      ∏ j : Fin m, (AddMonoidAlgebra.single (v j) (1 : ℤ) - AddMonoidAlgebra.single 0 1) :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ _)
  have he := action_mul P
    (AddMonoidAlgebra.single (v i) (1 : ℤ) - AddMonoidAlgebra.single 0 1) ξ
  rw [hprod, action_difference] at he
  intro z
  change laurentAction P.coeff (periodDifference ξ (v i)) z = 0
  rw [← he]
  exact hann z

theorem difference_product_halfplane_zero (f : Configuration ℤ)
    (m : ℕ) (v : Fin m → Lattice) (u : Lattice) (hu : u ≠ 0)
    (htransverse : ∀ i, latticeDot u (v i) ≠ 0)
    (hann : Annihilates (differenceFactors m v) f)
    (hzero : ∀ z ∈ strictHalf u, f z = 0) : f = 0 := by
  apply product_half_zero Finset.univ v f u _ hann hzero
  intro i _
  simpa [latticeDot, mul_comm] using htransverse i

theorem same_halfplane_same_perpendicular_factor (ξ x y : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) (hy : y ∈ OrbitClosure ξ)
    (m : ℕ) (v : Fin m → Lattice) (i₀ : Fin m)
    (hann : Annihilates (differenceFactors m v) ξ)
    (u : Lattice) (hu : u ≠ 0) (hperp : latticeDot u (v i₀) = 0)
    (htransverse : ∀ i, i ≠ i₀ → latticeDot u (v i) ≠ 0)
    (hagree : AgreesOn x y (strictHalf (-u))) :
    periodDifference x (v i₀) = periodDifference y (v i₀) := by
  classical
  let P : AddMonoidAlgebra ℤ Lattice := ∏ j ∈ (Finset.univ.erase i₀),
    (AddMonoidAlgebra.single (v j) (1 : ℤ) - AddMonoidAlgebra.single 0 1)
  have hxann := factor_image_remaining_annihilator x m v
    (orbitClosure_annihilator_inheritance ξ x hx _ hann) i₀
  have hyann := factor_image_remaining_annihilator y m v
    (orbitClosure_annihilator_inheritance ξ y hy _ hann) i₀
  have hfann : Annihilates P.coeff (periodDifference x (v i₀) - periodDifference y (v i₀)) := by
    intro z
    rw [action_sub_field]
    change laurentAction P.coeff (periodDifference x (v i₀)) z -
      laurentAction P.coeff (periodDifference y (v i₀)) z = 0
    exact sub_eq_zero.mpr ((hxann z).trans (hyann z).symm)
  have htrans : ∀ j ∈ Finset.univ.erase i₀, latticeDot (v j) (-u) ≠ 0 := by
    intro j hj
    rw [dot_neg_right, neg_ne_zero]
    simpa [latticeDot, mul_comm] using htransverse j (Finset.mem_erase.mp hj).1
  have hperp' : latticeDot (v i₀) (-u) = 0 := by
    rw [dot_neg_right]
    simpa [latticeDot, mul_comm] using congrArg Neg.neg hperp
  have hzero : ∀ z ∈ strictHalf (-u),
      (periodDifference x (v i₀) - periodDifference y (v i₀)) z = 0 := by
    intro z hz
    have hz' : z - v i₀ ∈ strictHalf (-u) := by
      change latticeDot (z - v i₀) (-u) < 0
      rw [dot_sub, hperp', sub_zero]
      exact hz
    simp only [Pi.sub_apply, periodDifference, hagree z hz, hagree (z - v i₀) hz', sub_self]
  have he := product_half_zero (Finset.univ.erase i₀) v _ (-u) htrans hfann hzero
  exact sub_eq_zero.mp he

end
end ConvexNivat.ExternalDynamicsHelpers
