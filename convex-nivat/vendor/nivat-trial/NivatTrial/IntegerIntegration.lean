import NivatTrial.Divisibility
import NivatTrial.OneSidedRecurrence

/-!
# Integral primitives of a periodic lattice difference

For independent lattice directions `h` and `k`, every integer-valued
`k`-periodic field is the `h`-difference of another `k`-periodic field.
The primitive is defined using the integral coordinates of the half-open
fundamental parallelogram, so no boundedness of the field is required.
-/

namespace NivatTrial.IntegerIntegration

open NivatTrial.Geometry NivatTrial.Divisibility NivatTrial.Periodicity
open NivatTrial.PeriodicDifference

open scoped Classical

noncomputable section

/-- Sum a doubly infinite sequence from zero to an integer endpoint. -/
def integerAntidifference (s : ℤ → ℤ) (n : ℤ) : ℤ :=
  if 0 ≤ n then ∑ i ∈ Finset.Ico 0 n, s i
  else -(∑ i ∈ Finset.Ico n 0, s i)

theorem integerAntidifference_step (s : ℤ → ℤ) (n : ℤ) :
    integerAntidifference s (n + 1) - integerAntidifference s n = s n := by
  by_cases hn : 0 ≤ n
  · have hn1 : 0 ≤ n + 1 := by omega
    simp only [integerAntidifference, if_pos hn, if_pos hn1]
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hn s]
    ring
  · by_cases hn1 : 0 ≤ n + 1
    · have heq : n = -1 := by omega
      subst n
      have hset : Finset.Ico (-1 : ℤ) 0 = {-1} := by
        ext i
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      simp [integerAntidifference, hset]
    · simp only [integerAntidifference, if_neg hn, if_neg hn1]
      have hset : Finset.Ico n 0 = insert n (Finset.Ico (n + 1) 0) :=
        (Finset.insert_Ico_add_one_left_eq_Ico (by omega : n < 0)).symm
      rw [hset, Finset.sum_insert]
      · ring
      · simp

def longitudinalIndex (h k z : Lattice) : ℤ :=
  Int.floor (longitudinalCoordinate h k z)

def transverseIndex (h k z : Lattice) : ℤ :=
  Int.floor (transverseCoordinate h k z)

theorem longitudinalIndex_add (h k z : Lattice) (hdet : Geometry.det h k ≠ 0)
    (m n : ℤ) :
    longitudinalIndex h k (z + m • h + n • k) = longitudinalIndex h k z + m := by
  unfold longitudinalIndex
  rw [longitudinalCoordinate_add_lattice h k z hdet]
  exact Int.floor_add_intCast _ _

theorem transverseIndex_add (h k z : Lattice) (hdet : Geometry.det h k ≠ 0)
    (m n : ℤ) :
    transverseIndex h k (z + m • h + n • k) = transverseIndex h k z + n := by
  unfold transverseIndex
  rw [transverseCoordinate_add_lattice h k z hdet]
  exact Int.floor_add_intCast _ _

theorem representative_add (h k z : Lattice) (hdet : Geometry.det h k ≠ 0)
    (m n : ℤ) :
    fundamentalRepresentative h k (z + m • h + n • k) =
      fundamentalRepresentative h k z := by
  simp only [fundamentalRepresentative]
  rw [show Int.floor (longitudinalCoordinate h k (z + m • h + n • k)) =
      longitudinalIndex h k z + m by exact longitudinalIndex_add h k z hdet m n,
    show Int.floor (transverseCoordinate h k (z + m • h + n • k)) =
      transverseIndex h k z + n by exact transverseIndex_add h k z hdet m n]
  unfold longitudinalIndex transverseIndex
  simp only [add_zsmul]
  abel

theorem index_representative (h k z : Lattice) (hdet : Geometry.det h k ≠ 0) :
    longitudinalIndex h k (fundamentalRepresentative h k z) = 0 := by
  have hm := longitudinalIndex_add h k (fundamentalRepresentative h k z) hdet
    (longitudinalIndex h k z) (transverseIndex h k z)
  have hr : z = fundamentalRepresentative h k z +
      longitudinalIndex h k z • h + transverseIndex h k z • k :=
    fundamentalRepresentative_decomposition h k z
  rw [← hr] at hm
  omega

theorem representative_decomposition (h k z : Lattice) :
    z = fundamentalRepresentative h k z +
      longitudinalIndex h k z • h + transverseIndex h k z • k :=
  fundamentalRepresentative_decomposition h k z

/-- The canonical integer-valued primitive, normalized to zero at each
fundamental representative. -/
def periodicPrimitive (h k : Lattice) (f : Lattice → ℤ) (z : Lattice) : ℤ :=
  integerAntidifference
    (fun m => f (fundamentalRepresentative h k z + m • h))
    (longitudinalIndex h k z)

theorem periodicPrimitive_period (h k : Lattice) (hdet : Geometry.det h k ≠ 0)
    (f : Lattice → ℤ) : IsPeriod (periodicPrimitive h k f) k := by
  intro z
  have hr := representative_add h k z hdet 0 1
  have hm := longitudinalIndex_add h k z hdet 0 1
  simp only [zero_zsmul, one_zsmul, add_zero] at hr hm
  simp only [periodicPrimitive, hr, hm]

theorem periodicPrimitive_increment (h k : Lattice) (hdet : Geometry.det h k ≠ 0)
    (f : Lattice → ℤ) (hf : IsPeriod f k) :
    increment (periodicPrimitive h k f) h = f := by
  funext z
  have hr := representative_add h k z hdet 1 0
  have hm := longitudinalIndex_add h k z hdet 1 0
  simp only [one_zsmul, zero_zsmul, add_zero] at hr hm
  have hz := representative_decomposition h k z
  have hval : f (fundamentalRepresentative h k z + longitudinalIndex h k z • h) = f z := by
    conv_rhs => rw [hz]
    simpa only [add_assoc] using
      ((hf.zsmul (transverseIndex h k z))
        (fundamentalRepresentative h k z + longitudinalIndex h k z • h)).symm
  simp only [increment, periodicPrimitive, hr, hm]
  rw [integerAntidifference_step, hval]

theorem exists_periodic_integral (h k : Lattice) (hdet : Geometry.det h k ≠ 0)
    (f : Lattice → ℤ) (hf : IsPeriod f k) :
    ∃ F : Lattice → ℤ, IsPeriod F k ∧ increment F h = f := by
  exact ⟨periodicPrimitive h k f, periodicPrimitive_period h k hdet f,
    periodicPrimitive_increment h k hdet f hf⟩

end

end NivatTrial.IntegerIntegration
