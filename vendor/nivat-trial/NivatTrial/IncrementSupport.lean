import NivatTrial.OneSidedRecurrence
import NivatTrial.RegionGeometry

/-! Actual finite windows of iterated differences and isolation of a periodic summand. -/

namespace NivatTrial.IncrementSupport

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.RegionGeometry
open scoped Classical

noncomputable section

def offsets : List Lattice → Finset Lattice
  | [] => {0}
  | h::hs => offsets hs ∪ (offsets hs).image (fun z => h+z)

variable {A : Type*} [AddCommGroup A]

theorem iteratedIncrement_congr_at (hs : List Lattice) (f g : Lattice → A)
    (z : Lattice) (hfg : ∀ e ∈ offsets hs, f (z+e)=g (z+e)) :
    iteratedIncrement hs f z = iteratedIncrement hs g z := by
  induction hs generalizing z with
  | nil => simpa using hfg 0 (by simp [offsets])
  | cons h hs ih =>
    change iteratedIncrement hs f (z+h)-iteratedIncrement hs f z =
      iteratedIncrement hs g (z+h)-iteratedIncrement hs g z
    congr 1
    · apply ih
      intro e he
      have hp := hfg (h+e) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,he,rfl⟩))
      simpa [add_assoc] using hp
    · exact ih z (fun e he => hfg e (Finset.mem_union_left _ he))

theorem zero_on_erosion (hs : List Lattice) (f g : Lattice → A) (R : Set Lattice)
    (hfg : ∀ z ∈ R, f z=g z) (hg : iteratedIncrement hs g=0) :
    ∀ z ∈ erosion R (offsets hs), iteratedIncrement hs f z=0 := by
  intro z hz
  rw [iteratedIncrement_congr_at hs f g z (fun e he => hfg _ (hz e he)), hg]
  rfl

variable {ι : Type*} [Fintype ι]

def cofactorDirections (H : ι → Lattice) (i : ι) : List Lattice :=
  (Finset.univ.erase i).toList.map H

theorem mem_cofactorDirections (H : ι → Lattice) (i j : ι) (hji : j ≠ i) :
    H j ∈ cofactorDirections H i := by
  simp only [cofactorDirections, List.mem_map, Finset.mem_toList]
  exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, rfl⟩

theorem cofactor_isolates (F : ι → Lattice → A) (H : ι → Lattice)
    (hp : ∀ i, IsPeriod (F i) (H i)) (i : ι) :
    iteratedIncrement (cofactorDirections H i) (∑ j, F j) =
      iteratedIncrement (cofactorDirections H i) (F i) := by
  rw [iteratedIncrement_sum]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact factor_kills_of_mem _ (H j) (mem_cofactorDirections H i j hji) (F j) (hp j)
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem cofactor_kills_background [Nontrivial ι] (H : ι → Lattice)
    (f : Lattice → A) (hp : ∀ i, IsPeriod f (H i)) (i : ι) :
    iteratedIncrement (cofactorDirections H i) f=0 := by
  obtain ⟨j,hji⟩ := exists_ne i
  exact factor_kills_of_mem _ (H j) (mem_cofactorDirections H i j hji) f (hp j)

theorem cofactor_transverse (H : ι → Lattice) (i : ι) (π : Lattice →+ ℤ)
    (ht : ∀ j, j ≠ i → π (H j) ≠ 0) :
    ∀ d ∈ cofactorDirections H i, π d ≠ 0 := by
  intro d hd
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
  exact ht j (Finset.mem_erase.mp (Finset.mem_toList.mp hj)).1

theorem decomposition_annihilator (F : ι → Lattice → A) (H : ι → Lattice)
    (hp : ∀ i, IsPeriod (F i) (H i)) :
    iteratedIncrement (Finset.univ.toList.map H) (∑ i,F i)=0 := by
  rw [iteratedIncrement_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply factor_kills_of_mem _ (H i) _ (F i) (hp i)
  exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩

theorem iteratedIncrement_passes_to_languageHull (hs : List Lattice)
    (f g : Lattice → A) (hg : g ∈ NivatTrial.Dynamics.languageHull f)
    (hf : iteratedIncrement hs f=0) : iteratedIncrement hs g=0 := by
  funext z
  obtain ⟨u,hu⟩ := hg ((offsets hs).image (fun e => z+e))
  have heq := iteratedIncrement_congr_at hs g (fun x => f (x+u)) z (by
    intro e he
    have hh := hu (z+e) (Finset.mem_image.mpr ⟨e,he,rfl⟩)
    simpa [add_comm] using hh.symm)
  rw [iteratedIncrement_translate, hf] at heq
  exact heq

end
end NivatTrial.IncrementSupport
