import ConvexNivat.ReductionDefinitions
import Nivat.Algebra.ProductDifferences

namespace ConvexNivat
open scoped BigOperators
open Nivat.Algebra

/-- Source 8.4(b), decomposition for every integer-valued configuration killed
by that product. Components may be unbounded; no finite-range hypothesis on η.
Same Kari–Szabados [11] provenance. -/
theorem external8_4b_decomposition_obligation (m : ℕ) (h : Fin m → Lattice)
    (hnonzero : ∀ i, h i ≠ 0)
    (hpairwise : Pairwise (fun i j => Nonparallel (h i) (h j)))
    (η : Configuration ℤ) (hann : ∀ z, mixedDifference h Finset.univ η z = 0) :
    ∃ component : Fin m → Configuration ℤ,
      (∀ i, HasPeriod (component i) (h i)) ∧ ∀ z, η z = ∑ i, component i z := by
  classical
  have hlift (u v : Lattice) (hd : Nonparallel v u) (b : Configuration ℤ)
      (hb : HasPeriod b v) :
      ∃ a : Configuration ℤ, HasPeriod a v ∧ Nivat.difference u a = b := by
    classical
    let integrate (f : ℤ → ℤ) (n : ℤ) : ℤ :=
      match n with
      | .ofNat n => ∑ i ∈ Finset.range n, f (i : ℤ)
      | .negSucc n => -(∑ i ∈ Finset.range (n + 1), f (-(i + 1 : ℤ)))
    have hint (f : ℤ → ℤ) (n : ℤ) : integrate f (n + 1) = integrate f n + f n := by
      cases n with
      | ofNat n =>
        change (∑ i ∈ Finset.range (n + 1), f (i : ℤ)) =
          (∑ i ∈ Finset.range n, f (i : ℤ)) + f n
        exact Finset.sum_range_succ _ _
      | negSucc n =>
        cases n with
        | zero =>
          change (0 : ℤ) = -(∑ i ∈ Finset.range 1, f (-(i + 1 : ℤ))) + f (-1)
          simp
        | succ n =>
          change -(∑ i ∈ Finset.range (n + 1), f (-(i + 1 : ℤ))) =
            -(∑ i ∈ Finset.range ((n + 1) + 1), f (-(i + 1 : ℤ))) + f (.negSucc (n + 1))
          rw [Finset.sum_range_succ _ (n + 1)]
          have he : (Int.negSucc (n + 1)) = -((n + 1 : ℕ) + 1 : ℤ) := by omega
          rw [he]
          abel
    let q (z : Lattice) : ℤ := det v z / det v u
    have hqu (z : Lattice) : q (z + u) = q z + 1 := by
      have hdet : det v (z + u) = det v z + det v u := by dsimp [det]; ring
      dsimp only [q]
      rw [hdet, Int.add_ediv_of_dvd_right (dvd_refl (det v u)), Int.ediv_self hd]
    have hqv (z : Lattice) : q (z + v) = q z := by
      have hdet : det v (z + v) = det v z := by dsimp [det]; ring
      simp only [q, hdet]
    let origin (z : Lattice) := z - q z • u
    have horiginu (z : Lattice) : origin (z + u) = origin z := by
      dsimp only [origin]
      rw [hqu, add_smul, one_smul]
      abel
    have horiginv (z : Lattice) : origin (z + v) = origin z + v := by
      dsimp only [origin]
      rw [hqv]
      abel
    let a (z : Lattice) := integrate (fun t => b (origin z + t • u)) (q z)
    refine ⟨a, ?_, ?_⟩
    · intro z
      dsimp only [a]
      rw [hqv, horiginv]
      have he : (fun t : ℤ => b (origin z + v + t • u)) =
          (fun t : ℤ => b (origin z + t • u)) := by
        funext t
        rw [add_right_comm, hb]
      rw [he]
    · funext z
      change a (z + u) - a z = b z
      dsimp only [a]
      rw [hqu, horiginu, hint (fun t => b (origin z + t • u)) (q z)]
      simp [origin]
  have hdiff (u : Lattice) (η : Configuration ℤ) :
      coefficientAct (AddMonoidAlgebra.single u 1 - 1) η = Nivat.difference u η := by
    funext z
    simp [coefficientAct_apply, Nivat.difference_apply, Finsupp.sum_sub_index,
      sub_mul]
    change (Finsupp.single 0 (1 : ℤ)).sum (fun h a => a * η (z + h)) = η z
    simp
  have hexpand {ι : Type} [DecidableEq ι] (h : ι → Lattice) (I : Finset ι)
      (c : Configuration ℤ) (z : Lattice) :
      coefficientAct (∏ i ∈ I, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)) c z =
        mixedDifference h I c z := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_add, coefficientAct_finset_sum]
    simp only [Finset.sum_apply, mixedDifference]
    apply Finset.sum_congr rfl
    intro C hC
    have hCI : C ⊆ I := Finset.mem_powerset.mp hC
    have hprod : (∏ i ∈ C, AddMonoidAlgebra.single (h i) (1 : ℤ)) =
        AddMonoidAlgebra.single (∑ i ∈ C, h i) (1 : ℤ) := by
      simp [AddMonoidAlgebra.prod_single]
    rw [hprod, Finset.prod_const, Finset.card_sdiff_of_subset hCI]
    have hneg (n : ℕ) : (-1 : Nivat.Algebra.IntegerLaurent) ^ n =
        AddMonoidAlgebra.single 0 ((-1 : ℤ) ^ n) := by
      change (-(AddMonoidAlgebra.single 0 (1 : ℤ))) ^ n = _
      rw [← AddMonoidAlgebra.single_neg, AddMonoidAlgebra.single_pow, nsmul_zero]
    rw [hneg]
    simp [coefficientAct_single, Nivat.shift]
  have hdecomp : ∀ (n : ℕ) (g : Fin n → Lattice),
      Pairwise (fun i j => Nonparallel (g i) (g j)) →
      ∀ c : Configuration ℤ,
        coefficientAct (∏ i, (AddMonoidAlgebra.single (g i) (1 : ℤ) - 1)) c = 0 →
        ∃ a : Fin n → Configuration ℤ,
          (∀ i, HasPeriod (a i) (g i)) ∧ ∀ z, c z = ∑ i, a i z := by
    intro n
    induction n with
    | zero =>
      intro g hg c hc
      have hc0 : c = 0 := by simpa using hc
      refine ⟨Fin.elim0, by simp, ?_⟩
      intro z
      simp [hc0]
    | succ n ih =>
      intro g hg c hc
      let u := g 0
      let t : Fin n → Lattice := fun i => g i.succ
      have ht : Pairwise (fun i j => Nonparallel (t i) (t j)) := by
        intro i j hij
        exact hg (fun he => hij (Fin.succ_injective n he))
      have htail : coefficientAct
          (∏ i, (AddMonoidAlgebra.single (t i) (1 : ℤ) - 1))
          (Nivat.difference u c) = 0 := by
        rw [Fin.prod_univ_succ, mul_comm, coefficientAct_mul, hdiff] at hc
        exact hc
      obtain ⟨b, hb, hbsum⟩ := ih t ht (Nivat.difference u c) htail
      have hlifts (i : Fin n) : ∃ a : Configuration ℤ,
          HasPeriod a (t i) ∧ Nivat.difference u a = b i := by
        exact hlift u (t i) (hg (Fin.succ_ne_zero i)) (b i) (hb i)
      choose a ha hda using hlifts
      let first : Configuration ℤ := fun z => c z - ∑ i, a i z
      refine ⟨Fin.cons first a, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro z
          change c (z + u) - ∑ i, a i (z + u) = c z - ∑ i, a i z
          have he := hbsum z
          have hrel (i : Fin n) : a i (z + u) - a i z = b i z := congrFun (hda i) z
          change c (z + u) - c z = ∑ i, b i z at he
          have hsum : (∑ i, a i (z + u)) - (∑ i, a i z) = ∑ i, b i z := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun i _ => hrel i)
          omega
        · exact ha j
      · intro z
        rw [Fin.sum_univ_succ]
        simp [first]
  have hη : coefficientAct
      (∏ i : Fin m, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)) η = 0 := by
    funext z
    have he : coefficientAct
        (∏ i : Fin m, (AddMonoidAlgebra.single (h i) (1 : ℤ) - 1)) η z =
        mixedDifference h Finset.univ η z := hexpand (ι := Fin m) h Finset.univ η z
    exact Eq.trans he (hann z)
  exact hdecomp m h hpairwise η hη

end ConvexNivat
