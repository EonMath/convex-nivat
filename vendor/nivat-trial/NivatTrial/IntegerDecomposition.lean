import NivatTrial.IntegerIntegration

/-!
# Decomposition of an integer field annihilated by independent differences

An integral primitive of each periodic summand allows the last difference
to be removed. Induction over the list of directions then gives an actual
integer-valued periodic decomposition. No finite-range assumption occurs.
-/

namespace NivatTrial.IntegerDecomposition

open NivatTrial.Geometry NivatTrial.Periodicity NivatTrial.PeriodicDifference
open NivatTrial.OneSidedRecurrence NivatTrial.IntegerIntegration

open scoped Classical

noncomputable section

private theorem increment_add (f g : Lattice → ℤ) (h : Lattice) :
    increment (f + g) h = increment f h + increment g h := by
  funext z
  simp only [increment, Pi.add_apply]
  abel

private theorem increment_list_sum (hs : List Lattice) (F : Lattice → Lattice → ℤ)
    (h : Lattice) :
    increment (hs.map F).sum h = (hs.map (fun k => increment (F k) h)).sum := by
  induction hs with
  | nil => funext z; simp [increment]
  | cons k hs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [increment_add, ih]

private theorem list_sum_toList {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → Lattice → ℤ) :
    (s.toList.map F).sum = ∑ i ∈ s, F i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha]

/-- Fixed-direction binomial part of Kari--Szabados Lemma 15. -/
theorem decompose_list (hs : List Lattice)
    (hind : hs.Pairwise (fun h k => Geometry.det h k ≠ 0))
    (f : Lattice → ℤ) (hann : iteratedIncrement hs f = 0) :
    ∃ F : Lattice → Lattice → ℤ,
      (∀ k ∈ hs, IsPeriod (F k) k) ∧ (hs.map F).sum = f := by
  induction hs generalizing f with
  | nil =>
    simp only [iteratedIncrement_nil] at hann
    exact ⟨fun _ _ => 0, by simp, by simpa using hann.symm⟩
  | cons h hs ih =>
    obtain ⟨htrans, hpair⟩ := List.pairwise_cons.mp hind
    have htail : iteratedIncrement hs (increment f h) = 0 := by
      rw [iteratedIncrement_commute]
      exact hann
    obtain ⟨G, hGperiod, hGsum⟩ := ih hpair (increment f h) htail
    have hne (k : Lattice) (hk : k ∈ hs) : k ≠ h := by
      intro heq
      subst k
      exact htrans h hk (Geometry.det_self h)
    have hint (k : Lattice) (hk : k ∈ hs) :
        ∃ H : Lattice → ℤ, IsPeriod H k ∧ increment H h = G k :=
      exists_periodic_integral h k (htrans k hk) (G k) (hGperiod k hk)
    let H : Lattice → Lattice → ℤ :=
      fun k => if hk : k ∈ hs then Classical.choose (hint k hk) else 0
    have hHperiod (k : Lattice) (hk : k ∈ hs) : IsPeriod (H k) k := by
      simpa only [H, dif_pos hk] using (Classical.choose_spec (hint k hk)).1
    have hHincrement (k : Lattice) (hk : k ∈ hs) :
        increment (H k) h = G k := by
      simpa only [H, dif_pos hk] using (Classical.choose_spec (hint k hk)).2
    have hsumdiff : increment (hs.map H).sum h = increment f h := by
      rw [increment_list_sum]
      have heq : hs.map (fun k => increment (H k) h) = hs.map G := by
        apply List.map_congr_left
        intro k hk
        exact hHincrement k hk
      rw [heq, hGsum]
    have hrest : IsPeriod (f - (hs.map H).sum) h := by
      intro z
      have heq := congrFun hsumdiff z
      simp only [increment, Pi.sub_apply] at heq ⊢
      omega
    let F : Lattice → Lattice → ℤ :=
      fun k => if k = h then f - (hs.map H).sum else H k
    refine ⟨F, ?_, ?_⟩
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simpa only [F, ↓reduceIte] using hrest
      · simpa only [F, if_neg (hne k hk)] using hHperiod k hk
    · have hmap : hs.map F = hs.map H := by
        apply List.map_congr_left
        intro k hk
        simp only [F, if_neg (hne k hk)]
      simp only [List.map_cons, List.sum_cons, hmap, F, ↓reduceIte]
      abel

/-- The finite-index form used by `ExternalInputs.KariSzabados`. -/
theorem product_decomposition (n : ℕ) (h : Fin n → Lattice)
    (_hnonzero : ∀ i, h i ≠ 0)
    (hind : ∀ i j, i ≠ j → Geometry.det (h i) (h j) ≠ 0)
    (f : Lattice → ℤ)
    (hann : iteratedIncrement (Finset.univ.toList.map h) f = 0) :
    ∃ F : Fin n → Lattice → ℤ,
      (∀ i, IsPeriod (F i) (h i)) ∧ (∑ i, F i) = f := by
  classical
  have hp : (Finset.univ.toList.map h).Pairwise
      (fun v w => Geometry.det v w ≠ 0) := by
    have hp0 : (Finset.univ.toList : List (Fin n)).Pairwise
        (fun i j => Geometry.det (h i) (h j) ≠ 0) :=
      (Finset.nodup_toList (Finset.univ : Finset (Fin n))).pairwise_of_forall_ne
        (fun i _ j _ hij => hind i j hij)
    exact hp0.map h (fun _ _ hij => hij)
  obtain ⟨G, hperiod, hsum⟩ := decompose_list _ hp f hann
  refine ⟨fun i => G (h i), ?_, ?_⟩
  · intro i
    exact hperiod (h i) (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr (Finset.mem_univ i), rfl⟩)
  · have heq : (Finset.univ.toList.map h).map G =
        Finset.univ.toList.map (fun i => G (h i)) := by
      simp only [List.map_map, Function.comp_def]
    rw [← hsum, heq]
    exact (list_sum_toList Finset.univ (fun i => G (h i))).symm

end

end NivatTrial.IntegerDecomposition
