import ConvexNivat.Geometry.Definitions
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace ConvexNivat
open scoped BigOperators Pointwise

private def latticeEmbedding : Lattice →+ RealPlane where
  toFun := embed
  map_zero' := by ext <;> simp [embed]
  map_add' a b := by ext <;> simp [embed]

private theorem embedding_sum {ι : Type*} (s : Finset ι) (f : ι → Lattice) :
    embed (∑ i ∈ s, f i) = ∑ i ∈ s, embed (f i) :=
  map_sum latticeEmbedding f s

private theorem embedding_nsmul (n : ℕ) (a : Lattice) :
    embed (n • a) = (n : ℝ) • embed a := by
  ext <;> simp [embed, nsmul_eq_mul]

namespace IntegralZonotope

private def parameterMap {m : ℕ} (Z : IntegralZonotope m) :
    (Fin m → ℝ) →ₗ[ℝ] RealPlane where
  toFun t := ∑ i, t i • embed (Z.direction i)
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [mul_smul, Finset.smul_sum]

private theorem selector_sum {m : ℕ} (Z : IntegralZonotope m) (I : Finset (Fin m)) :
    (∑ i : Fin m, (if i ∈ I then (Z.degree i : ℝ) else 0) • embed (Z.direction i)) =
      embed (∑ i ∈ I, Z.endpoint i) := by
  rw [embedding_sum]
  simp only [endpoint, embedding_nsmul, ite_smul, zero_smul]
  calc
    (∑ i : Fin m, if i ∈ I then (Z.degree i : ℝ) • embed (Z.direction i) else 0) =
        ∑ i ∈ I, if i ∈ I then (Z.degree i : ℝ) • embed (Z.direction i) else 0 :=
      (Finset.sum_subset (Finset.subset_univ I) (by intro i _ hi; simp [hi])).symm
    _ = ∑ i ∈ I, (Z.degree i : ℝ) • embed (Z.direction i) :=
      Finset.sum_congr rfl (by intro i hi; simp [hi])

theorem zero_mem {m : ℕ} (Z : IntegralZonotope m) :
    (0 : RealPlane) ∈ Z.carrier := by
  refine ⟨fun _ => 0, fun i => ⟨le_rfl, Nat.cast_nonneg _⟩, ?_⟩
  simp

theorem endpoint_mem {m : ℕ} (Z : IntegralZonotope m) (i : Fin m) :
    embed (Z.endpoint i) ∈ Z.carrier := by
  refine ⟨fun j => if j = i then (Z.degree j : ℝ) else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs <;> constructor <;> first | exact le_rfl | positivity
  · simp only [endpoint, embedding_nsmul]
    simp

theorem subsetSum_mem {m : ℕ} (Z : IntegralZonotope m) {q : Lattice}
    (hq : q ∈ Z.subsetSums) : embed q ∈ Z.carrier := by
  classical
  obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
  refine ⟨fun i => if i ∈ I then (Z.degree i : ℝ) else 0, ?_, (selector_sum Z I).symm⟩
  intro i
  dsimp only
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

private theorem carrier_image {m : ℕ} (Z : IntegralZonotope m) :
    Z.carrier = parameterMap Z '' (Set.univ.pi fun i => Set.Icc (0 : ℝ) (Z.degree i)) := by
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, fun i _ => ht i, hx.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, fun i => ht i (Set.mem_univ _), rfl⟩

private theorem corner_image {m : ℕ} (Z : IntegralZonotope m) :
    parameterMap Z '' (Set.univ.pi fun i => ({0, (Z.degree i : ℝ)} : Set ℝ)) =
      embed '' (Z.subsetSums : Set Lattice) := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    let I := Finset.univ.filter fun i => t i = (Z.degree i : ℝ)
    refine ⟨∑ i ∈ I, Z.endpoint i, Finset.mem_image.mpr ⟨I, by simp, rfl⟩, ?_⟩
    rw [← selector_sum Z I]
    apply Finset.sum_congr rfl
    intro i _
    have hi := ht i (Set.mem_univ _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with hi | hi
    · simp [hi, (Nat.cast_pos.mpr (Z.degree_pos i) : (0 : ℝ) < Z.degree i).ne]
    · simp [hi]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨fun i => if i ∈ I then (Z.degree i : ℝ) else 0, ?_, selector_sum Z I⟩
    intro i _
    dsimp only
    split_ifs <;> simp

/-- A finite lattice generating set for the zonotope, without claiming all
subset sums are extreme vertices. -/
theorem carrier_eq_hull_subsetSums {m : ℕ} (Z : IntegralZonotope m) :
    Z.carrier = windowHull Z.subsetSums := by
  have hbox : convexHull ℝ (Set.univ.pi fun i => ({0, (Z.degree i : ℝ)} : Set ℝ)) =
      Set.univ.pi (fun i => Set.Icc (0 : ℝ) (Z.degree i)) := by
    rw [convexHull_pi]
    congr 1
    funext i
    rw [convexHull_pair, segment_eq_Icc (Nat.cast_nonneg _)]
  rw [carrier_image, ← hbox, LinearMap.image_convexHull, corner_image]
  rfl

theorem carrier_convex {m : ℕ} (Z : IntegralZonotope m) :
    Convex ℝ Z.carrier := by
  rw [carrier_eq_hull_subsetSums]
  exact convex_convexHull ℝ _

theorem carrier_compact {m : ℕ} (Z : IntegralZonotope m) :
    IsCompact Z.carrier := by
  rw [carrier_eq_hull_subsetSums]
  exact ((Z.subsetSums.finite_toSet).image embed).isCompact_convexHull ℝ

theorem subsetSums_nonempty {m : ℕ} (Z : IntegralZonotope m) :
    Z.subsetSums.Nonempty := by
  classical
  exact ⟨0, Finset.mem_image.mpr ⟨∅, by simp, by simp⟩⟩

private def twoDirectionMap (u v : RealPlane) : RealPlane →ₗ[ℝ] RealPlane where
  toFun x := x.1 • u + x.2 • v
  map_add' x y := by simp [add_smul, add_add_add_comm]
  map_smul' c x := by simp [smul_add, smul_smul]

private theorem twoDirectionMap_surjective (u v : RealPlane)
    (hd : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    Function.Surjective (twoDirectionMap u v) := by
  intro x
  refine ⟨((x.1 * v.2 - x.2 * v.1) / (u.1 * v.2 - u.2 * v.1),
    (u.1 * x.2 - u.2 * x.1) / (u.1 * v.2 - u.2 * v.1)), ?_⟩
  ext <;> dsimp [twoDirectionMap]
  · calc
      _ = (x.1 * (u.1 * v.2 - u.2 * v.1)) / (u.1 * v.2 - u.2 * v.1) := by ring
      _ = x.1 := mul_div_cancel_right₀ _ hd
  · calc
      _ = (x.2 * (u.1 * v.2 - u.2 * v.1)) / (u.1 * v.2 - u.2 * v.1) := by ring
      _ = x.2 := mul_div_cancel_right₀ _ hd

private theorem parameterMap_single {m : ℕ} (Z : IntegralZonotope m)
    (i : Fin m) (a : ℝ) : parameterMap Z (Pi.single i a) = a • embed (Z.direction i) := by
  classical
  simp [parameterMap, Pi.single_apply, ite_smul]

/-- Nonparallel positive segments give genuine two-dimensional interior. -/
theorem interior_nonempty {m : ℕ} (Z : IntegralZonotope m) (hm : 2 ≤ m)
    (hdir : Nonparallel (Z.firstDirection hm) (Z.secondDirection hm)) :
    (interior Z.carrier).Nonempty := by
  classical
  let i₀ : Fin m := ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hm⟩
  let i₁ : Fin m := ⟨1, Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hm⟩
  have hij : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i₀, i₁] at hv
  let u := embed (Z.direction i₀)
  let v := embed (Z.direction i₁)
  have hd : u.1 * v.2 - u.2 * v.1 ≠ 0 := by
    have hh := hdir
    unfold Nonparallel det at hh
    dsimp [u, v, embed]
    dsimp [firstDirection, secondDirection] at hh
    exact_mod_cast hh
  let f := twoDirectionMap u v
  let U := Set.Ioo (0 : ℝ) (Z.degree i₀) ×ˢ Set.Ioo (0 : ℝ) (Z.degree i₁)
  have hopen : IsOpen (f '' U) :=
    (f.isOpenMap_of_finiteDimensional (twoDirectionMap_surjective u v hd)) _
      (isOpen_Ioo.prod isOpen_Ioo)
  have hnonempty : (f '' U).Nonempty :=
    ((Set.nonempty_Ioo.mpr (Nat.cast_pos.mpr (Z.degree_pos i₀))).prod
      (Set.nonempty_Ioo.mpr (Nat.cast_pos.mpr (Z.degree_pos i₁)))).image f
  have hsubset : f '' U ⊆ Z.carrier := by
    rintro x ⟨t, ⟨ha, hb⟩, rfl⟩
    refine ⟨Pi.single i₀ t.1 + Pi.single i₁ t.2, ?_, ?_⟩
    · intro i
      by_cases h₀ : i = i₀
      · subst i
        simpa [Pi.single_apply, hij] using And.intro ha.1.le ha.2.le
      · by_cases h₁ : i = i₁
        · subst i
          simpa [Pi.single_apply, hij.symm] using And.intro hb.1.le hb.2.le
        · simp [h₀, h₁, Nat.cast_nonneg]
    · change f t = parameterMap Z (Pi.single i₀ t.1 + Pi.single i₁ t.2)
      rw [map_add, parameterMap_single, parameterMap_single]
      rfl
  exact hnonempty.mono (interior_maximal hsubset hopen)

theorem erosion_finite {m : ℕ} (Z : IntegralZonotope m) {S : Finset Lattice}
    (hS : LatticeConvex S) : (erosion Z.carrier S).Finite := by
  apply S.finite_toSet.subset
  intro r hr
  apply (hS r).mp
  simpa using hr 0 (Z.zero_mem)

end IntegralZonotope
end ConvexNivat
