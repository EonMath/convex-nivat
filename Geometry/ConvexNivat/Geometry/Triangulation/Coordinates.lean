import ConvexNivat.Geometry.Triangulation.Definitions
import Mathlib.LinearAlgebra.AffineSpace.Independent

namespace ConvexNivat.PolygonTriangulation

open scoped BigOperators

/-- PT00: the existing real determinant, with the integer convention preserved. -/
theorem real_determinant_and_embedding_algebra :
    (∀ x y z : RealPlane, realDet (x + y) z = realDet x z + realDet y z) ∧
    (∀ x y z : RealPlane, realDet x (y + z) = realDet x y + realDet x z) ∧
    (∀ (a : ℝ) (x y : RealPlane), realDet (a • x) y = a * realDet x y) ∧
    (∀ (a : ℝ) (x y : RealPlane), realDet x (a • y) = a * realDet x y) ∧
    (∀ x : RealPlane, realDet x x = 0) ∧
    (∀ x y : RealPlane, realDet x y = -realDet y x) ∧
    (∀ u v : Lattice, realDet (embed u) (embed v) = (det u v : ℝ)) ∧
    (∀ u v w : RealPlane,
      realDet (v - u) (w - u) = realDet v w - realDet u w + realDet u v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  all_goals simp only [realDet, embed, det, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul,
    Int.cast_sub, Int.cast_mul, Prod.smul_fst, Prod.smul_snd]
  all_goals ring

private lemma real_delta (T : LatticeTriangle) :
    realDet (embed (T.b - T.a)) (embed (T.c - T.a)) = (delta T : ℝ) := by
  exact real_determinant_and_embedding_algebra.2.2.2.2.2.2.1 _ _

private lemma real_delta_ne (T : LatticeTriangle) (hT : delta T ≠ 0) :
    realDet (embed (T.b - T.a)) (embed (T.c - T.a)) ≠ 0 := by
  rw [real_delta]
  exact_mod_cast hT

private lemma barycentric_relation (T : LatticeTriangle) (hT : delta T ≠ 0)
    (x : RealPlane) : HasBarycentric T x (barycentric T x) := by
  have hd := real_delta_ne T hT
  constructor
  · simp [barycentric, Fin.sum_univ_succ]
  · apply Prod.ext
    all_goals simp [Fin.sum_univ_succ, barycentric, vertex, realDet, embed,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Int.cast_sub] at hd ⊢
    all_goals field_simp (disch := ring_nf at hd ⊢; assumption)
    all_goals ring

private lemma barycentric_unique (T : LatticeTriangle) (hT : delta T ≠ 0)
    (x : RealPlane) (w : Fin 3 → ℝ) (hw : HasBarycentric T x w) :
    w = barycentric T x := by
  have hd := real_delta_ne T hT
  have hs := hw.1
  have hx := congrArg Prod.fst hw.2
  have hy := congrArg Prod.snd hw.2
  simp [Fin.sum_univ_succ, vertex, embed, smul_eq_mul] at hs hx hy
  have h0 : w 0 = 1 - w 1 - w 2 := by linarith
  rw [h0] at hx hy
  funext i
  fin_cases i
  all_goals simp [barycentric, realDet, embed, Int.cast_sub] at hd ⊢
  all_goals rw [hx, hy]
  all_goals try rw [h0]
  all_goals field_simp (disch := ring_nf at hd ⊢; assumption)
  all_goals ring

private lemma barycentric_mix (T : LatticeTriangle) (x y : RealPlane)
    (a b : ℝ) (hab : a + b = 1) (i : Fin 3) :
    barycentric T (a • x + b • y) i =
      a * barycentric T x i + b * barycentric T y i := by
  have hb : b = 1 - a := by linarith
  subst b
  fin_cases i
  all_goals simp [barycentric, realDet, embed, Int.cast_sub, smul_eq_mul,
    Prod.smul_fst, Prod.smul_snd, div_eq_mul_inv]
  all_goals ring

private lemma barycentric_vertex (T : LatticeTriangle) (hT : delta T ≠ 0)
    (i : Fin 3) : barycentric T (embed (vertex T i)) = Pi.single i 1 := by
  symm
  apply barycentric_unique T hT
  simp [HasBarycentric, Finset.sum_pi_single]

private lemma vertices_range (T : LatticeTriangle) :
    Set.range (vertex T) = (T.vertices : Set Lattice) := by
  ext z
  simp [vertex, LatticeTriangle.vertices, Matrix.range_cons, Matrix.range_empty,
    or_comm, or_left_comm]

private lemma barycentric_face_hull (T : LatticeTriangle) (hT : delta T ≠ 0)
    (F : Finset Lattice) (hF : F ⊆ T.vertices) :
    ∀ x ∈ windowHull F,
      (∀ i, 0 ≤ barycentric T x i) ∧
      (∀ i, vertex T i ∉ F → barycentric T x i = 0) := by
  classical
  apply convexHull_min
  · rintro x ⟨z, hz, rfl⟩
    have hz' : z ∈ Set.range (vertex T) := by rw [vertices_range]; exact hF hz
    obtain ⟨j, rfl⟩ := hz'
    change (∀ i, 0 ≤ barycentric T (embed (vertex T j)) i) ∧ _
    rw [barycentric_vertex T hT]
    constructor
    · intro i
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · intro i hi
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hi hz
      simp [Pi.single_apply, hij]
  · intro x hx y hy a b ha hb hab
    constructor
    · intro i
      rw [barycentric_mix T x y a b hab]
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · intro i hi
      rw [barycentric_mix T x y a b hab, hx.2 i hi, hy.2 i hi]
      ring

private lemma barycentric_face_mem (T : LatticeTriangle) (hT : delta T ≠ 0)
    (F : Finset Lattice) (x : RealPlane)
    (hn : ∀ i, 0 ≤ barycentric T x i)
    (hz : ∀ i, vertex T i ∉ F → barycentric T x i = 0) :
    x ∈ windowHull F := by
  classical
  let s := Finset.univ.filter (fun i : Fin 3 => vertex T i ∈ F)
  have hw := barycentric_relation T hT x
  have hs : ∑ i ∈ s, barycentric T x i = 1 := by
    rw [← hw.1]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi his
    exact hz i (by simpa [s] using his)
  have hv : ∑ i ∈ s, barycentric T x i • embed (vertex T i) = x := by
    calc
      _ = ∑ i, barycentric T x i • embed (vertex T i) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi his
        rw [hz i (by simpa [s] using his), zero_smul]
      _ = x := hw.2.symm
  have hm := s.centerMass_mem_convexHull (R := ℝ) (w := barycentric T x)
    (s := embed '' (F : Set Lattice))
    (z := fun i => embed (vertex T i)) (fun i _ => hn i)
    (by rw [hs]; norm_num) (fun i hi => ⟨vertex T i, by simpa [s] using hi, rfl⟩)
  simpa [Finset.centerMass, hs, hv, windowHull] using hm

private lemma triangle_affineIndependent (T : LatticeTriangle) (hT : delta T ≠ 0) :
    AffineIndependent ℝ (fun i => embed (vertex T i)) := by
  apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ _).2
  intro w₁ w₂ hs₁ hs₂ hv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hs₁,
    Finset.affineCombination_eq_linear_combination _ _ _ hs₂] at hv
  have h₁ : HasBarycentric T (∑ i, w₁ i • embed (vertex T i)) w₁ := ⟨hs₁, rfl⟩
  have h₂ : HasBarycentric T (∑ i, w₁ i • embed (vertex T i)) w₂ := ⟨hs₂, hv⟩
  exact (barycentric_unique T hT _ w₁ h₁).trans
    (barycentric_unique T hT _ w₂ h₂).symm

private lemma embed_injective : Function.Injective embed := by
  intro p q hpq
  apply Prod.ext
  · have h : (p.1 : ℝ) = q.1 := congrArg Prod.fst hpq
    exact_mod_cast h
  · have h : (p.2 : ℝ) = q.2 := congrArg Prod.snd hpq
    exact_mod_cast h

/-- PT01: actual unique coordinates on any nondegenerate lattice triangle. -/
theorem nondegenerate_triangle_barycentric_unique (T : LatticeTriangle)
    (hT : delta T ≠ 0) (x : RealPlane) :
    (∃! w : Fin 3 → ℝ, HasBarycentric T x w) ∧
    HasBarycentric T x (barycentric T x) ∧
    (x ∈ T.carrier ↔ ∀ i, 0 ≤ barycentric T x i) ∧
    (x ∈ T.carrier → ∃ i, 0 < barycentric T x i) := by
  have hw := barycentric_relation T hT x
  refine ⟨⟨barycentric T x, hw, fun w hw => barycentric_unique T hT x w hw⟩,
    hw, ?_, ?_⟩
  · constructor
    · intro hx
      exact (barycentric_face_hull T hT T.vertices (fun _ h => h) x hx).1
    · intro hn
      apply barycentric_face_mem T hT T.vertices x hn
      intro i hi
      have hv : vertex T i ∈ (T.vertices : Set Lattice) := by
        rw [← vertices_range]; exact Set.mem_range_self i
      exact False.elim (hi hv)
  · intro hx
    have hn := (barycentric_face_hull T hT T.vertices (fun _ h => h) x hx).1
    by_contra! h
    have hz : barycentric T x = 0 := by
      funext i
      exact le_antisymm (h i) (hn i)
    simpa [hz] using hw.1

/-- PT02: faces are exactly the zero-coordinate restrictions of the parent. -/
theorem triangle_face_membership (T : LatticeTriangle) (hT : delta T ≠ 0)
    (F : Finset Lattice) (hF : F ⊆ T.vertices) :
    (∀ x : RealPlane, x ∈ windowHull F ↔
      x ∈ T.carrier ∧ ∀ i, vertex T i ∉ F → barycentric T x i = 0) ∧
    (∀ z ∈ T.vertices, embed z ∈ windowHull F ↔ z ∈ F) ∧
    AffineIndepOn ℝ embed (F : Set Lattice) := by
  classical
  have hn (x : RealPlane) := (nondegenerate_triangle_barycentric_unique T hT x).2.2.1
  have hf (x : RealPlane) : x ∈ windowHull F ↔
      x ∈ T.carrier ∧ ∀ i, vertex T i ∉ F → barycentric T x i = 0 := by
    constructor
    · intro hx
      obtain ⟨hnx, hzx⟩ := barycentric_face_hull T hT F hF x hx
      exact ⟨(hn x).2 hnx, hzx⟩
    · rintro ⟨hx, hz⟩
      exact barycentric_face_mem T hT F x ((hn x).1 hx) hz
  refine ⟨hf, ?_, ?_⟩
  · intro z hz
    constructor
    · intro hx
      have hz' : z ∈ Set.range (vertex T) := by rw [vertices_range]; exact hz
      obtain ⟨i, rfl⟩ := hz'
      by_contra hi
      have hzero := ((hf _).1 hx).2 i hi
      rw [barycentric_vertex T hT] at hzero
      simpa using hzero
    · intro hz
      exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩
  · have hai := triangle_affineIndependent T hT
    have hv : AffineIndepOn ℝ embed (T.vertices : Set Lattice) := by
      simpa [Set.image_univ, vertices_range] using
        (hai.affineIndepOn Set.univ).image_of_comp (vertex T) embed
    exact hv.mono hF

private lemma two_zero_coordinates_vertex (T : LatticeTriangle) (hT : delta T ≠ 0)
    (q : Lattice) (i j : Fin 3) (hij : i ≠ j)
    (hi : barycentric T (embed q) i = 0)
    (hj : barycentric T (embed q) j = 0) : q ∈ T.vertices := by
  have hw := barycentric_relation T hT (embed q)
  have hs := hw.1
  have hx := hw.2
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals norm_num at hi hj
  all_goals simp only [Fin.sum_univ_three, hi, hj, add_zero, zero_add] at hs
  all_goals simp only [Fin.sum_univ_three, hi, hj, hs, zero_smul, one_smul,
    add_zero, zero_add] at hx
  all_goals have he := embed_injective hx
  all_goals simpa [he, vertex, LatticeTriangle.vertices]

private lemma cone_delta_barycentric (T : LatticeTriangle) (hT : delta T ≠ 0)
    (q : Lattice) (i : Fin 3) :
    (delta (coneChild T q i) : ℝ) = barycentric T (embed q) i * (delta T : ℝ) := by
  have hd := real_delta_ne T hT
  fin_cases i
  all_goals simp [coneChild, delta, det, barycentric, realDet, embed,
    Int.cast_sub, Int.cast_mul] at hd ⊢
  all_goals field_simp (disch := ring_nf at hd ⊢; assumption)
  all_goals ring

/-- PT03: all incident nonvertex points, including points on an old edge.
The cyclic child ordering makes the determinant identity have positive sign. -/
theorem triangle_point_face_classification (T : LatticeTriangle)
    (hT : delta T ≠ 0) (q : Lattice) (hq : embed q ∈ T.carrier)
    (hqv : q ∉ T.vertices) :
    ((∀ i, 0 < barycentric T (embed q) i) ∨
      ∃ i, barycentric T (embed q) i = 0 ∧
        ∀ j, j ≠ i → 0 < barycentric T (embed q) j) ∧
    (∀ i, (delta (coneChild T q i) : ℝ) =
      barycentric T (embed q) i * (delta T : ℝ)) ∧
    (∀ i, delta (coneChild T q i) ≠ 0 ↔ 0 < barycentric T (embed q) i) := by
  have hn := (nondegenerate_triangle_barycentric_unique T hT (embed q)).2.2.1.mp hq
  refine ⟨?_, cone_delta_barycentric T hT q, ?_⟩
  · by_cases hp : ∀ i, 0 < barycentric T (embed q) i
    · exact Or.inl hp
    · right
      push Not at hp
      obtain ⟨i, hi⟩ := hp
      have hzero : barycentric T (embed q) i = 0 := le_antisymm hi (hn i)
      refine ⟨i, hzero, ?_⟩
      intro j hji
      apply lt_of_le_of_ne (hn j)
      intro hj
      exact hqv (two_zero_coordinates_vertex T hT q i j hji.symm hzero hj.symm)
  · intro i
    have hd : (delta T : ℝ) ≠ 0 := by exact_mod_cast hT
    have hc : delta (coneChild T q i) ≠ 0 ↔ (delta (coneChild T q i) : ℝ) ≠ 0 := by
      exact_mod_cast Iff.rfl
    rw [hc, cone_delta_barycentric T hT q i, mul_ne_zero_iff]
    exact ⟨fun h => lt_of_le_of_ne (hn i) (Ne.symm h.1), fun h => ⟨ne_of_gt h, hd⟩⟩

end ConvexNivat.PolygonTriangulation
