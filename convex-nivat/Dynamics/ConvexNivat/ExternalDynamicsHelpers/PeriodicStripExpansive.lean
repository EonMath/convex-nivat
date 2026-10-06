import ConvexNivat.Colle.Orbit
import ConvexNivat.CoreLattice
namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

private theorem positive_half_finite_code (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (v : Lattice)
    (hv : Primitive v) (hexp : ¬ OneSidedNonexpansive ξ (normal v)) :
    ∃ D : Finset Lattice, (∀ z ∈ D, 0 < det v z) ∧
      PatternDetermines ξ D 0 := by
  classical
  obtain ⟨w, hw⟩ := primitive_height_surjective v hv 1
  change det v w = 1 at hw
  have hdot (z : Lattice) : realDot (embed z) (normal v) = (det v z : ℝ) := by
    dsimp [realDot, embed, normal, det]
    push_cast
    ring
  have hn : normal v ≠ 0 := by
    intro e
    have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    have hv0 := primitive_ne_zero v hv
    apply hv0
    apply Prod.ext
    · dsimp [normal] at h2
      exact_mod_cast h2
    · dsimp [normal] at h1
      have : (v.2 : ℝ) = 0 := neg_eq_zero.mp h1
      exact_mod_cast this
  have hseparate : ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
      x 0 ≠ y 0 → ∃ z : Lattice, 0 < det v z ∧ x z ≠ y z := by
    intro x hx y hy hne
    by_contra! h
    apply hexp
    refine ⟨hn, translate w x, orbitClosure_translate_member ξ x hx w,
      translate w y, orbitClosure_translate_member ξ y hy w, ?_, ?_⟩
    · intro he
      have hh := congrFun he (-w)
      exact hne (by simpa [translate] using hh)
    · intro z hz
      change x (z + w) = y (z + w)
      apply h
      have hh : 0 ≤ det v z := by
        change 0 ≤ realDot (embed z) (normal v) at hz
        rw [hdot] at hz
        exact_mod_cast hz
      have hd : det v (z + w) = det v z + det v w := by dsimp [det]; ring
      rw [hd, hw]
      omega
  let K : Set (Configuration ℤ × Configuration ℤ) :=
    (OrbitClosure ξ ×ˢ OrbitClosure ξ) ∩ {p | p.1 0 ≠ p.2 0}
  have hK : IsCompact K := by
    apply ((orbitClosure_isCompact ξ A hA).prod (orbitClosure_isCompact ξ A hA)).inter_right
    exact (isClopen_discrete {q : ℤ × ℤ | q.1 ≠ q.2}).isClosed.preimage
      (show Continuous (fun p : Configuration ℤ × Configuration ℤ => (p.1 0, p.2 0)) by fun_prop)
  let U : {z : Lattice // 0 < det v z} → Set (Configuration ℤ × Configuration ℤ) :=
    fun z => {p | p.1 z ≠ p.2 z}
  have hU : ∀ z, IsOpen (U z) := by
    intro z
    exact (isClopen_discrete {q : ℤ × ℤ | q.1 ≠ q.2}).isOpen.preimage
      (show Continuous (fun p : Configuration ℤ × Configuration ℤ => (p.1 z, p.2 z)) by fun_prop)
  have hcover : K ⊆ ⋃ z, U z := by
    intro p hp
    obtain ⟨z, hz, he⟩ := hseparate p.1 hp.1.1 p.2 hp.1.2 hp.2
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, he⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨T.image Subtype.val, ?_, ?_⟩
  · intro z hz
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hz
    exact z.property
  · intro x hx y hy t hagree
    by_contra hne
    have htx := orbitClosure_translate_member ξ x hx t
    have hty := orbitClosure_translate_member ξ y hy t
    have hp : (translate t x, translate t y) ∈ K := by
      refine ⟨⟨htx, hty⟩, ?_⟩
      simpa [translate] using hne
    obtain ⟨z, hz, he⟩ := Set.mem_iUnion₂.mp (hT hp)
    exact he (hagree z (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

private theorem positive_hull_minimum (V : Finset Lattice) (v : Lattice)
    (hV : ∀ z ∈ V, z = 0 ∨ 0 < det v z) :
    ∀ z, embed z ∈ windowHull V → z = 0 ∨ 0 < det v z := by
  let ℓ : RealPlane →ₗ[ℝ] ℝ :=
    { toFun := fun x => (v.1 : ℝ) * x.2 - (v.2 : ℝ) * x.1
      map_add' := by intros; dsimp; ring
      map_smul' := by intros; dsimp; ring }
  have hℓ (z : Lattice) : ℓ (embed z) = (det v z : ℝ) := by
    dsimp [ℓ, embed, det]
    push_cast
    rfl
  have hconv : Convex ℝ {x : RealPlane | x = 0 ∨ 0 < ℓ x} := by
    intro x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hx
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · left; simp
    · right; simpa using mul_pos hbp hy
    · right; simpa using mul_pos hap hx
    · right
      simpa using add_pos (mul_pos hap hx) (mul_pos hbp hy)
  have hHull : windowHull V ⊆ {x : RealPlane | x = 0 ∨ 0 < ℓ x} := by
    apply convexHull_min _ hconv
    rintro _ ⟨z, hz, rfl⟩
    rcases hV z hz with rfl | h
    · left; simp [embed]
    · right; rw [hℓ]; exact_mod_cast h
  intro z hz
  rcases hHull hz with he | hp
  · left
    apply Prod.ext
    · have h := congrArg Prod.fst he
      dsimp [embed] at h
      exact_mod_cast h
    · have h := congrArg Prod.snd he
      dsimp [embed] at h
      exact_mod_cast h
  · right; rw [hℓ] at hp; exact_mod_cast hp

private theorem hull_interior_from_det_one (V : Finset Lattice) (u w : Lattice)
    (h0 : (0 : Lattice) ∈ V) (hu : u ∈ V) (hw : w ∈ V) (hd : det u w = 1) :
    (interior (windowHull V)).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  let H := affineSpan ℝ (embed '' (V : Set Lattice))
  have h0H : (0 : RealPlane) ∈ H :=
    subset_affineSpan ℝ _ ⟨0, h0, by simp [embed]⟩
  have huH : embed u ∈ H := subset_affineSpan ℝ _ ⟨u, hu, rfl⟩
  have hwH : embed w ∈ H := subset_affineSpan ℝ _ ⟨w, hw, rfl⟩
  have hud : embed u ∈ H.direction := by
    simpa using H.vsub_mem_direction huH h0H
  have hwd : embed w ∈ H.direction := by
    simpa using H.vsub_mem_direction hwH h0H
  have hdr : (u.1 : ℝ) * w.2 - (u.2 : ℝ) * w.1 = 1 := by
    exact_mod_cast hd
  apply top_unique
  intro x _
  let a := x.1 * (w.2 : ℝ) - x.2 * (w.1 : ℝ)
  let b := (u.1 : ℝ) * x.2 - (u.2 : ℝ) * x.1
  have he : a • embed u + b • embed w = x := by
    ext <;> dsimp [a, b, embed]
    · linear_combination x.1 * hdr
    · linear_combination x.2 * hdr
  rw [← he]
  have hm := H.direction.add_mem (H.direction.smul_mem a hud) (H.direction.smul_mem b hwd)
  simpa using H.vadd_mem_of_mem_direction hm h0H


theorem closed_expansive_singleton_generated_face (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (v : Lattice)
    (hv : Primitive v) (hexp : ¬ OneSidedNonexpansive ξ (normal v)) :
    ∃ S : Finset Lattice, S.Nonempty ∧ LatticeConvex S ∧
      (interior (windowHull S)).Nonempty ∧ ∃ g : Lattice,
        supportRow S v = {g} ∧ PatternDetermines ξ (S.erase g) g := by
  classical
  obtain ⟨D, hDpos, hDgen⟩ := positive_half_finite_code ξ A hA v hv hexp
  obtain ⟨w, hw⟩ := primitive_height_surjective v hv 1
  change det v w = 1 at hw
  let u := v + w
  have hu : det v u = 1 := by
    dsimp [u, det] at *
    nlinarith
  have huw : det u w = 1 := by
    dsimp [u, det] at *
    nlinarith
  let V := insert (0 : Lattice) (D ∪ {u, w})
  let S := convexLatticeWindow V
  have hVS : V ⊆ S := by
    intro z hz
    exact (lattice_windowHull_finite V).mem_toFinset.mpr
      (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
  have hSV : windowHull S = windowHull V := by
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨z, hz, rfl⟩
      exact (lattice_windowHull_finite V).mem_toFinset.mp hz
    · exact convexHull_mono (Set.image_mono hVS)
  have hSconv : LatticeConvex S := by
    intro z
    rw [hSV]
    exact (lattice_windowHull_finite V).mem_toFinset.symm
  have h0V : (0 : Lattice) ∈ V := Finset.mem_insert_self _ _
  have huV : u ∈ V := by simp [V]
  have hwV : w ∈ V := by simp [V]
  have h0S := hVS h0V
  have hVpos : ∀ z ∈ V, z = 0 ∨ 0 < det v z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Or.inl rfl
    · right
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hDpos z hz
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · omega
        · have he := Finset.mem_singleton.mp hz
          rw [he, hw]
          norm_num
  have hSpos : ∀ z ∈ S, z = 0 ∨ 0 < det v z := by
    intro z hz
    exact positive_hull_minimum V v hVpos z
      ((lattice_windowHull_finite V).mem_toFinset.mp hz)
  have hdot (z : Lattice) : realDot (embed z) (normal v) = (det v z : ℝ) := by
    dsimp [realDot, embed, normal, det]
    push_cast
    ring
  refine ⟨S, ⟨0, h0S⟩, hSconv, ?_, 0, ?_, ?_⟩
  · rw [hSV]
    exact hull_interior_from_det_one V u w h0V huV hwV huw
  · ext z
    constructor
    · intro hz
      obtain ⟨hzS, hmin⟩ := Finset.mem_filter.mp hz
      have hle := hmin 0 h0S
      rw [hdot, hdot] at hle
      have hznonpos : det v z ≤ 0 := by
        have hh : (det v z : ℝ) ≤ 0 := by simpa [det] using hle
        exact_mod_cast hh
      rcases hSpos z hzS with rfl | hp
      · simp
      · omega
    · intro hz
      have he := Finset.mem_singleton.mp hz
      subst z
      apply Finset.mem_filter.mpr
      refine ⟨h0S, fun q hq => ?_⟩
      rw [hdot, hdot]
      rcases hSpos q hq with rfl | hp
      · rfl
      · have hq0 : (0 : ℝ) ≤ (det v q : ℝ) := by exact_mod_cast hp.le
        simpa [det] using hq0
  · intro x hx y hy t hagree
    apply hDgen x hx y hy t
    intro z hz
    apply hagree z
    apply Finset.mem_erase.mpr
    refine ⟨?_, hVS (Finset.mem_insert_of_mem (Finset.mem_union_left _ hz))⟩
    intro he
    have hh := hDpos z hz
    simpa [he, det] using hh

end
end ConvexNivat.ExternalDynamicsHelpers
