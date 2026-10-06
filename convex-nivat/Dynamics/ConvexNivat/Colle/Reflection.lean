import ConvexNivat.Colle.Definitions

namespace ConvexNivat.Colle
noncomputable section

/-- The actual reflection M used at published p.4316. -/
def reflect (z : Lattice) : Lattice := (z.1, -z.2)

def reflectedConfiguration (ξ : Configuration ℤ) : Configuration ℤ :=
  fun z => ξ (reflect z)

def reflectedWindow (S : Finset Lattice) : Finset Lattice := S.image reflect

@[simp] private theorem reflect_reflect (z : Lattice) : reflect (reflect z) = z := by
  ext <;> simp [reflect]

@[simp] private theorem reflect_add (z w : Lattice) : reflect (z + w) = reflect z + reflect w := by
  ext <;> simp [reflect, add_comm]

@[simp] private theorem reflect_neg (z : Lattice) : reflect (-z) = -reflect z := by
  ext <;> simp [reflect]

@[simp] private theorem reflect_zsmul (k : ℤ) (z : Lattice) : reflect (k • z) = k • reflect z := by
  ext <;> simp [reflect]

private theorem reflect_injective : Function.Injective reflect := by
  intro a b h
  simpa using congrArg reflect h

@[simp] private theorem reflect_zero : reflect 0 = 0 := rfl

@[simp] private theorem reflect_eq_zero (z : Lattice) : reflect z = 0 ↔ z = 0 := by
  exact reflect_injective.eq_iff' reflect_zero

@[simp] private theorem reflected_reflected (ξ : Configuration ℤ) :
    reflectedConfiguration (reflectedConfiguration ξ) = ξ := by
  funext z
  simp [reflectedConfiguration]

@[simp] private theorem mem_reflected (S : Finset Lattice) (z : Lattice) :
    reflect z ∈ reflectedWindow S ↔ z ∈ S := by
  simp [reflectedWindow, reflect_injective.eq_iff]

@[simp] private theorem reflected_reflected_window (S : Finset Lattice) :
    reflectedWindow (reflectedWindow S) = S := by
  simp [reflectedWindow, Finset.image_image, Function.comp_def]

private theorem reflect_det (h k : Lattice) : det (reflect h) (reflect k) = -det h k := by
  simp [det, reflect]
  ring

private theorem reflection_orbit_forward (ξ x : Configuration ℤ) (hx : x ∈ OrbitClosure ξ) :
    reflectedConfiguration x ∈ OrbitClosure (reflectedConfiguration ξ) := by
  intro S
  obtain ⟨u, hu⟩ := hx (reflectedWindow S)
  refine ⟨reflect u, ?_⟩
  intro z hz
  simpa [reflectedConfiguration] using hu (reflect z) ((mem_reflected S z).mpr hz)

theorem reflection_orbitClosure (ξ x : Configuration ℤ) :
    x ∈ OrbitClosure ξ ↔ reflectedConfiguration x ∈ OrbitClosure (reflectedConfiguration ξ) := by
  constructor
  · exact reflection_orbit_forward ξ x
  · intro hx
    simpa using reflection_orbit_forward (reflectedConfiguration ξ) (reflectedConfiguration x) hx

theorem reflection_period (ξ : Configuration ℤ) (h : Lattice) :
    HasPeriod (reflectedConfiguration ξ) h ↔ HasPeriod ξ (reflect h) := by
  constructor
  · intro hp z
    simpa [reflectedConfiguration] using hp (reflect z)
  · intro hp z
    simpa [reflectedConfiguration] using hp (reflect z)

theorem reflection_periodic (ξ : Configuration ℤ) :
    Periodic (reflectedConfiguration ξ) ↔ Periodic ξ := by
  constructor
  · rintro ⟨h, hne, hp⟩
    exact ⟨reflect h, by simpa using hne, (reflection_period ξ h).mp hp⟩
  · rintro ⟨h, hne, hp⟩
    refine ⟨reflect h, by simpa using hne, (reflection_period ξ (reflect h)).mpr ?_⟩
    simpa using hp

theorem reflection_doublyPeriodic (ξ : Configuration ℤ) :
    DoublyPeriodic (reflectedConfiguration ξ) ↔ DoublyPeriodic ξ := by
  have hind (h k : Lattice) : Nonparallel (reflect h) (reflect k) ↔ Nonparallel h k := by
    simp [Nonparallel, reflect_det]
  constructor
  · rintro ⟨h, k, hi, hh, hk⟩
    exact ⟨reflect h, reflect k, (hind h k).mpr hi,
      (reflection_period ξ h).mp hh, (reflection_period ξ k).mp hk⟩
  · rintro ⟨h, k, hi, hh, hk⟩
    refine ⟨reflect h, reflect k, (hind h k).mpr hi,
      (reflection_period ξ (reflect h)).mpr ?_, (reflection_period ξ (reflect k)).mpr ?_⟩
    · simpa using hh
    · simpa using hk

theorem reflection_complexity (ξ : Configuration ℤ) (S : Finset Lattice) :
    complexity (reflectedConfiguration ξ) (reflectedWindow S) = complexity ξ S := by
  let f : Pattern ℤ S → Pattern ℤ (reflectedWindow S) := fun p z =>
    p ⟨reflect z.val, (mem_reflected S (reflect z.val)).mp (by simpa only [reflect_reflect] using z.property)⟩
  have hf : Function.Injective f := by
    intro p q h
    funext z
    have h' := congrFun h ⟨reflect z.val, (mem_reflected S z.val).mpr z.property⟩
    simpa [f] using h'
  have heq : patternSet (reflectedConfiguration ξ) (reflectedWindow S) = f '' patternSet ξ S := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨pattern ξ S (reflect u), ⟨reflect u, rfl⟩, ?_⟩
      funext z
      simp [f, pattern, reflectedConfiguration]
    · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
      refine ⟨reflect u, ?_⟩
      funext z
      simp [f, pattern, reflectedConfiguration]
  unfold complexity
  rw [heq]
  exact Set.ncard_image_of_injective _ hf

theorem reflection_annihilator (ξ : Configuration ℤ)
    (hann : HasNontrivialIntegerAnnihilator ξ) :
    HasNontrivialIntegerAnnihilator (reflectedConfiguration ξ) := by
  obtain ⟨a, hne, ha⟩ := hann
  refine ⟨a.mapDomain reflect, ?_, ?_⟩
  · intro hz
    apply hne
    apply Finsupp.mapDomain_injective reflect_injective
    simpa using hz
  · intro z
    unfold integerLaurentAction
    rw [Finsupp.sum_mapDomain_index_inj reflect_injective]
    simpa [reflectedConfiguration, integerLaurentAction] using ha (reflect z)

private theorem reflection_oned_forward (ξ : Configuration ℤ) (n : RealPlane) :
    OneSidedNonexpansive ξ n → OneSidedNonexpansive (reflectedConfiguration ξ) (n.1, -n.2) := by
  rintro ⟨hn, x, hx, y, hy, hne, hag⟩
  refine ⟨?_, reflectedConfiguration x, (reflection_orbitClosure ξ x).mp hx,
    reflectedConfiguration y, (reflection_orbitClosure ξ y).mp hy, ?_, ?_⟩
  · intro hz
    apply hn
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    apply Prod.ext
    · exact h1
    · simpa using h2
  · intro hxy
    apply hne
    simpa using congrArg reflectedConfiguration hxy
  · intro z hz
    apply hag
    simpa [realDot, embed, reflect, mul_neg, neg_mul] using hz

theorem reflection_oneSided (ξ : Configuration ℤ) (v : Lattice) :
    OneSidedNonexpansive (reflectedConfiguration ξ) (normal (reflect v)) ↔
      OneSidedNonexpansive ξ (-normal v) := by
  constructor
  · intro h
    have ht := reflection_oned_forward (reflectedConfiguration ξ) (normal (reflect v)) h
    simpa [normal, reflect] using ht
  · intro h
    have ht := reflection_oned_forward ξ (-normal v) h
    simpa [normal, reflect] using ht

private def realReflection : RealPlane ≃ₗ[ℝ] RealPlane where
  toFun z := (z.1, -z.2)
  invFun z := (z.1, -z.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

private def reflectionHomeomorph : RealPlane ≃ₜ RealPlane where
  toEquiv := realReflection.toEquiv
  continuous_toFun := by change Continuous (fun z : RealPlane => (z.1, -z.2)); fun_prop
  continuous_invFun := by change Continuous (fun z : RealPlane => (z.1, -z.2)); fun_prop

@[simp] private theorem rr_embed (z : Lattice) : realReflection (embed z) = embed (reflect z) := by
  ext <;> simp [realReflection, reflect, embed]

private theorem reflection_hull (S : Finset Lattice) :
    windowHull (reflectedWindow S) = realReflection '' windowHull S := by
  unfold windowHull
  change convexHull ℝ (embed '' (reflectedWindow S : Set Lattice)) =
    realReflection.toLinearMap '' convexHull ℝ (embed '' (S : Set Lattice))
  rw [realReflection.toLinearMap.image_convexHull]
  congr 1
  ext x
  simp only [Set.mem_image, Finset.mem_coe, reflectedWindow, Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨embed u, ⟨u, hu, rfl⟩, rr_embed u⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨reflect u, ⟨u, hu, rfl⟩, (rr_embed u).symm⟩

private theorem reflection_convex (S : Finset Lattice) (hS : LatticeConvex S) :
    LatticeConvex (reflectedWindow S) := by
  intro z
  rw [reflection_hull]
  constructor
  · rintro ⟨x, hx, hxeq⟩
    have heq : x = embed (reflect z) := by
      apply realReflection.injective
      rw [hxeq, rr_embed, reflect_reflect]
    rw [heq] at hx
    have hz := (hS (reflect z)).mp hx
    simpa only [reflect_reflect] using (mem_reflected S (reflect z)).mpr hz
  · intro hz
    have hz' : reflect z ∈ S := (mem_reflected S (reflect z)).mp (by simpa using hz)
    exact ⟨embed (reflect z), (hS _).mpr hz', by simp⟩

private theorem reflection_interior (S : Finset Lattice) :
    (interior (windowHull (reflectedWindow S))).Nonempty ↔
      (interior (windowHull S)).Nonempty := by
  rw [reflection_hull]
  change (interior (reflectionHomeomorph '' windowHull S)).Nonempty ↔ _
  rw [← reflectionHomeomorph.image_interior, Set.image_nonempty]

private theorem reflection_erase (S : Finset Lattice) (z : Lattice) :
    (reflectedWindow S).erase (reflect z) = reflectedWindow (S.erase z) := by
  exact (Finset.image_erase reflect_injective S z).symm

private theorem reflection_vertex (S : Finset Lattice) (z : Lattice)
    (hz : WindowVertex S z) : WindowVertex (reflectedWindow S) (reflect z) := by
  refine ⟨(mem_reflected S z).mpr hz.1, ?_⟩
  rw [reflection_erase]
  exact reflection_convex (S.erase z) hz.2

theorem reflection_generating (ξ : Configuration ℤ) (S : Finset Lattice)
    (hS : GeneratingSet ξ S) :
    GeneratingSet (reflectedConfiguration ξ) (reflectedWindow S) := by
  refine ⟨hS.1.image reflect, reflection_convex S hS.2.1, ?_⟩
  intro z hz x hx y hy t hag
  have hzr : WindowVertex S (reflect z) := by
    simpa only [reflected_reflected_window] using reflection_vertex (reflectedWindow S) z hz
  have hx' : reflectedConfiguration x ∈ OrbitClosure ξ := by
    simpa only [reflected_reflected] using
      (reflection_orbitClosure (reflectedConfiguration ξ) x).mp hx
  have hy' : reflectedConfiguration y ∈ OrbitClosure ξ := by
    simpa only [reflected_reflected] using
      (reflection_orbitClosure (reflectedConfiguration ξ) y).mp hy
  have heq := hS.2.2 (reflect z) hzr (reflectedConfiguration x) hx'
    (reflectedConfiguration y) hy' (reflect t) (by
      intro q hq
      have hq' : reflect q ∈ (reflectedWindow S).erase z := by
        have ht := (mem_reflected (S.erase (reflect z)) q).mpr hq
        simpa only [← reflection_erase, reflect_reflect] using ht
      simpa [reflectedConfiguration] using hag (reflect q) hq')
  simpa [reflectedConfiguration] using heq

private theorem reflection_row (S : Finset Lattice) (v : Lattice) :
    supportRow (reflectedWindow S) (-reflect v) = reflectedWindow (supportRow S v) := by
  have hdot (z : Lattice) : realDot (embed (reflect z)) (normal (-reflect v)) =
      realDot (embed z) (normal v) := by
    simp [realDot, normal, embed, reflect]
  apply Finset.ext
  intro z
  obtain ⟨z, rfl⟩ : ∃ q, reflect q = z := ⟨reflect z, by simp⟩
  simp only [mem_reflected, supportRow, supportFace, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, ?_⟩
    intro q hq
    simpa only [hdot] using hmin (reflect q) ((mem_reflected S q).mpr hq)
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, ?_⟩
    intro q hq
    obtain ⟨q, rfl⟩ : ∃ z, reflect z = q := ⟨reflect q, by simp⟩
    simpa only [hdot] using hmin q ((mem_reflected S q).mp hq)

private theorem reflection_edges (S : Finset Lattice) (v : Lattice) :
    -reflect v ∈ edgeDirections (reflectedWindow S) ↔ v ∈ edgeDirections S := by
  have hp : Primitive (-reflect v) ↔ Primitive v := by simp [Primitive, reflect]
  simp only [edgeDirections, Set.mem_ofPred_eq, hp, reflection_interior, reflection_row]
  rw [reflectedWindow, Finset.card_image_of_injective _ reflect_injective]

private theorem reflection_edges_set (S : Finset Lattice) :
    edgeDirections (reflectedWindow S) = (fun v => -reflect v) '' edgeDirections S := by
  ext v
  constructor
  · intro hv
    refine ⟨-reflect v, ?_, by simp⟩
    apply (reflection_edges S (-reflect v)).mp
    simpa using hv
  · rintro ⟨w, hw, rfl⟩
    exact (reflection_edges S w).mpr hw

theorem reflection_enveloped (S B : Finset Lattice) (hB : EnvelopedWindow S B) :
    EnvelopedWindow (reflectedWindow S) (reflectedWindow B) := by
  refine ⟨hB.1.image reflect, reflection_convex B hB.2.1,
    (reflection_interior B).mpr hB.2.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨v, rfl⟩ : ∃ w, -reflect w = v := ⟨-reflect v, by simp⟩
    obtain ⟨hS, hc⟩ := hB.2.2.2.1 v ((reflection_edges B v).mp hv)
    refine ⟨(reflection_edges S v).mpr hS, ?_⟩
    rw [reflection_row, reflection_row]
    simpa only [reflectedWindow, Finset.card_image_of_injective _ reflect_injective] using hc
  · have hinj : Function.Injective (fun v : Lattice => -reflect v) :=
      neg_injective.comp reflect_injective
    rw [reflection_edges_set B, reflection_edges_set S,
      Set.ncard_image_of_injective _ hinj, Set.ncard_image_of_injective _ hinj]
    exact hB.2.2.2.2

private theorem reflection_segment (a b z : Lattice) :
    embed (reflect z) ∈ segment ℝ (embed (reflect a)) (embed (reflect b)) ↔
      embed z ∈ segment ℝ (embed a) (embed b) := by
  rw [← rr_embed a, ← rr_embed b, ← rr_embed z]
  have himage := image_segment (𝕜 := ℝ) realReflection.toLinearMap.toAffineMap
    (embed a) (embed b)
  change realReflection (embed z) ∈ segment ℝ
    (realReflection.toLinearMap.toAffineMap (embed a))
    (realReflection.toLinearMap.toAffineMap (embed b)) ↔ _
  rw [← himage]
  exact realReflection.injective.mem_set_image

/-- Reflection reverses cyclic order and reverses the positively oriented
edge direction. This supplies the actual cycle used in §3.1 Case 2. -/
theorem reflection_edge_cycle (S : Finset Lattice) (m : ℕ)
    (C : AntipodalEdgeCycle S m) :
    ∃ C' : AntipodalEdgeCycle (reflectedWindow S) m,
      ∀ i : ℤ, C'.direction i = -reflect (C.direction (-i)) := by
  have hN : 0 < (2 * (m : ℤ)) := by have := C.at_least_two; omega
  have hreduce (i : ℤ) : C.direction (i % (2 * (m : ℤ))) = C.direction i := by
    have ht := Function.Periodic.sub_int_mul_eq C.direction_periodic
      (x := i) (i / (2 * (m : ℤ)))
    calc
      C.direction (i % (2 * (m : ℤ))) =
          C.direction (i - i / (2 * (m : ℤ)) * (2 * (m : ℤ))) := by
        rw [Int.emod_def]
        congr 1
        ring
      _ = C.direction i := by simpa only [Int.cast_id] using ht
  let rho (i : Fin (2 * m)) : Fin (2 * m) :=
    ⟨((- (i.val : ℤ)) % (2 * (m : ℤ))).toNat, by
      have h0 := Int.emod_nonneg (-(i.val : ℤ)) (ne_of_gt hN)
      have hlt := Int.emod_lt_of_pos (-(i.val : ℤ)) hN
      omega⟩
  have hrho (i : Fin (2 * m)) : ((rho i).val : ℤ) = (-(i.val : ℤ)) % (2 * (m : ℤ)) := by
    dsimp [rho]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hN))
  have hnegmod (i : Fin (2 * m)) :
      (- (-(i.val : ℤ) % (2 * (m : ℤ)))) % (2 * (m : ℤ)) = (i.val : ℤ) := by
    calc
      (- (-(i.val : ℤ) % (2 * (m : ℤ)))) % (2 * (m : ℤ)) =
          (i.val : ℤ) % (2 * (m : ℤ)) := by
        simpa only [zero_sub, neg_neg] using
          Int.sub_emod_emod 0 (-(i.val : ℤ)) (2 * (m : ℤ))
      _ = (i.val : ℤ) := Int.emod_eq_of_lt (by omega) (by have := i.isLt; omega)
  have hrhoinj : Function.Injective rho := by
    intro i j hij
    have hh := congrArg (fun i : Fin (2 * m) => (i.val : ℤ)) hij
    rw [hrho, hrho] at hh
    apply Fin.ext
    have ht := congrArg (fun z : ℤ => (-z) % (2 * (m : ℤ))) hh
    rw [hnegmod i, hnegmod j] at ht
    exact_mod_cast ht
  refine ⟨{
    at_least_two := C.at_least_two
    direction := fun i => -reflect (C.direction (-i))
    vertex := fun i => reflect (C.vertex (1 - i))
    direction_periodic := ?_
    vertex_periodic := ?_
    antipodal := ?_
    primitive := ?_
    distinct := ?_
    covers := ?_
    initial_mem := ?_
    terminal_mem := ?_
    edge_length := ?_
    support_segment := ?_
  }, fun i => rfl⟩
  · intro i
    have ht := C.direction_periodic (-i - 2 * (m : ℤ))
    have heq : -i - 2 * (m : ℤ) + 2 * (m : ℤ) = -i := by ring
    rw [heq] at ht
    congr 2
    convert ht.symm using 1
    congr 1
    ring
  · intro i
    have ht := C.vertex_periodic (1 - i - 2 * (m : ℤ))
    have heq : 1 - i - 2 * (m : ℤ) + 2 * (m : ℤ) = 1 - i := by ring
    rw [heq] at ht
    congr 1
    convert ht.symm using 1
    congr 1
    ring
  · intro i
    have ht := C.antipodal (-i - (m : ℤ))
    have heq : -i - (m : ℤ) + (m : ℤ) = -i := by ring
    rw [heq] at ht
    have heq' : C.direction (-(i + (m : ℤ))) = -C.direction (-i) := by
      have h := congrArg Neg.neg ht
      simpa only [neg_neg, neg_add_rev, sub_eq_add_neg, add_comm] using h.symm
    simp only [heq', reflect_neg, neg_neg]
  · intro i
    simpa [Primitive, reflect] using C.primitive (-i)
  · intro i j hij
    apply hrhoinj
    apply C.distinct
    change C.direction ((rho i).val : ℤ) = C.direction ((rho j).val : ℤ)
    rw [hrho, hrho, hreduce, hreduce]
    exact reflect_injective (neg_injective hij)
  · intro v
    constructor
    · intro hv
      have hv' : -reflect v ∈ edgeDirections S := by
        apply (reflection_edges S (-reflect v)).mp
        simpa using hv
      obtain ⟨j, hj⟩ := (C.covers (-reflect v)).mp hv'
      refine ⟨rho j, ?_⟩
      have hmod : (-((rho j).val : ℤ)) % (2 * (m : ℤ)) = (j.val : ℤ) := by
        rw [hrho]
        exact hnegmod j
      have heq : C.direction (-((rho j).val : ℤ)) = C.direction (j.val : ℤ) := by
        rw [← hreduce (-((rho j).val : ℤ)), hmod]
      rw [heq, hj]
      simp
    · rintro ⟨j, rfl⟩
      apply (reflection_edges S (C.direction (-(j.val : ℤ)))).mpr
      apply (C.covers _).mpr
      exact ⟨rho j, by rw [hrho, hreduce]⟩
  · intro i
    rw [reflection_row]
    apply (mem_reflected _ _).mpr
    simpa only [sub_eq_add_neg, add_comm] using C.terminal_mem (-i)
  · intro i
    rw [reflection_row]
    have hi : 1 - (i + 1) = -i := by ring
    rw [hi]
    exact (mem_reflected _ _).mpr (C.initial_mem (-i))
  · intro i
    obtain ⟨k, hk, heq⟩ := C.edge_length (-i)
    refine ⟨k, hk, ?_⟩
    have hm := congrArg reflect heq
    have hi : 1 - (i + 1) = -i := by ring
    rw [hi]
    have hj : 1 - i = -i + 1 := by ring
    rw [hj]
    simp only [sub_eq_add_neg, reflect_add, reflect_neg, reflect_zsmul] at hm
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left (by rw [← hm]; abel)
  · intro i z
    obtain ⟨z, rfl⟩ : ∃ q, reflect q = z := ⟨reflect z, by simp⟩
    rw [reflection_row, mem_reflected, mem_reflected]
    have hi : 1 - (i + 1) = -i := by ring
    have hj : 1 - i = -i + 1 := by ring
    rw [hi, hj, reflection_segment, segment_symm]
    exact C.support_segment (-i) z

private theorem reflection_halfStrip (S : Finset Lattice) (v z : Lattice) :
    reflect z ∈ halfStrip (reflectedWindow S) (reflect v) ↔ z ∈ halfStrip S v := by
  constructor
  · rintro ⟨g, hg, t, heq⟩
    refine ⟨reflect g, (mem_reflected S (reflect g)).mp (by simpa using hg), t, ?_⟩
    simpa only [reflect_add, reflect_zsmul, reflect_reflect] using congrArg reflect heq
  · rintro ⟨g, hg, t, rfl⟩
    exact ⟨reflect g, (mem_reflected S g).mpr hg, t, by simp only [reflect_add, reflect_zsmul]⟩

theorem opposite_mismatch_reflection (ξ xper : Configuration ℤ)
    (S : Finset Lattice) (v : Lattice)
    (hmismatch : UnboundedOppositeHalfStripMismatch ξ xper S v) :
    UnboundedHalfStripMismatch (reflectedConfiguration ξ) (reflectedConfiguration xper)
      (reflectedWindow S) (-reflect v) := by
  intro B₀ hB₀ hrow₀
  have hB₀' : EnvelopedWindow S (reflectedWindow B₀) := by
    simpa only [reflected_reflected_window] using reflection_enveloped (reflectedWindow S) B₀ hB₀
  have hrow₀' : ∀ z ∈ supportRow (reflectedWindow B₀) v, det v z = -1 := by
    intro z hz
    have hrow : supportRow (reflectedWindow B₀) v = reflectedWindow (supportRow B₀ (-reflect v)) := by
      simpa only [reflect_neg, reflect_reflect, neg_neg] using reflection_row B₀ (-reflect v)
    rw [hrow] at hz
    have ht := hrow₀ (reflect z) ((mem_reflected _ (reflect z)).mp (by simpa using hz))
    simpa [det, reflect] using ht
  obtain ⟨B, hsub, hB, hrow, u, hag, hbad⟩ := hmismatch (reflectedWindow B₀) hB₀' hrow₀'
  refine ⟨reflectedWindow B, ?_, reflection_enveloped S B hB, ?_, reflect u, ?_, ?_⟩
  · intro z hz
    have ht := hsub ((mem_reflected B₀ z).mpr hz)
    simpa only [reflect_reflect] using (mem_reflected B (reflect z)).mpr ht
  · intro z hz
    rw [reflection_row] at hz
    have ht := hrow (reflect z) ((mem_reflected _ (reflect z)).mp (by simpa using hz))
    simpa [det, reflect] using ht
  · intro z hz
    have hz' := (mem_reflected B (reflect z)).mp (by simpa using hz)
    simpa [translate, reflectedConfiguration] using hag (reflect z) hz'
  · intro hbad'
    apply hbad
    intro z hz
    have hz' : reflect z ∈ halfStrip (reflectedWindow B) (-reflect v) := by
      simpa only [reflect_neg] using (reflection_halfStrip B (-v) z).mpr hz
    simpa [translate, reflectedConfiguration] using hbad' (reflect z) hz'

end
end ConvexNivat.Colle
