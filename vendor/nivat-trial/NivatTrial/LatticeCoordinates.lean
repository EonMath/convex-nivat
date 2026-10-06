import NivatTrial.LatticePolygon
import NivatTrial.Periodicity

/-! Changes of integer basis preserve the actual convex windows and their languages. -/

namespace NivatTrial.LatticeCoordinates

open NivatTrial.Zonotope NivatTrial.LatticePolygon NivatTrial.Dynamics
open NivatTrial.Periodicity
open scoped Classical

noncomputable section

def realMap (e : Lattice →+ Lattice) : Plane →ₗ[ℝ] Plane where
  toFun z := z.1 • embed (e (1,0)) + z.2 • embed (e (0,1))
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      smul_add, smul_smul]

theorem realMap_embed (e : Lattice →+ Lattice) (z : Lattice) :
    realMap e (embed z) = embed (e z) := by
  have hz : z = z.1 • (1,0) + z.2 • (0,1) := by ext <;> simp
  conv_rhs => rw [hz, map_add, map_zsmul, map_zsmul, embed_add,
    embed_zsmul, embed_zsmul]
  rfl

def mapWindow (e : Lattice ≃+ Lattice) (S : Finset Lattice) : Finset Lattice :=
  S.map e.toEquiv.toEmbedding

@[simp] theorem mem_mapWindow (e : Lattice ≃+ Lattice) (S : Finset Lattice) (z : Lattice) :
    z ∈ mapWindow e S ↔ e.symm z ∈ S := by
  simp [mapWindow]

@[simp] theorem card_mapWindow (e : Lattice ≃+ Lattice) (S : Finset Lattice) :
    (mapWindow e S).card = S.card := Finset.card_map _

theorem mapWindow_nonempty (e : Lattice ≃+ Lattice) {S : Finset Lattice}
    (hS : S.Nonempty) : (mapWindow e S).Nonempty := hS.map

theorem mapWindow_subset (e : Lattice ≃+ Lattice) {S T : Finset Lattice}
    (h : S ⊆ T) : mapWindow e S ⊆ mapWindow e T := by
  intro z hz
  exact (mem_mapWindow e T z).mpr (h ((mem_mapWindow e S z).mp hz))

theorem isLatticeConvex_mapWindow (e : Lattice ≃+ Lattice)
    {S : Finset Lattice} (hS : IsLatticeConvex S) : IsLatticeConvex (mapWindow e S) := by
  apply (isLatticeConvex_iff _).mpr
  intro z hz
  rw [mem_mapWindow]
  apply (hS (e.symm z)).mp
  have hsub : windowHull (mapWindow e S) ⊆
      (realMap e.symm.toAddMonoidHom) ⁻¹' windowHull S := by
    apply convexHull_min _ ((windowHull_convex S).linear_preimage _)
    rintro p ⟨y, hy, rfl⟩
    change realMap e.symm.toAddMonoidHom (embed y) ∈ windowHull S
    rw [realMap_embed]
    exact mem_windowHull_of_mem S ((mem_mapWindow e S y).mp hy)
  have hh := hsub hz
  change realMap e.symm.toAddMonoidHom (embed z) ∈ windowHull S at hh
  rw [realMap_embed] at hh
  exact hh

def windowEquiv (e : Lattice ≃+ Lattice) (S : Finset Lattice) : S ≃ mapWindow e S where
  toFun z := ⟨e z, by simpa using z.property⟩
  invFun z := ⟨e.symm z, (mem_mapWindow e S z).mp z.property⟩
  left_inv z := by apply Subtype.ext; exact e.symm_apply_apply z
  right_inv z := by apply Subtype.ext; exact e.apply_symm_apply z

variable {A : Type*}

def patternMap (e : Lattice ≃+ Lattice) (θ : Lattice → A) (S : Finset Lattice) :
    patternSet θ (mapWindow e S) → patternSet (θ ∘ e) S := fun p =>
  ⟨fun z => p.val (windowEquiv e S z), by
    obtain ⟨u, hu⟩ := p.property
    refine ⟨e.symm u, ?_⟩
    rw [← hu]
    funext z
    simp [patternAt, windowEquiv]⟩

theorem patternMap_bijective (e : Lattice ≃+ Lattice) (θ : Lattice → A)
    (S : Finset Lattice) : Function.Bijective (patternMap e θ S) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    funext z
    obtain ⟨w, rfl⟩ := (windowEquiv e S).surjective z
    exact congrFun (congrArg (fun p : patternSet (θ ∘ e) S => p.val) hpq) w
  · rintro ⟨p, u, rfl⟩
    refine ⟨⟨patternAt θ (mapWindow e S) (e u), ⟨e u, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    funext z
    simp [patternMap, patternAt, windowEquiv]

theorem patternComplexity_mapWindow [Fintype A] (e : Lattice ≃+ Lattice)
    (θ : Lattice → A) (S : Finset Lattice) :
    patternComplexity θ (mapWindow e S) = patternComplexity (θ ∘ e) S := by
  exact Nat.card_congr (Equiv.ofBijective (patternMap e θ S) (patternMap_bijective e θ S))

theorem isPeriod_comp_iff (e : Lattice ≃+ Lattice) (θ : Lattice → A) (h : Lattice) :
    IsPeriod (θ ∘ e) h ↔ IsPeriod θ (e h) := by
  constructor
  · intro hp z
    simpa using hp (e.symm z)
  · intro hp z
    simpa using hp (e z)

def reflectY : Lattice ≃+ Lattice where
  toFun z := (z.1, -z.2)
  invFun z := (z.1, -z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by ext <;> simp [add_comm]

@[simp] theorem reflectY_apply (z : Lattice) : reflectY z = (z.1, -z.2) := rfl
@[simp] theorem reflectY_symm_apply (z : Lattice) : reflectY.symm z = (z.1, -z.2) := rfl

@[simp] theorem mem_translateWindow (u : Lattice) (S : Finset Lattice) (z : Lattice) :
    z ∈ translateWindow u S ↔ z-u ∈ S := by
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    simpa using hw
  · intro hz
    exact Finset.mem_map.mpr ⟨z-u, hz, by simp⟩

theorem isLatticeConvex_translateWindow (u : Lattice) {S : Finset Lattice}
    (hS : IsLatticeConvex S) : IsLatticeConvex (translateWindow u S) := by
  apply (isLatticeConvex_iff _).mpr
  intro z hz
  rw [mem_translateWindow]
  apply (hS (z-u)).mp
  have hsub : windowHull (translateWindow u S) ⊆
      (fun x : Plane => -embed u + x) ⁻¹' windowHull S := by
    apply convexHull_min _ ((windowHull_convex S).translate_preimage_right (-embed u))
    rintro p ⟨y, hy, rfl⟩
    have hm := mem_windowHull_of_mem S ((mem_translateWindow u S y).mp hy)
    simpa [embed_sub, sub_eq_add_neg, add_comm] using hm
  have hh := hsub hz
  simpa [Set.mem_preimage, embed_sub, sub_eq_add_neg, add_comm] using hh

end
end NivatTrial.LatticeCoordinates
