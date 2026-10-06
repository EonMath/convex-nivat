import ConvexNivat.ExternalDynamicsHelpers.BoyleLindDefinitions

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

/-- A finite code from a determining band to an arbitrary finite lattice window. -/
theorem band_finite_window_code (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (n : RealPlane) (hn : n ∈ unitNormals) (t : ℝ) (ht : 0 < t)
    (hdet : BandDetermines ξ n t) (D : Finset Lattice) :
    ∃ B : Finset Lattice, (B : Set Lattice) ⊆ embed ⁻¹' realBand n t ∧
      ∀ x ∈ OrbitClosure ξ, ∀ y ∈ OrbitClosure ξ,
        AgreesOn x y (B : Set Lattice) → AgreesOn x y (D : Set Lattice) := by
  classical
  let C : Set (Configuration ℤ × Configuration ℤ) := {p | p.1 ∈ OrbitClosure ξ ∧ p.2 ∈ OrbitClosure ξ}
  let V : Set (Configuration ℤ × Configuration ℤ) := {p | AgreesOn p.1 p.2 (D : Set Lattice)}
  have hV : IsOpen V := by
    have hEq : V = ⋂ z ∈ D, {p : Configuration ℤ × Configuration ℤ | p.1 z = p.2 z} := by
      ext p
      simp [V, AgreesOn]
    rw [hEq]
    apply isOpen_biInter_finset
    intro z hz
    have hc : Continuous (fun p : Configuration ℤ × Configuration ℤ => (p.1 z, p.2 z)) := by fun_prop
    exact (isOpen_discrete {q : ℤ × ℤ | q.1 = q.2}).preimage hc
  have hC : IsCompact (C \ V) :=
    ((orbitClosure_isCompact ξ A hA).prod (orbitClosure_isCompact ξ A hA)).diff hV
  let S := embed ⁻¹' realBand n t
  let U : S → Set (Configuration ℤ × Configuration ℤ) := fun z => {p | p.1 z ≠ p.2 z}
  have hU : ∀ z, IsOpen (U z) := by
    intro z
    exact (isClosed_eq ((continuous_apply z.val).comp continuous_fst)
      ((continuous_apply z.val).comp continuous_snd)).isOpen_compl
  have hcover : C \ V ⊆ ⋃ z, U z := by
    rintro ⟨x,y⟩ ⟨⟨hx,hy⟩,hbad⟩
    by_contra h
    have hag : AgreesOn x y S := by
      intro z hz
      by_contra hne
      apply h
      exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hne⟩
    have heq := hdet x hx y hy hag
    apply hbad
    intro z hz
    exact congrFun heq z
  obtain ⟨B,hB⟩ := hC.elim_finite_subcover U hU hcover
  refine ⟨B.image Subtype.val, ?_, ?_⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact w.property
  · intro x hx y hy hag
    by_contra hbad
    have hp := hB (show (x,y) ∈ C \ V from ⟨⟨hx,hy⟩,hbad⟩)
    obtain ⟨z,hz,hne⟩ := Set.mem_iUnion₂.mp hp
    exact hne (hag z (Finset.mem_image.mpr ⟨z,hz,rfl⟩))

end
end ConvexNivat.ExternalDynamicsHelpers
