import ConvexNivat.ExternalDynamicsHelpers.KariMoutotPropagation
import ConvexNivat.ExternalDynamicsHelpers.KariMoutotAlgebra

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

theorem halfplane_pair_enlarges_fibre (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (m : ℕ) (v : Fin m → Lattice) (i₀ : Fin m)
    (hann : Annihilates (differenceFactors m v) ξ)
    (u : Lattice) (hu : u ≠ 0) (hperp : latticeDot u (v i₀) = 0)
    (htransverse : ∀ i, i ≠ i₀ → latticeDot u (v i) ≠ 0)
    (n : ℕ) (d : Fin n → Configuration ℤ) (j₀ : Fin n)
    (hd : ∀ j, d j ∈ OrbitClosure ξ)
    (himage : ∀ j j', periodDifference (d j) (v i₀) = periodDifference (d j') (v i₀))
    (B : Finset Lattice)
    (hsep : ∀ i j, i ≠ j → ∀ t, ∃ z ∈ translatedWindow B t, d i z ≠ d j z)
    (x y : Configuration ℤ) (hx : x ∈ OrbitClosure (d j₀))
    (hy : y ∈ OrbitClosure (d j₀)) (hne : x ≠ y)
    (hagree : AgreesOn x y (strictHalf (-u))) :
    ∃ e : Fin (n + 1) → Configuration ℤ,
      (∀ j, e j ∈ OrbitClosure ξ) ∧ Function.Injective e ∧
      ∀ j j', periodDifference (e j) (v i₀) = periodDifference (e j') (v i₀) := by
  classical
  have hx' := orbitClosure_transitive ξ (d j₀) (hd j₀) hx
  have hy' := orbitClosure_transitive ξ (d j₀) (hd j₀) hy
  obtain ⟨t, e, he, hex, hlim⟩ := finite_tuple_orbit_member_joint_limit ξ A hA n d hd j₀ x hx
  have heimage : ∀ i j, periodDifference (e i) (v i₀) = periodDifference (e j) (v i₀) := by
    apply equal_factor_images_joint_limit n (fun k j => translate (t k) (d j)) e (v i₀) hlim
    intro k i j
    funext z
    have h := congrFun (himage i j) (z + t k)
    simpa [periodDifference, translate, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hesep := window_separation_joint_limit n d e B hsep t hlim
  have heinj : Function.Injective e := by
    intro i j heq
    by_contra hij
    obtain ⟨z, _, hz⟩ := hesep i j hij 0
    exact hz (congrFun heq z)
  have hyeq : periodDifference y (v i₀) = periodDifference x (v i₀) :=
    (same_halfplane_same_perpendicular_factor ξ x y hx' hy' m v i₀ hann u hu hperp htransverse hagree).symm
  have hynew : ∀ j, y ≠ e j := by
    intro j heq
    by_cases hj : j = j₀
    · subst j
      exact hne (hex.symm.trans heq.symm)
    · obtain ⟨a, ha⟩ := finite_window_translate_into_half B (-u) (neg_ne_zero.mpr hu)
      obtain ⟨z, hz, hne'⟩ := hesep j j₀ hj a
      apply hne'
      rw [← heq, hex]
      exact (hagree z (ha hz)).symm
  refine ⟨Fin.cons y e, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hy'
    · exact he i
  · intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro _; rfl
    · intro hij; exact (hynew j (by simpa using hij)).elim
    · intro hij; exact (hynew i (by simpa using hij.symm)).elim
    · intro hij
      exact congrArg Fin.succ (heinj (by simpa using hij))
  · have hcommon : ∀ j, periodDifference ((Fin.cons y e : Fin (n + 1) → Configuration ℤ) j) (v i₀) = periodDifference x (v i₀) := by
      intro j
      refine Fin.cases hyeq (fun i => ?_) j
      simpa only [Fin.cons_succ, hex] using heimage i j₀
    intro i j
    exact (hcommon i).trans (hcommon j).symm

theorem kariMoutot_lemma12 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (m : ℕ) (v : Fin m → Lattice) (i₀ : Fin m)
    (hann : Annihilates (differenceFactors m v) ξ)
    (u : Lattice) (hu : u ≠ 0) (hperp : latticeDot u (v i₀) = 0)
    (htransverse : ∀ i, i ≠ i₀ → latticeDot u (v i) ≠ 0)
    (n : ℕ) (d : Fin n → Configuration ℤ) (j₀ : Fin n)
    (hd : ∀ j, d j ∈ OrbitClosure ξ)
    (himage : ∀ j j', periodDifference (d j) (v i₀) = periodDifference (d j') (v i₀))
    (B : Finset Lattice)
    (hsep : ∀ i j, i ≠ j → ∀ t, ∃ z ∈ translatedWindow B t, d i z ≠ d j z)
    (hfinite : ∀ b, (factorFibre ξ (v i₀) b).Finite)
    (hmax : ∀ b, (factorFibre ξ (v i₀) b).ncard ≤ n) :
    StrictDeterministic (d j₀) (-u) := by
  intro x hx y hy hagree
  by_contra hne
  have hag : AgreesOn x y (strictHalf (-u)) := by
    intro z hz
    apply hagree z
    change realDot (embed z) (embed (-u)) < 0
    rw [← latticeDot_cast]
    exact_mod_cast hz
  obtain ⟨e, he, hinj, him⟩ := halfplane_pair_enlarges_fibre ξ A hA m v i₀ hann u hu
    hperp htransverse n d j₀ hd himage B hsep x y hx hy hne hag
  let b := periodDifference (e 0) (v i₀)
  let F := factorFibre ξ (v i₀) b
  letI := (hfinite b).fintype
  let f : Fin (n + 1) → F := fun i => ⟨e i, he i, him i 0⟩
  have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Set.fintypeCard_eq_ncard] at hc
  have hm := hmax b
  change n + 1 ≤ (factorFibre ξ (v i₀) b).ncard at hc
  omega

end
end ConvexNivat.ExternalDynamicsHelpers
