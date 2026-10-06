import NivatTrial.MinimalHull
import NivatTrial.RealDirectionGeometry
import NivatTrial.PeriodicBandCoding
import NivatTrial.DirectionalElimination
import NivatTrial.BinomialDirections
import NivatTrial.IntegerAnnihilator

/-!
# Directional symmetry from an integer annihilator

For a finite alphabet, a product of differences in pairwise independent
directions has a minimal orbit closure whose one-sided expansive directions
are invariant under reversal. The only possible factor tangent to an
expansive boundary is removed by finite-fiber elimination.
-/

namespace NivatTrial.KariMoutot

open NivatTrial.Dynamics NivatTrial.Nonexpansive
open NivatTrial.OneSidedRecurrence NivatTrial.PeriodicDifference
open NivatTrial.IncrementSupport NivatTrial.RealHalfPlaneRecurrence
open NivatTrial.RealDirectionGeometry NivatTrial.PeriodicBandCoding
open NivatTrial.DirectionalElimination NivatTrial.MinimalHull
open NivatTrial.BinomialDirections NivatTrial.LaurentAction

open scoped Classical
noncomputable section

private theorem det_relation_symmetric {h k : Lattice}
    (hdet : Geometry.det h k ≠ 0) : Geometry.det k h ≠ 0 := by
  rw [Geometry.det_swap]
  exact neg_ne_zero.mpr hdet

/-- The tangent difference agrees globally whenever two points of the hull
agree on the lower half-plane. The other difference directions are transverse
and are therefore uniquely determined by that half-plane. -/
theorem tangent_increment_agrees {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hs : List Lattice)
    (hann : iteratedIncrement hs (encode w θ) = 0)
    (v : Plane) (hv : v ≠ 0) (h : Lattice) (hmem : h ∈ hs)
    (hh : score v h = 0)
    (hpair : hs.Pairwise (fun a b => Geometry.det a b ≠ 0))
    {x y : Lattice → A} (hx : x ∈ languageHull θ)
    (hy : y ∈ languageHull θ)
    (hagree : ∀ z, score v z ≤ 0 → x z = y z) :
    increment (encode w x) h = increment (encode w y) h := by
  let ks := hs.erase h
  have hp : hs.Perm (h :: ks) := List.perm_cons_erase hmem
  have hpair' : (h :: ks).Pairwise (fun a b => Geometry.det a b ≠ 0) :=
    hpair.perm hp (fun hab => det_relation_symmetric hab)
  have htrans : ∀ k ∈ ks, score (-v) k ≠ 0 := by
    intro k hk
    have hdet : Geometry.det h k ≠ 0 := (List.pairwise_cons.mp hpair').1 k hk
    have hkv := transverse_other v hv h k hh hdet
    simpa only [score_neg_direction] using neg_ne_zero.mpr hkv
  have hxa : iteratedIncrement (h :: ks) (encode w x) = 0 := by
    rw [← iteratedIncrement_perm hp]
    exact iteratedIncrement_passes_to_languageHull hs
      (encode w θ) (encode w x) (encode_mem_languageHull w hx) hann
  have hya : iteratedIncrement (h :: ks) (encode w y) = 0 := by
    rw [← iteratedIncrement_perm hp]
    exact iteratedIncrement_passes_to_languageHull hs
      (encode w θ) (encode w y) (encode_mem_languageHull w hy) hann
  have hxinc : iteratedIncrement ks (increment (encode w x) h) = 0 := by
    rw [iteratedIncrement_commute, ← iteratedIncrement_cons]
    exact hxa
  have hyinc : iteratedIncrement ks (increment (encode w y) h) = 0 := by
    rw [iteratedIncrement_commute, ← iteratedIncrement_cons]
    exact hya
  apply eq_of_transverse_product ks (increment (encode w x) h)
    (increment (encode w y) h) (-v) 0 htrans hxinc hyinc
  intro z hz
  have hz0 : score v z ≤ 0 := by
    rw [score_neg_direction] at hz
    linarith
  have hz1 : score v (z + h) ≤ 0 := by
    rw [score_add, hh]
    simpa using hz0
  simp only [increment]
  change w (x (z + h)) - w (x z) = w (y (z + h)) - w (y z)
  rw [hagree (z + h) hz1, hagree z hz0]

/-- The finite-alphabet Kari--Moutot direction-symmetrization theorem for an
explicit product of nonparallel differences. -/
theorem directional_symmetry_of_product {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (hs : List Lattice) (hnonzero : ∀ h ∈ hs, h ≠ 0)
    (hpair : hs.Pairwise (fun h k => Geometry.det h k ≠ 0))
    (hann : iteratedIncrement hs (encode w θ) = 0) :
    ∃ ξ ∈ languageHull θ, ∀ v : Plane, v ≠ 0 →
      OneSidedExpansive ξ v → OneSidedExpansive ξ (-v) := by
  obtain ⟨ξ, hξ, hminimal⟩ := exists_minimal_hull θ
  have hannξ : iteratedIncrement hs (encode w ξ) = 0 :=
    iteratedIncrement_passes_to_languageHull hs (encode w θ)
      (encode w ξ) (encode_mem_languageHull w hξ) hann
  refine ⟨ξ, hξ, ?_⟩
  intro v hv hexp
  by_cases htrans : ∀ h ∈ hs, score v h ≠ 0
  · apply oneSidedExpansive_of_transverse_product ξ w hw hs (-v) _ hannξ
    intro h hh
    simpa only [score_neg_direction] using neg_ne_zero.mpr (htrans h hh)
  · have htan : ∃ h, h ∈ hs ∧ score v h = 0 := by
      push Not at htrans
      exact htrans
    obtain ⟨h, hmem, hh⟩ := htan
    obtain ⟨d, hd⟩ := exists_positive_score hv
    have hdet : Geometry.det h d ≠ 0 :=
      independent_of_score v h d (hnonzero h hmem) hh (ne_of_gt hd)
    obtain ⟨B, hcode⟩ := exists_finite_fiber_coding ξ w hw v hv hexp
      h d hdet hh hd
    have hfactor : ∀ x ∈ languageHull ξ, ∀ y ∈ languageHull ξ,
        (∀ z, score v z ≤ 0 → x z = y z) →
        increment (encode w x) h = increment (encode w y) h := by
      intro x hx y hy hagree
      exact tangent_increment_agrees ξ w hs hannξ v hv h hmem hh hpair hx hy hagree
    obtain ⟨η, hη, hηexp⟩ :=
      eliminate_direction ξ w h d v hd B hcode hfactor
    have heq := hminimal η hη
    simpa only [OneSidedExpansive, OneSidedNonexpansive, heq] using hηexp

/-- Any nonzero integral Laurent annihilator of a finite-alphabet encoding
produces the product hypothesis internally. -/
theorem directional_symmetry_of_annihilator {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (f : RingLaurent ℤ) (hf : f ≠ 0)
    (hann : act f (encode w θ) = 0) :
    ∃ ξ ∈ languageHull θ, ∀ v : Plane, v ≠ 0 →
      OneSidedExpansive ξ v → OneSidedExpansive ξ (-v) := by
  have hfinite : (Set.range (encode w θ)).Finite := by
    apply (Set.finite_range w).subset
    rintro a ⟨z, rfl⟩
    exact ⟨θ z, rfl⟩
  obtain ⟨ks, hpair, hnonzero, hprod⟩ :=
    independent_difference_annihilator f (encode w θ) hf hfinite hann
  exact directional_symmetry_of_product θ w hw ks hnonzero hpair hprod

/-- Low pattern complexity supplies the integral annihilator as well, so no
algebraic annihilator need be supplied by the caller. -/
theorem directional_symmetry_of_low_complexity {A : Type*} [Fintype A]
    (θ : Lattice → A) (w : A → ℤ) (hw : Function.Injective w)
    (S : Finset Lattice) (hlow : patternComplexity θ S ≤ S.card) :
    ∃ ξ ∈ languageHull θ, ∀ v : Plane, v ≠ 0 →
      OneSidedExpansive ξ v → OneSidedExpansive ξ (-v) := by
  obtain ⟨f, hf, hann⟩ :=
    NivatTrial.IntegerAnnihilator.exists_integer_annihilator θ S w hlow
  exact directional_symmetry_of_annihilator θ w hw f hf hann

/-- An injective relabeling identifies the two finite-window orbit closures.
The reverse direction is proved directly from each finite patch, rather than
using a compactness or topological embedding premise. -/
theorem decode_mem_languageHull {A B : Type*} (θ : Lattice → A)
    (w : A → B) (hw : Function.Injective w)
    {y : Lattice → B} (hy : y ∈ languageHull (encode w θ)) :
    ∃ x ∈ languageHull θ, encode w x = y := by
  have hvalue (z : Lattice) : ∃ a : A, w a = y z := by
    obtain ⟨u, hu⟩ := hy {z}
    exact ⟨θ (u + z), hu z (by simp)⟩
  let x : Lattice → A := fun z => Classical.choose (hvalue z)
  have hxvalue (z : Lattice) : w (x z) = y z := Classical.choose_spec (hvalue z)
  refine ⟨x, ?_, ?_⟩
  · intro S
    obtain ⟨u, hu⟩ := hy S
    refine ⟨u, ?_⟩
    intro z hz
    apply hw
    exact (hu z hz).trans (hxvalue z).symm
  · funext z
    exact hxvalue z

theorem oneSidedExpansive_encode_iff {A B : Type*} (θ : Lattice → A)
    (w : A → B) (hw : Function.Injective w) (v : Plane) :
    OneSidedExpansive (encode w θ) v ↔ OneSidedExpansive θ v := by
  constructor
  · intro henc hne
    obtain ⟨x, hx, y, hy, hxy, hagree⟩ := hne
    apply henc
    refine ⟨encode w x, encode_mem_languageHull w hx,
      encode w y, encode_mem_languageHull w hy, ?_, ?_⟩
    · intro he
      exact hxy (encode_injective hw he)
    · intro z hz
      exact congrArg w (hagree z hz)
  · intro hθ hne
    obtain ⟨x, hx, y, hy, hxy, hagree⟩ := hne
    obtain ⟨x', hx', heqx⟩ := decode_mem_languageHull θ w hw hx
    obtain ⟨y', hy', heqy⟩ := decode_mem_languageHull θ w hw hy
    apply hθ
    refine ⟨x', hx', y', hy', ?_, ?_⟩
    · intro he
      exact hxy (heqx ▸ heqy ▸ congrArg (encode w) he)
    · intro z hz
      apply hw
      exact (congrFun heqx z).trans ((hagree z hz).trans (congrFun heqy z).symm)

/-- Integer-valued form of Kari--Moutot: finite range and a nonzero integral
Laurent annihilator suffice for some point of the original language hull to
have symmetric one-sided expansive directions. -/
theorem directional_symmetry_of_finite_range (x : Lattice → ℤ)
    (hfinite : (Set.range x).Finite) (f : RingLaurent ℤ) (hf : f ≠ 0)
    (hann : act f x = 0) :
    ∃ ξ ∈ languageHull x, ∀ v : Plane, v ≠ 0 →
      OneSidedExpansive ξ v → OneSidedExpansive ξ (-v) := by
  let A := Set.range x
  let : Fintype A := hfinite.fintype
  let θ : Lattice → A := fun z => ⟨x z, ⟨z, rfl⟩⟩
  have hencode : encode Subtype.val θ = x := rfl
  have hinj : Function.Injective (Subtype.val : A → ℤ) := Subtype.val_injective
  obtain ⟨ξ, hξ, hsymm⟩ := directional_symmetry_of_annihilator θ
    Subtype.val hinj f hf (hencode ▸ hann)
  refine ⟨encode Subtype.val ξ, ?_, ?_⟩
  · rw [← hencode]
    exact encode_mem_languageHull Subtype.val hξ
  · intro v hv hexp
    have hξexp : OneSidedExpansive ξ v :=
      (oneSidedExpansive_encode_iff ξ Subtype.val hinj v).mp hexp
    exact (oneSidedExpansive_encode_iff ξ Subtype.val hinj (-v)).mpr
      (hsymm v hv hξexp)

end
end NivatTrial.KariMoutot
