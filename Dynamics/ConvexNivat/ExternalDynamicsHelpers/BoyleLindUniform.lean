import ConvexNivat.ExternalDynamicsHelpers.BoyleLindLemma32
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindRotation
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindGrowth

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

/-- Published Lemma 3.4, pulled back from unoriented lines to unit normals. -/
theorem boyleLind_lemma3_4 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (n : RealPlane) (hn : n ∈ unitNormals) (hexp : ¬ NonexpansiveLine ξ n) :
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ ∃ U : Set RealPlane,
      IsOpen U ∧ n ∈ U ∧ ∀ w ∈ U, w ∈ unitNormals →
        RealCodes ξ (lineBox w r t) (lineBox w 0 (t + 1)) := by
  obtain ⟨u,hu,hcode⟩ := boyleLind_lemma3_2 ξ A hA n hn hexp
  obtain ⟨s,hs,hcode⟩ := hcode (u+3) (by positivity)
  have hc := finite_box_code_tangential_extension ξ n hn s u (u+3) 1 hs.le hu.le
    (by positivity) (by norm_num) hcode
  obtain ⟨U,hU,hnU,hinc⟩ := near_normal_box_inclusions n hn (s+1) u (by positivity) hu
  refine ⟨(s+1)+1,u+1,by positivity,by positivity,U,hU,hnU,?_⟩
  intro w hw hwunit
  obtain ⟨hleft,hright⟩ := hinc w hw hwunit
  have hc' := realCodes_mono ξ _ _ _ _ hc hleft hright
  have he : u+1+1=u+2 := by ring
  rw [he]
  exact hc'

/-- Published Lemma 3.5, exact compact-family uniform finite coding. -/
theorem boyleLind_lemma3_5 (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A)
    (K : Set RealPlane) (hK : IsCompact K) (hunit : K ⊆ unitNormals)
    (hexp : ∀ n ∈ K, ¬ NonexpansiveLine ξ n) :
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧ ∀ n ∈ K,
      RealCodes ξ (lineBox n r t) (lineBox n 0 (t + 1)) := by
  classical
  have hlocal (n : K) := boyleLind_lemma3_4 ξ A hA n (hunit n.property) (hexp n n.property)
  choose r t hr ht U hU hnU hcode using hlocal
  have hcover : K ⊆ ⋃ n : K, U n := by
    intro n hn
    exact Set.mem_iUnion.mpr ⟨⟨n,hn⟩,hnU ⟨n,hn⟩⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover U hU hcover
  let R := 1+∑ n ∈ F, r n
  let T := 1+∑ n ∈ F, t n
  have hRs : 0 ≤ ∑ n ∈ F, r n := Finset.sum_nonneg (fun n _ => (hr n).le)
  have hTs : 0 ≤ ∑ n ∈ F, t n := Finset.sum_nonneg (fun n _ => (ht n).le)
  refine ⟨R,T,by dsimp [R]; linarith,by dsimp [T]; linarith,?_⟩
  intro n hn
  obtain ⟨i,hi,hin⟩ := Set.mem_iUnion₂.mp (hF hn)
  have hri : r i ≤ R := by
    have hsum := Finset.single_le_sum (fun j _ => (hr j).le) hi
    dsimp [R]
    linarith
  have hti : t i ≤ T := by
    have hsum := Finset.single_le_sum (fun j _ => (ht j).le) hi
    dsimp [T]
    linarith
  exact finite_box_growth_code_mono ξ n (hunit hn) (r i) (t i) R T (hr i).le (ht i).le
    hri hti (hcode i n hin (hunit hn))

end
end ConvexNivat.ExternalDynamicsHelpers
