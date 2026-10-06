import ConvexNivat.ExternalDynamicsHelpers.BoyleLindCoding
import ConvexNivat.ExternalDynamicsHelpers.BoyleLindBoxes

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

/-- The final statement of Lemma 3.2, derived by the same Minkowski sum. -/
theorem finite_box_code_tangential_extension (ξ : Configuration ℤ)
    (n : RealPlane) (hn : n ∈ unitNormals) (r t s a : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hcode : RealCodes ξ (lineBox n r t) (lineBox n 0 s)) :
    RealCodes ξ (lineBox n (r + a) t) (lineBox n a s) := by
  have h := realCodes_minkowski_sum ξ _ _ (lineBox n a 0) hcode
  rw [lineBox_minkowski_sum n hn r t a 0 hr ht ha (by norm_num),
    lineBox_minkowski_sum n hn 0 s a 0 (by norm_num) hs ha (by norm_num)] at h
  simpa using h

/-- Band enlargement and iteration in the proof of Lemma 3.3. -/
theorem box_growth_codes_band_growth (ξ : Configuration ℤ)
    (n : RealPlane) (hn : n ∈ unitNormals) (r t ε : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hε : 0 < ε)
    (hcode : RealCodes ξ (lineBox n r t) (lineBox n 0 (t + ε))) :
    RealCodes ξ (realBand n t) (realBand n (t + ε)) := by
  intro b x hx y hy hag z hz
  let a := |realDot (embed z-b) (realQuarterTurn n)|
  have hc := finite_box_code_tangential_extension ξ n hn r t (t+ε) a
    hr.le ht.le (by positivity) (abs_nonneg _) hcode
  refine hc b x hx y hy ?_ z ?_
  · intro w hw
    exact hag w hw.2
  · exact ⟨le_rfl,hz⟩

private theorem band_split_abs (r q a : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q)
    (ha : |a| ≤ r+q) : ∃ b c : ℝ, |b| ≤ r ∧ |c| ≤ q ∧ a=b+c := by
  rw [abs_le] at ha
  by_cases hlo : a < -r
  · refine ⟨-r,a+r,?_,?_,by ring⟩
    · simpa [abs_of_nonneg hr]
    · rw [abs_le]; constructor <;> linarith
  · by_cases hhi : r<a
    · refine ⟨r,a-r,?_,?_,by ring⟩
      · simpa [abs_of_nonneg hr]
      · rw [abs_le]; constructor <;> linarith
    · refine ⟨a,0,?_,by simpa,by ring⟩
      rw [abs_le]; constructor <;> linarith

private theorem band_minkowski (n : RealPlane) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    realMinkowskiSum (realBand n r) (realBand n s) = realBand n (r+s) := by
  ext x
  constructor
  · rintro ⟨e,he,f,hf,rfl⟩
    change |realDot (e+f) n| ≤ r+s
    have hd : realDot (e+f) n=realDot e n+realDot f n := by dsimp [realDot]; ring
    rw [hd]
    exact (abs_add_le _ _).trans (add_le_add he hf)
  · intro hx
    by_cases hn : n=0
    · subst n
      refine ⟨0,?_,x,?_,by simp⟩
      · simpa [realBand,realDot] using hr
      · simpa [realBand,realDot] using hs
    · have hv : ∃ v : RealPlane, realDot v n=1 := by
        by_cases h1 : n.1=0
        · have h2 : n.2≠0 := by intro h2; exact hn (Prod.ext h1 h2)
          exact ⟨(0,1/n.2),by simp [realDot,h2]⟩
        · exact ⟨(1/n.1,0),by simp [realDot,h1]⟩
      obtain ⟨v,hv⟩ := hv
      obtain ⟨b,c,hb,hc,heq⟩ := band_split_abs r s (realDot x n) hr hs hx
      let e : RealPlane := (b*v.1,b*v.2)
      have hde : realDot e n=b := by dsimp [realDot,e] at *; nlinarith [congrArg (fun k : ℝ => b*k) hv]
      have hdf : realDot (x-e) n=c := by
        have hsub : realDot (x-e) n=realDot x n-realDot e n := by dsimp [realDot]; ring
        rw [hsub,hde,heq]; ring
      refine ⟨e,?_,x-e,?_,by dsimp [e]; abel⟩
      · change |realDot e n| ≤ r
        rwa [hde]
      · change |realDot (x-e) n| ≤ s
        rwa [hdf]

theorem band_growth_iterates (ξ : Configuration ℤ) (n : RealPlane)
    (t ε : ℝ) (ht : 0 ≤ t) (hε : 0 < ε)
    (hcode : RealCodes ξ (realBand n t) (realBand n (t + ε))) :
    ∀ j : ℕ, RealCodes ξ (realBand n t) (realBand n (t + (j : ℝ) * ε)) := by
  intro j
  induction j with
  | zero => simpa using (show RealCodes ξ (realBand n t) (realBand n t) from
      fun _ _ _ _ _ h => h)
  | succ j ih =>
    have h := realCodes_minkowski_sum ξ _ _ (realBand n ((j:ℝ)*ε)) hcode
    rw [band_minkowski n t ((j:ℝ)*ε) ht (by positivity),
      band_minkowski n (t+ε) ((j:ℝ)*ε) (by positivity) (by positivity)] at h
    have hc := realCodes_trans ξ _ _ _ ih h
    have he : t+((j+1:ℕ):ℝ)*ε=(t+ε)+(j:ℝ)*ε := by push_cast; ring
    rw [he]
    exact hc

/-- Published Lemma 3.3, finite coding implies expansiveness. -/
theorem boyleLind_lemma3_3 (ξ : Configuration ℤ)
    (n : RealPlane) (hn : n ∈ unitNormals) (r t ε : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hε : 0 < ε)
    (hcode : RealCodes ξ (lineBox n r t) (lineBox n 0 (t + ε))) :
    ¬ NonexpansiveLine ξ n := by
  intro hnon
  have hband := box_growth_codes_band_growth ξ n hn r t ε hr ht hε hcode
  have hdet : BandDetermines ξ n t := by
    intro x hx y hy hag
    funext z
    obtain ⟨j,hj⟩ := exists_nat_gt ((|realDot (embed z) n|-t)/ε)
    have hmul := (div_lt_iff₀ hε).mp hj
    have hc := band_growth_iterates ξ n t ε ht.le hε hband j 0 x hx y hy
    apply hc ?_ z ?_
    · simpa [realTranslate] using hag
    · change |realDot (embed z-0) n| ≤ t+(j:ℝ)*ε
      simp only [sub_zero]
      linarith
  exact (nonexpansive_iff_no_determining_band ξ n (unit_normal_ne_zero n hn)).mp hnon t ht hdet

/-- Raising both dimensions preserves the unit normal-growth code, Lemma 3.5. -/
theorem finite_box_growth_code_mono (ξ : Configuration ℤ)
    (n : RealPlane) (hn : n ∈ unitNormals) (r t R T : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hR : r ≤ R) (hT : t ≤ T)
    (hcode : RealCodes ξ (lineBox n r t) (lineBox n 0 (t + 1))) :
    RealCodes ξ (lineBox n R T) (lineBox n 0 (T + 1)) := by
  have h := realCodes_minkowski_sum ξ _ _ (lineBox n 0 (T-t)) hcode
  rw [lineBox_minkowski_sum n hn r t 0 (T-t) hr ht (by norm_num) (sub_nonneg.mpr hT),
    lineBox_minkowski_sum n hn 0 (t+1) 0 (T-t) (by norm_num) (by positivity)
      (by norm_num) (sub_nonneg.mpr hT)] at h
  have h1 : t+1+(T-t)=T+1 := by ring
  simp only [add_zero,zero_add,add_sub_cancel,h1] at h
  apply realCodes_mono ξ _ _ _ _ h
  · intro p hp
    exact ⟨hp.1.trans hR,hp.2⟩
  · exact Set.Subset.rfl

end
end ConvexNivat.ExternalDynamicsHelpers
