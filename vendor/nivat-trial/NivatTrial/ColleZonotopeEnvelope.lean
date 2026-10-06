import NivatTrial.ColleLongFaces

/-! Finite directional envelopes with genuine long supporting faces. -/

namespace NivatTrial.ColleZonotopeEnvelope

open NivatTrial.Geometry NivatTrial.ColleEnvelopeGeometry
open NivatTrial.ColleMaximalEnvelope NivatTrial.ColleLongFaces
open NivatTrial.LatticePolygon
open scoped Classical
noncomputable section

def signedDirections {n : ℕ} (v : Fin n → Lattice) : Finset Lattice :=
  (Finset.univ.image v) ∪ (Finset.univ.image fun i => -v i)

theorem mem_signedDirections {n : ℕ} (v : Fin n → Lattice) (d : Lattice) :
    d ∈ signedDirections v ↔ ∃ i, d = v i ∨ d = -v i := by
  simp only [signedDirections, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨i,Or.inl hi.symm⟩
    · exact ⟨i,Or.inr hi.symm⟩
  · rintro ⟨i,hi | hi⟩
    · exact Or.inl ⟨i,hi.symm⟩
    · exact Or.inr ⟨i,hi.symm⟩

def boxCoefficients {n : ℕ} (N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

def boxPoint {n : ℕ} (v : Fin n → Lattice) (t : Fin n → ℤ) : Lattice :=
  ∑ i, t i • v i

def coefficientBox {n : ℕ} (v : Fin n → Lattice) (N : ℕ) : Finset Lattice :=
  (boxCoefficients N).image (boxPoint v)

theorem mem_boxCoefficients {n : ℕ} (N : ℕ) (t : Fin n → ℤ) :
    t ∈ boxCoefficients N ↔ ∀ i, -(N : ℤ) ≤ t i ∧ t i ≤ N := by
  simp [boxCoefficients, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mem_coefficientBox {n : ℕ} (v : Fin n → Lattice) (N : ℕ) (z : Lattice) :
    z ∈ coefficientBox v N ↔
      ∃ t : Fin n → ℤ, (∀ i, -(N : ℤ) ≤ t i ∧ t i ≤ N) ∧ boxPoint v t = z := by
  simp only [coefficientBox, Finset.mem_image, mem_boxCoefficients]

theorem boxPoint_change {n : ℕ} (v : Fin n → Lattice) (t : Fin n → ℤ)
    (i : Fin n) (a b : ℤ) :
    boxPoint v (fun j => if j = i then b else t j) =
      boxPoint v (fun j => if j = i then a else t j) + (b-a) • v i := by
  let s := Finset.univ.erase i
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hsum (c : ℤ) :
      boxPoint v (fun j => if j = i then c else t j) =
        (∑ j ∈ s, t j • v j) + c • v i := by
    unfold boxPoint
    calc
      (∑ j, (if j = i then c else t j) • v j) =
          (∑ j ∈ s, (if j = i then c else t j) • v j) +
            (if i = i then c else t i) • v i := by
              exact (Finset.sum_erase_add Finset.univ _ hi).symm
      _ = (∑ j ∈ s, t j • v j) + c • v i := by
        have hs : (∑ j ∈ s, (if j = i then c else t j) • v j) =
            ∑ j ∈ s, t j • v j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          simp [hji]
        simp only [hs, ite_true]
  rw [hsum, hsum]
  simp only [sub_smul]
  abel

theorem det_boxPoint {n : ℕ} (d : Lattice) (v : Fin n → Lattice)
    (t : Fin n → ℤ) :
    det d (boxPoint v t) = ∑ i, t i * det d (v i) := by
  let φ : Lattice →+ ℤ :=
    { toFun := det d
      map_zero' := det_zero_right d
      map_add' := det_add_right d }
  change φ (∑ i, t i • v i) = ∑ i, t i * det d (v i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact det_zsmul_right d (v i) (t i)

theorem coefficientBox_nonempty {n : ℕ} (v : Fin n → Lattice) (N : ℕ) :
    (coefficientBox v N).Nonempty := by
  refine ⟨boxPoint v (fun _ => 0), (mem_coefficientBox v N _).2 ?_⟩
  exact ⟨fun _ => 0, by simp, rfl⟩

theorem coefficientBox_longFaces_at {n : ℕ} (v : Fin n → Lattice)
    (N : ℕ) (hN : 1 ≤ N) (i : Fin n) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    LongFaces {δ • v i} (coefficientBox v N : Set Lattice) := by
  intro d hd z hz hmin
  have hd' : d = δ • v i := Finset.mem_singleton.mp hd
  obtain ⟨t,ht,rfl⟩ := (mem_coefficientBox v N z).mp hz
  let t0 : Fin n → ℤ := fun j => if j = i then 0 else t j
  let t1 : Fin n → ℤ := fun j => if j = i then δ else t j
  have ht0 : ∀ j, -(N : ℤ) ≤ t0 j ∧ t0 j ≤ N := by
    intro j
    by_cases hji : j = i
    · simp [t0,hji]
    · simpa [t0,hji] using ht j
  have ht1 : ∀ j, -(N : ℤ) ≤ t1 j ∧ t1 j ≤ N := by
    intro j
    by_cases hji : j = i
    · rcases hδ with rfl | rfl <;> simp [t1,hji] <;> omega
    · simpa [t1,hji] using ht j
  have hdet : det d (v i) = 0 := by
    rw [hd', det_zsmul_left, det_self, mul_zero]
  have hp0 : boxPoint v t = boxPoint v t0 + t i • v i := by
    have heq : (fun j => if j = i then t i else t j) = t := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    simpa only [heq, t0, sub_zero] using boxPoint_change v t i 0 (t i)
  have hp1 : boxPoint v t1 = boxPoint v t0 + d := by
    simpa [t0,t1,hd'] using boxPoint_change v t i 0 δ
  have hface : det d (boxPoint v t0) = det d (boxPoint v t) := by
    rw [hp0, det_add_right, det_zsmul_right, hdet]
    simp
  refine ⟨boxPoint v t0, (mem_coefficientBox v N _).2 ⟨t0,ht0,rfl⟩,?_,hface⟩
  rw [← hp1]
  exact (mem_coefficientBox v N _).2 ⟨t1,ht1,rfl⟩

theorem coefficientBox_longFaces {n : ℕ} (v : Fin n → Lattice)
    (N : ℕ) (hN : 1 ≤ N) :
    LongFaces (signedDirections v) (coefficientBox v N : Set Lattice) := by
  intro d hd z hz hmin
  obtain ⟨i,hi | hi⟩ := (mem_signedDirections v d).mp hd
  · subst d
    exact (coefficientBox_longFaces_at v N hN i 1 (Or.inl rfl))
      (v i) (by simp) z hz hmin
  · subst d
    exact (coefficientBox_longFaces_at v N hN i (-1) (Or.inr rfl))
      (-v i) (by simp) z hz hmin

theorem other_index {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    ∃ j : Fin n, j ≠ i := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i1 ≠ i0 := by
    intro he
    have hv := congrArg Fin.val he
    norm_num [i0,i1] at hv
  by_cases hi : i = i0
  · exact ⟨i1,by simpa [hi] using h01⟩
  · exact ⟨i0,Ne.symm hi⟩

theorem signedDirection_transverse {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (d : Lattice) (hd : d ∈ signedDirections v) :
    ∃ j : Fin n, det d (v j) ≠ 0 := by
  obtain ⟨i,rfl | rfl⟩ := (mem_signedDirections v d).mp hd
  · obtain ⟨j,hji⟩ := other_index hn i
    exact ⟨j,hpair i j (Ne.symm hji)⟩
  · obtain ⟨j,hji⟩ := other_index hn i
    refine ⟨j,?_⟩
    rw [det_neg_left]
    exact neg_ne_zero.mpr (hpair i j (Ne.symm hji))

theorem boxPoint_single {n : ℕ} (v : Fin n → Lattice)
    (j : Fin n) (k : ℤ) :
    boxPoint v (fun i => if i = j then k else 0) = k • v j := by
  simp [boxPoint]

theorem smul_mem_coefficientBox {n : ℕ} (v : Fin n → Lattice)
    (N : ℕ) (j : Fin n) (k : ℤ)
    (hk : -(N : ℤ) ≤ k ∧ k ≤ N) : k • v j ∈ coefficientBox v N := by
  apply (mem_coefficientBox v N _).2
  refine ⟨fun i => if i = j then k else 0,?_,boxPoint_single v j k⟩
  intro i
  by_cases hij : i = j
  · simpa [hij] using hk
  · simp [hij]

theorem coefficientBox_deep_support {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (N : ℕ) (hN : 1 ≤ N)
    (d : Lattice) (hd : d ∈ signedDirections v) :
    ∃ w ∈ coefficientBox v N, det d w ≤ -(N : ℤ) := by
  obtain ⟨j,hj⟩ := signedDirection_transverse hn v hpair d hd
  by_cases hpos : 0 < det d (v j)
  · refine ⟨(-(N : ℤ)) • v j,?_,?_⟩
    · apply smul_mem_coefficientBox
      omega
    · rw [det_zsmul_right]
      have hprod := mul_nonneg (show (0 : ℤ) ≤ N by omega)
        (show (0 : ℤ) ≤ det d (v j)-1 by omega)
      nlinarith
  · refine ⟨(N : ℤ) • v j,?_,?_⟩
    · apply smul_mem_coefficientBox
      omega
    · rw [det_zsmul_right]
      have hprod := mul_nonneg (show (0 : ℤ) ≤ N by omega)
        (show (0 : ℤ) ≤ -det d (v j)-1 by omega)
      nlinarith

theorem exists_finite_long_envelope {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (F : Finset Lattice) :
    ∃ T : Finset Lattice, F ⊆ T ∧ IsLatticeConvex T ∧
      IsEnvelope (signedDirections v) (T : Set Lattice) ∧
      LongFaces (signedDirections v) (T : Set Lattice) := by
  let D := signedDirections v
  let N : ℕ := (D.product F).sup (fun p => (det p.1 p.2).natAbs) + 1
  have hN : 1 ≤ N := by omega
  let B := coefficientBox v N
  have hB : B.Nonempty := coefficientBox_nonempty v N
  have hbound : ∀ d ∈ D, ∀ z ∈ F, -(N : ℤ) ≤ det d z := by
    intro d hd z hz
    have hp : (d,z) ∈ D.product F := Finset.mem_product.mpr ⟨hd,hz⟩
    have hle : (det d z).natAbs ≤ (D.product F).sup
        (fun p => (det p.1 p.2).natAbs) :=
      Finset.le_sup (f := fun p : Lattice × Lattice => (det p.1 p.2).natAbs) hp
    have hcast : ((det d z).natAbs : ℤ) ≤ N := by
      exact_mod_cast (show (det d z).natAbs ≤ N by omega)
    have hlow : -(det d z) ≤ ((det d z).natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -(det d z)))
    omega
  have hF : (F : Set Lattice) ⊆ envelope D (lowerSupport B) := by
    intro z hz d hd
    obtain ⟨w,hw,hdeep⟩ := coefficientBox_deep_support hn v hpair N hN d hd
    exact (lowerSupport_le hw d).trans (hdeep.trans (hbound d hd z hz))
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro he
    have hv := congrArg Fin.val he
    norm_num [i0,i1] at hv
  have hv0 : v i0 ∈ D := (mem_signedDirections v _).2 ⟨i0,Or.inl rfl⟩
  have hnv0 : -v i0 ∈ D := (mem_signedDirections v _).2 ⟨i0,Or.inr rfl⟩
  have hv1 : v i1 ∈ D := (mem_signedDirections v _).2 ⟨i1,Or.inl rfl⟩
  have hnv1 : -v i1 ∈ D := (mem_signedDirections v _).2 ⟨i1,Or.inr rfl⟩
  obtain ⟨T,hBT,hconv,hTeq,_⟩ := exists_finite_envelope D B hB
    (v i0) (v i1) (hpair i0 i1 h01) hv0 hnv0 hv1 hnv1
  refine ⟨T,?_,hconv,?_,?_⟩
  · intro z hz
    have hz' := hF hz
    rwa [← hTeq] at hz'
  · rw [hTeq]
    exact envelope_isEnvelope D (lowerSupport B)
  · rw [hTeq]
    exact (coefficientBox_longFaces v N hN).finite_envelope hB

/-- Orient all generators other than the selected tangent toward its
nonnegative determinant half-plane. -/
def positiveGenerators {n : ℕ} (v : Fin n → Lattice) (i0 : Fin n) :
    Fin n → Lattice := fun j =>
  if j = i0 then v j else
    if 0 < det (v i0) (v j) then v j else -v j

theorem positiveGenerators_self {n : ℕ} (v : Fin n → Lattice) (i0 : Fin n) :
    positiveGenerators v i0 i0 = v i0 := by simp [positiveGenerators]

theorem positiveGenerators_det_pos {n : ℕ} (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 j : Fin n) (hji : j ≠ i0) :
    0 < det (v i0) (positiveGenerators v i0 j) := by
  by_cases hpos : 0 < det (v i0) (v j)
  · simp [positiveGenerators,hji,hpos]
  · have hne := hpair i0 j (Ne.symm hji)
    have hneg : det (v i0) (v j) < 0 := by omega
    simpa [positiveGenerators,hji,hpos,det_neg_right] using (neg_pos.mpr hneg)

theorem signedDirections_positiveGenerators {n : ℕ}
    (v : Fin n → Lattice) (i0 : Fin n) :
    signedDirections (positiveGenerators v i0) = signedDirections v := by
  ext d
  simp only [mem_signedDirections]
  constructor
  · rintro ⟨i,hi | hi⟩
    · by_cases h : i = i0
      · exact ⟨i,Or.inl (by simpa [positiveGenerators,h] using hi)⟩
      · by_cases hp : 0 < det (v i0) (v i)
        · exact ⟨i,Or.inl (by simpa [positiveGenerators,h,hp] using hi)⟩
        · exact ⟨i,Or.inr (by simpa [positiveGenerators,h,hp] using hi)⟩
    · by_cases h : i = i0
      · exact ⟨i,Or.inr (by simpa [positiveGenerators,h] using hi)⟩
      · by_cases hp : 0 < det (v i0) (v i)
        · exact ⟨i,Or.inr (by simpa [positiveGenerators,h,hp] using hi)⟩
        · exact ⟨i,Or.inl (by simpa [positiveGenerators,h,hp] using hi)⟩
  · rintro ⟨i,hi | hi⟩
    · by_cases h : i = i0
      · exact ⟨i,Or.inl (by simpa [positiveGenerators,h] using hi)⟩
      · by_cases hp : 0 < det (v i0) (v i)
        · exact ⟨i,Or.inl (by simpa [positiveGenerators,h,hp] using hi)⟩
        · exact ⟨i,Or.inr (by simpa [positiveGenerators,h,hp] using hi)⟩
    · by_cases h : i = i0
      · exact ⟨i,Or.inr (by simpa [positiveGenerators,h] using hi)⟩
      · by_cases hp : 0 < det (v i0) (v i)
        · exact ⟨i,Or.inr (by simpa [positiveGenerators,h,hp] using hi)⟩
        · exact ⟨i,Or.inl (by simpa [positiveGenerators,h,hp] using hi)⟩

def oneSidedCoefficients {n : ℕ} (i0 : Fin n) (N : ℕ) :
    Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j =>
    if j = i0 then Finset.Icc (-(N : ℤ)) (N : ℤ)
    else Finset.Icc 0 (N : ℤ)

def oneSidedBox {n : ℕ} (v : Fin n → Lattice) (i0 : Fin n)
    (N : ℕ) : Finset Lattice :=
  (oneSidedCoefficients i0 N).image (boxPoint (positiveGenerators v i0))

theorem mem_oneSidedCoefficients {n : ℕ} (i0 : Fin n)
    (N : ℕ) (t : Fin n → ℤ) :
    t ∈ oneSidedCoefficients i0 N ↔
      ∀ j, (if j = i0 then -(N : ℤ) else 0) ≤ t j ∧ t j ≤ N := by
  simp only [oneSidedCoefficients,Fintype.mem_piFinset]
  constructor
  · intro ht j
    have hj := ht j
    by_cases h : j = i0 <;> simpa [h] using hj
  · intro ht j
    have hj := ht j
    by_cases h : j = i0 <;> simpa [h] using hj

theorem mem_oneSidedBox {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) (z : Lattice) :
    z ∈ oneSidedBox v i0 N ↔
      ∃ t : Fin n → ℤ,
        (∀ j, (if j = i0 then -(N : ℤ) else 0) ≤ t j ∧ t j ≤ N) ∧
        boxPoint (positiveGenerators v i0) t = z := by
  simp only [oneSidedBox,Finset.mem_image,mem_oneSidedCoefficients]

theorem oneSidedBox_nonempty {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) : (oneSidedBox v i0 N).Nonempty := by
  refine ⟨0,(mem_oneSidedBox v i0 N 0).2 ?_⟩
  refine ⟨fun _ => 0,?_,?_⟩
  · intro j
    by_cases h : j = i0 <;> simp [h]
  · simp [boxPoint]

theorem oneSidedBox_longFaces_at {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) (hN : 1 ≤ N) (i : Fin n) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) :
    LongFaces {δ • positiveGenerators v i0 i} (oneSidedBox v i0 N : Set Lattice) := by
  intro d hd z hz hmin
  have hd' : d = δ • positiveGenerators v i0 i := Finset.mem_singleton.mp hd
  obtain ⟨t,ht,rfl⟩ := (mem_oneSidedBox v i0 N z).mp hz
  let a : ℤ := if δ = 1 then 0 else 1
  let b : ℤ := if δ = 1 then 1 else 0
  have hab : b - a = δ := by
    rcases hδ with h | h <;> simp [a,b,h]
  let t0 : Fin n → ℤ := fun j => if j = i then a else t j
  let t1 : Fin n → ℤ := fun j => if j = i then b else t j
  have hcoeff (c : ℤ) (hc : c = 0 ∨ c = 1) :
      ∀ j, (if j = i0 then -(N : ℤ) else 0) ≤
        (if j = i then c else t j) ∧
        (if j = i then c else t j) ≤ N := by
    intro j
    by_cases hji : j = i
    · rcases hc with rfl | rfl
      · simp [hji]; omega
      · simp [hji]; omega
    · simpa [hji] using ht j
  have ha : a = 0 ∨ a = 1 := by
    rcases hδ with h | h <;> simp [a,h]
  have hb : b = 0 ∨ b = 1 := by
    rcases hδ with h | h <;> simp [b,h]
  have ht0 : ∀ j, (if j = i0 then -(N : ℤ) else 0) ≤ t0 j ∧ t0 j ≤ N :=
    hcoeff a ha
  have ht1 : ∀ j, (if j = i0 then -(N : ℤ) else 0) ≤ t1 j ∧ t1 j ≤ N :=
    hcoeff b hb
  have hdet : det d (positiveGenerators v i0 i) = 0 := by
    rw [hd',det_zsmul_left,det_self,mul_zero]
  have heq : (fun j => if j = i then t i else t j) = t := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  have hp0 : boxPoint (positiveGenerators v i0) t =
      boxPoint (positiveGenerators v i0) t0 + (t i-a) • positiveGenerators v i0 i := by
    simpa only [heq,t0] using boxPoint_change (positiveGenerators v i0) t i a (t i)
  have hp1 : boxPoint (positiveGenerators v i0) t1 =
      boxPoint (positiveGenerators v i0) t0 + d := by
    simpa only [t0,t1,hab,hd'] using
      boxPoint_change (positiveGenerators v i0) t i a b
  have hface : det d (boxPoint (positiveGenerators v i0) t0) =
      det d (boxPoint (positiveGenerators v i0) t) := by
    rw [hp0,det_add_right,det_zsmul_right,hdet]
    simp
  refine ⟨boxPoint (positiveGenerators v i0) t0,
    (mem_oneSidedBox v i0 N _).2 ⟨t0,ht0,rfl⟩,?_,hface⟩
  rw [← hp1]
  exact (mem_oneSidedBox v i0 N _).2 ⟨t1,ht1,rfl⟩

theorem oneSidedBox_longFaces {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) (hN : 1 ≤ N) :
    LongFaces (signedDirections v) (oneSidedBox v i0 N : Set Lattice) := by
  rw [← signedDirections_positiveGenerators v i0]
  intro d hd z hz hmin
  obtain ⟨i,hi | hi⟩ := (mem_signedDirections (positiveGenerators v i0) d).mp hd
  · subst d
    exact (oneSidedBox_longFaces_at v i0 N hN i 1 (Or.inl rfl))
      (positiveGenerators v i0 i) (by simp) z hz hmin
  · subst d
    exact (oneSidedBox_longFaces_at v i0 N hN i (-1) (Or.inr rfl))
      (-positiveGenerators v i0 i) (by simp) z hz hmin

theorem oneSidedBox_mem_zero {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) : 0 ∈ oneSidedBox v i0 N := by
  exact (mem_oneSidedBox v i0 N 0).2
    ⟨fun _ => 0,by intro j; by_cases h : j = i0 <;> simp [h],by simp [boxPoint]⟩

theorem oneSidedBox_score_nonneg {n : ℕ} (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 : Fin n) (N : ℕ) (z : Lattice)
    (hz : z ∈ oneSidedBox v i0 N) : 0 ≤ det (v i0) z := by
  obtain ⟨t,ht,rfl⟩ := (mem_oneSidedBox v i0 N z).mp hz
  rw [det_boxPoint]
  apply Finset.sum_nonneg
  intro j hj
  by_cases h : j = i0
  · subst j
    simp [positiveGenerators_self,det_self]
  · have htj : 0 ≤ t j := by simpa [h] using (ht j).1
    exact mul_nonneg htj (le_of_lt (positiveGenerators_det_pos v hpair i0 j h))

theorem oneSidedBox_support_zero {n : ℕ} (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 : Fin n) (N : ℕ) :
    lowerSupport (oneSidedBox v i0 N) (v i0) = 0 := by
  apply le_antisymm
  · simpa using lowerSupport_le (oneSidedBox_mem_zero v i0 N) (v i0)
  · obtain ⟨z,hz,he⟩ := lowerSupport_attained
      (oneSidedBox v i0 N) (oneSidedBox_nonempty v i0 N) (v i0)
    rw [← he]
    exact oneSidedBox_score_nonneg v hpair i0 N z hz

theorem oneSidedBox_smul_mem {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) (j : Fin n) (k : ℤ)
    (hk : (if j = i0 then -(N : ℤ) else 0) ≤ k ∧ k ≤ N) :
    k • positiveGenerators v i0 j ∈ oneSidedBox v i0 N := by
  apply (mem_oneSidedBox v i0 N _).2
  refine ⟨fun i => if i = j then k else 0,?_,boxPoint_single (positiveGenerators v i0) j k⟩
  intro i
  by_cases hij : i = j
  · simpa [hij] using hk
  · by_cases hi0 : i = i0
    · subst i
      simp [hij]
    · simp [hij,hi0]

theorem oneSidedBox_deep_transverse {n : ℕ} (v : Fin n → Lattice)
    (i0 : Fin n) (N : ℕ) (hN : 1 ≤ N)
    (d : Lattice) (hd : det d (v i0) ≠ 0) :
    ∃ w ∈ oneSidedBox v i0 N, det d w ≤ -(N : ℤ) := by
  by_cases hpos : 0 < det d (v i0)
  · refine ⟨(-(N : ℤ)) • v i0,?_,?_⟩
    · rw [← positiveGenerators_self v i0]
      exact oneSidedBox_smul_mem v i0 N i0 _ (by simp)
    · rw [det_zsmul_right]
      have hprod := mul_nonneg (show (0 : ℤ) ≤ N by omega)
        (show (0 : ℤ) ≤ det d (v i0)-1 by omega)
      nlinarith
  · refine ⟨(N : ℤ) • v i0,?_,?_⟩
    · rw [← positiveGenerators_self v i0]
      exact oneSidedBox_smul_mem v i0 N i0 _ (by simp)
    · rw [det_zsmul_right]
      have hprod := mul_nonneg (show (0 : ℤ) ≤ N by omega)
        (show (0 : ℤ) ≤ -det d (v i0)-1 by omega)
      nlinarith

theorem oneSidedBox_deep_negative_tangent {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 : Fin n) (N : ℕ) (hN : 1 ≤ N) :
    ∃ w ∈ oneSidedBox v i0 N, det (-v i0) w ≤ -(N : ℤ) := by
  obtain ⟨j,hji⟩ := other_index hn i0
  have hpos := positiveGenerators_det_pos v hpair i0 j hji
  refine ⟨(N : ℤ) • positiveGenerators v i0 j,?_,?_⟩
  · exact oneSidedBox_smul_mem v i0 N j _ (by simp [hji])
  · rw [det_zsmul_right,det_neg_left]
    have hprod := mul_nonneg (show (0 : ℤ) ≤ N by omega)
      (show (0 : ℤ) ≤ det (v i0) (positiveGenerators v i0 j)-1 by omega)
    nlinarith

theorem oneSidedBox_deep_except_tangent {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 : Fin n) (N : ℕ) (hN : 1 ≤ N)
    (d : Lattice) (hd : d ∈ signedDirections v) (hd0 : d ≠ v i0) :
    ∃ w ∈ oneSidedBox v i0 N, det d w ≤ -(N : ℤ) := by
  obtain ⟨i,hi | hi⟩ := (mem_signedDirections v d).mp hd
  · have hneq : i ≠ i0 := by
      intro he
      exact hd0 (by simpa [he] using hi)
    have htrans : det d (v i0) ≠ 0 := by
      rw [hi]
      exact hpair i i0 hneq
    exact oneSidedBox_deep_transverse v i0 N hN d htrans
  · by_cases hieq : i = i0
    · subst i
      subst d
      exact oneSidedBox_deep_negative_tangent hn v hpair i0 N hN
    · have htrans : det d (v i0) ≠ 0 := by
        rw [hi,det_neg_left]
        exact neg_ne_zero.mpr (hpair i i0 hieq)
      exact oneSidedBox_deep_transverse v i0 N hN d htrans

/-- The initial E-enveloped window can have a prescribed exposed face at
score zero, provided the finite observation window lies on that side. -/
theorem exists_finite_long_envelope_on_face {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → Lattice)
    (hpair : ∀ i j, i ≠ j → det (v i) (v j) ≠ 0)
    (i0 : Fin n) (F : Finset Lattice)
    (hF : ∀ z ∈ F, 0 ≤ det (v i0) z) :
    ∃ T : Finset Lattice, F ⊆ T ∧ IsLatticeConvex T ∧
      IsEnvelope (signedDirections v) (T : Set Lattice) ∧
      LongFaces (signedDirections v) (T : Set Lattice) ∧
      lowerSupport T (v i0) = 0 := by
  let D := signedDirections v
  let N : ℕ := (D.product F).sup (fun p => (det p.1 p.2).natAbs) + 1
  have hN : 1 ≤ N := by omega
  let B := oneSidedBox v i0 N
  have hB : B.Nonempty := oneSidedBox_nonempty v i0 N
  have hbound : ∀ d ∈ D, ∀ z ∈ F, -(N : ℤ) ≤ det d z := by
    intro d hd z hz
    have hp : (d,z) ∈ D.product F := Finset.mem_product.mpr ⟨hd,hz⟩
    have hle : (det d z).natAbs ≤ (D.product F).sup
        (fun p => (det p.1 p.2).natAbs) :=
      Finset.le_sup (f := fun p : Lattice × Lattice => (det p.1 p.2).natAbs) hp
    have hcast : ((det d z).natAbs : ℤ) ≤ N := by
      exact_mod_cast (show (det d z).natAbs ≤ N by omega)
    have hlow : -(det d z) ≤ ((det d z).natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -(det d z)))
    omega
  have hsupport : lowerSupport B (v i0) = 0 :=
    oneSidedBox_support_zero v hpair i0 N
  have hFenv : (F : Set Lattice) ⊆ envelope D (lowerSupport B) := by
    intro z hz d hd
    by_cases hd0 : d = v i0
    · subst d
      rw [hsupport]
      exact hF z hz
    · obtain ⟨w,hw,hdeep⟩ :=
        oneSidedBox_deep_except_tangent hn v hpair i0 N hN d hd hd0
      exact (lowerSupport_le hw d).trans (hdeep.trans (hbound d hd z hz))
  obtain ⟨j,hji⟩ := other_index hn i0
  have hi0j : i0 ≠ j := Ne.symm hji
  have hv0 : v i0 ∈ D := (mem_signedDirections v _).2 ⟨i0,Or.inl rfl⟩
  have hnv0 : -v i0 ∈ D := (mem_signedDirections v _).2 ⟨i0,Or.inr rfl⟩
  have hvj : v j ∈ D := (mem_signedDirections v _).2 ⟨j,Or.inl rfl⟩
  have hnvj : -v j ∈ D := (mem_signedDirections v _).2 ⟨j,Or.inr rfl⟩
  obtain ⟨T,hBT,hconv,hTeq,hsupportT⟩ := exists_finite_envelope D B hB
    (v i0) (v j) (hpair i0 j hi0j) hv0 hnv0 hvj hnvj
  refine ⟨T,?_,hconv,?_,?_,?_⟩
  · intro z hz
    have hz' := hFenv hz
    rwa [← hTeq] at hz'
  · rw [hTeq]
    exact envelope_isEnvelope D (lowerSupport B)
  · rw [hTeq]
    exact (oneSidedBox_longFaces v i0 N hN).finite_envelope hB
  · rw [hsupportT (v i0) hv0,hsupport]

end
end NivatTrial.ColleZonotopeEnvelope
