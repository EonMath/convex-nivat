import ConvexNivat.Colle.Shared.BoundaryCycle

namespace ConvexNivat.Colle
noncomputable section

/-- The finite source cycle turns the cardinality clause of enveloping into equality. -/
private theorem enveloped_edgeDirections_eq {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : EnvelopedWindow S B) :
    edgeDirections B = edgeDirections S := by
  have hfinite : (edgeDirections S).Finite := by
    have he : edgeDirections S = Set.range (fun i : Fin (2 * m) => C.direction (i.val : ℤ)) := by
      ext v
      exact C.covers v
    rw [he]
    exact Set.finite_range _
  exact Set.eq_of_subset_of_ncard_le (fun v hv => (hB.2.2.2.1 v hv).1)
    (le_of_eq hB.2.2.2.2.symm) hfinite

private theorem row_mem (S : Finset Lattice) (u a : Lattice) :
    a ∈ supportRow S u ↔ a ∈ S ∧ ∀ z ∈ S, det u a ≤ det u z := by
  simp only [supportRow,supportFace,Finset.mem_filter,normal_height]
  constructor
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz
  · rintro ⟨ha,hh⟩
    refine ⟨ha,?_⟩
    intro z hz
    exact_mod_cast hh z hz

private theorem support_det_nonneg {S : Finset Lattice} {u a z : Lattice}
    (ha : a ∈ supportRow S u) (hz : z ∈ S) : 0 ≤ det u (z-a) := by
  have hh := ((row_mem S u a).mp ha).2 z hz
  have he : det u (z-a)=det u z-det u a := by simp [det]; ring
  rw [he]
  omega

private theorem support_pair_forbids_middle {S : Finset Lattice} {u v w a : Lattice}
    (hu : a ∈ supportRow S u) (hv : a ∈ supportRow S v)
    (huv : 0 < det u v) (huw : 0 < det u w) (hwv : 0 < det w v) :
    w ∉ edgeDirections S := by
  intro hw
  have hz_eq : ∀ z ∈ supportRow S w, z=a := by
    intro z hz
    have hzS := ((row_mem S w z).mp hz).1
    have hu0 := support_det_nonneg hu hzS
    have hv0 := support_det_nonneg hv hzS
    have hw0 : det w (z-a) ≤ 0 := by
      have hh := ((row_mem S w z).mp hz).2 a ((row_mem S u a).mp hu).1
      have he : det w (z-a)=det w z-det w a := by simp [det]; ring
      rw [he]
      omega
    have hid : det u v * det w (z-a) =
        det w v * det u (z-a)+det u w * det v (z-a) := by simp [det]; ring
    have huz : det u (z-a)=0 := by nlinarith [mul_nonneg huw.le hv0]
    have hvz : det v (z-a)=0 := by nlinarith [mul_nonneg hwv.le hu0]
    have hcoord1 : det u v * (z-a).1 =
        v.1 * det u (z-a)-u.1 * det v (z-a) := by simp [det]; ring
    have hcoord2 : det u v * (z-a).2 =
        v.2 * det u (z-a)-u.2 * det v (z-a) := by simp [det]; ring
    rw [huz,hvz,mul_zero,mul_zero,sub_self] at hcoord1 hcoord2
    have h1 := (mul_eq_zero.mp hcoord1).resolve_left huv.ne'
    have h2 := (mul_eq_zero.mp hcoord2).resolve_left huv.ne'
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  have hcard : (supportRow S w).card ≤ 1 := Finset.card_le_one.mpr
    (fun z hz q hq => (hz_eq z hz).trans (hz_eq q hq).symm)
  have hh := hw.2.2
  omega

private theorem periodic_mod {α : Type*} (f : ℤ → α) (n : ℕ)
    (hn : 0 < n) (hf : ∀ j, f (j+(n : ℤ))=f j) (j : ℤ) : f (j % n)=f j := by
  have hp : Function.Periodic f (n : ℤ) := hf
  have h := hp.int_mul (j/(n : ℤ)) (j % (n : ℤ))
  simpa only [Int.cast_id,Int.emod_add_ediv_mul] using h.symm


private theorem cycle_direction_mem {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (j : ℤ) : C.direction j ∈ edgeDirections S := by
  have hm := C.at_least_two
  have hj0 : 0 ≤ j % (2*m : ℕ) := Int.emod_nonneg _ (by omega)
  have hjlt : j % (2*m : ℕ) < (2*m : ℕ) := Int.emod_lt_of_pos _ (by omega)
  let k : Fin (2*m) := ⟨(j % (2*m : ℕ)).toNat,(Int.toNat_lt hj0).mpr hjlt⟩
  apply (C.covers _).mpr
  refine ⟨k,?_⟩
  change C.direction ((j % (2*m : ℕ)).toNat : ℤ)=C.direction j
  rw [Int.toNat_of_nonneg hj0]
  exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) j

private theorem cycle_direction_inj_between {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+2*m) :
    C.direction i ≠ C.direction j := by
  have hm := C.at_least_two
  have hmod : ∀ k : ℤ, 0 ≤ k % (2*m : ℕ) ∧ k % (2*m : ℕ) < (2*m : ℕ) := by
    intro k
    exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
  let index (k : ℤ) : Fin (2*m) := ⟨(k % (2*m : ℕ)).toNat,(Int.toNat_lt (hmod k).1).mpr (hmod k).2⟩
  have he (k : ℤ) : C.direction ((index k).val : ℤ)=C.direction k := by
    change C.direction ((k % (2*m : ℕ)).toNat : ℤ)=C.direction k
    rw [Int.toNat_of_nonneg (hmod k).1]
    exact periodic_mod C.direction (2*m) (by omega) (by simpa using C.direction_periodic) k
  intro h
  have hi : index i=index j := C.distinct ((he i).trans (h.trans (he j).symm))
  have hrem : i % (2*m : ℕ)=j % (2*m : ℕ) := by
    have hv := congrArg (fun k : Fin (2*m) => (k.val : ℤ)) hi
    simpa only [index,Int.toNat_of_nonneg (hmod i).1,Int.toNat_of_nonneg (hmod j).1] using hv
  have hdvd : (2*m : ℤ) ∣ j-i := by
    apply Int.dvd_of_emod_eq_zero
    have h' := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hrem.symm
    simpa using h'
  have hpos : 0 < j-i := by omega
  have hlt : j-i < 2*m := by omega
  have hle := Int.le_of_dvd hpos hdvd
  omega


private theorem primitive_parallel_eq_or_neg (u v : Lattice)
    (hu : Primitive u) (hv : Primitive v) (hdet : det u v=0) : v=u ∨ v= -u := by
  have hz : det u 0=det u v := by simp [det] at hdet ⊢; exact hdet.symm
  obtain ⟨k,hk⟩ := (primitive_row_coordinates u hu).2.1 0 v |>.mp hz
  simp only [zero_add] at hk
  have hg : k.natAbs=1 := by
    have h := hv
    rw [hk] at h
    change Int.gcd (k*u.1) (k*u.2)=1 at h
    rw [Int.gcd_mul_left,show Int.gcd u.1 u.2=1 from hu,mul_one] at h
    exact h
  have hkpm : k=1 ∨ k= -1 := by omega
  rcases hkpm with h | h
  · left; simpa [h] using hk
  · right; simpa [h] using hk

private theorem cycle_half_det_ne_zero {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) {i j : ℤ} (hij : i < j) (hji : j < i+m) :
    det (C.direction i) (C.direction j) ≠ 0 := by
  have hm := C.at_least_two
  intro hzero
  rcases primitive_parallel_eq_or_neg _ _ (C.primitive i) (C.primitive j) hzero with he | he
  · exact cycle_direction_inj_between C hij (by omega) he.symm
  · have hianti : C.direction j=C.direction (i+m) := by rw [C.antipodal]; exact he
    exact cycle_direction_inj_between C hji (by omega) hianti

private theorem cycle_turn_positive {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) :
    0 < det (C.direction i) (C.direction (i+1)) := by
  have hm := C.at_least_two
  have hn := support_det_nonneg (C.terminal_mem i)
    (((row_mem S _ _).mp (C.terminal_mem (i+1))).1)
  obtain ⟨k,hk,hedge⟩ := C.edge_length (i+1)
  rw [hedge] at hn
  have he : det (C.direction i) (k • C.direction (i+1)) =
      k * det (C.direction i) (C.direction (i+1)) := by simp [det]; ring
  rw [he] at hn
  have hnon : 0 ≤ det (C.direction i) (C.direction (i+1)) := by nlinarith
  exact lt_of_le_of_ne hnon (Ne.symm (cycle_half_det_ne_zero C (by omega) (by omega)))

private theorem cycle_nat_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i : ℤ) (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    0 < det (C.direction i) (C.direction (i+n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      simpa using cycle_turn_positive C i
    have hprev := ih (by omega) (by omega)
    have hnext := cycle_turn_positive C (i+n)
    have hne : det (C.direction i) (C.direction (i+(n+1 : ℕ))) ≠ 0 :=
      cycle_half_det_ne_zero C (by omega) (by exact_mod_cast (show (i : ℤ)+(n+1 : ℕ) < i+m by omega))
    by_contra! hnon
    have hneg : det (C.direction i) (C.direction (i+(n+1 : ℕ))) < 0 :=
      lt_of_le_of_ne hnon hne
    have h1 : 0 < det (C.direction (i+n)) (C.direction (i+m)) := by
      rw [C.antipodal]
      have he : det (C.direction (i+n)) (-C.direction i)=
          det (C.direction i) (C.direction (i+n)) := by simp [det]; ring
      rw [he]
      exact hprev
    have h2 : 0 < det (C.direction (i+m)) (C.direction (i+(n+1 : ℕ))) := by
      rw [C.antipodal]
      have he : det (-C.direction i) (C.direction (i+(n+1 : ℕ))) =
          -det (C.direction i) (C.direction (i+(n+1 : ℕ))) := by simp [det]; ring
      rw [he]
      omega
    have hforbid := support_pair_forbids_middle (C.terminal_mem (i+n))
      (C.initial_mem (i+n+1)) hnext h1
      (by simpa [Nat.cast_add,Nat.cast_one,add_assoc] using h2)
    exact hforbid (cycle_direction_mem C (i+m))

private theorem cycle_half_order {S : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (i j : ℤ) (hij : i < j) (hji : j < i+m) :
    0 < det (C.direction i) (C.direction j) := by
  have h := cycle_nat_half_order C i (j-i).toNat (by omega) (by omega)
  have hj : i+((j-i).toNat : ℤ)=j := by omega
  rwa [hj] at h


private theorem boundary_direction_mem {B : Finset Lattice}
    (W : WindowBoundary B) (j : ℤ) : W.direction j ∈ edgeDirections B := by
  have hn := W.at_least_three
  have hj0 : 0 ≤ j % W.count := Int.emod_nonneg _ (by omega)
  have hjlt : j % W.count < W.count := Int.emod_lt_of_pos _ (by omega)
  let k : Fin W.count := ⟨(j % W.count).toNat,(Int.toNat_lt hj0).mpr hjlt⟩
  rw [W.covers]
  refine ⟨k,?_⟩
  change W.direction ((j % W.count).toNat : ℤ)=W.direction j
  rw [Int.toNat_of_nonneg hj0]
  exact periodic_mod W.direction W.count (by omega) W.direction_periodic j

private theorem boundary_initial {B : Finset Lattice}
    (W : WindowBoundary B) (j : ℤ) : W.vertex j ∈ supportRow B (W.direction j) := by
  apply (W.support_segment j _).mpr
  exact left_mem_segment _ _ _

private theorem boundary_terminal {B : Finset Lattice}
    (W : WindowBoundary B) (j : ℤ) : W.vertex (j+1) ∈ supportRow B (W.direction j) := by
  apply (W.support_segment j _).mpr
  exact right_mem_segment _ _ _

private theorem aligned_successor_direction {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (W : WindowBoundary B)
    (hE : edgeDirections B=edgeDirections S) (i j : ℤ)
    (hij : W.direction j=C.direction i) :
    W.direction (j+1)=C.direction (i+1) := by
  have hturnC := cycle_turn_positive C i
  have hturnW := W.turns j
  rw [hij] at hturnW
  rcases lt_trichotomy (det (C.direction (i+1)) (W.direction (j+1))) 0 with hneg | hzero | hpos
  · have hcross : 0 < det (W.direction (j+1)) (C.direction (i+1)) := by
      have he : det (W.direction (j+1)) (C.direction (i+1)) =
          -det (C.direction (i+1)) (W.direction (j+1)) := by simp [det]; ring
      rw [he]
      omega
    have hforbid := support_pair_forbids_middle (C.terminal_mem i)
      (C.initial_mem (i+1)) hturnC hturnW hcross
    exact False.elim (hforbid (hE ▸ boundary_direction_mem W (j+1)))
  · rcases primitive_parallel_eq_or_neg _ _ (C.primitive (i+1)) (W.primitive (j+1)) hzero with he | he
    · exact he
    · rw [he] at hturnW
      have hid : det (C.direction i) (-C.direction (i+1)) =
          -det (C.direction i) (C.direction (i+1)) := by simp [det]; ring
      rw [hid] at hturnW
      omega
  · have hfirst : W.vertex (j+1) ∈ supportRow B (C.direction i) := by
      rw [← hij]
      exact boundary_terminal W j
    have hforbid := support_pair_forbids_middle hfirst (boundary_initial W (j+1))
      hturnW hturnC hpos
    exact False.elim (hforbid (hE.symm ▸ cycle_direction_mem C (i+1)))

private theorem periodic_injective_transfer {α : Type*} {n : ℕ}
    (hn : 0 < n) (d : ℤ → Lattice) (f : ℤ → α)
    (hd : ∀ j, d (j+(n : ℤ))=d j) (hf : ∀ j, f (j+(n : ℤ))=f j)
    (hinj : Function.Injective (fun i : Fin n => d (i.val : ℤ)))
    {i j : ℤ} (hij : d i=d j) : f i=f j := by
  have hmod : ∀ k : ℤ, 0 ≤ k % n ∧ k % n < n := by
    intro k
    exact ⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩
  let index (k : ℤ) : Fin n := ⟨(k % n).toNat,(Int.toNat_lt (hmod k).1).mpr (hmod k).2⟩
  have he (k : ℤ) : d ((index k).val : ℤ)=d k := by
    change d ((k % n).toNat : ℤ)=d k
    rw [Int.toNat_of_nonneg (hmod k).1]
    exact periodic_mod d n hn hd k
  have hi : index i=index j := hinj ((he i).trans (hij.trans (he j).symm))
  have hrem : i % n=j % n := by
    have hv := congrArg (fun k : Fin n => (k.val : ℤ)) hi
    simpa only [index,Int.toNat_of_nonneg (hmod i).1,Int.toNat_of_nonneg (hmod j).1] using hv
  calc
    f i = f (i%n) := (periodic_mod f n hn hf i).symm
    _ = f (j%n) := congrArg f hrem
    _ = f j := periodic_mod f n hn hf j

private theorem boundary_same_direction_vertex {B : Finset Lattice} (W : WindowBoundary B)
    {i j : ℤ} (hij : W.direction i=W.direction j) : W.vertex i=W.vertex j := by
  exact periodic_injective_transfer (by have h := W.at_least_three; omega)
    W.direction W.vertex W.direction_periodic W.vertex_periodic W.distinct_directions hij

private theorem boundary_same_direction_length {B : Finset Lattice} (W : WindowBoundary B)
    {i j : ℤ} (hij : W.direction i=W.direction j) : W.length i=W.length j := by
  exact periodic_injective_transfer (by have h := W.at_least_three; omega)
    W.direction W.length W.direction_periodic W.length_periodic W.distinct_directions hij


private theorem boundary_support_card_le {B : Finset Lattice}
    (W : WindowBoundary B) (j : ℤ) :
    (supportRow B (W.direction j)).card ≤ W.length j+1 := by
  classical
  let f : ℤ → Lattice := fun k => W.vertex j+k • W.direction j
  have hedge : W.vertex (j+1)=W.vertex j+(W.length j : ℤ) • W.direction j := by
    have h := W.edge_eq j
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hsub : supportRow B (W.direction j) ⊆
      (Finset.Icc (0 : ℤ) (W.length j : ℤ)).image f := by
    intro z hz
    have hseg := (W.support_segment j z).mp hz
    rw [hedge] at hseg
    have hparam := (primitive_row_coordinates (W.direction j) (W.primitive j)).2.2
      (W.vertex j) 0 (W.length j : ℤ) (by omega) z
    simp only [zero_smul,add_zero] at hparam
    obtain ⟨k,hk0,hkn,hz⟩ := hparam.mp hseg
    exact Finset.mem_image.mpr ⟨k,Finset.mem_Icc.mpr ⟨hk0,hkn⟩,hz.symm⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa using hc

/-- RC02: align an actual enveloped polygon with the source cycle. -/
theorem enveloped_boundary_aligned_cycle {S B : Finset Lattice} {m : ℕ}
    (C : AntipodalEdgeCycle S m) (hB : EnvelopedWindow S B) :
    Nonempty (AlignedBoundary C B) ∧ edgeDirections B = edgeDirections S := by
  classical
  have hE := enveloped_edgeDirections_eq C hB
  obtain ⟨W⟩ := finite_window_support_polygon B hB.2.1 hB.2.2.1
  have hidx : ∀ i : ℤ, ∃ j : Fin W.count, W.direction (j.val : ℤ)=C.direction i := by
    intro i
    have hmem := hE.symm ▸ cycle_direction_mem C i
    rw [W.covers] at hmem
    exact hmem
  choose index hindex using hidx
  let V : ℤ → Lattice := fun i => W.vertex ((index i).val : ℤ)
  let L : ℤ → ℕ := fun i => W.length ((index i).val : ℤ)
  have hvertex {i j : ℤ} (hij : C.direction i=W.direction j) : V i=W.vertex j := by
    exact boundary_same_direction_vertex W ((hindex i).trans hij)
  have hnext (i : ℤ) : V (i+1)=W.vertex ((index i).val+1 : ℤ) := by
    apply hvertex
    exact (aligned_successor_direction C W hE i ((index i).val : ℤ) (hindex i)).symm
  have hpV : ∀ i, V (i+2*(m : ℤ))=V i := by
    intro i
    apply boundary_same_direction_vertex W
    rw [hindex,hindex,C.direction_periodic]
  have hpL : ∀ i, L (i+2*(m : ℤ))=L i := by
    intro i
    apply boundary_same_direction_length W
    rw [hindex,hindex,C.direction_periodic]
  have hseg : ∀ i z, z ∈ supportRow B (C.direction i) ↔
      embed z ∈ segment ℝ (embed (V i)) (embed (V (i+1))) := by
    intro i z
    rw [hnext]
    exact (hindex i) ▸ W.support_segment ((index i).val : ℤ) z
  refine ⟨⟨{
    vertex := V
    length := L
    vertex_periodic := hpV
    length_periodic := hpL
    initial := ?_
    terminal := ?_
    length_positive := fun i => W.length_positive ((index i).val : ℤ)
    edge_eq := ?_
    segment_eq := hseg
    hull_eq := ?_
    frontier_eq := ?_
    edge_eq_source := hE
    source_length_le := ?_
  }⟩,hE⟩
  · intro i
    exact (hseg i (V i)).mpr (left_mem_segment _ _ _)
  · intro i
    exact (hseg i (V (i+1))).mpr (right_mem_segment _ _ _)
  · intro i
    rw [hnext]
    exact (hindex i) ▸ W.edge_eq ((index i).val : ℤ)
  · ext x
    constructor
    · intro hx i
      exact (hindex i) ▸ W.supports ((index i).val : ℤ) x hx
    · intro hx
      rw [W.hull_eq]
      intro j
      have hdmem := hE ▸ boundary_direction_mem W j
      obtain ⟨i,hi⟩ := (C.covers (W.direction j)).mp hdmem
      have h := hx (i.val : ℤ)
      rw [hi,hvertex hi] at h
      exact h
  · ext x
    constructor
    · intro hx
      rw [W.frontier_eq] at hx
      obtain ⟨j,hj⟩ := hx
      have hdmem := hE ▸ boundary_direction_mem W (j.val : ℤ)
      obtain ⟨i,hi⟩ := (C.covers (W.direction (j.val : ℤ))).mp hdmem
      refine ⟨i,?_⟩
      have hsucc : C.direction (i.val+1 : ℤ)=W.direction (j.val+1 : ℤ) :=
        (aligned_successor_direction C W hE (i.val : ℤ) (j.val : ℤ) hi.symm).symm
      rw [hvertex hi,hvertex hsucc]
      exact hj
    · rintro ⟨i,hi⟩
      rw [W.frontier_eq]
      refine ⟨index (i.val : ℤ),?_⟩
      rw [hnext] at hi
      exact hi
  · intro i
    have hbound := (hB.2.2.2.1 (C.direction i) (hE.symm ▸ cycle_direction_mem C i)).2
    have hcard := boundary_support_card_le W ((index i).val : ℤ)
    rw [hindex] at hcard
    exact hbound.trans hcard

end
end ConvexNivat.Colle
