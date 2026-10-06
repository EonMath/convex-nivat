import ConvexNivat.Colle.Orbit

namespace ConvexNivat.ExternalDynamicsHelpers
open ConvexNivat.Colle
noncomputable section

def latticeDot (z u : Lattice) : ℤ := z.1 * u.1 + z.2 * u.2

def quarterTurn (u : Lattice) : Lattice := (u.2, -u.1)

/-- Kari--Moutot §2.2: open half-plane, with no boundary row. -/
def strictHalf (u : Lattice) : Set Lattice := {z | latticeDot z u < 0}

/-- Kari--Moutot's literal discrete box B_u^k. -/
def discreteBox (u : Lattice) (k : ℕ) : Set Lattice :=
  {z | -(k : ℤ) < latticeDot z u ∧ latticeDot z u < 0 ∧
    -(k : ℤ) < latticeDot z (quarterTurn u) ∧ latticeDot z (quarterTurn u) < k}

def translatedWindow (B : Finset Lattice) (t : Lattice) : Set Lattice :=
  {z | z + t ∈ B}

/-- Actual fibre of the factor map, inside the actual orbit subshift. -/
def factorFibre (ξ : Configuration ℤ) (v : Lattice) (b : Configuration ℤ) :
    Set (Configuration ℤ) := {x | x ∈ OrbitClosure ξ ∧ periodDifference x v = b}


private theorem dot_add (a b u : Lattice) : latticeDot (a + b) u = latticeDot a u + latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_sub (a b u : Lattice) : latticeDot (a - b) u = latticeDot a u - latticeDot b u := by
  simp [latticeDot]; ring
private theorem dot_smul (k : ℤ) (a u : Lattice) : latticeDot (k • a) u = k * latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_neg_right (a u : Lattice) : latticeDot a (-u) = -latticeDot a u := by
  simp [latticeDot]; ring
private theorem dot_self_pos (u : Lattice) (hu : u ≠ 0) : 0 < latticeDot u u := by
  have hn : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    by_contra h; push_neg at h; exact hu (Prod.ext h.1 h.2)
  unfold latticeDot
  rcases hn with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.2]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg u.1]

private theorem limit_on_finset (xs : ℕ → Configuration ℤ) (x : Configuration ℤ)
    (h : PointwiseLimit xs x) (B : Finset Lattice) :
    ∃ N, ∀ j ≥ N, ∀ z ∈ B, xs j z = x z := by
  classical
  induction B using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a B ha ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := h a
    refine ⟨max N M, fun j hj z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hM j (le_trans (le_max_right _ _) hj)
    · exact hN j (le_trans (le_max_left _ _) hj) z hz

private theorem limit_subseq (xs : ℕ → Configuration ℤ) (x : Configuration ℤ)
    (h : PointwiseLimit xs x) (s : ℕ → ℕ) (hs : StrictMono s) :
    PointwiseLimit (fun j => xs (s j)) x := by
  intro z
  obtain ⟨N, hN⟩ := h z
  exact ⟨N, fun j hj => hN (s j) (hj.trans (hs.id_le j))⟩

private theorem limit_unique (xs : ℕ → Configuration ℤ) (x y : Configuration ℤ)
    (hx : PointwiseLimit xs x) (hy : PointwiseLimit xs y) : x = y := by
  funext z
  obtain ⟨N, hN⟩ := hx z
  obtain ⟨M, hM⟩ := hy z
  exact (hN (max N M) (le_max_left _ _)).symm.trans (hM _ (le_max_right _ _))

theorem latticeDot_cast (z u : Lattice) :
    (latticeDot z u : ℝ) = realDot (embed z) (embed u) := by
  simp [latticeDot, realDot, embed]

theorem discreteBox_finite (u : Lattice) (hu : u ≠ 0) (k : ℕ) :
    (discreteBox u k).Finite := by
  let f : Lattice → Lattice := fun z => (latticeDot z u, latticeDot z (quarterTurn u))
  have hi : Function.Injective f := by
    intro x y he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change x.1 * u.1 + x.2 * u.2 = y.1 * u.1 + y.2 * u.2 at h1
    change x.1 * u.2 + x.2 * (-u.1) = y.1 * u.2 + y.2 * (-u.1) at h2
    have hp := dot_self_pos u hu
    unfold latticeDot at hp
    have hx : (x.1 - y.1) * (u.1 * u.1 + u.2 * u.2) = 0 := by
      linear_combination u.1 * h1 + u.2 * h2
    have hy : (x.2 - y.2) * (u.1 * u.1 + u.2 * u.2) = 0 := by
      linear_combination u.2 * h1 - u.1 * h2
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (ne_of_gt hp)))
      (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right (ne_of_gt hp)))
  apply Set.Finite.of_finite_image (f := f) _ hi.injOn
  apply ((Set.finite_Ioo (-(k : ℤ)) 0).prod (Set.finite_Ioo (-(k : ℤ)) k)).subset
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

theorem equal_factor_images_iff_periodic_difference (x y : Configuration ℤ)
    (v : Lattice) :
    periodDifference x v = periodDifference y v ↔
      HasPeriod (fun z => x z - y z) v := by
  constructor
  · intro h z
    have he := congrFun h (z + v)
    simp only [periodDifference, add_sub_cancel_right] at he
    dsimp
    omega
  · intro h
    funext z
    have he := h (z - v)
    simp only [sub_add_cancel] at he
    dsimp [periodDifference]
    omega

theorem finite_tuple_joint_subsequence (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (n : ℕ)
    (xs : ℕ → Fin n → Configuration ℤ) (hxs : ∀ j i, xs j i ∈ OrbitClosure ξ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ d : Fin n → Configuration ℤ,
      (∀ i, d i ∈ OrbitClosure ξ) ∧
      ∀ i, PointwiseLimit (fun j => xs (s j) i) (d i) := by
  open Filter Topology in
  have hcompact : IsCompact {c : Fin n → Configuration ℤ | ∀ i, c i ∈ OrbitClosure ξ} :=
    isCompact_pi_infinite (fun _ => orbitClosure_isCompact ξ A hA)
  obtain ⟨d, hd, s, hs, hlim⟩ := hcompact.tendsto_subseq hxs
  refine ⟨s, hs, d, hd, ?_⟩
  simpa only [PointwiseLimit, tendsto_pi_nhds, nhds_discrete, Filter.tendsto_pure,
    Filter.eventually_atTop, Function.comp_apply] using hlim

theorem periodDifference_pointwise_limit (xs : ℕ → Configuration ℤ)
    (x : Configuration ℤ) (v : Lattice) (hlim : PointwiseLimit xs x) :
    PointwiseLimit (fun j => periodDifference (xs j) v) (periodDifference x v) := by
  intro z
  obtain ⟨N, hN⟩ := hlim (z - v)
  obtain ⟨M, hM⟩ := hlim z
  exact ⟨max N M, fun j hj => by
    dsimp [periodDifference]
    rw [hN j ((le_max_left _ _).trans hj), hM j ((le_max_right _ _).trans hj)]⟩

theorem equal_factor_images_joint_limit (n : ℕ) (xs : ℕ → Fin n → Configuration ℤ)
    (d : Fin n → Configuration ℤ) (v : Lattice)
    (hlim : ∀ i, PointwiseLimit (fun j => xs j i) (d i))
    (himage : ∀ j i i', periodDifference (xs j i) v = periodDifference (xs j i') v) :
    ∀ i i', periodDifference (d i) v = periodDifference (d i') v := by
  intro i i'
  apply limit_unique (fun j => periodDifference (xs j i) v)
  · exact periodDifference_pointwise_limit _ _ _ (hlim i)
  · have h := periodDifference_pointwise_limit _ _ v (hlim i')
    simpa only [himage _ i i'] using h

theorem orbit_member_translate_sequence (ξ x : Configuration ℤ)
    (hx : x ∈ OrbitClosure ξ) :
    ∃ t : ℕ → Lattice, PointwiseLimit (fun j => translate (t j) ξ) x := by
  classical
  let B : ℕ → Finset Lattice := fun n =>
    (Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n)
  choose t ht using fun n => hx (B n)
  refine ⟨t, fun z => ⟨z.1.natAbs + z.2.natAbs, fun j hj => ?_⟩⟩
  have hz1 := Int.natCast_natAbs z.1
  have hz2 := Int.natCast_natAbs z.2
  have hz : z ∈ B j := by
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    all_goals
      have h1 := le_abs_self z.1
      have h2 := neg_le_abs z.1
      have h3 := le_abs_self z.2
      have h4 := neg_le_abs z.2
      constructor <;> omega
  simpa [translate, add_comm] using (ht j z hz).symm

theorem finite_tuple_orbit_member_joint_limit (ξ : Configuration ℤ)
    (A : Finset ℤ) (hA : ∀ z, ξ z ∈ A) (n : ℕ)
    (d : Fin n → Configuration ℤ) (hd : ∀ i, d i ∈ OrbitClosure ξ)
    (i₀ : Fin n) (x : Configuration ℤ) (hx : x ∈ OrbitClosure (d i₀)) :
    ∃ t : ℕ → Lattice, ∃ e : Fin n → Configuration ℤ,
      (∀ i, e i ∈ OrbitClosure ξ) ∧ e i₀ = x ∧
      ∀ i, PointwiseLimit (fun j => translate (t j) (d i)) (e i) := by
  obtain ⟨t, ht⟩ := orbit_member_translate_sequence (d i₀) x hx
  obtain ⟨s, hs, e, he, hlim⟩ := finite_tuple_joint_subsequence ξ A hA n
    (fun j i => translate (t j) (d i))
    (fun j i => orbitClosure_translate_member ξ (d i) (hd i) (t j))
  refine ⟨fun j => t (s j), e, he, ?_, hlim⟩
  exact limit_unique _ _ _ (hlim i₀) (limit_subseq _ _ ht s hs)

theorem finite_window_translate_into_half (B : Finset Lattice)
    (u : Lattice) (hu : u ≠ 0) :
    ∃ t : Lattice, translatedWindow B t ⊆ strictHalf u := by
  classical
  let M := B.sup (fun z => (latticeDot z u).toNat)
  let t : Lattice := ((M + 1 : ℕ) : ℤ) • u
  refine ⟨t, fun z hz => ?_⟩
  have hb : latticeDot (z + t) u ≤ M :=
    (Int.self_le_toNat _).trans (by exact_mod_cast
      (Finset.le_sup (f := fun z => (latticeDot z u).toNat) hz))
  have hp := dot_self_pos u hu
  have hm : 0 ≤ (M : ℤ) := Int.natCast_nonneg _
  change latticeDot z u < 0
  rw [dot_add, dot_smul] at hb
  push_cast at hb
  nlinarith

theorem finite_tuple_distinguished_on_half (n : ℕ) (c : Fin n → Configuration ℤ)
    (hc : Function.Injective c) (u : Lattice) (hu : u ≠ 0) :
    ∃ t : Lattice, ∀ i j, i ≠ j →
      ∃ z, z + t ∈ strictHalf (-u) ∧ c i z ≠ c j z := by
  classical
  have hw : ∀ i j : Fin n, ∃ z, i ≠ j → c i z ≠ c j z := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun hij => (hij h).elim⟩
    · obtain ⟨z, hz⟩ := Function.ne_iff.mp (fun he => h (hc he))
      exact ⟨z, fun _ => hz⟩
  choose z hz using hw
  let B : Finset Lattice := Finset.univ.image (fun ij : Fin n × Fin n => z ij.1 ij.2)
  obtain ⟨t, ht⟩ := finite_window_translate_into_half B (-u) (neg_ne_zero.mpr hu)
  refine ⟨-t, fun i j hij => ⟨z i j, ?_, hz i j hij⟩⟩
  apply ht
  change z i j + -t + t ∈ B
  simp only [neg_add_cancel_right]
  exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩

theorem window_separation_joint_limit (n : ℕ) (d e : Fin n → Configuration ℤ)
    (B : Finset Lattice)
    (hsep : ∀ i j, i ≠ j → ∀ t, ∃ z ∈ translatedWindow B t, d i z ≠ d j z)
    (t : ℕ → Lattice)
    (hlim : ∀ i, PointwiseLimit (fun j => translate (t j) (d i)) (e i)) :
    ∀ i j, i ≠ j → ∀ a, ∃ z ∈ translatedWindow B a, e i z ≠ e j z := by
  classical
  intro i j hij a
  by_contra hn
  push_neg at hn
  let W := B.image (fun z => z - a)
  obtain ⟨N, hN⟩ := limit_on_finset _ _ (hlim i) W
  obtain ⟨M, hM⟩ := limit_on_finset _ _ (hlim j) W
  let q := max N M
  obtain ⟨z, hz, hne⟩ := hsep i j hij (a - t q)
  have hw : z - t q ∈ translatedWindow B a := by
    change z - t q + a ∈ B
    change z + (a - t q) ∈ B at hz
    rwa [show z - t q + a = z + (a - t q) by abel]
  have hw' : z - t q ∈ W := by
    exact Finset.mem_image.mpr ⟨z - t q + a, hw, by abel⟩
  have h1 := hN q (le_max_left _ _) _ hw'
  have h2 := hM q (le_max_right _ _) _ hw'
  simp only [translate, sub_add_cancel] at h1 h2
  exact hne (h1.trans ((hn _ hw).trans h2.symm))

end
end ConvexNivat.ExternalDynamicsHelpers
