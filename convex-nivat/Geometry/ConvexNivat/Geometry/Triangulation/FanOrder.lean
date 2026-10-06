import ConvexNivat.Geometry.Triangulation.Definitions
import ConvexNivat.Geometry.Basic
import Mathlib.Data.Finset.Sort

namespace ConvexNivat.PolygonTriangulation

private theorem same_slope_segment (N : ℕ) (p q r : RealPlane)
    (hq : 0 < ell N (q - p)) (hr : 0 < ell N (r - p))
    (hs : slope N (q - p) = slope N (r - p))
    (hle : ell N (q - p) ≤ ell N (r - p)) :
    q ∈ segment ℝ p r := by
  let t := ell N (q - p) / ell N (r - p)
  have ht0 : 0 ≤ t := le_of_lt (div_pos hq hr)
  have ht1 : t ≤ 1 := (div_le_one hr).2 hle
  have hs' : kappa (q - p) * ell N (r - p) =
      kappa (r - p) * ell N (q - p) :=
    (div_eq_div_iff (ne_of_gt hq) (ne_of_gt hr)).1 hs
  have ht : t * ell N (r - p) = ell N (q - p) := div_mul_cancel₀ _ (ne_of_gt hr)
  have hfirst : q.1 = (1-t)*p.1 + t*r.1 := by
    simp only [kappa, Prod.fst_sub] at hs'
    have hmul : (q.1-p.1-t*(r.1-p.1)) * ell N (r-p) = 0 := by
      nlinarith [congrArg (fun z : ℝ => (r.1-p.1)*z) ht]
    have hz := (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hr)
    linarith
  have he : q = (1 - t) • p + t • r := by
    apply Prod.ext
    · exact hfirst
    · change q.2 = (1-t)*p.2 + t*r.2
      simp only [ell, Prod.fst_sub, Prod.snd_sub] at ht
      nlinarith [congrArg (fun z : ℝ => (N:ℝ)*z) hfirst]
  exact ⟨1-t, t, sub_nonneg.mpr ht1, ht0, by ring, he.symm⟩

/-- PT20: irredundancy excludes two generators on the same positive ray. -/
theorem irredundant_anchor_slopes_injective (Q : Finset Lattice)
    (hirr : Irredundant Q) (p : Lattice) (N : ℕ) (ha : Anchor Q p N) :
    Function.Injective
      (fun q : {q : Lattice // q ∈ Q.erase p} => slope N (embed (q.val - p))) := by
  classical
  intro q r hs
  apply Subtype.ext
  by_contra hne
  have hq := Finset.mem_erase.mp q.property
  have hr := Finset.mem_erase.mp r.property
  have forbid : ∀ a b : {q : Lattice // q ∈ Q.erase p}, a.val ≠ b.val →
      slope N (embed (a.val-p)) = slope N (embed (b.val-p)) →
      ell N (embed (a.val-p)) ≤ ell N (embed (b.val-p)) → False := by
    intro a b hab habs hle
    apply hirr a.val (Finset.mem_of_mem_erase a.property)
    have hseg := same_slope_segment N (embed p) (embed a.val) (embed b.val)
      (by simpa only [← embed_sub] using ha.2 a.val a.property)
      (by simpa only [← embed_sub] using ha.2 b.val b.property)
      (by simpa only [← embed_sub] using habs)
      (by simpa only [← embed_sub] using hle)
    exact (windowHull_convex (Q.erase a.val)).segment_subset
      (window_mem_hull _ (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp a.property).1.symm, ha.1⟩))
      (window_mem_hull _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_of_mem_erase b.property⟩)) hseg
  rcases le_total (ell N (embed (q.val-p))) (ell N (embed (r.val-p))) with hle | hle
  · exact forbid q r hne hs hle
  · exact forbid r q (Ne.symm hne) hs.symm hle

/-- PT21: the same anchor admits a complete strictly ordered radial chain. -/
theorem sorted_irredundant_radial_chain (Q : Finset Lattice) (hcard : 3 ≤ Q.card)
    (hirr : Irredundant Q) (p : Lattice) (N : ℕ) (ha : Anchor Q p N) :
    Nonempty (RadialChain Q p N) := by
  classical
  let S := Q.erase p
  let f : S → ℝ := fun q => slope N (embed (q.val - p))
  have hf : Function.Injective f := irredundant_anchor_slopes_injective Q hirr p N ha
  letI inst : LinearOrder S := LinearOrder.lift' f hf
  letI : LE S := inst.toLE
  letI : LT S := inst.toLT
  have hsize : S.card = (Q.card - 3) + 2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem ha.1]
    omega
  let e := Fintype.orderIsoFinOfCardEq S (k := Q.card - 3 + 2)
    (by simpa only [Fintype.card_coe] using hsize)
  refine ⟨{
    length := Q.card - 3
    point := fun i => (e i).val
    range_eq := ?_
    injective := Subtype.val_injective.comp e.injective
    slopes := ?_
    determinants := ?_
  }⟩
  · ext q
    constructor
    · rintro ⟨i,rfl⟩
      exact (e i).property
    · intro hq
      exact ⟨e.symm ⟨q,hq⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  · exact @OrderIso.strictMono _ _ _ inst.toPreorder e
  · intro i j hij
    have hs : slope N (embed ((e i).val-p)) < slope N (embed ((e j).val-p)) :=
      @OrderIso.strictMono _ _ _ inst.toPreorder e i j hij
    have hi := ha.2 (e i).val (e i).property
    have hj := ha.2 (e j).val (e j).property
    have hcross := (div_lt_div_iff₀ hi hj).1 hs
    have hid : realDet (embed ((e i).val-p)) (embed ((e j).val-p)) =
        ell N (embed ((e i).val-p)) * kappa (embed ((e j).val-p)) -
        kappa (embed ((e i).val-p)) * ell N (embed ((e j).val-p)) := by
      simp only [realDet,ell,kappa]
      ring
    have hd : 0 < realDet (embed ((e i).val-p)) (embed ((e j).val-p)) := by
      rw [hid]
      linarith
    have hcast : realDet (embed ((e i).val-p)) (embed ((e j).val-p)) =
        (det ((e i).val-p) ((e j).val-p) : ℝ) := by simp [realDet,embed,det]
    rw [hcast] at hd
    exact_mod_cast hd

end ConvexNivat.PolygonTriangulation
