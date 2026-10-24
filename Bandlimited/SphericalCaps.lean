module

public import Bandlimited.SphericalQuadrature
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Sharp spherical cap estimates using coordinate boxes in the defining cone.
The box-volume formula and the volume-preserving Euclidean coordinate map
are reused from Mathlib's Lebesgue and Haar-measure developments. -/

@[expose] public section
open scoped BigOperators Pointwise
open MeasureTheory Set
noncomputable section
namespace Bandlimited.SphereQuadrature

def axis (s : ℕ) : E (s + 1) := PiLp.single 2 0 1

def pole (s : ℕ) : Sphere (s + 1) :=
  ⟨axis s, by simp [axis]⟩

@[simp] theorem norm_axis (s : ℕ) : ‖axis s‖ = 1 := by simp [axis]
@[simp] theorem axis_zero (s : ℕ) : axis s 0 = 1 := by simp [axis]
@[simp] theorem axis_succ (s : ℕ) (i : Fin s) : axis s i.succ = 0 := by simp [axis]

theorem euclidean_norm_le_sum_abs {d : ℕ} (x : E d) : ‖x‖ ≤ ∑ i, |x i| := by
  have hx : (∑ i, PiLp.single 2 i (x i)) = x := by ext i; simp
  calc
    ‖x‖ = ‖∑ i, PiLp.single 2 i (x i)‖ := congrArg norm hx.symm
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : E d)‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := by simp [Real.norm_eq_abs]

def coordinateBox {d : ℕ} (a b : Fin d → ℝ) : Set (E d) :=
  WithLp.ofLp ⁻¹' pi univ (fun i => Ioo (a i) (b i))

theorem coordinateBox_volume {d : ℕ} (a b : Fin d → ℝ) :
    volume (coordinateBox a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [coordinateBox, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet]
  exact Real.volume_pi_Ioo

theorem coordinateBox_real_volume {d : ℕ} (a b : Fin d → ℝ) (hab : a ≤ b) :
    (volume (coordinateBox a b)).toReal = ∏ i, (b i - a i) := by
  rw [coordinateBox_volume, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i))

def capScale (s : ℕ) (r : ℝ) : ℝ := r / (16 * ((s : ℝ) + 1))
def lowerA (s : ℕ) (r : ℝ) (i : Fin (s + 1)) : ℝ :=
  if i = 0 then 1 / 4 else -capScale s r
def lowerB (s : ℕ) (r : ℝ) (i : Fin (s + 1)) : ℝ :=
  if i = 0 then 1 / 2 else capScale s r
def upperA (s : ℕ) (r : ℝ) (i : Fin (s + 1)) : ℝ := if i = 0 then -1 else -r
def upperB (s : ℕ) (r : ℝ) (i : Fin (s + 1)) : ℝ := if i = 0 then 1 else r

def capCone (s : ℕ) (r : ℝ) : Set (E (s + 1)) :=
  Ioo (0 : ℝ) 1 • ((Subtype.val : Sphere (s + 1) → E (s + 1)) '' Metric.ball (pole s) r)

theorem normalized_distance_bound {d : ℕ} (x u : E d) (hu : ‖u‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x - u‖ ≤ 2 * ‖x - t • u‖ / ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hab : |‖x‖ - t| ≤ ‖x - t • u‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu, mul_one] using
      abs_norm_sub_norm_le x (t • u)
  have hdecomp : x - ‖x‖ • u = (x - t • u) + (t - ‖x‖) • u := by
    rw [sub_smul]
    abel
  have hb : ‖x - ‖x‖ • u‖ ≤ 2 * ‖x - t • u‖ := by
    rw [hdecomp]
    calc
      ‖(x - t • u) + (t - ‖x‖) • u‖ ≤ ‖x - t • u‖ + ‖(t - ‖x‖) • u‖ := norm_add_le _ _
      _ = ‖x - t • u‖ + |‖x‖ - t| := by
        rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_sub_comm]
      _ ≤ 2 * ‖x - t • u‖ := by linarith
  have hid : ‖x‖⁻¹ • x - u = ‖x‖⁻¹ • (x - ‖x‖ • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖x‖⁻¹ * ‖x - ‖x‖ • u‖ ≤ ‖x‖⁻¹ * (2 * ‖x - t • u‖) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
    _ = 2 * ‖x - t • u‖ / ‖x‖ := by ring

theorem lowerBox_subset_capCone (s : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    coordinateBox (lowerA s r) (lowerB s r) ⊆ capCone s r := by
  intro x hx
  have hcoord : ∀ i : Fin (s + 1), lowerA s r i < x i ∧ x i < lowerB s r i := by
    simpa only [coordinateBox, mem_preimage, mem_pi, mem_univ, forall_const, mem_Ioo] using hx
  have hx0 : (1 : ℝ) / 4 < x 0 ∧ x 0 < 1 / 2 := by simpa [lowerA, lowerB] using hcoord 0
  have hx0pos : 0 < x 0 := by linarith
  have ha : 0 < capScale s r := by unfold capScale; positivity
  let y : E (s + 1) := x - (x 0) • axis s
  have hy0 : y 0 = 0 := by simp [y]
  have hyi (i : Fin s) : |y i.succ| ≤ capScale s r := by
    have h := hcoord i.succ
    have h' : -capScale s r < x i.succ ∧ x i.succ < capScale s r := by
      simpa [lowerA, lowerB] using h
    simpa [y] using (abs_lt.mpr h').le
  have hy : ‖y‖ ≤ r / 16 := by
    calc
      ‖y‖ ≤ ∑ i : Fin (s + 1), |y i| := euclidean_norm_le_sum_abs y
      _ = ∑ i : Fin s, |y i.succ| := by rw [Fin.sum_univ_succ]; simp [hy0]
      _ ≤ ∑ _i : Fin s, capScale s r := Finset.sum_le_sum fun i _ => hyi i
      _ = (s : ℝ) * capScale s r := by simp
      _ ≤ ((s : ℝ) + 1) * capScale s r := mul_le_mul_of_nonneg_right (by linarith) ha.le
      _ = r / 16 := by unfold capScale; field_simp
  have hxnormlower : (1 : ℝ) / 4 < ‖x‖ := by
    have h := PiLp.norm_apply_le (p := 2) x (0 : Fin (s + 1))
    have h' : x 0 ≤ ‖x‖ := by simpa only [Real.norm_eq_abs, abs_of_pos hx0pos] using h
    linarith
  have hxnormpos : 0 < ‖x‖ := by linarith
  have hxne : x ≠ 0 := norm_ne_zero_iff.mp hxnormpos.ne'
  have hxnormupper : ‖x‖ < 1 := by
    have hid : x = (x 0) • axis s + y := by dsimp [y]; abel
    calc
      ‖x‖ = ‖(x 0) • axis s + y‖ := congrArg norm hid
      _ ≤ ‖(x 0) • axis s‖ + ‖y‖ := norm_add_le _ _
      _ ≤ x 0 + r / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx0pos, norm_axis, mul_one]
        exact add_le_add le_rfl hy
      _ < 1 := by linarith
  let u : Sphere (s + 1) := ⟨‖x‖⁻¹ • x, by
    simp [norm_smul, norm_ne_zero_iff.mpr hxne]⟩
  have hudist : dist u (pole s) < r := by
    change ‖‖x‖⁻¹ • x - axis s‖ < r
    apply (normalized_distance_bound x (axis s) (norm_axis s) (x 0) hx0pos.le hxne).trans_lt
    apply (div_lt_iff₀ hxnormpos).mpr
    have hmul := mul_lt_mul_of_pos_left hxnormlower hr
    change 2 * ‖y‖ < r * ‖x‖
    nlinarith
  refine ⟨‖x‖, ⟨hxnormpos, hxnormupper⟩, (u : E (s + 1)),
    ⟨u, hudist, rfl⟩, ?_⟩
  change ‖x‖ • (‖x‖⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ hxnormpos.ne', one_smul]

theorem capCone_subset_upperBox (s : ℕ) {r : ℝ} (_hr : 0 < r) :
    capCone s r ⊆ coordinateBox (upperA s r) (upperB s r) := by
  rintro x ⟨t, ht, z, ⟨u, hu, rfl⟩, rfl⟩
  have hunorm : ‖(u : E (s + 1))‖ = 1 := sphere_norm u
  have hudist : ‖(u : E (s + 1)) - axis s‖ < r := hu
  have htnorm : ‖t • (u : E (s + 1))‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hunorm, mul_one]
  change ∀ i ∈ (univ : Set (Fin (s + 1))),
    t • (u : E (s + 1)) i ∈ Ioo (upperA s r i) (upperB s r i)
  intro i hi
  refine Fin.cases ?_ (fun j => ?_) i
  · have hcoord : |(t • (u : E (s + 1))) 0| < 1 := by
      have h := PiLp.norm_apply_le (p := 2) (t • (u : E (s + 1))) (0 : Fin (s + 1))
      rw [htnorm] at h
      exact lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using h) ht.2
    simpa [upperA, upperB] using abs_lt.mp hcoord
  · have hcoord : |(u : E (s + 1)) j.succ| < r := by
      have h := PiLp.norm_apply_le (p := 2) ((u : E (s + 1)) - axis s) j.succ
      have h' : |(u : E (s + 1)) j.succ| ≤ ‖(u : E (s + 1)) - axis s‖ := by simpa only [PiLp.sub_apply, axis_succ, sub_zero, Real.norm_eq_abs] using h
      exact h'.trans_lt hudist
    have hcoord' : |(t • (u : E (s + 1))) j.succ| < r := by
      change |t * (u : E (s + 1)) j.succ| < r
      rw [abs_mul, abs_of_pos ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans_lt hcoord
    simpa [upperA, upperB] using abs_lt.mp hcoord'

theorem lowerBox_real_volume (s : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (coordinateBox (lowerA s r) (lowerB s r))).toReal =
      (1 / 4 : ℝ) * (2 * capScale s r) ^ s := by
  have ha : 0 ≤ capScale s r := by unfold capScale; positivity
  rw [coordinateBox_real_volume _ _ (by
    intro i
    unfold lowerA lowerB
    split_ifs <;> linarith)]
  rw [Fin.prod_univ_succ]
  norm_num [lowerA, lowerB, sub_neg_eq_add, ← two_mul]

theorem upperBox_real_volume (s : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (coordinateBox (upperA s r) (upperB s r))).toReal = 2 * (2 * r) ^ s := by
  rw [coordinateBox_real_volume _ _ (by
    intro i
    unfold upperA upperB
    split_ifs <;> linarith)]
  rw [Fin.prod_univ_succ]
  simp [upperA, upperB, sub_neg_eq_add, ← two_mul]

theorem coordinateBox_measure_ne_top {d : ℕ} (a b : Fin d → ℝ) :
    volume (coordinateBox a b) ≠ ⊤ := by
  rw [coordinateBox_volume]
  exact ENNReal.prod_ne_top (fun i hi => ENNReal.ofReal_ne_top)

theorem cap_measure_cone (s : ℕ) (r : ℝ) :
    (surfaceMeasure s).real (Metric.ball (pole s) r) =
      ((s : ℝ) + 1) * (volume (capCone s r)).toReal := by
  change (((volume : Measure (E (s + 1))).toSphere) (Metric.ball (pole s) r)).toReal = _
  rw [Measure.toSphere_apply' _ measurableSet_ball, ENNReal.toReal_mul]
  simp only [E, finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_natCast]
  simp [capCone]

def capLowerConstant (s : ℕ) : ℝ := ((s : ℝ) + 1) * (1 / 4) * (2 * capScale s 1) ^ s
def capUpperConstant (s : ℕ) : ℝ := ((s : ℝ) + 1) * 2 * 2 ^ s

theorem capLowerConstant_pos (s : ℕ) : 0 < capLowerConstant s := by
  unfold capLowerConstant capScale
  positivity

theorem capUpperConstant_pos (s : ℕ) : 0 < capUpperConstant s := by
  unfold capUpperConstant
  positivity

theorem pole_cap_bounds (s : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    capLowerConstant s * r ^ s ≤ (surfaceMeasure s).real (Metric.ball (pole s) r) ∧
      (surfaceMeasure s).real (Metric.ball (pole s) r) ≤ capUpperConstant s * r ^ s := by
  have hlow := measure_mono (μ := (volume : Measure (E (s + 1)))) (lowerBox_subset_capCone s hr hr1)
  have hup := measure_mono (μ := (volume : Measure (E (s + 1)))) (capCone_subset_upperBox s hr)
  have hconeFinite : volume (capCone s r) ≠ ⊤ :=
    ne_top_of_le_ne_top (coordinateBox_measure_ne_top (upperA s r) (upperB s r)) hup
  have hlowReal := ENNReal.toReal_mono hconeFinite hlow
  have hupReal := ENNReal.toReal_mono
    (coordinateBox_measure_ne_top (upperA s r) (upperB s r)) hup
  rw [lowerBox_real_volume s hr.le] at hlowReal
  rw [upperBox_real_volume s hr.le] at hupReal
  have hscale : 2 * capScale s r = r * (2 * capScale s 1) := by unfold capScale; ring
  rw [cap_measure_cone]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hlowReal (show 0 ≤ (s : ℝ) + 1 by positivity)
    rw [hscale, mul_pow] at hmul
    unfold capLowerConstant
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left hupReal (show 0 ≤ (s : ℝ) + 1 by positivity)
    rw [mul_pow] at hmul
    unfold capUpperConstant
    nlinarith

theorem pole_cap_upper (s : ℕ) {r : ℝ} (hr : 0 < r) :
    (surfaceMeasure s).real (Metric.ball (pole s) r) ≤ capUpperConstant s * r ^ s := by
  have hup := measure_mono (μ := (volume : Measure (E (s + 1)))) (capCone_subset_upperBox s hr)
  have hupReal := ENNReal.toReal_mono
    (coordinateBox_measure_ne_top (upperA s r) (upperB s r)) hup
  rw [upperBox_real_volume s hr.le] at hupReal
  rw [cap_measure_cone]
  have hmul := mul_le_mul_of_nonneg_left hupReal (show 0 ≤ (s : ℝ) + 1 by positivity)
  rw [mul_pow] at hmul
  unfold capUpperConstant
  nlinarith

theorem cap_measure_rotation (s : ℕ) (f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1))
    (u : Sphere (s + 1)) (r : ℝ) :
    (surfaceMeasure s).real (Metric.ball (sphereMap f u) r) =
      (surfaceMeasure s).real (Metric.ball u r) := by
  have hpre : sphereMap f ⁻¹' Metric.ball (sphereMap f u) r = Metric.ball u r := by
    ext v
    change ‖f v - f u‖ < r ↔ ‖(v : E (s + 1)) - u‖ < r
    rw [← f.map_sub, f.norm_map]
  have hm := (sphereMap_measurePreserving s f).measure_preimage
    (measurableSet_ball.nullMeasurableSet : NullMeasurableSet (Metric.ball (sphereMap f u) r) _)
  rw [hpre] at hm
  exact (congrArg ENNReal.toReal hm).symm

theorem cap_measure_eq_pole (s : ℕ) (u : Sphere (s + 1)) (r : ℝ) :
    (surfaceMeasure s).real (Metric.ball u r) =
      (surfaceMeasure s).real (Metric.ball (pole s) r) := by
  let f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1) :=
    Submodule.reflection (ℝ ∙ ((pole s : E (s + 1)) - u))ᗮ
  have heq : sphereMap f (pole s) = u := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((sphere_norm (pole s)).trans (sphere_norm u).symm)
  simpa only [heq] using cap_measure_rotation s f (pole s) r

theorem cap_lower (s : ℕ) (u : Sphere (s + 1)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    capLowerConstant s * r ^ s ≤ (surfaceMeasure s).real (Metric.ball u r) := by
  rw [cap_measure_eq_pole]
  exact (pole_cap_bounds s hr hr1).1

theorem cap_upper (s : ℕ) (u : Sphere (s + 1)) {r : ℝ} (hr : 0 < r) :
    (surfaceMeasure s).real (Metric.ball u r) ≤ capUpperConstant s * r ^ s := by
  rw [cap_measure_eq_pole]
  exact pole_cap_upper s hr

def antipode {d : ℕ} (u : Sphere d) : Sphere d := ⟨-(u : E d), by simp⟩
def projectiveBall {d : ℕ} (u : Sphere d) (r : ℝ) : Set (Sphere d) :=
  {v | rho u v < r}

theorem projectiveBall_eq_union {d : ℕ} (u : Sphere d) (r : ℝ) :
    projectiveBall u r = Metric.ball u r ∪ Metric.ball (antipode u) r := by
  ext v
  simp only [projectiveBall, mem_setOf_eq, rho, min_lt_iff, mem_union, Metric.mem_ball]
  change (‖(u : E d) - v‖ < r ∨ ‖(u : E d) + v‖ < r) ↔
    (‖(v : E d) - u‖ < r ∨ ‖(v : E d) - -(u : E d)‖ < r)
  rw [norm_sub_rev (u : E d) v, sub_neg_eq_add, add_comm (v : E d) u]

theorem projectiveBall_lower (s : ℕ) (u : Sphere (s + 1)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    capLowerConstant s * r ^ s ≤ (surfaceMeasure s).real (projectiveBall u r) := by
  apply (cap_lower s u hr hr1).trans
  rw [projectiveBall_eq_union]
  exact measureReal_mono subset_union_left

theorem projectiveBall_upper (s : ℕ) (u : Sphere (s + 1)) {r : ℝ} (hr : 0 < r) :
    (surfaceMeasure s).real (projectiveBall u r) ≤ (2 * capUpperConstant s) * r ^ s := by
  rw [projectiveBall_eq_union]
  calc
    _ ≤ (surfaceMeasure s).real (Metric.ball u r) +
        (surfaceMeasure s).real (Metric.ball (antipode u) r) := measureReal_union_le _ _
    _ ≤ capUpperConstant s * r ^ s + capUpperConstant s * r ^ s :=
      add_le_add (cap_upper s u hr) (cap_upper s (antipode u) hr)
    _ = (2 * capUpperConstant s) * r ^ s := by ring

#print axioms cap_lower
#print axioms cap_upper
#print axioms projectiveBall_lower
#print axioms projectiveBall_upper

#print axioms lowerBox_subset_capCone
#print axioms capCone_subset_upperBox
#print axioms pole_cap_bounds

end Bandlimited.SphereQuadrature
end
