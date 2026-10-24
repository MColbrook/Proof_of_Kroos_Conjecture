module

public import Bandlimited.KernelGeometry
public import Bandlimited.KernelTails

@[expose] public section
noncomputable section
namespace Bandlimited
namespace KernelEstimates

 theorem angular_weight_global {d : ℕ} (u v : Sphere d) {N A L : ℝ}
    (hN : 0 ≤ N) (hA : 0 < A) (hL : 0 ≤ L) :
    (1 + N / A * rho u v) ^ L ≤ (1 + (2 / A) * N) ^ L := by
  have hr0 := rho_nonnegative u v
  apply Real.rpow_le_rpow (by positivity) _ hL
  have h := mul_le_mul_of_nonneg_left (rho_le_two u v) (div_nonneg hN hA.le)
  have heq : 2 / A * N = N / A * 2 := by ring
  rw [heq]
  linarith

 theorem chart_weight_bound {d : ℕ} (u v : Sphere d) (t : E d) {K N A L : ℝ}
    (hK : 1 ≤ K) (hN : 0 ≤ N) (hA : 0 < A) (hL : 0 ≤ L)
    (hρ : rho u v ≤ K * ‖t‖) :
    (1 + N / A * rho u v) ^ L ≤ K ^ L * gaussianWeight A L (N • t) := by
  have hr0 := rho_nonnegative u v
  have hNt : ‖N • t‖ = N * ‖t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hN]
  unfold gaussianWeight
  rw [← Real.mul_rpow (by linarith : 0 ≤ K) (by positivity : 0 ≤ 1 + ‖N • t‖ / A)]
  apply Real.rpow_le_rpow (by positivity) _ hL
  rw [hNt]
  have h := mul_le_mul_of_nonneg_left hρ (div_nonneg hN hA.le)
  have heq : N / A * (K * ‖t‖) = K * (N * ‖t‖ / A) := by ring
  rw [heq] at h
  nlinarith

 theorem gaussianWeight_le_one_scale {d : ℕ} (x : E d) {A L : ℝ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) : gaussianWeight A L x ≤ gaussianWeight 1 L x := by
  unfold gaussianWeight
  apply Real.rpow_le_rpow (by positivity) _ hL
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have h := (div_le_iff₀ hAp).2 (show ‖x‖ ≤ ‖x‖ * A by nlinarith [norm_nonneg x])
  simp only [div_one]
  linarith

 theorem central_angular_weight_bound {d : ℕ} (u v : Sphere d) (t : E d)
    {K M N A L : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hA : 0 < A) (hL : 0 ≤ L) (hρ : rho u v ≤ K * ‖t‖) (hcentral : ‖N • t‖ ≤ M) :
    (1 + N / A * rho u v) ^ L ≤ K ^ L * (1 + M / A) ^ L := by
  apply (chart_weight_bound u v t hK hN hA hL hρ).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
  unfold gaussianWeight
  exact Real.rpow_le_rpow (by positivity) (by gcongr) hL

 theorem chart_gaussian_tail {d : ℕ} (u v : Sphere d) (t : E d)
    {K N A : ℝ} (hK : 0 < K) (hN : 0 ≤ N) (hA : 0 < A)
    (hρ : ‖t‖ / K ≤ rho u v) :
    Real.exp (-(N ^ 2 / A ^ 2) * (rho u v) ^ 2) ≤
      Real.exp (-(1 / (K ^ 2 * A ^ 2)) * ‖N • t‖ ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hs : ‖t‖ ^ 2 / K ^ 2 ≤ (rho u v) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_nonneg (norm_nonneg t) hK.le) hρ 2
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ N ^ 2 / A ^ 2 by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hN, mul_pow]
  have heq : N ^ 2 / A ^ 2 * (‖t‖ ^ 2 / K ^ 2) =
      (1 / (K ^ 2 * A ^ 2)) * (N ^ 2 * ‖t‖ ^ 2) := by ring
  rw [heq] at hm
  linarith only [hm]

 theorem separated_gaussian_tail {d : ℕ} (u v : Sphere d) {D N A : ℝ}
    (hD : 0 < D) (hN : 1 ≤ N) (hA : 0 < A) (hρ : (4 * D)⁻¹ ≤ rho u v) :
    Real.exp (-(N ^ 2 / A ^ 2) * (rho u v) ^ 2) ≤
      Real.exp (-(1 / (16 * D ^ 2 * A ^ 2)) * N) := by
  apply Real.exp_le_exp.mpr
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (4 * D)⁻¹) hρ 2
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ N ^ 2 / A ^ 2 by positivity)
  have hb : 0 ≤ 1 / (16 * D ^ 2 * A ^ 2) := by positivity
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hn := mul_le_mul_of_nonneg_left hN2 hb
  have heq : (N ^ 2 / A ^ 2) * ((4 * D)⁻¹) ^ 2 =
      (1 / (16 * D ^ 2 * A ^ 2)) * N ^ 2 := by ring
  rw [heq] at hm
  nlinarith

#print axioms chart_weight_bound
#print axioms chart_gaussian_tail
#print axioms separated_gaussian_tail
end KernelEstimates
end Bandlimited
end
