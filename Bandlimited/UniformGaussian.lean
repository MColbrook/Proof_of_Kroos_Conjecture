module
public import Bandlimited.ConvexGaussianClosed
public import Bandlimited.KernelTaylor
public import Bandlimited.FunctionalPolynomial
public import Bandlimited.KernelErrorAssembly
@[expose] public section
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Bandlimited
open KernelTaylor KernelEstimates

set_option maxHeartbeats 250000

theorem uniform_gaussian_of_finite_family (hfinite : FiniteFamilyStatement) :
    UniformGaussianStatement := by
  classical
  intro s hs α β L ε hα hαβ hL hε
  let d := s + 1
  let D := β / α
  have hβ : 0 < β := hα.trans_le hαβ
  have hD : 1 ≤ D := (le_div_iff₀ hα).2 (by simpa only [one_mul] using hαβ)
  have hDp : 0 < D := by linarith
  let C := D * (1 + D)
  have hC : 0 < C := by dsimp [C]; positivity
  let K := 2 * D
  have hK : 1 ≤ K := by dsimp [K]; linarith
  let B := K ^ L
  have hB : 0 < B := by dsimp [B]; positivity
  let τ := ε / (16 * B)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let σ := 1 / (64 * Real.exp 1 * D)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  obtain ⟨A, hA, m, hm, F, hF, hfamily⟩ := hfinite d (by dsimp [d]; omega)
    L σ C τ hL hσ hC hτ
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  choose φ hφ hFeq using fun j => (hF j).1.exists_frequency hσ
  obtain ⟨H, hH⟩ := (Set.finite_range (fun j => fourierMass (φ j))).bddAbove
  let Q := max 1 H
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmass (j : Fin m) : fourierMass (φ j) ≤ Q :=
    (hH (Set.mem_range_self j)).trans (le_max_right _ _)
  obtain ⟨M, hM, htail⟩ := finite_bandlimited_gaussian_tail
    (by dsimp [d]; omega : d ≠ 0) σ L (1 / (K ^ 2 * A ^ 2)) hL (by positivity)
    F (fun j => (hF j).1) τ hτ
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let G₀ := ConvexGaussian.uniformGaussianBound L
  have hG₀ : 0 < G₀ := ConvexGaussian.uniformGaussianBound_pos L
  let δ := τ / (G₀ + τ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Nr, hNr, hratio⟩ := central_exponential_error_tends_to_zero C M δ hδ
  obtain ⟨Rt, hRt, hTaylorTail⟩ := polynomial_exponential_tail (2 / A) L (1 / 4)
    (by positivity) hL (by norm_num) (ε / (16 * Q)) (by positivity)
  obtain ⟨Rs, hRs, hSeparated⟩ := polynomial_exponential_tail (2 / A) L
    (1 / (16 * D ^ 2 * A ^ 2)) (by positivity) hL (by positivity) (ε / 16) (by positivity)
  let W := B * (1 + M / A) ^ L
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let J := W * (12 * (1 + D) * M ^ 3) / A ^ 2
  let Ra := 1 + J / (ε / 16)
  let R₀ := max Rt (max Rs (max (2 * (1 + D) * M) Ra))
  let N₀ := max 2 (max Nr ⌈R₀⌉₊)
  have hN₀ : 2 ≤ N₀ := le_max_left _ _
  refine ⟨A, hA, N₀, hN₀, ?_⟩
  intro ν hν v N hNeven hNlarge
  have hN2 : 2 ≤ N := hN₀.trans hNlarge
  have hNnat : 0 < N := by omega
  have hNp : 0 < (N : ℝ) := Nat.cast_pos.mpr hNnat
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNrN : Nr ≤ N := (le_max_left Nr ⌈R₀⌉₊).trans ((le_max_right 2 _).trans hNlarge)
  have hR₀N : R₀ ≤ (N : ℝ) := (Nat.le_ceil R₀).trans (by
    exact_mod_cast ((le_max_right Nr ⌈R₀⌉₊).trans ((le_max_right 2 _).trans hNlarge)))
  have hRtN : Rt ≤ (N : ℝ) := (le_max_left _ _).trans hR₀N
  have hRsN : Rs ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hR₀N)
  have hLarge : 2 * (1 + D) * M ≤ (N : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hR₀N))
  have hRaN : Ra ≤ (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hR₀N))
  have hTaylorN : (1 + (2 / A) * (N : ℝ)) ^ L *
      (Q * Real.exp (-(N : ℝ) / 4)) < ε / 16 := by
    have h := mul_lt_mul_of_pos_left (hTaylorTail (N : ℝ) hRtN) hQ
    have hc : Q * (ε / (16 * Q)) = ε / 16 := by field_simp
    rw [hc] at h
    have heq : -(1 / 4 : ℝ) * (N : ℝ) = -(N : ℝ) / 4 := by ring
    rw [heq] at h
    nlinarith only [h]
  have hSeparatedN := hSeparated (N : ℝ) hRsN
  have hAngularN : W * (12 * (1 + D) * M ^ 3 / ((N : ℝ) * A ^ 2)) < ε / 16 := by
    have h : J / (ε / 16) < (N : ℝ) := by dsimp [Ra] at hRaN; linarith
    have hc := (div_lt_iff₀ (show 0 < ε / 16 by positivity)).1 h
    have hc' : J / (N : ℝ) < ε / 16 := (div_lt_iff₀ hNp).2 (by nlinarith only [hc])
    have heq : W * (12 * (1 + D) * M ^ 3 / ((N : ℝ) * A ^ 2)) = J / (N : ℝ) := by dsimp [J]; ring
    rw [heq]
    exact hc'
  have hvne : (v : E d) ≠ 0 := by
    intro hz
    have h := sphere_norm v
    rw [hz, norm_zero] at h
    norm_num at h
  obtain ⟨ℓ, hvℓ, hℓ, hnℓ⟩ := ν.supporting_functional hβ.le hν (v : E d) hvne
  let a₀ := ν.toFun (v : E d)
  have ha₀ : 0 < a₀ := ν.sphere_value_pos hα hν v
  have hαv : α ≤ a₀ := by simpa only [sphere_norm, mul_one] using (hν (v : E d)).1
  have hβv : a₀ ≤ β := by simpa only [sphere_norm, mul_one] using (hν (v : E d)).2
  have hDquot : β / a₀ ≤ D := div_le_div_of_nonneg_left hβ.le hα hαv
  let f := supportingProfile ν (v : E d) ℓ a₀ (N : ℝ)
  have hf : HasProfileLipschitzBound C f :=
    supportingProfile_common_bound ν (v : E d) (sphere_norm v) ℓ hα hαβ hNp hν hvℓ hℓ hnℓ
  obtain ⟨j, b₁, hb₁, hApprox⟩ := hfamily f hf
  let ell := functionalPolynomial ℓ.toLinearMap
  let b : E d →ₗ[ℝ] E d := a₀ • orthogonalResidualLinear (v : E d)
  let p := homogeneousApproximation N (φ j) ell b
  have hp : p.IsHomogeneous N := homogeneousApproximation_homogeneous N (φ j) ell
    (functionalPolynomial_homogeneous ℓ.toLinearMap) b
  have hb (u : Sphere d) : ‖b (radial ν u)‖ ≤ D := by
    change ‖a₀ • orthogonalResidual (v : E d) (radial ν u)‖ ≤ D
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha₀]
    calc
      _ ≤ a₀ * α⁻¹ := mul_le_mul_of_nonneg_left
        ((orthogonalResidual_norm _ _ (sphere_norm v)).trans (ν.radial_norm_bound hα hν u)) ha₀.le
      _ ≤ β * α⁻¹ := mul_le_mul_of_nonneg_right hβv (by positivity)
      _ = D := by dsimp [D]; ring
  have hBmap (t : E d) : ‖supportProjection (v : E d) ℓ a₀ t‖ ≤ (1 + D) * ‖t‖ :=
    (supportProjection_norm (v : E d) (sphere_norm v) ℓ ha₀ hnℓ t).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg t))
  have hℓmap (t : E d) : |ℓ t / a₀| ≤ D * ‖t‖ := by
    rw [abs_div, abs_of_pos ha₀]
    calc
      _ ≤ (β * ‖t‖) / a₀ := div_le_div_of_nonneg_right ((hℓ t).trans (hν t).2) ha₀.le
      _ = (β / a₀) * ‖t‖ := by ring
      _ ≤ D * ‖t‖ := mul_le_mul_of_nonneg_right hDquot (norm_nonneg t)
  have hGlobal (u : Sphere d) := angular_weight_global u v hNp.le hAp hL
  have hWeight0 (u : Sphere d) : 0 ≤ (1 + (N : ℝ) / A * rho u v) ^ L :=
    Real.rpow_nonneg (by positivity [rho_nonnegative u v]) _
  refine ⟨p, hp, ε / 2, by linarith, ?_⟩
  apply kernel_error_of_three_regions ν v ℓ A L (ε / 2) p hp hNeven
  · intro u hu
    have hsmall := homogeneousApproximation_small_height (hφ j) hNeven hD (le_refl σ)
      ell b (radial ν u) (by simpa only [ell, functionalPolynomial_eval, ContinuousLinearMap.coe_coe, supportingHeight_radial] using hu) (hb u)
    have hpbound : |evalPolynomial p (radial ν u)| ≤ Q * Real.exp (-(N : ℝ) / 4) :=
      hsmall.trans (mul_le_mul_of_nonneg_right (hmass j) (Real.exp_pos _).le)
    have hsep := supportingHeight_separation ν ℓ hα hαβ hν hℓ hnℓ v u hvℓ hu
    have hg := separated_gaussian_tail u v hDp hN1 hAp hsep
    have htri := norm_sub_le (evalPolynomial p (radial ν u))
      (Real.exp (-((N : ℝ) ^ 2 / A ^ 2) * rho u v ^ 2))
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at htri
    have hpw := mul_le_mul (hGlobal u) hpbound (abs_nonneg _) (by positivity : 0 ≤ (1 + 2 / A * (N : ℝ)) ^ L)
    have hgw := mul_le_mul (hGlobal u) hg (Real.exp_pos _).le (by positivity : 0 ≤ (1 + 2 / A * (N : ℝ)) ^ L)
    have hwtri := mul_le_mul_of_nonneg_left htri (hWeight0 u)
    change angularKernelError ν v N A L p u ≤ ε / 2
    unfold angularKernelError
    nlinarith only [hpw, hgw, hwtri, hTaylorN, hSeparatedN, hε]
  · intro u hu
    let a := ℓ (radial ν u)
    have ha : 1 / 2 ≤ a := by simpa only [a, supportingHeight_radial] using hu
    have hap : 0 < a := by linarith
    have ha1 : a ≤ 1 := (le_abs_self a).trans (by
      simpa only [a, supportingHeight_radial] using supportingHeight_abs_le ν ℓ hα hν hℓ u)
    have haN : 0 ≤ a ^ N := pow_nonneg hap.le _
    have haN1 : a ^ N ≤ 1 := pow_le_one₀ hap.le ha1
    let t := supportingChart (v : E d) (radial ν u) ℓ a₀
    let y := (N : ℝ) • t
    have ht : ‖t‖ ≤ 2 * D := supportingChart_norm_bound ν ℓ hα hαβ hν u v ha
    have hchart : a⁻¹ • b (radial ν u) = t := by
      change a⁻¹ • (a₀ • orthogonalResidual (v : E d) (radial ν u)) =
        (a₀ / a) • orthogonalResidual (v : E d) (radial ν u)
      rw [smul_smul]
      congr 1
      ring
    have heval : evalPolynomial p (radial ν u) = a ^ N * evalPolynomial (approximatingPolynomial N (φ j)) t := by
      have h := homogeneousApproximation_eval N (φ j) ell b (radial ν u)
        (by simpa only [ell, functionalPolynomial_eval, ContinuousLinearMap.coe_coe] using hap.ne')
      simp only [ell, functionalPolynomial_eval, ContinuousLinearMap.coe_coe] at h
      change evalPolynomial p (radial ν u) = a ^ N * evalPolynomial (approximatingPolynomial N (φ j)) (a⁻¹ • b (radial ν u)) at h
      simpa only [hchart] using h
    have hP := approximatingPolynomial_chart_error (hφ j) hNeven hN2 hD (le_refl σ) t ht
    rw [← hFeq j] at hP
    have hTaylor : (1 + (N : ℝ) / A * rho u v) ^ L *
        |evalPolynomial p (radial ν u) - a ^ N * (F j y).re| ≤ ε / 16 := by
      have he : |evalPolynomial p (radial ν u) - a ^ N * (F j y).re| ≤
          Q * Real.exp (-(N : ℝ) / 4) := by
        rw [heval, ← mul_sub, abs_mul, abs_of_nonneg haN]
        have h₁ := mul_le_mul_of_nonneg_left hP haN
        have h₂ : a ^ N * (fourierMass (φ j) * Real.exp (-(N : ℝ))) ≤
            Q * Real.exp (-(N : ℝ) / 4) := by
          have hq := mul_le_mul (hmass j) (Real.exp_le_exp.mpr (show -(N : ℝ) ≤ -(N : ℝ) / 4 by linarith))
            (Real.exp_pos _).le hQ.le
          have hpw := mul_le_mul_of_nonneg_right haN1 (show 0 ≤ fourierMass (φ j) * Real.exp (-(N : ℝ)) by positivity [fourierMass_nonneg (φ j)])
          nlinarith only [hq, hpw]
        exact h₁.trans h₂
      exact (mul_le_mul (hGlobal u) he (abs_nonneg _) (by positivity)).trans hTaylorN.le
    obtain ⟨hρlower, hρupper⟩ := supportingChart_angular_bounds ν ℓ hα hαβ hν hℓ u v ha
    have hw := chart_weight_bound u v t hK hNp.le hAp hL hρupper
    by_cases hcentral : ‖y‖ ≤ M
    · let q := f y
      have hq : 0 ≤ q := hf.1.2.1 y
      have hqCM : q ≤ C * M := by
        have h := hf.2 y 0
        rw [hf.1.2.2.1, sub_zero, sub_zero] at h
        exact ((le_abs_self _).trans h).trans (mul_le_mul_of_nonneg_left hcentral hC.le)
      have haeq : a = (1 + q / (N : ℝ))⁻¹ :=
        supportingChart_radial_identity ν ℓ hα hν u v hvℓ hap hNp.ne'
      have hr := compact_rescaling_ratio_bound hq hC.le hMp.le hqCM hNnat
      rw [← haeq] at hr
      have hrδ : a ^ N * Real.exp q - 1 ≤ δ := by
        have h := hratio N hNrN
        linarith [hr.2]
      have hAng := local_angular_gaussian_error u v t ℓ a₀ D M (N : ℝ) A hDp.le hMp.le hNp hAp
        (supportingChart_orthogonal _ _ _ _ (sphere_norm v)) (hBmap t) (hℓmap t)
        hcentral hLarge (supportingChart_direction ν ℓ hα hν u v hvℓ hap)
      have hAngw : (1 + (N : ℝ) / A * rho u v) ^ L *
          |gaussian A y - Real.exp (-((N : ℝ) ^ 2 / A ^ 2) * rho u v ^ 2)| ≤ ε / 16 := by
        rw [abs_sub_comm]
        have hWb := central_angular_weight_bound u v t hK hMp.le hNp.le hAp hL hρupper hcentral
        simpa only [neg_mul] using (mul_le_mul hWb hAng (abs_nonneg _) hW).trans hAngularN.le
      have hG : gaussianWeight A L y * ‖(gaussian A y : ℂ)‖ ≤ G₀ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by unfold gaussian; positivity)]
        exact ConvexGaussian.weighted_gaussian_uniform A L hAp hL y
      have hmain := central_real_error _ _ B τ G₀ δ a q _ (gaussian A y) _ (ε / 16) (ε / 16) (F j y) N
        (hWeight0 u) (by unfold gaussianWeight; positivity) hB.le hτ.le hG₀.le hw hr.1 hrδ
        ((hApprox y).trans hb₁.le) hG hTaylor hAngw
      have hδeq : δ * (G₀ + τ) = τ := by dsimp [δ]; field_simp
      rw [hδeq] at hmain
      change angularKernelError ν v N A L p u ≤ ε / 2
      unfold angularKernelError
      have hτeq : B * τ = ε / 16 := by dsimp [τ]; field_simp
      linarith only [hmain, hτeq, hε]
    · have htailu := (htail j y (le_of_not_ge hcentral)).le
      have hg := chart_gaussian_tail u v t (lt_of_lt_of_le zero_lt_one hK) hNp.le hAp hρlower
      have hw1 : (1 + (N : ℝ) / A * rho u v) ^ L ≤ B * gaussianWeight 1 L y :=
        hw.trans (mul_le_mul_of_nonneg_left (gaussianWeight_le_one_scale y hA hL) hB.le)
      have hTail : gaussianWeight 1 L y *
          (‖F j y‖ + Real.exp (-((N : ℝ) ^ 2 / A ^ 2) * rho u v ^ 2)) ≤ τ := by
        have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ gaussianWeight 1 L y by unfold gaussianWeight; positivity)
        nlinarith only [h, htailu]
      have hmain := outer_real_error _ _ B a _ _ (ε / 16) τ (F j y) N
        (hWeight0 u) (by unfold gaussianWeight; positivity) hB.le haN haN1 (Real.exp_pos _).le hw1 hTaylor hTail
      change angularKernelError ν v N A L p u ≤ ε / 2
      unfold angularKernelError
      have hτeq : B * τ = ε / 16 := by dsimp [τ]; field_simp
      linarith only [hmain, hτeq, hε]

 theorem uniform_gaussian : UniformGaussianStatement :=
   uniform_gaussian_of_finite_family finite_family

#print axioms uniform_gaussian_of_finite_family
#print axioms uniform_gaussian
end Bandlimited
end
