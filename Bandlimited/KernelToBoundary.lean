module

public import Bandlimited.BodyGeometry
public import Bandlimited.Summation
public import Lean.Elab.Tactic.Omega

/-! The finite quadrature argument passing from the uniform angular kernel
and the spherical estimates to approximation of one on a norm-ball boundary.
The two analytic principal results are explicit hypotheses. -/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited

theorem bounded_norm_uniform_large_dimension_of_kernels
    (hG : UniformGaussianStatement) (hQ : PositiveSphericalQuadratureStatement)
    (s : ℕ) (hs : 1 ≤ s) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ ν : BodyNorm (s + 1), NormBounds α β ν →
      ∃ p : Polynomial (s + 1), p.IsHomogeneous (2 * n) ∧
        BoundaryErrorLT (normBall ν) p (fun _ => 1) ε := by
  classical
  obtain ⟨c, C, hc, hC, hq⟩ := hQ s hs
  let L : ℝ := (s : ℝ) + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨C_L, hCL, hqL⟩ := hq L (by dsimp [L]; linarith)
  let B : ℝ := 2 * C_L / c
  have hB : 0 < B := by dsimp [B]; positivity
  let δ : ℝ := ε / (4 * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, N₀, hN₀, hk⟩ := hG s hs α β L δ hα hαβ hL hδ
  have hApos : 0 < A := by linarith
  obtain ⟨N_A, hNA⟩ := exists_nat_ge A
  refine ⟨max N₀ N_A, ?_⟩
  intro n hn ν hν
  let N : ℕ := 2 * n
  have hNN : N₀ ≤ N := by dsimp [N]; omega
  have hAN : A ≤ (N : ℝ) := by
    have hNAN : N_A ≤ N := by dsimp [N]; omega
    exact hNA.trans (by exact_mod_cast hNAN)
  let lam : ℝ := (N : ℝ) / A
  have hlam : 1 ≤ lam := (le_div_iff₀ hApos).2 (by simpa only [one_mul] using hAN)
  have hlampos : 0 < lam := by linarith
  let u₀ : Sphere (s + 1) := ⟨PiLp.single 2 ⟨0, by omega⟩ (1 : ℝ), by
    simp only [Metric.mem_sphere, dist_zero_right, PiLp.norm_single, norm_one]⟩
  let I : ℝ := sphericalGaussianIntegral s lam u₀
  let J : ℝ := sphericalTailIntegral s lam L u₀
  obtain ⟨hinv, hbounds, hquadrature⟩ := hqL lam hlam
  have hscale : 0 < (lam ^ s)⁻¹ := inv_pos.mpr (pow_pos hlampos s)
  have hI : 0 < I := (mul_pos hc hscale).trans_le (hbounds u₀).1
  have hratio : 2 * J / I ≤ B := by
    apply (div_le_iff₀ hI).2
    have hBC : B * c = 2 * C_L := by
      dsimp [B]
      field_simp
    calc
      2 * J ≤ 2 * (C_L * (lam ^ s)⁻¹) := by
        have h := (hbounds u₀).2.2
        dsimp [J]
        linarith
      _ = B * (c * (lam ^ s)⁻¹) := by rw [← mul_assoc, ← hBC]; ring
      _ ≤ B * I := mul_le_mul_of_nonneg_left (hbounds u₀).1 hB.le
  obtain ⟨m, hm, v, w, hw, hquad⟩ := hquadrature (ε / 4) (by positivity)
  have hEven : Even N := by refine ⟨n, ?_⟩; dsimp [N]; omega
  have hpolys (i : Fin m) : ∃ p : Polynomial (s + 1), p.IsHomogeneous N ∧
      AngularKernelErrorLT ν (v i) N A L p δ := hk ν hν (v i) N hEven hNN
  choose p hp herr using hpolys
  let P : Polynomial (s + 1) := MvPolynomial.C I⁻¹ *
    ∑ i : Fin m, MvPolynomial.C (w i) * p i
  have hPhom : P.IsHomogeneous N := by
    apply MvPolynomial.IsHomogeneous.C_mul
    exact MvPolynomial.IsHomogeneous.sum Finset.univ _ N (fun i _ => (hp i).C_mul (w i))
  refine ⟨P, hPhom, ?_⟩
  apply boundary_error_of_radial ν (by linarith : 0 ≤ β) hν P ε
  refine ⟨ε / 2, by linarith, ?_⟩
  intro u
  have hlocal (i : Fin m) :
      |evalPolynomial (p i) (radial ν u) - gaussianKernel lam u (v i)| ≤
        δ * tailKernel lam L u (v i) := by
    obtain ⟨b, hb, hbound⟩ := herr i
    have hrho : 0 ≤ rho u (v i) := le_min (norm_nonneg _) (norm_nonneg _)
    have hbase : 0 < 1 + lam * rho u (v i) := by positivity
    have hW : 0 < (1 + lam * rho u (v i)) ^ L := Real.rpow_pos_of_pos hbase L
    rw [tailKernel, Real.rpow_neg hbase.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ hW).2
    have hb' : (1 + lam * rho u (v i)) ^ L *
        |evalPolynomial (p i) (radial ν u) - gaussianKernel lam u (v i)| ≤ b := by
      simpa only [gaussianKernel, lam, div_pow] using hbound u
    simpa only [mul_comm] using (hb'.trans hb.le)
  have hquad' : |(∑ i : Fin m, w i * gaussianKernel lam u (v i)) - I| ≤
      (ε / 4) * I := by
    have huI := (hinv u u₀).1
    simpa only [I, huI] using ((hquad u).1.le)
  have htail' : (∑ i : Fin m, w i * tailKernel lam L u (v i)) ≤ 2 * J := by
    have huJ := (hinv u u₀).2
    simpa only [J, huJ] using (hquad u).2
  have hs := weighted_sum_error Finset.univ w
    (fun i => evalPolynomial (p i) (radial ν u))
    (fun i => gaussianKernel lam u (v i)) (fun i => tailKernel lam L u (v i))
    I J δ (ε / 4) hI hδ.le (fun i _ => (hw i).le) (fun i _ => hlocal i)
    hquad' htail'
  have hPeval : evalPolynomial P (radial ν u) =
      I⁻¹ * (∑ i : Fin m, w i * evalPolynomial (p i) (radial ν u)) := by
    simp only [P, evalPolynomial, map_mul, map_sum, MvPolynomial.eval_C]
  rw [hPeval]
  apply hs.trans
  have hδB : δ * B = ε / 4 := by
    dsimp [δ]
    field_simp
  calc
    ε / 4 + δ * (2 * J / I) ≤ ε / 4 + δ * B := by
      have hmul := mul_le_mul_of_nonneg_left hratio hδ.le
      linarith
    _ = ε / 2 := by rw [hδB]; ring

theorem bounded_norm_uniform_of_kernels
    (hG : UniformGaussianStatement) (hQ : PositiveSphericalQuadratureStatement) :
    BoundedNormUniformStatement := by
  intro d α β hα hαβ ε hε
  cases d with
  | zero =>
    refine ⟨0, ?_⟩
    intro n hn ν hν
    refine ⟨0, MvPolynomial.isHomogeneous_zero (Fin 0) ℝ (2 * n), 0, hε, ?_⟩
    intro x
    exact False.elim (by
      simpa [zero_dimensional_boundary_empty ν] using x.property)
  | succ d =>
    cases d with
    | zero =>
      refine ⟨0, ?_⟩
      intro n hn ν hν
      refine ⟨oneDimensionalPolynomial ν n, oneDimensionalPolynomial_homogeneous ν n,
        0, hε, ?_⟩
      intro x
      have hval := ν.frontier_value (by linarith : 0 ≤ β) hν x.property
      rw [oneDimensionalPolynomial_exact ν n (x : E 1) hval]
      norm_num
    | succ s =>
      exact bounded_norm_uniform_large_dimension_of_kernels hG hQ (s + 1) (by omega)
        α β hα hαβ ε hε

#print axioms bounded_norm_uniform_of_kernels

#print axioms bounded_norm_uniform_large_dimension_of_kernels

end Bandlimited
end
