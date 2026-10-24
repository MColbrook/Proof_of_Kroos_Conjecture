module

public import Bandlimited.Definitions
public import Bandlimited.GaussianCutoff

/- Dimension-independent Gaussian bounds and the final two-factor error estimate. -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited
namespace ConvexGaussian

def uniformGaussianBound (L : ℝ) : ℝ :=
  (2 : ℝ) ^ ⌈L⌉₊ * (Nat.factorial ⌈L⌉₊ : ℝ)

theorem uniformGaussianBound_pos (L : ℝ) : 0 < uniformGaussianBound L := by
  unfold uniformGaussianBound
  positivity

theorem weighted_gaussian_uniform {d : ℕ} (A L : ℝ) (hA : 0 < A) (_hL : 0 ≤ L)
    (x : E d) : gaussianWeight A L x * gaussian A x ≤ uniformGaussianBound L := by
  let m : ℕ := ⌈L⌉₊
  let r : ℝ := ‖x‖ / A
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) hA.le
  have hpoly : (1 + r) ^ L ≤ (1 + r) ^ m := by
    calc
      (1 + r) ^ L ≤ (1 + r) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil L)
      _ = (1 + r) ^ m := Real.rpow_natCast _ _
  have heq : gaussian A x = Real.exp (-r ^ 2) := by
    unfold gaussian
    congr 1
    dsimp [r]
    rw [div_pow]
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans
    (polynomial_gaussian_bound m r hr)

/-- One common finite-dimensional cutoff error yields a profile-independent
budget. No choice of profile or its Lipschitz constant enters Δ. -/
theorem finite_error_budget (s : ℕ) (e : ℕ → ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hnonneg : ∀ k, k ≤ s → ∀ A : ℝ, 1 ≤ A → 0 ≤ e k A)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ k : ℕ, k ≤ s → e k A < ε) :
    ∃ Δ : ℝ → ℝ, TendsToZeroAtInfinity Δ ∧ ∀ A : ℝ, 1 ≤ A →
      0 ≤ Δ A ∧ ∀ k : ℕ, k ≤ s → C * e k A ≤ Δ A := by
  let Δ : ℝ → ℝ := fun A => C * ∑ i : Fin (s + 1), e i A
  have hΔ : ∀ A, 1 ≤ A → 0 ≤ Δ A := by
    intro A hA
    exact mul_nonneg hC (Finset.sum_nonneg fun i _ => hnonneg i (by omega) A hA)
  refine ⟨Δ, ?_, ?_⟩
  · intro ε hε
    let D : ℝ := 1 + C * (s + 1)
    have hD : 0 < D := by dsimp [D]; positivity
    let δ : ℝ := ε / D
    have hδ : 0 < δ := div_pos hε hD
    have hcancel : δ * D = ε := by dsimp [δ]; field_simp
    obtain ⟨A₀, hA₀, htail⟩ := huniform δ hδ
    refine ⟨A₀, ?_⟩
    intro A hA
    have hA1 : 1 ≤ A := hA₀.trans hA
    rw [abs_of_nonneg (hΔ A hA1)]
    have hsum : (∑ i : Fin (s + 1), e i A) ≤ (s + 1 : ℕ) * δ := by
      calc
        (∑ i : Fin (s + 1), e i A) ≤ ∑ _ : Fin (s + 1), δ :=
          Finset.sum_le_sum fun i _ => (htail A hA i (by omega)).le
        _ = (s + 1 : ℕ) * δ := by simp
    have hbound := mul_le_mul_of_nonneg_left hsum hC
    change C * ∑ i : Fin (s + 1), e i A < ε
    dsimp [D] at hcancel
    simp only [Nat.cast_add, Nat.cast_one] at hbound
    nlinarith
  · intro A hA
    refine ⟨hΔ A hA, ?_⟩
    intro k hk
    apply mul_le_mul_of_nonneg_left _ hC
    exact Finset.single_le_sum (fun (i : Fin (s + 1)) _ => hnonneg i (by omega) A hA)
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (s + 1)))

/-- The weighted tensor error splits into an arbitrarily small active error
and the common cutoff error on the orthogonal complement. -/
theorem weighted_product_error (w wy wz ε B e : ℝ) (a F G H K : ℂ)
    (_hw : 0 ≤ w) (hwy : 0 ≤ wy) (hwz : 0 ≤ wz) (hε : 0 ≤ ε)
    (hB : 0 ≤ B) (_he : 0 ≤ e) (hwbound : w ≤ wy * wz)
    (hactive : wy * ‖a * F - H‖ ≤ ε)
    (hcutoff : wz * ‖G - K‖ ≤ e)
    (hH : wy * ‖H‖ ≤ B) (hK : wz * ‖K‖ ≤ B) :
    w * ‖a * (F * G) - H * K‖ ≤ ε * (B + e) + B * e := by
  have hGnorm : wz * ‖G‖ ≤ B + e := by
    have hnorm : ‖G‖ ≤ ‖G - K‖ + ‖K‖ := by
      calc
        ‖G‖ = ‖(G - K) + K‖ := by rw [sub_add_cancel]
        _ ≤ ‖G - K‖ + ‖K‖ := norm_add_le _ _
    have hm := mul_le_mul_of_nonneg_left hnorm hwz
    nlinarith
  have hnorm : ‖a * (F * G) - H * K‖ ≤
      ‖a * F - H‖ * ‖G‖ + ‖H‖ * ‖G - K‖ := by
    calc
      ‖a * (F * G) - H * K‖ = ‖(a * F - H) * G + H * (G - K)‖ := by
        congr 1
        ring
      _ ≤ ‖(a * F - H) * G‖ + ‖H * (G - K)‖ := norm_add_le _ _
      _ = ‖a * F - H‖ * ‖G‖ + ‖H‖ * ‖G - K‖ := by rw [norm_mul, norm_mul]
  calc
    w * ‖a * (F * G) - H * K‖ ≤
        (wy * wz) * (‖a * F - H‖ * ‖G‖ + ‖H‖ * ‖G - K‖) :=
      mul_le_mul hwbound hnorm (norm_nonneg _) (mul_nonneg hwy hwz)
    _ = (wy * ‖a * F - H‖) * (wz * ‖G‖) +
        (wy * ‖H‖) * (wz * ‖G - K‖) := by ring
    _ ≤ ε * (B + e) + B * e := add_le_add
      (mul_le_mul hactive hGnorm (mul_nonneg hwz (norm_nonneg _)) hε)
      (mul_le_mul hH hcutoff (mul_nonneg hwz (norm_nonneg _)) hB)

#print axioms weighted_gaussian_uniform
#print axioms finite_error_budget
#print axioms weighted_product_error
end ConvexGaussian
end Bandlimited
end
