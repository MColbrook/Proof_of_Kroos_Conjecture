module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
The finite-sum estimates in Section 5. Analytic construction of the summands
and quadrature is an explicit hypothesis, not a conclusion of this module.
Reuses Mathlib's ordered finite sums and field algebra (Apache 2.0).
-/

@[expose] public section
open scoped BigOperators

namespace Bandlimited

theorem weighted_sum_error {ι : Type*} (s : Finset ι)
    (w r g t : ι → ℝ) (I J ε ζ : ℝ)
    (hI : 0 < I) (hε : 0 ≤ ε)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (herr : ∀ i ∈ s, |r i - g i| ≤ ε * t i)
    (hquad : |(∑ i ∈ s, w i * g i) - I| ≤ ζ * I)
    (htail : (∑ i ∈ s, w i * t i) ≤ 2 * J) :
    |I⁻¹ * (∑ i ∈ s, w i * r i) - 1| ≤ ζ + ε * (2 * J / I) := by
  have hlocal : |∑ i ∈ s, w i * (r i - g i)| ≤
      ε * (∑ i ∈ s, w i * t i) := by
    calc
      |∑ i ∈ s, w i * (r i - g i)| ≤
          ∑ i ∈ s, |w i * (r i - g i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, w i * |r i - g i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw i hi)]
      _ ≤ ∑ i ∈ s, w i * (ε * t i) := by
        exact Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (herr i hi) (hw i hi))
      _ = ε * (∑ i ∈ s, w i * t i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hdecomp : (∑ i ∈ s, w i * r i) - I =
      (∑ i ∈ s, w i * (r i - g i)) + ((∑ i ∈ s, w i * g i) - I) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have htotal : |(∑ i ∈ s, w i * r i) - I| ≤ ζ * I + ε * (2 * J) := by
    calc
      |(∑ i ∈ s, w i * r i) - I| =
          |(∑ i ∈ s, w i * (r i - g i)) + ((∑ i ∈ s, w i * g i) - I)| :=
        congrArg abs hdecomp
      _ ≤ |∑ i ∈ s, w i * (r i - g i)| + |(∑ i ∈ s, w i * g i) - I| :=
        abs_add_le _ _
      _ ≤ ε * (∑ i ∈ s, w i * t i) + ζ * I := add_le_add hlocal hquad
      _ ≤ ε * (2 * J) + ζ * I := by
        have hmul := mul_le_mul_of_nonneg_left htail hε
        linarith
      _ = ζ * I + ε * (2 * J) := by ring
  have hnormalize : I⁻¹ * (∑ i ∈ s, w i * r i) - 1 =
      ((∑ i ∈ s, w i * r i) - I) / I := by
    field_simp
  rw [hnormalize, abs_div, abs_of_pos hI]
  apply (div_le_iff₀ hI).2
  calc
    |(∑ i ∈ s, w i * r i) - I| ≤ ζ * I + ε * (2 * J) := htotal
    _ = (ζ + ε * (2 * J / I)) * I := by
      field_simp

theorem error_budget (ζ ε B η : ℝ)
    (hB : 0 < B) (hζ : ζ < η / 2) (hε : ε < η / (2 * B)) :
    ζ + ε * B < η := by
  have hmul : ε * B < η / 2 := by
    apply (lt_div_iff₀ hB).1
    convert hε using 1 <;> field_simp <;> ring
  linarith

theorem polynomial_sum_error {ι : Type*} (s : Finset ι) (p h : ι → ℝ) :
    |(∑ i ∈ s, p i * h i) - ∑ i ∈ s, p i| ≤
      ∑ i ∈ s, |p i| * |h i - 1| := by
  calc
    |(∑ i ∈ s, p i * h i) - ∑ i ∈ s, p i| =
        |∑ i ∈ s, p i * (h i - 1)| := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |p i * (h i - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |p i| * |h i - 1| := by
      simp only [abs_mul]

end Bandlimited
