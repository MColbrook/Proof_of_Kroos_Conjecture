module

public import Bandlimited.Definitions
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Weighted tensor approximation

This file develops the tensor-product density argument in Lemma 2.2.
The manuscript is not imported as an assumption. In particular, no axiom or
unproved declaration is used to assert the tensor-density conclusion.
-/

@[expose] public section

open scoped BigOperators
open Set

noncomputable section
namespace Bandlimited
namespace TensorDensity

def scalarLine (t : ℝ) : E 1 := PiLp.single 2 0 t

@[simp] theorem scalarLine_apply (t : ℝ) (i : Fin 1) : scalarLine t i = t := by
  fin_cases i
  simp [scalarLine]

@[simp] theorem norm_scalarLine (t : ℝ) : ‖scalarLine t‖ = |t| := by
  simp [scalarLine, PiLp.norm_single, Real.norm_eq_abs]

@[simp] theorem scalarLine_coord (x : E 1) : scalarLine (x 0) = x := by
  ext i
  fin_cases i
  simp

theorem continuous_scalarLine : Continuous scalarLine := by
  have h : scalarLine = fun t => WithLp.toLp 2 (fun _ : Fin 1 => t) := by
    funext t
    ext i
    exact scalarLine_apply t i
  rw [h]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp
    (continuous_pi fun _ : Fin 1 => continuous_id)

theorem weightedC0_to_scalar {W : ℝ → ℝ} {H : E 1 → ℂ}
    (hH : WeightedC0 (fun x => W (x 0)) H) :
    ScalarWeightedC0 W (fun t => H (scalarLine t)) := by
  refine ⟨hH.1.comp continuous_scalarLine, ?_, ?_⟩
  · simpa only [Function.comp_def, scalarLine_apply] using
      hH.2.1.comp continuous_scalarLine
  · intro ε hε
    obtain ⟨R, hR, htail⟩ := hH.2.2 ε hε
    refine ⟨R, hR, ?_⟩
    intro t ht
    simpa only [scalarLine_apply] using
      htail (scalarLine t) (by simpa only [norm_scalarLine] using ht)

/- This is the complete one-factor instance of T09. The general finite-dimensional theorem is proved below. -/
theorem tensor_density_one
    (W : Fin 1 → ℝ → ℝ)
    (D : Fin 1 → Set (ℝ → ℂ))
    (hD : ∀ i, ScalarWeightedDense (W i) (D i))
    (H : E 1 → ℂ)
    (hH : WeightedC0 (fun x => ∏ i : Fin 1, W i (x i)) H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∃ F : Fin m → Fin 1 → ℝ → ℂ,
      (∀ j i, F j i ∈ D i) ∧
      WeightedErrorLT (fun x => ∏ i : Fin 1, W i (x i))
        (fun x => ∑ j : Fin m, ∏ i : Fin 1, F j i (x i)) H ε := by
  have hH' : WeightedC0 (fun x : E 1 => W 0 (x 0)) H := by
    simpa only [Fin.prod_univ_one] using hH
  obtain ⟨F, hFD, b, hb, hF⟩ :=
    (hD 0).2 (fun t => H (scalarLine t)) (weightedC0_to_scalar hH') ε hε
  refine ⟨1, (fun _ _ => F), ?_, b, hb, ?_⟩
  · intro j i
    fin_cases i
    exact hFD
  · intro x
    simpa only [Fin.prod_univ_one, Fin.sum_univ_one, scalarLine_coord] using hF (x 0)

/- A finite scalar partition supplies the rectangular approximation of an
arbitrary C₀ target. The factors have compact support and their sum is globally
at most one, as required to control the error outside the truncation box. -/
theorem finite_interval_partition (R δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ v : Fin m → ℝ,
      (∀ j, v j ∈ Icc (-R) R) ∧
      ∃ f : PartitionOfUnity (Fin m) ℝ (Icc (-R) R),
        f.IsSubordinate (fun j => Metric.ball (v j) δ) ∧
        ∀ j, HasCompactSupport (f j) := by
  classical
  have hcover : Icc (-R) R ⊆
      ⋃ t : ↥(Icc (-R) R), Metric.ball (t : ℝ) δ := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, by simpa using hδ⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : ↥(Icc (-R) R) => Metric.ball (t : ℝ) δ)
    (fun _ => Metric.isOpen_ball) hcover
  let m : ℕ := s.card
  let v : Fin m → ℝ := fun j => ((s.equivFin.symm j).val : ℝ)
  have hvc (j : Fin m) : v j ∈ Icc (-R) R :=
    (s.equivFin.symm j).val.property
  have hvcover : Icc (-R) R ⊆ ⋃ j : Fin m, Metric.ball (v j) δ := by
    intro t ht
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hs ht)
    obtain ⟨has, hball⟩ := mem_iUnion.mp ha
    refine mem_iUnion.mpr ⟨s.equivFin ⟨a, has⟩, ?_⟩
    simpa only [v, Equiv.symm_apply_apply] using hball
  obtain ⟨f, hf, hcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    isCompact_Icc (fun j : Fin m => Metric.ball (v j) δ)
    (fun _ => Metric.isOpen_ball) (locallyFinite_of_finite _) hvcover
  exact ⟨m, v, hvc, f, hf, hcp⟩

theorem vanishesAtInfinity_tendsto {d : ℕ} {G : E d → ℂ}
    (hG : VanishesAtInfinity G) :
    Filter.Tendsto G (Filter.cocompact (E d)) (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR, htail⟩ := hG.2 ε hε
  filter_upwards [(tendsto_norm_cocompact_atTop (E := E d)).eventually
    (Filter.eventually_ge_atTop R)] with x hx
  simpa only [dist_zero_right] using htail x hx

theorem vanishesAtInfinity_uniformContinuous {d : ℕ} {G : E d → ℂ}
    (hG : VanishesAtInfinity G) : UniformContinuous G :=
  hG.1.uniformContinuous_of_tendsto_cocompact (vanishesAtInfinity_tendsto hG)

theorem norm_prod_le_pow {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {M : ℝ} (_hM : 0 ≤ M) (hf : ∀ i ∈ s, ‖f i‖ ≤ M) :
    ‖∏ i ∈ s, f i‖ ≤ M ^ s.card := by
  calc
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := Finset.norm_prod_le s f
    _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hf
    _ = M ^ s.card := by simp

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) (hg : ∀ i ∈ s, ‖g i‖ ≤ M)
    (herr : ∀ i ∈ s, ‖f i - g i‖ ≤ δ) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ (s.card : ℝ) * δ * M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hM0 : 0 ≤ M := by linarith
    have hf' : ∀ i ∈ s, ‖f i‖ ≤ M := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, ‖g i‖ ≤ M := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have herr' : ∀ i ∈ s, ‖f i - g i‖ ≤ δ :=
      fun i hi => herr i (Finset.mem_insert_of_mem hi)
    have hb := ih hf' hg' herr'
    have hp := norm_prod_le_pow s f hM0 hf'
    have hi : ‖f a - g a‖ ≤ δ := herr a (Finset.mem_insert_self _ _)
    have hgi : ‖g a‖ ≤ M := hg a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      ‖f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ =
          ‖(f a - g a) * (∏ i ∈ s, f i) +
            g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := by congr 1; ring
      _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
          ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ = ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ +
          ‖g a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := by rw [norm_mul, norm_mul]
      _ ≤ δ * M ^ s.card + M * ((s.card : ℝ) * δ * M ^ s.card) := by
        apply add_le_add
        · exact mul_le_mul hi hp (norm_nonneg _) hδ
        · exact mul_le_mul hgi hb (norm_nonneg _) hM0
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * δ * M ^ (s.card + 1) := by
        have hstep : δ * M ^ s.card ≤ M * (δ * M ^ s.card) := by
          exact le_mul_of_one_le_left (mul_nonneg hδ (pow_nonneg hM0 _)) hM
        push_cast
        rw [pow_succ]
        nlinarith

theorem norm_le_sum_abs {r : ℕ} (x : E r) : ‖x‖ ≤ ∑ i : Fin r, |x i| := by
  have hx : (∑ i : Fin r, PiLp.single 2 i (x i)) = x := by
    ext j
    simp
  calc
    ‖x‖ = ‖∑ i : Fin r, PiLp.single 2 i (x i)‖ := congrArg norm hx.symm
    _ ≤ ∑ i : Fin r, ‖(PiLp.single 2 i (x i) : E r)‖ := norm_sum_le _ _
    _ = ∑ i : Fin r, |x i| := by simp [PiLp.norm_single, Real.norm_eq_abs]

theorem subconvex_sum_error {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (c : ι → ℂ) (z : ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i ≤ 1)
    (hnear : ∀ i ∈ s, q i ≠ 0 → ‖c i - z‖ ≤ η)
    (hsmall : (∑ i ∈ s, q i) ≠ 1 → ‖z‖ ≤ η) :
    ‖(∑ i ∈ s, (q i : ℂ) * c i) - z‖ ≤ 2 * η := by
  classical
  have hsum0 : 0 ≤ ∑ i ∈ s, q i := Finset.sum_nonneg hq
  have hfirst : ‖∑ i ∈ s, (q i : ℂ) * (c i - z)‖ ≤ η := by
    calc
      ‖∑ i ∈ s, (q i : ℂ) * (c i - z)‖ ≤
          ∑ i ∈ s, ‖(q i : ℂ) * (c i - z)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, q i * ‖c i - z‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq i hi)]
      _ ≤ ∑ i ∈ s, q i * η := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hqi : q i = 0
        · simp [hqi]
        · exact mul_le_mul_of_nonneg_left (hnear i hi hqi) (hq i hi)
      _ = (∑ i ∈ s, q i) * η := (Finset.sum_mul ..).symm
      _ ≤ η := by nlinarith
  have hsecond : ‖(((∑ i ∈ s, q i : ℝ) : ℂ) - 1) * z‖ ≤ η := by
    by_cases hsum : (∑ i ∈ s, q i) = 1
    · simp [hsum, hη]
    · rw [norm_mul]
      have hnorm : ‖((∑ i ∈ s, q i : ℝ) : ℂ) - 1‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      calc
        ‖((∑ i ∈ s, q i : ℝ) : ℂ) - 1‖ * ‖z‖ ≤ 1 * η :=
          mul_le_mul hnorm (hsmall hsum) (norm_nonneg _) (by norm_num)
        _ = η := one_mul _
  have hid : (∑ i ∈ s, (q i : ℂ) * c i) - z =
      (∑ i ∈ s, (q i : ℂ) * (c i - z)) +
        (((∑ i ∈ s, q i : ℝ) : ℂ) - 1) * z := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    push_cast
    ring
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

def rectangularWeight {r m : ℕ} (f : Fin m → ℝ → ℝ)
    (x : E r) (j : Fin r → Fin m) : ℝ := ∏ i, f (j i) (x i)

theorem sum_rectangularWeight {r m : ℕ} (f : Fin m → ℝ → ℝ) (x : E r) :
    ∑ j : Fin r → Fin m, rectangularWeight f x j =
      ∏ i : Fin r, ∑ k : Fin m, f k (x i) := by
  classical
  simp only [rectangularWeight, Fintype.prod_sum]

def rectangularNode {r m : ℕ} (v : Fin m → ℝ) (j : Fin r → Fin m) : E r :=
  WithLp.toLp 2 (fun i => v (j i))

@[simp] theorem rectangularNode_apply {r m : ℕ} (v : Fin m → ℝ)
    (j : Fin r → Fin m) (i : Fin r) : rectangularNode v j i = v (j i) := rfl

theorem rectangular_approximation {r : ℕ} (G : E r → ℂ)
    (hG : VanishesAtInfinity G) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∃ m : ℕ, ∃ v : Fin m → ℝ,
      ∃ f : PartitionOfUnity (Fin m) ℝ (Icc (-R) R),
        (∀ j, HasCompactSupport (f j)) ∧
        ∀ x : E r,
          ‖(∑ j : Fin r → Fin m,
            (rectangularWeight (fun k => f k) x j : ℂ) * G (rectangularNode v j)) - G x‖
            ≤ ε / 2 := by
  classical
  obtain ⟨R, hR, htail⟩ := hG.2 (ε / 4) (by positivity)
  obtain ⟨κ, hκ, huc⟩ := Metric.uniformContinuous_iff.mp
    (vanishesAtInfinity_uniformContinuous hG) (ε / 4) (by positivity)
  let δ : ℝ := κ / ((r : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδκ : (r : ℝ) * δ < κ := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mpr
    nlinarith
  obtain ⟨m, v, hv, f, hsub, hcp⟩ := finite_interval_partition R δ hδ
  have hsum_le (t : ℝ) : (∑ k : Fin m, f k t) ≤ 1 := by
    simpa only [finsum_eq_sum_of_fintype] using f.sum_le_one t
  have hsum_eq (t : ℝ) (ht : t ∈ Icc (-R) R) : (∑ k : Fin m, f k t) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one ht
  have hq0 (x : E r) (j : Fin r → Fin m) :
      0 ≤ rectangularWeight (fun k => f k) x j :=
    Finset.prod_nonneg fun i _ => f.nonneg (j i) (x i)
  have hqsum (x : E r) :
      (∑ j : Fin r → Fin m, rectangularWeight (fun k => f k) x j) ≤ 1 := by
    rw [sum_rectangularWeight]
    calc
      (∏ i : Fin r, ∑ k : Fin m, f k (x i)) ≤ ∏ _i : Fin r, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => f.nonneg k (x i))
          (fun i _ => hsum_le (x i))
      _ = 1 := by simp
  have hqsum_eq (x : E r) (hx : ∀ i, x i ∈ Icc (-R) R) :
      (∑ j : Fin r → Fin m, rectangularWeight (fun k => f k) x j) = 1 := by
    rw [sum_rectangularWeight]
    apply Finset.prod_eq_one
    intro i hi
    exact hsum_eq (x i) (hx i)
  refine ⟨R, m, v, f, hcp, ?_⟩
  intro x
  have hnear (j : Fin r → Fin m)
      (hj : rectangularWeight (fun k => f k) x j ≠ 0) :
      ‖G (rectangularNode v j) - G x‖ ≤ ε / 4 := by
    have hcoord (i : Fin r) : |x i - v (j i)| ≤ δ := by
      have hi : f (j i) (x i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hj i (Finset.mem_univ _)
      have hsupp : x i ∈ tsupport (f (j i)) := subset_closure hi
      exact (show |x i - v (j i)| < δ by simpa only [Metric.mem_ball, Real.dist_eq] using hsub (j i) hsupp).le
    have hdist : dist x (rectangularNode v j) < κ := by
      rw [dist_eq_norm]
      calc
        ‖x - rectangularNode v j‖ ≤ ∑ i : Fin r, |(x - rectangularNode v j) i| :=
          norm_le_sum_abs _
        _ ≤ ∑ _i : Fin r, δ := Finset.sum_le_sum fun i _ => by simpa using hcoord i
        _ = (r : ℝ) * δ := by simp
        _ < κ := hδκ
    have hclose := huc hdist
    simpa only [dist_eq_norm, norm_sub_rev] using hclose.le
  have hsmall
      (hne : (∑ j : Fin r → Fin m, rectangularWeight (fun k => f k) x j) ≠ 1) :
      ‖G x‖ ≤ ε / 4 := by
    apply (htail x ?_).le
    by_contra hnorm
    have hnorm' : ‖x‖ < R := lt_of_not_ge hnorm
    apply hne
    apply hqsum_eq
    intro i
    apply abs_le.mp
    exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p := 2) x i).trans
      hnorm'.le
  have hb := subconvex_sum_error Finset.univ
    (rectangularWeight (fun k => f k) x)
    (fun j => G (rectangularNode v j)) (G x) (by positivity : 0 ≤ ε / 4)
    (fun j _ => hq0 x j) (hqsum x) (fun j _ hj => hnear j hj) hsmall
  convert hb using 1; ring

theorem scalarWeightedC0_of_compactFactor
    (W : ℝ → ℝ) (hW : Continuous W) (hWpos : ∀ t, 0 < W t)
    (f : C(ℝ, ℝ)) (hcp : HasCompactSupport f) (c : ℂ) :
    ScalarWeightedC0 W (fun t => c * (f t : ℂ) / (W t : ℂ)) := by
  have hWne (t : ℝ) : (W t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (hWpos t))
  have heq (t : ℝ) : (W t : ℂ) * (c * (f t : ℂ) / (W t : ℂ)) = c * (f t : ℂ) := by
    field_simp [hWne t]
  refine ⟨(continuous_const.mul (Complex.continuous_ofReal.comp f.continuous)).div
    (Complex.continuous_ofReal.comp hW) hWne, ?_, ?_⟩
  · have hg : Continuous (fun t : ℝ => c * (f t : ℂ)) := by fun_prop
    simpa only [heq] using hg
  · intro ε hε
    obtain ⟨R, hR, htail⟩ := hcp.exists_pos_le_norm
    refine ⟨R, hR.le, ?_⟩
    intro t ht
    rw [heq, htail t (by simpa only [Real.norm_eq_abs] using ht)]
    simpa using hε

theorem weighted_error_identity {w : ℝ} (hw : 0 ≤ w) (F H : ℂ) :
    w * ‖F - H‖ = ‖(w : ℂ) * F - (w : ℂ) * H‖ := by
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]

theorem product_weight_sum_identity {r : ℕ} {ι : Type*} (s : Finset ι)
    (W : Fin r → ℝ) (F : ι → Fin r → ℂ) :
    ((∏ i, W i : ℝ) : ℂ) * (∑ j ∈ s, ∏ i, F j i) =
      ∑ j ∈ s, ∏ i, ((W i : ℂ) * F j i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_mul_distrib]
  simp

theorem approximate_finite_tensor_sum {r : ℕ} {J : Type*} [Fintype J]
    (W : Fin r → ℝ → ℝ) (hWpos : ∀ i t, 0 < W i t)
    (D : Fin r → Set (ℝ → ℂ)) (hD : ∀ i, ScalarWeightedDense (W i) (D i))
    (a : J → Fin r → ℝ → ℂ)
    (ha : ∀ j i, ScalarWeightedC0 (W i) (fun t => a j i t / (W i t : ℂ)))
    (B : ℝ) (hB : 1 ≤ B) (hbound : ∀ j i t, ‖a j i t‖ ≤ B)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : J → Fin r → ℝ → ℂ, (∀ j i, F j i ∈ D i) ∧
      ∀ x : E r,
        ‖(∑ j : J, ∏ i : Fin r, ((W i (x i) : ℂ) * F j i (x i))) -
          ∑ j : J, ∏ i : Fin r, a j i (x i)‖ ≤ η := by
  classical
  let M : ℝ := B + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := by linarith
  let K : ℝ := (Fintype.card J : ℝ) * (r : ℝ) * M ^ r + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min 1 (η / K)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη hK)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ η := (le_div_iff₀ hK).mp (min_le_right 1 (η / K))
  have hex (j : J) (i : Fin r) : ∃ F ∈ D i, ∃ b : ℝ, b < δ ∧
      ∀ t, W i t * ‖F t - a j i t / (W i t : ℂ)‖ ≤ b :=
    (hD i).2 _ (ha j i) δ hδ
  choose F hmem b hb herr using hex
  let Q (j : J) (i : Fin r) (t : ℝ) : ℂ := (W i t : ℂ) * F j i t
  have herror (j : J) (i : Fin r) (t : ℝ) : ‖Q j i t - a j i t‖ ≤ δ := by
    have hne : (W i t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hWpos i t))
    have hid : (W i t : ℂ) * (a j i t / (W i t : ℂ)) = a j i t := by field_simp [hne]
    have h := herr j i t
    rw [weighted_error_identity (hWpos i t).le] at h
    have h' : ‖Q j i t - a j i t‖ ≤ b j i := by simpa only [Q, hid] using h
    exact h'.trans (hb j i).le
  have hQbound (j : J) (i : Fin r) (t : ℝ) : ‖Q j i t‖ ≤ M := by
    calc
      ‖Q j i t‖ = ‖(Q j i t - a j i t) + a j i t‖ := by congr 1; ring
      _ ≤ ‖Q j i t - a j i t‖ + ‖a j i t‖ := norm_add_le _ _
      _ ≤ δ + B := add_le_add (herror j i t) (hbound j i t)
      _ ≤ M := by dsimp [M]; linarith
  have hprod (x : E r) (j : J) :
      ‖(∏ i : Fin r, Q j i (x i)) - ∏ i : Fin r, a j i (x i)‖ ≤
        (r : ℝ) * δ * M ^ r := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      norm_prod_sub_prod_le Finset.univ (fun i : Fin r => Q j i (x i))
        (fun i : Fin r => a j i (x i)) hM hδ.le
        (fun i _ => hQbound j i (x i))
        (fun i _ => (hbound j i (x i)).trans (by dsimp [M]; linarith))
        (fun i _ => herror j i (x i))
  refine ⟨F, hmem, ?_⟩
  intro x
  change ‖(∑ j : J, ∏ i : Fin r, Q j i (x i)) -
      ∑ j : J, ∏ i : Fin r, a j i (x i)‖ ≤ η
  calc
    _ = ‖∑ j : J, ((∏ i : Fin r, Q j i (x i)) - ∏ i : Fin r, a j i (x i))‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : J, ‖(∏ i : Fin r, Q j i (x i)) - ∏ i : Fin r, a j i (x i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : J, (r : ℝ) * δ * M ^ r := Finset.sum_le_sum fun j _ => hprod x j
    _ = ((Fintype.card J : ℝ) * (r : ℝ) * M ^ r) * δ := by simp; ring
    _ ≤ K * δ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hδ.le
    _ = δ * K := mul_comm _ _
    _ ≤ η := hδK

end TensorDensity
open TensorDensity in
 theorem tensor_density : TensorDensityStatement := by
  classical
  intro r hr W hW hWpos D hD H hH ε hε
  let i₀ : Fin r := ⟨0, by omega⟩
  let w (x : E r) : ℝ := ∏ i : Fin r, W i (x i)
  let G (x : E r) : ℂ := (w x : ℂ) * H x
  have hG : VanishesAtInfinity G := hH.2
  obtain ⟨R, m, v, f, hcp, hrect⟩ := rectangular_approximation G hG (ε / 2) (by positivity)
  let J := Fin r → Fin m
  let c (j : J) (i : Fin r) : ℂ := if i = i₀ then G (rectangularNode v j) else 1
  let a (j : J) (i : Fin r) (t : ℝ) : ℂ := c j i * (f (j i) t : ℂ)
  let B : ℝ := 1 + ∑ j : J, ‖G (rectangularNode v j)‖
  have hB : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hc (j : J) (i : Fin r) : ‖c j i‖ ≤ B := by
    dsimp [c]
    split_ifs with hi
    · have hle : ‖G (rectangularNode v j)‖ ≤ ∑ k : J, ‖G (rectangularNode v k)‖ :=
        Finset.single_le_sum (fun k _ => norm_nonneg (G (rectangularNode v k))) (Finset.mem_univ j)
      dsimp [B]
      linarith
    · simpa only [norm_one] using hB
  have ha_bound (j : J) (i : Fin r) (t : ℝ) : ‖a j i t‖ ≤ B := by
    dsimp [a]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (f.nonneg (j i) t)]
    simpa only [mul_one] using
      mul_le_mul (hc j i) (f.le_one (j i) t) (f.nonneg (j i) t) (by linarith : 0 ≤ B)
  have ha (j : J) (i : Fin r) :
      ScalarWeightedC0 (W i) (fun t => a j i t / (W i t : ℂ)) :=
    scalarWeightedC0_of_compactFactor (W i) (hW i) (hWpos i) (f (j i)) (hcp (j i)) (c j i)
  obtain ⟨F, hmem, htransfer⟩ := approximate_finite_tensor_sum W hWpos D hD a ha B hB
    ha_bound (ε / 4) (by positivity)
  have hcprod (j : J) : (∏ i : Fin r, c j i) = G (rectangularNode v j) := by
    simp [c]
  have haprod (x : E r) (j : J) :
      (∏ i : Fin r, a j i (x i)) =
        (rectangularWeight (fun k => f k) x j : ℂ) * G (rectangularNode v j) := by
    dsimp [a]
    rw [Finset.prod_mul_distrib, hcprod]
    dsimp [rectangularWeight]
    push_cast
    ring
  have hasum (x : E r) :
      (∑ j : J, ∏ i : Fin r, a j i (x i)) =
        ∑ j : J, (rectangularWeight (fun k => f k) x j : ℂ) * G (rectangularNode v j) :=
    Finset.sum_congr rfl fun j _ => haprod x j
  have hrect' (x : E r) : ‖(∑ j : J, ∏ i : Fin r, a j i (x i)) - G x‖ ≤ ε / 4 := by
    rw [hasum]
    convert hrect x using 1; ring
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, (fun j i => F (e.symm j) i), (fun j i => hmem _ _), ?_⟩
  refine ⟨ε / 2, by linarith, ?_⟩
  intro x
  have hw : 0 ≤ ∏ i : Fin r, W i (x i) :=
    Finset.prod_nonneg fun i _ => (hWpos i (x i)).le
  rw [weighted_error_identity hw]
  change ‖(w x : ℂ) * (∑ j : Fin (Fintype.card J), ∏ i : Fin r, F (e.symm j) i (x i)) - G x‖ ≤ ε / 2
  have hreindex :
      (∑ j : Fin (Fintype.card J), ∏ i : Fin r, F (e.symm j) i (x i)) =
        ∑ j : J, ∏ i : Fin r, F j i (x i) :=
    Equiv.sum_comp e.symm (fun j : J => ∏ i : Fin r, F j i (x i))
  rw [hreindex]
  rw [product_weight_sum_identity]
  calc
    ‖(∑ j : J, ∏ i : Fin r, ((W i (x i) : ℂ) * F j i (x i))) - G x‖ ≤
        ‖(∑ j : J, ∏ i : Fin r, ((W i (x i) : ℂ) * F j i (x i))) -
          ∑ j : J, ∏ i : Fin r, a j i (x i)‖ +
        ‖(∑ j : J, ∏ i : Fin r, a j i (x i)) - G x‖ := by
          simpa only [dist_eq_norm] using
            dist_triangle
              (∑ j : J, ∏ i : Fin r, ((W i (x i) : ℂ) * F j i (x i)))
              (∑ j : J, ∏ i : Fin r, a j i (x i)) (G x)
    _ ≤ ε / 4 + ε / 4 := add_le_add (htransfer x) (hrect' x)
    _ = ε / 2 := by ring

#print axioms tensor_density

end Bandlimited

end
