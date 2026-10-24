module

public import Bandlimited.MainReductions
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Polynomial density on the boundary and homogeneous degree lifting.
Reuses Mathlib's real Stone–Weierstrass theorem and the homogeneous
component decomposition (Apache 2.0). -/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace Bandlimited

def boundaryCoordinate {d : ℕ} (K : Set (E d)) (i : Fin d) :
    C(↥(frontier K), ℝ) where
  toFun x := (x : E d) i
  continuous_toFun := (EuclideanSpace.proj i).continuous.comp continuous_subtype_val

def boundaryPolynomialHom {d : ℕ} (K : Set (E d)) :
    Polynomial d →ₐ[ℝ] C(↥(frontier K), ℝ) :=
  MvPolynomial.aeval (boundaryCoordinate K)

@[simp] theorem boundaryPolynomialHom_apply {d : ℕ} (K : Set (E d))
    (p : Polynomial d) (x : ↥(frontier K)) :
    boundaryPolynomialHom K p x = evalPolynomial p (x : E d) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [boundaryPolynomialHom, evalPolynomial]
  | add p q hp hq => simp [map_add, hp, hq, evalPolynomial]
  | mul_X p i hp =>
      rw [map_mul, ContinuousMap.mul_apply, hp]
      have hX : boundaryPolynomialHom K (MvPolynomial.X i) x = (x : E d) i := by
        simp only [boundaryPolynomialHom, MvPolynomial.aeval_X]
        rfl
      rw [hX]
      simp [evalPolynomial]

theorem boundary_polynomial_separates {d : ℕ} (K : Set (E d)) :
    (boundaryPolynomialHom K).range.SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i : Fin d, (x : E d) i ≠ (y : E d) i := by
    by_contra h
    push Not at h
    apply hxy
    apply Subtype.ext
    ext i
    exact h i
  refine ⟨boundaryPolynomialHom K (MvPolynomial.X i),
    ⟨boundaryPolynomialHom K (MvPolynomial.X i), ⟨MvPolynomial.X i, rfl⟩, rfl⟩, ?_⟩
  simpa [evalPolynomial] using hi

theorem boundary_polynomial_approximation {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (f : C(↥(frontier K), ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial d, BoundaryErrorLT K p f ε := by
  have hc : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier (by
    intro x hx
    have hxcl : x ∈ closure K := frontier_subset_closure hx
    simpa only [hK.isClosed.closure_eq] using hxcl)
  let : CompactSpace ↥(frontier K) := isCompact_iff_compactSpace.mp hc
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (boundaryPolynomialHom K).range (boundary_polynomial_separates K) f ε hε
  obtain ⟨p, hp⟩ := g.property
  refine ⟨p, ‖(g : C(↥(frontier K), ℝ)) - f‖, hg, ?_⟩
  intro x
  have hx := ContinuousMap.norm_coe_le_norm ((g : C(↥(frontier K), ℝ)) - f) x
  have hxv : (g : C(↥(frontier K), ℝ)) x = evalPolynomial p (x : E d) := by
    calc
      (g : C(↥(frontier K), ℝ)) x = boundaryPolynomialHom K p x :=
        congrArg (fun g : C(↥(frontier K), ℝ) => g x) hp.symm
      _ = evalPolynomial p (x : E d) := boundaryPolynomialHom_apply K p x
  simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, hxv] using hx

/-- Scaling all variables of a homogeneous polynomial scales its value by the
corresponding power. This uses the exact monomial support definition. -/
theorem eval_homogeneous_scale {d k : ℕ} {p : Polynomial d}
    (hp : p.IsHomogeneous k) (a : ℝ) (x : Fin d → ℝ) :
    MvPolynomial.eval (fun i => a * x i) p = a ^ k * MvPolynomial.eval x p := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, MvPolynomial.eval_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd := hp.degree_eq_sum_deg_support hm
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hd]
  ring

#print axioms eval_homogeneous_scale

def parityComponent {d : ℕ} (p : Polynomial d) (e m : ℕ) : Polynomial d :=
  if m % 2 = e then MvPolynomial.homogeneousComponent m p else 0

def parityPolynomial {d : ℕ} (p : Polynomial d) (e : ℕ) : Polynomial d :=
  ∑ m ∈ Finset.range (p.totalDegree + 1), parityComponent p e m

theorem parityComponent_homogeneous {d : ℕ} (p : Polynomial d)
    (e m : ℕ) (_he : e ≤ 1) :
    (parityComponent p e m).IsHomogeneous (2 * (m / 2) + e) := by
  classical
  unfold parityComponent
  split_ifs with hm
  · convert MvPolynomial.homogeneousComponent_isHomogeneous m p using 1
    omega
  · exact MvPolynomial.isHomogeneous_zero (Fin d) ℝ _

theorem eval_homogeneous_neg {d k : ℕ} {p : Polynomial d}
    (hp : p.IsHomogeneous k) (x : E d) :
    evalPolynomial p (-x) = (-1 : ℝ) ^ k * evalPolynomial p x := by
  simpa only [evalPolynomial, neg_one_mul, PiLp.neg_apply] using
    eval_homogeneous_scale hp (-1) (fun i => x i)

theorem parityComponent_eval {d : ℕ} (p : Polynomial d)
    (e m : ℕ) (he : e ≤ 1) (x : E d) :
    evalPolynomial (parityComponent p e m) x =
      (evalPolynomial (MvPolynomial.homogeneousComponent m p) x +
        (-1 : ℝ) ^ e * evalPolynomial (MvPolynomial.homogeneousComponent m p) (-x)) / 2 := by
  classical
  have hn := eval_homogeneous_neg
    (MvPolynomial.homogeneousComponent_isHomogeneous m p) x
  have hzero : evalPolynomial (0 : Polynomial d) x = 0 := by simp [evalPolynomial]
  rcases Nat.even_or_odd m with hm | hm
  · have hmod : m % 2 = 0 := by rcases hm with ⟨k, hk⟩; omega
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp [parityComponent, hmod, hn, hm.neg_one_pow, hzero]
  · have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp [parityComponent, hmod, hn, hm.neg_one_pow, hzero]

theorem parityPolynomial_eval {d : ℕ} (p : Polynomial d)
    (e : ℕ) (he : e ≤ 1) (x : E d) :
    evalPolynomial (parityPolynomial p e) x =
      (evalPolynomial p x + (-1 : ℝ) ^ e * evalPolynomial p (-x)) / 2 := by
  classical
  have hex (y : E d) :
      (∑ m ∈ Finset.range (p.totalDegree + 1),
        evalPolynomial (MvPolynomial.homogeneousComponent m p) y) = evalPolynomial p y := by
    simpa only [evalPolynomial, map_sum] using
      congrArg (fun q => evalPolynomial q y) (MvPolynomial.sum_homogeneousComponent p)
  simp only [parityPolynomial, evalPolynomial, map_sum]
  change (∑ m ∈ Finset.range (p.totalDegree + 1), evalPolynomial (parityComponent p e m) x) = _
  simp_rw [parityComponent_eval p e _ he x]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hex x, hex (-x)]
  rfl

#print axioms parityComponent_homogeneous
#print axioms parityComponent_eval
#print axioms parityPolynomial_eval

def parityLift {d : ℕ} (p : Polynomial d) (e : ℕ)
    (h : ℕ → Polynomial d) (n : ℕ) : Polynomial d :=
  ∑ m ∈ Finset.range (p.totalDegree + 1), parityComponent p e m * h (n - m / 2)

theorem parityLift_homogeneous {d : ℕ} (p : Polynomial d) (e : ℕ)
    (he : e ≤ 1) (h : ℕ → Polynomial d)
    (hh : ∀ n, (h n).IsHomogeneous (2 * n))
    (n : ℕ) (hn : p.totalDegree ≤ n) :
    (parityLift p e h n).IsHomogeneous (2 * n + e) := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro m hm
  have hm' : m ≤ p.totalDegree := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  have hhom := (parityComponent_homogeneous p e m he).mul (hh (n - m / 2))
  convert hhom using 1
  omega

theorem boundary_sequence_tendsto {d : ℕ} {K : Set (E d)}
    [CompactSpace ↥(frontier K)] (h : ℕ → Polynomial d)
    (hh : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      BoundaryErrorLT K (h n) (fun _ => 1) ε) :
    Filter.Tendsto (fun n => boundaryPolynomialHom K (h n)) Filter.atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hh ε hε
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨b, hb, hbound⟩ := hn₀ n hn
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_lt_iff _ hε).2
  intro x
  simpa only [ContinuousMap.sub_apply, boundaryPolynomialHom_apply,
    ContinuousMap.one_apply, Real.norm_eq_abs] using (hbound x).trans_lt hb

theorem parityLift_tendsto {d : ℕ} {K : Set (E d)}
    [CompactSpace ↥(frontier K)] (p : Polynomial d) (e : ℕ)
    (h : ℕ → Polynomial d)
    (hh : Filter.Tendsto (fun n => boundaryPolynomialHom K (h n))
      Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => boundaryPolynomialHom K (parityLift p e h n))
      Filter.atTop (nhds (boundaryPolynomialHom K (parityPolynomial p e))) := by
  classical
  have hm (m : ℕ) : Filter.Tendsto
      (fun n => boundaryPolynomialHom K (parityComponent p e m) *
        boundaryPolynomialHom K (h (n - m / 2))) Filter.atTop
      (nhds (boundaryPolynomialHom K (parityComponent p e m))) := by
    simpa only [mul_one] using
      Filter.Tendsto.mul (g := fun n => boundaryPolynomialHom K (h (n - m / 2)))
        tendsto_const_nhds (hh.comp (Filter.tendsto_sub_atTop_nat (m / 2)))
  have hs := tendsto_finsetSum (Finset.range (p.totalDegree + 1)) (fun m _ => hm m)
  simpa only [parityLift, parityPolynomial, map_sum, map_mul] using hs

#print axioms parityLift_homogeneous
#print axioms boundary_sequence_tendsto
#print axioms parityLift_tendsto

theorem boundary_error_parity_projection {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (p : Polynomial d)
    (f : C(↥(frontier K), ℝ)) (e : ℕ) (he : e ≤ 1)
    (hf : ∀ x, f (boundaryNeg hK x) = (-1 : ℝ) ^ e * f x)
    {ε : ℝ} (hp : BoundaryErrorLT K p f ε) :
    BoundaryErrorLT K (parityPolynomial p e) f ε := by
  obtain ⟨b, hb, hbound⟩ := hp
  refine ⟨b, hb, ?_⟩
  intro x
  have hx := hbound x
  have hy := hbound (boundaryNeg hK x)
  change |evalPolynomial p (-(x : E d)) - f (boundaryNeg hK x)| ≤ b at hy
  have hsign : (-1 : ℝ) ^ e * (-1 : ℝ) ^ e = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hpar : (-1 : ℝ) ^ e * f (boundaryNeg hK x) = f x := by
    rw [hf x, ← mul_assoc, hsign, one_mul]
  have hid : evalPolynomial (parityPolynomial p e) (x : E d) - f x =
      ((evalPolynomial p (x : E d) - f x) + (-1 : ℝ) ^ e *
        (evalPolynomial p (-(x : E d)) - f (boundaryNeg hK x))) / 2 := by
    rw [parityPolynomial_eval p e he]
    linarith [hpar]
  rw [hid, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    |(evalPolynomial p (x : E d) - f x) + (-1 : ℝ) ^ e *
        (evalPolynomial p (-(x : E d)) - f (boundaryNeg hK x))| ≤
      |evalPolynomial p (x : E d) - f x| +
        |(-1 : ℝ) ^ e * (evalPolynomial p (-(x : E d)) - f (boundaryNeg hK x))| :=
      abs_add_le _ _
    _ = |evalPolynomial p (x : E d) - f x| +
        |evalPolynomial p (-(x : E d)) - f (boundaryNeg hK x)| := by
      rw [abs_mul, abs_neg_one_pow, one_mul]
    _ ≤ b + b := add_le_add hx hy
    _ = b * 2 := by ring

/-- Full parity approximation follows from the original single sequence of
homogeneous approximants to one, via polynomial density and degree lifting. -/
theorem parity_approximation_of_constant_sequence
    (hconst : ConstantSequenceStatement) {d : ℕ} {K : Set (E d)}
    (hK : IsSymmetricConvexBody K) (f : C(↥(frontier K), ℝ))
    (e : ℕ) (he : e ≤ 1)
    (hf : ∀ x, f (boundaryNeg hK.2.2.2 x) = (-1 : ℝ) ^ e * f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ p : Polynomial d,
      p.IsHomogeneous (2 * n + e) ∧ BoundaryErrorLT K p f ε := by
  classical
  have hc : IsCompact (frontier K) := hK.1.of_isClosed_subset isClosed_frontier (by
    intro x hx
    have hxcl : x ∈ closure K := frontier_subset_closure hx
    simpa only [hK.1.isClosed.closure_eq] using hxcl)
  let : CompactSpace ↥(frontier K) := isCompact_iff_compactSpace.mp hc
  obtain ⟨p, hp⟩ := boundary_polynomial_approximation hK.1 f (ε / 2) (by positivity)
  have hprojection := boundary_error_parity_projection hK.2.2.2 p f e he hf hp
  obtain ⟨h, hh, hconv⟩ := hconst d K hK
  have hlimit := parityLift_tendsto p e h (boundary_sequence_tendsto h hconv)
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hlimit (ε / 2) (by positivity)
  refine ⟨max n₀ p.totalDegree, ?_⟩
  intro n hn
  refine ⟨parityLift p e h n,
    parityLift_homogeneous p e he h hh n (le_trans (le_max_right _ _) hn), ?_⟩
  have herr := hn₀ n (le_trans (le_max_left _ _) hn)
  obtain ⟨b, hb, hpoint⟩ := hprojection
  refine ⟨dist (boundaryPolynomialHom K (parityLift p e h n))
      (boundaryPolynomialHom K (parityPolynomial p e)) + b,
    by linarith, ?_⟩
  intro x
  have hx := ContinuousMap.norm_coe_le_norm
    (boundaryPolynomialHom K (parityLift p e h n) -
      boundaryPolynomialHom K (parityPolynomial p e)) x
  have hfirst : |evalPolynomial (parityLift p e h n) (x : E d) -
      evalPolynomial (parityPolynomial p e) (x : E d)| ≤
      dist (boundaryPolynomialHom K (parityLift p e h n))
        (boundaryPolynomialHom K (parityPolynomial p e)) := by
    simpa only [dist_eq_norm, ContinuousMap.sub_apply, Real.norm_eq_abs,
      boundaryPolynomialHom_apply] using hx
  calc
    |evalPolynomial (parityLift p e h n) (x : E d) - f x| ≤
        |evalPolynomial (parityLift p e h n) (x : E d) -
          evalPolynomial (parityPolynomial p e) (x : E d)| +
        |evalPolynomial (parityPolynomial p e) (x : E d) - f x| := by
      simpa only [Real.dist_eq] using dist_triangle
        (evalPolynomial (parityLift p e h n) (x : E d))
        (evalPolynomial (parityPolynomial p e) (x : E d)) (f x)
    _ ≤ _ := add_le_add hfirst (hpoint x)

theorem even_functions_of_constant_sequence
    (hconst : ConstantSequenceStatement) : EvenFunctionsStatement := by
  intro d K hK f hf ε hε
  have hpar (x : ↥(frontier K)) :
      f (boundaryNeg hK.2.2.2 x) = (-1 : ℝ) ^ (0 : ℕ) * f x := by
    simpa only [pow_zero, one_mul] using hf x (boundaryNeg hK.2.2.2 x) rfl
  simpa only [add_zero] using
    parity_approximation_of_constant_sequence hconst hK f 0 (by omega) hpar ε hε

theorem odd_functions_of_constant_sequence
    (hconst : ConstantSequenceStatement) : OddFunctionsStatement := by
  intro d K hK f hf ε hε
  have hpar (x : ↥(frontier K)) :
      f (boundaryNeg hK.2.2.2 x) = (-1 : ℝ) ^ (1 : ℕ) * f x := by
    simpa only [pow_one, neg_one_mul] using hf x (boundaryNeg hK.2.2.2 x) rfl
  exact parity_approximation_of_constant_sequence hconst hK f 1 (by omega) hpar ε hε

theorem consecutive_degrees_of_constant_sequence
    (hconst : ConstantSequenceStatement) : ConsecutiveDegreesStatement :=
  consecutive_degrees_of_even_and_odd
    (even_functions_of_constant_sequence hconst) (odd_functions_of_constant_sequence hconst)

#print axioms boundary_error_parity_projection
#print axioms parity_approximation_of_constant_sequence
#print axioms even_functions_of_constant_sequence
#print axioms odd_functions_of_constant_sequence
#print axioms consecutive_degrees_of_constant_sequence

#print axioms boundary_polynomial_separates
#print axioms boundary_polynomial_approximation

end Bandlimited
end
