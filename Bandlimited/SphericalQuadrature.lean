module

public import Bandlimited.Definitions
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Positive spherical quadrature

This development uses Mathlib's `Convex.average_mem` (Yury Kudryashov),
`convexHull_range_eq_exists_affineCombination`, and Bochner integration of
continuous maps. All measures below are the canonical measures in the source
specification. Quantitative spherical integral estimates are separate from the
finite positive quadrature argument.
-/

@[expose] public section
open scoped BigOperators Pointwise
open MeasureTheory Set
noncomputable section
namespace Bandlimited
namespace SphereQuadrature

/-- An integrable Banach-valued function admits a finite strictly positive
atomic approximation of its integral. Zero convex coefficients are removed. -/
theorem finite_positive_integral_approximation
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (F : X → V) (hF : Integrable F μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset X, t.Nonempty ∧ ∃ w : X → ℝ,
      (∀ i ∈ t, 0 < w i) ∧
        ‖(∑ i ∈ t, w i • F i) - ∫ x, F x ∂μ‖ < ε := by
  classical
  let M : ℝ := μ.real univ
  have hM : 0 < M := by
    exact ENNReal.toReal_pos (fun h => NeZero.ne μ (Measure.measure_univ_eq_zero.mp h))
      (measure_ne_top μ univ)
  have havg : (⨍ x, F x ∂μ) ∈ closure (convexHull ℝ (range F)) := by
    apply (convex_convexHull ℝ (range F)).closure.average_mem isClosed_closure
    · exact Filter.Eventually.of_forall fun x =>
        subset_closure (subset_convexHull ℝ (range F) (mem_range_self x))
    · exact hF
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp havg (ε / M) (div_pos hε hM)
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, a, ha, hasum, hsum⟩ := hy
  rw [Finset.affineCombination_eq_linear_combination s F a hasum] at hsum
  let t : Finset X := s.filter fun x => a x ≠ 0
  have ht_sub : t ⊆ s := Finset.filter_subset _ _
  have hzero : ∀ x ∈ s, x ∉ t → a x = 0 := by
    intro x hxs hxt
    simpa [t, hxs] using hxt
  have htasum : (∑ i ∈ t, a i) = 1 := by
    rw [← hasum]
    exact Finset.sum_subset ht_sub hzero
  have htsum : (∑ i ∈ t, a i • F i) = y := by
    rw [← hsum]
    apply Finset.sum_subset ht_sub
    intro x hxs hxt
    rw [hzero x hxs hxt, zero_smul]
  have ht : t.Nonempty := by
    by_contra h
    have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at htasum
  refine ⟨t, ht, fun x => M * a x, ?_, ?_⟩
  · intro x hxt
    have hax : 0 < a x := lt_of_le_of_ne (ha x (ht_sub hxt))
      (Ne.symm (Finset.mem_filter.mp hxt).2)
    exact mul_pos hM hax
  · have hfactor : (∑ i ∈ t, (M * a i) • F i) = M • y := by
      rw [← htsum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_smul M (a i) (F i)
    have hnorm : ‖y - ⨍ x, F x ∂μ‖ < ε / M := by
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    calc
      ‖(∑ i ∈ t, (M * a i) • F i) - ∫ x, F x ∂μ‖ =
          M * ‖y - ⨍ x, F x ∂μ‖ := by
        rw [hfactor, ← measure_smul_average, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_of_pos hM]
      _ < M * (ε / M) := mul_lt_mul_of_pos_left hnorm hM
      _ = ε := by field_simp [ne_of_gt hM]

theorem rho_nonneg {d : ℕ} (u v : Sphere d) : 0 ≤ rho u v :=
  le_min (norm_nonneg _) (norm_nonneg _)

theorem sphere_norm {d : ℕ} (u : Sphere d) : ‖(u : E d)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

theorem rho_le_two {d : ℕ} (u v : Sphere d) : rho u v ≤ 2 := by
  calc
    rho u v ≤ ‖(u : E d) - (v : E d)‖ := min_le_left _ _
    _ ≤ ‖(u : E d)‖ + ‖(v : E d)‖ := norm_sub_le _ _
    _ = 2 := by rw [sphere_norm, sphere_norm]; norm_num

theorem continuous_rho {d : ℕ} :
    Continuous (fun p : Sphere d × Sphere d => rho p.1 p.2) := by
  exact ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).norm.min
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).norm

theorem continuous_gaussianKernel {d : ℕ} (lam : ℝ) :
    Continuous (fun p : Sphere d × Sphere d => gaussianKernel lam p.1 p.2) := by
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_rho.pow 2))

theorem continuous_tailKernel {d : ℕ} (lam L : ℝ) (hlam : 0 ≤ lam) :
    Continuous (fun p : Sphere d × Sphere d => tailKernel lam L p.1 p.2) := by
  have hbase : Continuous (fun p : Sphere d × Sphere d => 1 + lam * rho p.1 p.2) :=
    continuous_const.add (continuous_const.mul continuous_rho)
  have hpos (p : Sphere d × Sphere d) : 0 < 1 + lam * rho p.1 p.2 :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hlam (rho_nonneg _ _))
  have hexp : Continuous (fun p : Sphere d × Sphere d =>
      Real.exp (Real.log (1 + lam * rho p.1 p.2) * (-L))) := Real.continuous_exp.comp
    ((hbase.log (fun p => ne_of_gt (hpos p))).mul continuous_const)
  convert hexp using 1
  funext p
  exact Real.rpow_def_of_pos (hpos p) (-L)

/-- Both continuous kernels are approximated by one finite positive rule,
uniformly in their first variable. This assertion has absolute error `ε`. -/
theorem simultaneous_absolute_quadrature
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (G H : C(X × X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset X, t.Nonempty ∧ ∃ w : X → ℝ,
      (∀ i ∈ t, 0 < w i) ∧ ∀ u : X,
        |(∑ i ∈ t, w i * G (u, i)) - ∫ v, G (u, v) ∂μ| < ε ∧
        |(∑ i ∈ t, w i * H (u, i)) - ∫ v, H (u, v) ∂μ| < ε := by
  classical
  let K : C(X × X, ℝ × ℝ) :=
    ⟨fun p => (G (p.2, p.1), H (p.2, p.1)),
      (G.continuous.comp continuous_swap).prodMk (H.continuous.comp continuous_swap)⟩
  let F : X → C(X, ℝ × ℝ) := K.curry
  have hF : Integrable F μ :=
    K.curry.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨t, ht, w, hw, herr⟩ := finite_positive_integral_approximation μ F hF hε
  refine ⟨t, ht, w, hw, fun u => ?_⟩
  have hGint : Integrable (fun v => G (u, v)) μ :=
    (G.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHint : Integrable (fun v => H (u, v)) μ :=
    (H.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : (∑ i ∈ t, w i • F i) u =
      (∑ i ∈ t, w i * G (u, i), ∑ i ∈ t, w i * H (u, i)) := by
    clear ht hw herr
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, ContinuousMap.zero_apply]
      rfl
    | @insert a t ha ih =>
      simp only [Finset.sum_insert ha, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, ih]
      rfl
  have hint : (∫ v, F v ∂μ) u = (∫ v, G (u, v) ∂μ, ∫ v, H (u, v) ∂μ) := by
    rw [ContinuousMap.integral_apply hF]
    exact integral_pair hGint hHint
  have heval : ‖((∑ i ∈ t, w i • F i) - ∫ v, F v ∂μ) u‖ < ε :=
    lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm _ u) herr
  have hdiff : ((∑ i ∈ t, w i • F i) - ∫ v, F v ∂μ) u =
      ((∑ i ∈ t, w i * G (u, i)) - ∫ v, G (u, v) ∂μ,
       (∑ i ∈ t, w i * H (u, i)) - ∫ v, H (u, v) ∂μ) := by
    rw [ContinuousMap.sub_apply, hsum, hint]
    rfl
  rw [hdiff] at heval
  simpa only [Prod.norm_mk, Real.norm_eq_abs, max_lt_iff] using heval

/-- Absolute approximation gives the required relative Gaussian error and
tail majorization whenever the two kernels have positive constant lower bounds. -/
theorem simultaneous_relative_quadrature
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (G H : C(X × X, ℝ)) (g₀ h₀ : ℝ) (hg₀ : 0 < g₀) (hh₀ : 0 < h₀)
    (hG : ∀ u v, g₀ ≤ G (u, v)) (hH : ∀ u v, h₀ ≤ H (u, v))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ t : Finset X, t.Nonempty ∧ ∃ w : X → ℝ,
      (∀ i ∈ t, 0 < w i) ∧ ∀ u : X,
        |(∑ i ∈ t, w i * G (u, i)) - ∫ v, G (u, v) ∂μ| <
          ζ * ∫ v, G (u, v) ∂μ ∧
        (∑ i ∈ t, w i * H (u, i)) ≤ 2 * ∫ v, H (u, v) ∂μ := by
  classical
  let M : ℝ := μ.real univ
  have hM : 0 < M := ENNReal.toReal_pos
    (fun h => NeZero.ne μ (Measure.measure_univ_eq_zero.mp h)) (measure_ne_top μ univ)
  have hGintegrable (u : X) : Integrable (fun v => G (u, v)) μ :=
    (G.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hHintegrable (u : X) : Integrable (fun v => H (u, v)) μ :=
    (H.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIG (u : X) : g₀ * M ≤ ∫ v, G (u, v) ∂μ := by
    have h := integral_mono (integrable_const g₀) (hGintegrable u) (hG u)
    simpa only [integral_const, smul_eq_mul, mul_comm, M] using h
  have hIH (u : X) : h₀ * M ≤ ∫ v, H (u, v) ∂μ := by
    have h := integral_mono (integrable_const h₀) (hHintegrable u) (hH u)
    simpa only [integral_const, smul_eq_mul, mul_comm, M] using h
  let ε : ℝ := min (ζ * (g₀ * M)) (h₀ * M)
  have hε : 0 < ε := lt_min (mul_pos hζ (mul_pos hg₀ hM)) (mul_pos hh₀ hM)
  obtain ⟨t, ht, w, hw, herr⟩ := simultaneous_absolute_quadrature μ G H hε
  refine ⟨t, ht, w, hw, fun u => ?_⟩
  constructor
  · exact (herr u).1.trans_le ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (hIG u) hζ.le))
  · have he := (herr u).2.trans_le ((min_le_right _ _).trans (hIH u))
    have hle := le_abs_self ((∑ i ∈ t, w i * H (u, i)) - ∫ v, H (u, v) ∂μ)
    linarith

instance sphereCompactSpace (d : ℕ) : CompactSpace (Sphere d) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E d) 1)

instance surfaceFiniteMeasure (s : ℕ) : IsFiniteMeasure (surfaceMeasure s) := by
  unfold surfaceMeasure
  infer_instance

instance surfaceNonzero (s : ℕ) : NeZero (surfaceMeasure s) := by
  constructor
  exact Measure.toSphere_ne_zero volume

theorem gaussianKernel_lower {d : ℕ} (lam : ℝ) (u v : Sphere d) :
    Real.exp (-4 * lam ^ 2) ≤ gaussianKernel lam u v := by
  have hr : (rho u v) ^ 2 ≤ 4 := by
    nlinarith [rho_nonneg u v, rho_le_two u v]
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg lam)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem tailKernel_lower {d : ℕ} (lam L : ℝ) (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (u v : Sphere d) : (1 + 2 * lam) ^ (-L) ≤ tailKernel lam L u v := by
  have hb : 0 < 1 + lam * rho u v :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hlam (rho_nonneg _ _))
  have hle : 1 + lam * rho u v ≤ 1 + 2 * lam := by
    have h := mul_le_mul_of_nonneg_left (rho_le_two u v) hlam
    linarith
  exact Real.rpow_le_rpow_of_nonpos hb hle (neg_nonpos.mpr hL)

/-- The simultaneous, strictly positive quadrature clause of manuscript Lemma 5.1.
The measure is exactly the canonical Euclidean surface measure, and the same
finite family and weights satisfy both estimates for every centre. -/
theorem positive_spherical_quadrature_rule (s : ℕ) (lam L : ℝ)
    (hlam : 1 ≤ lam) (hL : 0 ≤ L) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ m : ℕ, 0 < m ∧ ∃ v : Fin m → Sphere (s + 1), ∃ w : Fin m → ℝ,
      (∀ i, 0 < w i) ∧ ∀ u : Sphere (s + 1),
        |(∑ i : Fin m, w i * gaussianKernel lam u (v i)) -
          sphericalGaussianIntegral s lam u| < ζ * sphericalGaussianIntegral s lam u ∧
        (∑ i : Fin m, w i * tailKernel lam L u (v i)) ≤
          2 * sphericalTailIntegral s lam L u := by
  classical
  have hl0 : 0 ≤ lam := by linarith
  let G : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => gaussianKernel lam p.1 p.2, continuous_gaussianKernel lam⟩
  let H : C(Sphere (s + 1) × Sphere (s + 1), ℝ) :=
    ⟨fun p => tailKernel lam L p.1 p.2, continuous_tailKernel lam L hl0⟩
  have hh₀ : 0 < (1 + 2 * lam) ^ (-L) := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨t, ht, w, hw, hquad⟩ := simultaneous_relative_quadrature
    (surfaceMeasure s) G H (Real.exp (-4 * lam ^ 2)) ((1 + 2 * lam) ^ (-L))
    (Real.exp_pos _) hh₀ (gaussianKernel_lower lam) (tailKernel_lower lam L hl0 hL) hζ
  let : Nonempty t := by
    obtain ⟨x, hx⟩ := ht
    exact ⟨⟨x, hx⟩⟩
  let m : ℕ := Fintype.card t
  let e : Fin m ≃ t := (Fintype.equivFin t).symm
  have hm : 0 < m := Fintype.card_pos_iff.mpr inferInstance
  have hsum (k : Sphere (s + 1) → ℝ) :
      (∑ i : Fin m, w (e i) * k (e i)) = ∑ i ∈ t, w i * k i := by
    calc
      (∑ i : Fin m, w (e i) * k (e i)) = ∑ i : t, w i * k i :=
        Fintype.sum_equiv e _ _ (fun i => rfl)
      _ = ∑ i ∈ t, w i * k i := Finset.sum_attach t (fun i => w i * k i)
  refine ⟨m, hm, fun i => (e i).val, fun i => w (e i), ?_, ?_⟩
  · intro i
    exact hw (e i) (e i).property
  · intro u
    change |(∑ i : Fin m, w (e i) * gaussianKernel lam u (e i)) -
      sphericalGaussianIntegral s lam u| < ζ * sphericalGaussianIntegral s lam u ∧
      (∑ i : Fin m, w (e i) * tailKernel lam L u (e i)) ≤
        2 * sphericalTailIntegral s lam L u
    rw [hsum (gaussianKernel lam u), hsum (tailKernel lam L u)]
    exact hquad u

/-- Restriction of an orthogonal map to the unit sphere. -/
def sphereMap {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) : Sphere d ≃ₜ Sphere d where
  toFun u := ⟨f u, by simpa only [Metric.mem_sphere, dist_zero_right, f.norm_map]
    using u.property⟩
  invFun u := ⟨f.symm u, by simpa only [Metric.mem_sphere, dist_zero_right, f.symm.norm_map]
    using u.property⟩
  left_inv u := by apply Subtype.ext; exact f.symm_apply_apply u
  right_inv u := by apply Subtype.ext; exact f.apply_symm_apply u
  continuous_toFun := (f.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (f.symm.continuous.comp continuous_subtype_val).subtype_mk _

open scoped Pointwise in
private theorem sphereMap_sector_preimage {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d)
    (S : Set (Sphere d)) :
    f ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' S)) =
      Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap f ⁻¹' S)) := by
  ext x
  constructor
  · rintro ⟨t, ht, z, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨t, ht, ((sphereMap f).symm v : E d),
      ⟨(sphereMap f).symm v, ?_, rfl⟩, ?_⟩
    · simpa using hv
    · apply f.injective
      rw [f.map_smul]
      change t • f (f.symm (v : E d)) = f x
      simpa only [f.apply_symm_apply] using hx
  · rintro ⟨t, ht, z, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨t, ht, f v, ⟨sphereMap f v, hv, rfl⟩, ?_⟩
    exact (f.map_smul t v).symm

/-- Canonical sphere measure is invariant under every orthogonal map.
This is derived from Haar volume invariance and the defining cone formula. -/
theorem sphereMap_measurePreserving (s : ℕ)
    (f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1)) :
    MeasurePreserving (sphereMap f) (surfaceMeasure s) (surfaceMeasure s) := by
  refine ⟨(sphereMap f).measurable, ?_⟩
  apply Measure.OuterRegular.ext_isOpen
  intro S hS
  rw [Measure.map_apply (sphereMap f).measurable hS.measurableSet]
  unfold surfaceMeasure
  rw [Measure.toSphere_apply' _ ((sphereMap f).continuous.isOpen_preimage S hS).measurableSet,
    Measure.toSphere_apply' _ hS.measurableSet,
    ← sphereMap_sector_preimage]
  congr 1
  have hcone : IsOpen (Ioo (0 : ℝ) 1 • ((Subtype.val : Sphere (s + 1) → E (s + 1)) '' S) : Set (E (s + 1))) :=
    isOpen_Ioo.smul_sphere one_ne_zero (by simp) hS
  exact f.measurePreserving.measure_preimage hcone.measurableSet.nullMeasurableSet

theorem rho_sphereMap {d : ℕ} (f : E d ≃ₗᵢ[ℝ] E d) (u v : Sphere d) :
    rho (sphereMap f u) (sphereMap f v) = rho u v := by
  change min ‖f u - f v‖ ‖f u + f v‖ = min ‖(u : E d) - v‖ ‖(u : E d) + v‖
  rw [← f.map_sub, ← f.map_add, f.norm_map, f.norm_map]

theorem sphericalIntegrals_rotation (s : ℕ) (lam L : ℝ)
    (f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1)) (u : Sphere (s + 1)) :
    sphericalGaussianIntegral s lam (sphereMap f u) = sphericalGaussianIntegral s lam u ∧
    sphericalTailIntegral s lam L (sphereMap f u) = sphericalTailIntegral s lam L u := by
  constructor
  · unfold sphericalGaussianIntegral
    calc
      (∫ v, gaussianKernel lam (sphereMap f u) v ∂surfaceMeasure s) =
          ∫ v, gaussianKernel lam (sphereMap f u) (sphereMap f v) ∂surfaceMeasure s :=
        ((sphereMap_measurePreserving s f).integral_comp (sphereMap f).measurableEmbedding _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun v => by
        simp only [gaussianKernel, rho_sphereMap])
  · unfold sphericalTailIntegral
    calc
      (∫ v, tailKernel lam L (sphereMap f u) v ∂surfaceMeasure s) =
          ∫ v, tailKernel lam L (sphereMap f u) (sphereMap f v) ∂surfaceMeasure s :=
        ((sphereMap_measurePreserving s f).integral_comp (sphereMap f).measurableEmbedding _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun v => by
        simp only [tailKernel, rho_sphereMap])

/-- Both actual spherical integrals are independent of the centre. -/
theorem sphericalIntegrals_independent (s : ℕ) (lam L : ℝ)
    (u v : Sphere (s + 1)) :
    sphericalGaussianIntegral s lam u = sphericalGaussianIntegral s lam v ∧
    sphericalTailIntegral s lam L u = sphericalTailIntegral s lam L v := by
  let f : E (s + 1) ≃ₗᵢ[ℝ] E (s + 1) :=
    Submodule.reflection (ℝ ∙ ((u : E (s + 1)) - v))ᗮ
  have huv : sphereMap f u = v := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((sphere_norm u).trans (sphere_norm v).symm)
  have h := sphericalIntegrals_rotation s lam L f u
  rw [huv] at h
  exact ⟨h.1.symm, h.2.symm⟩

#print axioms finite_positive_integral_approximation
#print axioms simultaneous_absolute_quadrature
#print axioms simultaneous_relative_quadrature
#print axioms sphereMap_measurePreserving
#print axioms sphericalIntegrals_independent
#print axioms positive_spherical_quadrature_rule

end SphereQuadrature
end Bandlimited
end
