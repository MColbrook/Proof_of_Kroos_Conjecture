module

public import Bandlimited.Definitions
public import Bandlimited.FourierConvention
public import Bandlimited.GaussianCutoff
public import Mathlib.Analysis.Convex.FunctionTopology
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# A common finite family for bounded Lipschitz convex profiles

The compactness and continuity assertions below are actual analytic facts.
The final reduction keeps the preceding convex weighted Gaussian theorem as
an explicit hypothesis until that separate principal result has been proved.
Mathlib reuse: Tychonoff compactness, closedness of convex functions,
ArzelaAscoli.isCompact_of_equicontinuous (Apache 2.0).
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Bandlimited
namespace FiniteFamily

def ProfilePred (d : ℕ) (C : ℝ) (f : E d → ℝ) : Prop :=
  ConvexOn ℝ univ f ∧ (∀ x, 0 ≤ f x) ∧ f 0 = 0 ∧
    ∀ x y, |f x - f y| ≤ C * ‖x - y‖

theorem profilePred_iff {d : ℕ} {C : ℝ} (hC : 0 ≤ C) (f : E d → ℝ) :
    ProfilePred d C f ↔ HasProfileLipschitzBound C f := by
  constructor
  · rintro ⟨hc, hn, h0, hl⟩
    exact ⟨⟨hc, hn, h0, C, hC, hl⟩, hl⟩
  · rintro ⟨⟨hc, hn, h0, _⟩, hl⟩
    exact ⟨hc, hn, h0, hl⟩

theorem profilePred_isClosed (d : ℕ) (C : ℝ) :
    IsClosed {f : E d → ℝ | ProfilePred d C f} := by
  unfold ProfilePred
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_setOfPred_convexOn (𝕜 := ℝ) (s := (univ : Set (E d)))).inter ?_
  apply IsClosed.inter
  · exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le ((continuous_apply x).sub (continuous_apply y)).abs continuous_const

theorem profilePred_lipschitz {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {f : E d → ℝ} (hf : ProfilePred d C f) :
    LipschitzWith (NNReal.mk C hC) f := by
  apply (lipschitzWith_iff_dist_le_mul).mpr
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using hf.2.2.2 x y

theorem profilePred_bound {d : ℕ} {C : ℝ} {f : E d → ℝ}
    (hf : ProfilePred d C f) (x : E d) : f x ∈ Icc 0 (C * ‖x‖) := by
  refine ⟨hf.2.1 x, ?_⟩
  have h := hf.2.2.2 x 0
  rw [hf.2.2.1, sub_zero, sub_zero, abs_of_nonneg (hf.2.1 x)] at h
  exact h

theorem rawProfile_isCompact (d : ℕ) (C : ℝ) :
    IsCompact {f : E d → ℝ | ProfilePred d C f} := by
  apply (isCompact_univ_pi (fun x : E d => isCompact_Icc (a := (0 : ℝ))
    (b := C * ‖x‖))).of_isClosed_subset (profilePred_isClosed d C)
  intro f hf x hx
  exact profilePred_bound hf x

def continuousProfileSet (d : ℕ) (C : ℝ) : Set C(E d, ℝ) :=
  {f | ProfilePred d C f}

abbrev Profile (d : ℕ) (C : ℝ) := ↥(continuousProfileSet d C)

theorem continuousProfile_isCompact (d : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact (continuousProfileSet d C) := by
  have himage : ContinuousMap.toFun '' continuousProfileSet d C =
      {f : E d → ℝ | ProfilePred d C f} := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, (profilePred_lipschitz hC hf).continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    exact rawProfile_isCompact d C
  · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t)
      (by simpa only [mul_zero] using (continuous_const_mul C).tendsto (0 : ℝ))
    intro x y f
    simpa only [dist_eq_norm, Real.norm_eq_abs] using f.property.2.2.2 x y

instance profileCompactSpace (d : ℕ) (C : ℝ) [Fact (0 ≤ C)] : CompactSpace (Profile d C) :=
  isCompact_iff_compactSpace.mp (continuousProfile_isCompact d C Fact.out)

def zeroProfile (d : ℕ) (C : ℝ) (hC : 0 ≤ C) : Profile d C := by
  let f : C(E d, ℝ) := ⟨fun _ => 0, continuous_const⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · change ConvexOn ℝ (univ : Set (E d)) (fun _ => (0 : ℝ))
    exact convexOn_const 0 convex_univ
  · intro x
    exact le_refl 0
  · rfl
  · intro x y
    change |(0 : ℝ) - 0| ≤ C * ‖x - y‖
    simpa only [sub_self, abs_zero] using mul_nonneg hC (norm_nonneg (x - y))

theorem weighted_schwartz_tail_bound {d : ℕ} (F : SchwartzMap (E d) ℂ)
    {A L R : ℝ} {m : ℕ} (hA : 1 ≤ A) (hL : 0 ≤ L) (hm : L ≤ (m : ℝ))
    (hR : 1 ≤ R) (x : E d) (hx : R ≤ ‖x‖) :
    gaussianWeight A L x * ‖F x‖ ≤
      ((2 : ℝ) ^ m * SchwartzMap.seminorm ℂ (m + 1) 0 F) / R := by
  have hxp : 1 ≤ ‖x‖ := le_trans hR hx
  have hpow : (1 + ‖x‖) ^ m ≤ (2 * ‖x‖) ^ m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  have htail := schwartz_weighted_derivative_tail F m 0
    (lt_of_lt_of_le zero_lt_one hR) x hx
  calc
    gaussianWeight A L x * ‖F x‖ ≤ (1 + ‖x‖) ^ m * ‖F x‖ :=
      mul_le_mul_of_nonneg_right (gaussian_weight_le_integer_weight hA hL hm x) (norm_nonneg _)
    _ ≤ (2 * ‖x‖) ^ m * ‖F x‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = (2 : ℝ) ^ m * (‖x‖ ^ m * ‖F x‖) := by rw [mul_pow, mul_assoc]
    _ ≤ (2 : ℝ) ^ m * (SchwartzMap.seminorm ℂ (m + 1) 0 F / R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [norm_iteratedFDeriv_zero] using htail
    _ = _ := by ring

theorem weighted_schwartz_vanishes {d : ℕ} (F : SchwartzMap (E d) ℂ)
    (A L : ℝ) (hA : 1 ≤ A) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x : E d, R ≤ ‖x‖ → gaussianWeight A L x * ‖F x‖ < ε := by
  obtain ⟨m, hm⟩ := exists_nat_ge L
  let B : ℝ := (2 : ℝ) ^ m * SchwartzMap.seminorm ℂ (m + 1) 0 F
  let R : ℝ := max 1 (B / ε + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  refine ⟨R, hR, ?_⟩
  intro x hx
  apply lt_of_le_of_lt (weighted_schwartz_tail_bound F hA hL hm hR x hx)
  apply (div_lt_iff₀ hRp).mpr
  have ht : B / ε < R := by dsimp [R]; linarith [le_max_right 1 (B / ε + 1)]
  have hm := mul_lt_mul_of_pos_right ht hε
  rw [div_mul_cancel₀ B hε.ne'] at hm
  simpa only [mul_comm R ε, B] using hm

theorem gaussianWeight_continuous {d : ℕ} (A L : ℝ) (hA : 1 ≤ A) :
    Continuous (gaussianWeight (d := d) A L) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hb : Continuous (fun x : E d => 1 + ‖x‖ / A) :=
    continuous_const.add (continuous_norm.div_const A)
  have hpos (x : E d) : 0 < 1 + ‖x‖ / A := by positivity
  have heq : gaussianWeight (d := d) A L = fun x => Real.exp (Real.log (1 + ‖x‖ / A) * L) := by
    funext x
    exact Real.rpow_def_of_pos (hpos x) L
  rw [heq]
  exact Real.continuous_exp.comp ((hb.log (fun x => (hpos x).ne')).mul continuous_const)

theorem profile_eval_continuous (d : ℕ) (C : ℝ) :
    Continuous (fun p : Profile d C × E d => p.1.val p.2) := by
  exact (continuous_subtype_val.comp continuous_fst).eval continuous_snd

theorem weighted_exp_difference_continuous {d : ℕ} {C A L : ℝ}
    (hA : 1 ≤ A) (F : SchwartzMap (E d) ℂ) (f : Profile d C) :
    Continuous (fun p : Profile d C × E d => gaussianWeight A L p.2 *
      ‖((Real.exp (-p.1.val p.2) : ℂ) - (Real.exp (-f.val p.2) : ℂ)) * F p.2‖) := by
  have hg := Real.continuous_exp.comp (profile_eval_continuous d C).neg
  have hf : Continuous (fun p : Profile d C × E d => Real.exp (-f.val p.2)) :=
    Real.continuous_exp.comp (f.val.continuous.comp continuous_snd).neg
  exact ((gaussianWeight_continuous A L hA).comp continuous_snd).mul
    (((Complex.continuous_ofReal.comp hg).sub (Complex.continuous_ofReal.comp hf)).mul
      (F.continuous.comp continuous_snd)).norm

theorem profile_exp_norm_le_one {d : ℕ} {C : ℝ} (f : Profile d C) (x : E d) :
    ‖(Real.exp (-f.val x) : ℂ)‖ ≤ 1 := by
  have he : Real.exp (-f.val x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (f.property.2.1 x))
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he

theorem weighted_exp_difference_eventually {d : ℕ} {C A L : ℝ}
    (hA : 1 ≤ A) (hL : 0 ≤ L) (F : SchwartzMap (E d) ℂ)
    (f : Profile d C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g : Profile d C in 𝓝 f, ∀ x : E d,
      gaussianWeight A L x *
        ‖((Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * F x‖ < ε := by
  obtain ⟨R, hR1, hR⟩ := weighted_schwartz_vanishes F A L hA hL (ε / 4) (by positivity)
  have hinside : ∀ᶠ g : Profile d C in 𝓝 f, ∀ x ∈ Metric.closedBall (0 : E d) R,
      gaussianWeight A L x *
        ‖((Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * F x‖ < ε := by
    apply (isCompact_closedBall (0 : E d) R).eventually_forall_of_forall_eventually
    intro x hx
    have hcont := (weighted_exp_difference_continuous (L := L) hA F f).tendsto (f, x)
    have hzero : gaussianWeight A L x *
        ‖((Real.exp (-f.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * F x‖ = 0 := by simp
    rw [hzero] at hcont
    exact hcont (Iio_mem_nhds hε)
  filter_upwards [hinside] with g hg
  intro x
  by_cases hx : ‖x‖ ≤ R
  · exact hg x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · have htail := hR x (le_of_lt (lt_of_not_ge hx))
    have hdiff : ‖(Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [profile_exp_norm_le_one g x, profile_exp_norm_le_one f x])
    have hw : 0 ≤ gaussianWeight A L x := Real.rpow_nonneg (by positivity) _
    rw [norm_mul]
    calc
      gaussianWeight A L x *
          (‖(Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)‖ * ‖F x‖) ≤
          gaussianWeight A L x * (2 * ‖F x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)) hw
      _ = 2 * (gaussianWeight A L x * ‖F x‖) := by ring
      _ < ε := by linarith

theorem bandlimited_has_schwartz {d : ℕ} (hd : d ≠ 0) {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) :
    ∃ S : SchwartzMap (E d) ℂ, ∀ x, S x = F x := by
  simp only [InBandlimitedSpace, hd, ↓reduceIte] at hF
  obtain ⟨φ, hφ, hFeq⟩ := hF
  obtain ⟨S, hS⟩ := hφ.inverse_schwartz
  exact ⟨S, fun x => by rw [hFeq]; exact hS x⟩

end FiniteFamily
open FiniteFamily

/-- Full finite-family conclusion from the explicit preceding principal
Gaussian approximation theorem. The hypothesis is retained until T11 is proved. -/
theorem finite_family_of_convex_weighted_gaussian
    (hweighted : ConvexWeightedGaussianStatement) : FiniteFamilyStatement := by
  classical
  intro s hs L σ C τ hL hσ hC hτ
  have hC0 : 0 ≤ C := hC.le
  letI : Fact (0 ≤ C) := ⟨hC0⟩
  obtain ⟨Δ, hΔ, happrox⟩ := hweighted s hs L σ hL hσ
  obtain ⟨A₀, hA₀⟩ := hΔ (τ / 4) (by positivity)
  let A : ℝ := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hΔA : Δ A < τ / 4 :=
    lt_of_le_of_lt (le_abs_self _) (hA₀ A (le_max_right _ _))
  let b₀ : ℝ := Δ A + τ / 4
  have hb₀ : b₀ + τ / 4 < τ := by dsimp [b₀]; linarith
  have hcenter (f : Profile s C) :
      ∃ S : SchwartzMap (E s) ℂ, InBandlimitedSpace s σ S ∧ IsRealValued S ∧
        ∀ x : E s, gaussianWeight A L x *
          ‖(Real.exp (-f.val x) : ℂ) * S x - (gaussian A x : ℂ)‖ ≤ b₀ := by
    have hf : IsConvexProfile (f.val : E s → ℝ) :=
      ((profilePred_iff hC0 f.val).mp f.property).1
    obtain ⟨F, hFspace, hFreal, hFerr⟩ := (happrox A hA).2 f.val hf (τ / 4) (by positivity)
    obtain ⟨S, hS⟩ := bandlimited_has_schwartz (by omega : s ≠ 0) hFspace
    have heq : (S : E s → ℂ) = F := funext hS
    refine ⟨S, ?_, ?_, ?_⟩
    · rw [heq]
      exact hFspace
    · rw [heq]
      exact hFreal
    · intro x
      rw [hS]
      exact hFerr x
  choose S hSspace hSreal hSerr using hcenter
  have hneighborhood (f : Profile s C) :
      ∃ U : Set (Profile s C), IsOpen U ∧ f ∈ U ∧
        ∀ g ∈ U, ∃ b : ℝ, b < τ ∧ ∀ x : E s, gaussianWeight A L x *
          ‖(Real.exp (-g.val x) : ℂ) * S f x - (gaussian A x : ℂ)‖ ≤ b := by
    have hevent := weighted_exp_difference_eventually hA hL (S f) f (τ / 4) (by positivity)
    obtain ⟨U, hUsub, hUopen, hfU⟩ := mem_nhds_iff.mp hevent
    refine ⟨U, hUopen, hfU, ?_⟩
    intro g hg
    refine ⟨b₀ + τ / 4, hb₀, ?_⟩
    intro x
    have hdiff := hUsub hg x
    have hw : 0 ≤ gaussianWeight A L x := Real.rpow_nonneg (by positivity) _
    have hid : (Real.exp (-g.val x) : ℂ) * S f x - (gaussian A x : ℂ) =
        ((Real.exp (-f.val x) : ℂ) * S f x - (gaussian A x : ℂ)) +
          (((Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * S f x) := by ring
    rw [hid]
    calc
      _ ≤ gaussianWeight A L x *
          (‖(Real.exp (-f.val x) : ℂ) * S f x - (gaussian A x : ℂ)‖ +
            ‖((Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * S f x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
      _ = gaussianWeight A L x *
          ‖(Real.exp (-f.val x) : ℂ) * S f x - (gaussian A x : ℂ)‖ +
            gaussianWeight A L x *
              ‖((Real.exp (-g.val x) : ℂ) - (Real.exp (-f.val x) : ℂ)) * S f x‖ := by ring
      _ ≤ b₀ + τ / 4 := add_le_add (hSerr f x) hdiff.le
  choose U hUopen hfU hUerr using hneighborhood
  have hcover : (univ : Set (Profile s C)) ⊆ ⋃ f, U f := by
    intro f hf
    exact mem_iUnion.mpr ⟨f, hfU f⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  have htne : t.Nonempty := by
    have h := ht (Set.mem_univ (zeroProfile s C hC0))
    obtain ⟨f, hf⟩ := mem_iUnion.mp h
    obtain ⟨hft, hzero⟩ := mem_iUnion.mp hf
    exact ⟨f, hft⟩
  letI : Nonempty t := by obtain ⟨f, hf⟩ := htne; exact ⟨⟨f, hf⟩⟩
  let J : ℕ := Fintype.card t
  let e : Fin J ≃ t := (Fintype.equivFin t).symm
  have hJ : 0 < J := Fintype.card_pos_iff.mpr inferInstance
  refine ⟨A, hA, J, hJ, fun j => (S (e j).val : E s → ℂ), ?_, ?_⟩
  · intro j
    exact ⟨hSspace (e j).val, hSreal (e j).val⟩
  · intro f hf
    have hp : ProfilePred s C f := (profilePred_iff hC0 f).mpr hf
    let fC : C(E s, ℝ) := ⟨f, (profilePred_lipschitz hC0 hp).continuous⟩
    let g : Profile s C := ⟨fC, hp⟩
    have h := ht (Set.mem_univ g)
    obtain ⟨z, hz⟩ := mem_iUnion.mp h
    obtain ⟨hzt, hgU⟩ := mem_iUnion.mp hz
    obtain ⟨b, hb, herr⟩ := hUerr z g hgU
    refine ⟨e.symm ⟨z, hzt⟩, b, hb, ?_⟩
    intro x
    simpa only [e.apply_symm_apply, g, fC, ContinuousMap.coe_mk] using herr x

#print axioms finite_family_of_convex_weighted_gaussian

namespace FiniteFamily
#print axioms weighted_schwartz_vanishes
#print axioms gaussianWeight_continuous
#print axioms profile_eval_continuous
#print axioms weighted_exp_difference_eventually
#print axioms profilePred_isClosed
#print axioms rawProfile_isCompact
#print axioms continuousProfile_isCompact

end FiniteFamily
end Bandlimited
