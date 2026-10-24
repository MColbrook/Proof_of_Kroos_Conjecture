module

public import Bandlimited.FourierConvention
public import Mathlib.Topology.Algebra.Support

/- Algebra, translation, and modulation for the exact compact-frequency class. -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace

namespace Bandlimited

 theorem InBandlimitedSpace.exists_schwartz {d : ℕ} (hd : d ≠ 0) {σ : ℝ}
    {F : E d → ℂ} (hF : InBandlimitedSpace d σ F) :
    ∃ G : SchwartzMap (E d) ℂ, ∀ x, G x = F x := by
  obtain ⟨φ, hφ, rfl⟩ := (ite_eq_right hd).mp hF
  exact hφ.inverse_schwartz

 theorem SmoothFrequency.add {d : ℕ} {σ : ℝ} {φ ψ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hψ : SmoothFrequency σ ψ) :
    SmoothFrequency σ (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  exact (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)

 theorem SmoothFrequency.smul {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (a : ℂ) : SmoothFrequency σ (a • φ) := by
  refine ⟨hφ.1.const_smul a, hφ.2.1.smul_left, ?_⟩
  exact (tsupport_smul_subset_right (fun _ : E d => a) φ).trans hφ.2.2

 theorem inverseFourierSchwartz_add {d : ℕ} (φ ψ : SchwartzMap (E d) ℂ) :
    inverseFourierSchwartz (φ + ψ) = inverseFourierSchwartz φ + inverseFourierSchwartz ψ := by
  simp only [inverseFourierSchwartz, FourierTransform.fourierInv_add, map_add, smul_add]

 theorem inverseFourierSchwartz_smul {d : ℕ} (a : ℂ) (φ : SchwartzMap (E d) ℂ) :
    inverseFourierSchwartz (a • φ) = a • inverseFourierSchwartz φ := by
  simp only [inverseFourierSchwartz, FourierTransform.fourierInv_smul, map_smul, smul_comm a]

 theorem inverseFourier_add_of_smoothFrequency {d : ℕ} {σ : ℝ} {φ ψ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (hψ : SmoothFrequency σ ψ) :
    inverseFourier (φ + ψ) = inverseFourier φ + inverseFourier ψ := by
  let φS := hφ.2.1.toSchwartzMap hφ.1
  let ψS := hψ.2.1.toSchwartzMap hψ.1
  ext x
  have h := congrArg (fun f : SchwartzMap (E d) ℂ => f x)
    (inverseFourierSchwartz_add φS ψS)
  have hφcoe : (φS : E d → ℂ) = φ := rfl
  have hψcoe : (ψS : E d → ℂ) = ψ := rfl
  have hsumcoe : ((φS + ψS : SchwartzMap (E d) ℂ) : E d → ℂ) = φ + ψ := by
    funext ξ
    rw [add_apply]
    rfl
  simpa only [inverseFourierSchwartz_apply, add_apply, hsumcoe, hφcoe, hψcoe,
    Pi.add_apply] using h

 theorem inverseFourier_smul_of_smoothFrequency {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (a : ℂ) :
    inverseFourier (a • φ) = a • inverseFourier φ := by
  let φS := hφ.2.1.toSchwartzMap hφ.1
  ext x
  have h := congrArg (fun f : SchwartzMap (E d) ℂ => f x)
    (inverseFourierSchwartz_smul a φS)
  have hφcoe : (φS : E d → ℂ) = φ := rfl
  have hsmulcoe : ((a • φS : SchwartzMap (E d) ℂ) : E d → ℂ) = a • φ := by
    funext ξ
    rw [smul_apply]
    rfl
  simpa only [inverseFourierSchwartz_apply, smul_apply, hsmulcoe, hφcoe,
    Pi.smul_apply] using h

 theorem InBandlimitedSpace.add {d : ℕ} {σ : ℝ} {F G : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (hG : InBandlimitedSpace d σ G) :
    InBandlimitedSpace d σ (F + G) := by
  by_cases hd : d = 0
  · obtain ⟨a, ha⟩ := (ite_eq_left hd).mp hF
    obtain ⟨b, hb⟩ := (ite_eq_left hd).mp hG
    exact (ite_eq_left hd).mpr ⟨a + b, fun x => by simp only [Pi.add_apply, ha, hb]⟩
  · obtain ⟨φ, hφ, rfl⟩ := (ite_eq_right hd).mp hF
    obtain ⟨ψ, hψ, rfl⟩ := (ite_eq_right hd).mp hG
    exact (ite_eq_right hd).mpr ⟨φ + ψ, hφ.add hψ,
      (inverseFourier_add_of_smoothFrequency hφ hψ).symm⟩

 theorem InBandlimitedSpace.smul {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (a : ℂ) : InBandlimitedSpace d σ (a • F) := by
  by_cases hd : d = 0
  · obtain ⟨b, hb⟩ := (ite_eq_left hd).mp hF
    exact (ite_eq_left hd).mpr ⟨a * b, fun x => by simp only [Pi.smul_apply, smul_eq_mul, hb]⟩
  · obtain ⟨φ, hφ, rfl⟩ := (ite_eq_right hd).mp hF
    exact (ite_eq_right hd).mpr ⟨a • φ, hφ.smul a,
      (inverseFourier_smul_of_smoothFrequency hφ a).symm⟩

 theorem InBandlimitedSpace.zero (d : ℕ) (σ : ℝ) :
    InBandlimitedSpace d σ (0 : E d → ℂ) := by
  by_cases hd : d = 0
  · exact (ite_eq_left hd).mpr ⟨0, fun _ => rfl⟩
  · refine (ite_eq_right hd).mpr ⟨0, ?_, ?_⟩
    · exact ⟨contDiff_const, by simpa only [HasCompactSupport, tsupport_zero] using
          (isCompact_empty : IsCompact (∅ : Set (E d))),
        by simp⟩
    · ext x
      simp [inverseFourier]

 theorem SmoothFrequency.mul_phase {d : ℕ} {σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency σ φ) (a : E d) :
    SmoothFrequency σ (fun ξ => φ ξ *
      Complex.exp (-Complex.I * ((∑ i : Fin d, a i * ξ i : ℝ) : ℂ))) := by
  have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : E d => ∑ i : Fin d, a i * ξ i) := by
    simpa only [coe_innerSL_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      star_trivial, mul_comm] using (innerSL ℝ a).contDiff
  have hreal := Complex.ofRealCLM.contDiff.comp hsum
  have hphase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ξ : E d => Complex.exp (-Complex.I *
        ((∑ i : Fin d, a i * ξ i : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hreal)
  refine ⟨hφ.1.mul hphase, hφ.2.1.mul_right, ?_⟩
  exact tsupport_mul_subset_left.trans hφ.2.2

 theorem inverseFourier_mul_phase {d : ℕ} (φ : E d → ℂ) (a x : E d) :
    inverseFourier (fun ξ => φ ξ *
      Complex.exp (-Complex.I * ((∑ i : Fin d, a i * ξ i : ℝ) : ℂ))) x =
      inverseFourier φ (x - a) := by
  unfold inverseFourier
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib, Complex.ofReal_sub]
  ring

 theorem InBandlimitedSpace.translate {d : ℕ} {σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d σ F) (a : E d) :
    InBandlimitedSpace d σ (fun x => F (x - a)) := by
  by_cases hd : d = 0
  · obtain ⟨b, hb⟩ := (ite_eq_left hd).mp hF
    exact (ite_eq_left hd).mpr ⟨b, fun x => hb (x - a)⟩
  · obtain ⟨φ, hφ, rfl⟩ := (ite_eq_right hd).mp hF
    exact (ite_eq_right hd).mpr ⟨_, hφ.mul_phase a, by ext x; exact (inverseFourier_mul_phase φ a x).symm⟩

 theorem SmoothFrequency.comp_add {d : ℕ} {ρ σ : ℝ} {φ : E d → ℂ}
    (hφ : SmoothFrequency ρ φ) (a : E d) (hσ : ρ + ‖a‖ ≤ σ) :
    SmoothFrequency σ (fun ξ => φ (ξ + a)) := by
  refine ⟨hφ.1.comp (by fun_prop),
    hφ.2.1.comp_isClosedEmbedding (Homeomorph.addRight a).isClosedEmbedding, ?_⟩
  intro ξ hξ
  have hpre := tsupport_comp_subset_preimage φ (continuous_id.add continuous_const) hξ
  have hb : ‖ξ + a‖ < ρ := by
    simpa only [Metric.mem_ball, dist_zero_right, Pi.add_apply, id_eq] using hφ.2.2 hpre
  have hnorm : ‖ξ‖ ≤ ‖ξ + a‖ + ‖a‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (ξ + a) a
  have hbσ : ‖ξ‖ < σ := by linarith
  simpa only [Metric.mem_ball, dist_zero_right] using hbσ

 theorem inverseFourier_comp_add {d : ℕ} (φ : E d → ℂ) (a x : E d) :
    inverseFourier (fun ξ => φ (ξ + a)) x =
      Complex.exp (-Complex.I * ((∑ i : Fin d, x i * a i : ℝ) : ℂ)) * inverseFourier φ x := by
  let H : E d → ℂ := fun ξ => φ ξ *
    Complex.exp (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ))
  have hphase (ξ : E d) : φ (ξ + a) *
      Complex.exp (Complex.I * ((∑ i : Fin d, x i * ξ i : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((∑ i : Fin d, x i * a i : ℝ) : ℂ)) * H (ξ + a) := by
    dsimp [H]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add]
    ring
  unfold inverseFourier
  simp_rw [hphase]
  rw [integral_const_mul, integral_add_right_eq_self]
  dsimp [H]
  ring

 theorem InBandlimitedSpace.modulate {d : ℕ} (hd : d ≠ 0) {ρ σ : ℝ} {F : E d → ℂ}
    (hF : InBandlimitedSpace d ρ F) (a : E d) (hσ : ρ + ‖a‖ ≤ σ) :
    InBandlimitedSpace d σ (fun x =>
      Complex.exp (-Complex.I * ((∑ i : Fin d, x i * a i : ℝ) : ℂ)) * F x) := by
  obtain ⟨φ, hφ, rfl⟩ := (ite_eq_right hd).mp hF
  exact (ite_eq_right hd).mpr ⟨_, hφ.comp_add a hσ,
    by ext x; exact (inverseFourier_comp_add φ a x).symm⟩

#print axioms InBandlimitedSpace.exists_schwartz
#print axioms InBandlimitedSpace.add
#print axioms InBandlimitedSpace.smul
#print axioms InBandlimitedSpace.translate
#print axioms InBandlimitedSpace.modulate

end Bandlimited
end
