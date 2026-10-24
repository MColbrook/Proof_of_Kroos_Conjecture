module

public import Bandlimited.Definitions
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Pullback of an actual multivariate homogeneous polynomial by a linear map.
The degree is preserved in the homogeneous sense, including the zero polynomial.
The proof reuses Mathlib's homogeneous substitution theorem (Apache 2.0). -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Bandlimited

def linearSubstitution {d e : ℕ} (f : E d →ₗ[ℝ] E e) (i : Fin e) : Polynomial d :=
  ∑ j : Fin d, MvPolynomial.C (f (PiLp.single 2 j 1) i) * MvPolynomial.X j

theorem linearSubstitution_homogeneous {d e : ℕ} (f : E d →ₗ[ℝ] E e)
    (i : Fin e) : (linearSubstitution f i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C (Fin d) (f (PiLp.single 2 j 1) i)).mul
      (MvPolynomial.isHomogeneous_X ℝ j)

theorem linearSubstitution_eval {d e : ℕ} (f : E d →ₗ[ℝ] E e)
    (i : Fin e) (x : E d) : evalPolynomial (linearSubstitution f i) x = f x i := by
  classical
  have hx : x = ∑ j : Fin d, x j • PiLp.single 2 j 1 := by
    ext k
    simp [PiLp.single_apply, Pi.single_apply]
  have hf : f x = ∑ j : Fin d, x j • f (PiLp.single 2 j 1) := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  rw [hf]
  simp only [evalPolynomial, linearSubstitution, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def polynomialPullback {d e : ℕ} (f : E d →ₗ[ℝ] E e) (p : Polynomial e) : Polynomial d :=
  MvPolynomial.aeval (linearSubstitution f) p

theorem polynomialPullback_homogeneous {d e k : ℕ} (f : E d →ₗ[ℝ] E e)
    {p : Polynomial e} (hp : p.IsHomogeneous k) :
    (polynomialPullback f p).IsHomogeneous k := by
  simpa only [polynomialPullback, one_mul] using
    hp.aeval (linearSubstitution f) (linearSubstitution_homogeneous f)

theorem polynomialPullback_eval {d e : ℕ} (f : E d →ₗ[ℝ] E e)
    (p : Polynomial e) (x : E d) :
    evalPolynomial (polynomialPullback f p) x = evalPolynomial p (f x) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [polynomialPullback, evalPolynomial]
  | add p q hp hq => simp [polynomialPullback, evalPolynomial, map_add] at *; rw [hp, hq]
  | mul_X p i hp =>
      change MvPolynomial.eval (fun i => x i)
        ((MvPolynomial.aeval (linearSubstitution f)) (p * MvPolynomial.X i)) = _
      rw [map_mul, MvPolynomial.aeval_X, map_mul]
      change evalPolynomial (polynomialPullback f p) x *
        evalPolynomial (linearSubstitution f i) x = _
      rw [hp, linearSubstitution_eval]
      simp only [evalPolynomial, map_mul, MvPolynomial.eval_X]

#print axioms linearSubstitution_eval
#print axioms polynomialPullback_homogeneous
#print axioms polynomialPullback_eval

end Bandlimited
end
