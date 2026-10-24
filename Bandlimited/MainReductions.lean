module

public import Bandlimited.Definitions
public import Mathlib.Data.Nat.Find
public import Lean.Elab.Tactic.Omega

/-!
Parity and sequence reductions for the principal approximation results.
The dependencies in each theorem are explicit propositions; no analytic
approximation conclusion is assumed as an axiom. Reuses Mathlib's
homeomorphism/frontier and homogeneous-polynomial APIs (Apache 2.0).
-/

@[expose] public section
noncomputable section
open Set

namespace Bandlimited

private def ambientNeg (d : ℕ) : E d ≃ₜ E d where
  toFun x := -x
  invFun x := -x
  left_inv := neg_neg
  right_inv := neg_neg
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

theorem neg_mem_frontier_of_symmetric {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) {x : E d} (hx : x ∈ frontier K) :
    -x ∈ frontier K := by
  have himage : ambientNeg d '' K = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hK z).1 hz
    · intro hy
      exact ⟨-y, (hK y).1 hy, neg_neg y⟩
  have hf := (ambientNeg d).image_frontier K
  rw [himage] at hf
  rw [← hf]
  exact ⟨x, hx, rfl⟩

def boundaryNeg {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) :
    C(↥(frontier K), ↥(frontier K)) where
  toFun x := ⟨-(x : E d), neg_mem_frontier_of_symmetric hK x.property⟩
  continuous_toFun := continuous_subtype_val.neg.subtype_mk _

@[simp] theorem boundaryNeg_val {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (x : ↥(frontier K)) :
    (boundaryNeg hK x : E d) = -(x : E d) := rfl

@[simp] theorem boundaryNeg_involutive {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (x : ↥(frontier K)) :
    boundaryNeg hK (boundaryNeg hK x) = x := by
  apply Subtype.ext
  exact neg_neg _

def evenPart {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (f : C(↥(frontier K), ℝ)) :
    C(↥(frontier K), ℝ) :=
  (1 / 2 : ℝ) • (f + f.comp (boundaryNeg hK))

def oddPart {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (f : C(↥(frontier K), ℝ)) :
    C(↥(frontier K), ℝ) :=
  (1 / 2 : ℝ) • (f - f.comp (boundaryNeg hK))

theorem evenPart_even {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (f : C(↥(frontier K), ℝ)) :
    EvenOnBoundary (evenPart hK f) := by
  intro x y hxy
  have hy : y = boundaryNeg hK x := Subtype.ext hxy
  subst y
  simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.comp_apply, boundaryNeg_involutive, smul_eq_mul]
  ring

theorem oddPart_odd {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (f : C(↥(frontier K), ℝ)) :
    OddOnBoundary (oddPart hK f) := by
  intro x y hxy
  have hy : y = boundaryNeg hK x := Subtype.ext hxy
  subst y
  simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.comp_apply, boundaryNeg_involutive, smul_eq_mul]
  ring

theorem evenPart_add_oddPart {d : ℕ} {K : Set (E d)}
    (hK : ∀ x, x ∈ K ↔ -x ∈ K) (f : C(↥(frontier K), ℝ))
    (x : ↥(frontier K)) : evenPart hK f x + oddPart hK f x = f x := by
  simp only [evenPart, oddPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.comp_apply, smul_eq_mul]
  ring

theorem boundary_error_add {d : ℕ} {K : Set (E d)}
    {p q : Polynomial d} {f g : ↥(frontier K) → ℝ} {ε δ : ℝ}
    (hp : BoundaryErrorLT K p f ε) (hq : BoundaryErrorLT K q g δ) :
    BoundaryErrorLT K (p + q) (fun x => f x + g x) (ε + δ) := by
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨b, hb, hqb⟩ := hq
  refine ⟨a + b, add_lt_add ha hb, ?_⟩
  intro x
  have heval : evalPolynomial (p + q) (x : E d) =
      evalPolynomial p (x : E d) + evalPolynomial q (x : E d) := by
    simp [evalPolynomial]
  rw [heval]
  calc
    |evalPolynomial p (x : E d) + evalPolynomial q (x : E d) - (f x + g x)| =
        |(evalPolynomial p (x : E d) - f x) +
          (evalPolynomial q (x : E d) - g x)| := by congr 1; ring
    _ ≤ |evalPolynomial p (x : E d) - f x| +
          |evalPolynomial q (x : E d) - g x| := abs_add_le _ _
    _ ≤ a + b := add_le_add (hpa x) (hqb x)

theorem consecutive_degrees_of_even_and_odd
    (heven : EvenFunctionsStatement) (hodd : OddFunctionsStatement) :
    ConsecutiveDegreesStatement := by
  intro d K hK f ε hε
  obtain ⟨ne, hne⟩ := heven d K hK (evenPart hK.2.2.2 f)
    (evenPart_even hK.2.2.2 f) (ε / 2) (by positivity)
  obtain ⟨no, hno⟩ := hodd d K hK (oddPart hK.2.2.2 f)
    (oddPart_odd hK.2.2.2 f) (ε / 2) (by positivity)
  refine ⟨2 * max ne no + 2, ?_⟩
  intro n hn
  let m := n / 2
  have hme : ne ≤ m := by dsimp [m]; omega
  have hmo : no ≤ m := by dsimp [m]; omega
  have hpar : n = 2 * m ∨ n = 2 * m + 1 := by dsimp [m]; omega
  rcases hpar with hpar | hpar
  · obtain ⟨p, hp, hep⟩ := hne m hme
    obtain ⟨q, hq, hoq⟩ := hno m hmo
    refine ⟨p, q, ?_, ?_, ?_⟩
    · simpa only [hpar] using hp
    · simpa only [hpar] using hq
    · have hsum := boundary_error_add hep hoq
      have hf : (fun x => evenPart hK.2.2.2 f x + oddPart hK.2.2.2 f x) = f :=
        funext (evenPart_add_oddPart hK.2.2.2 f)
      simpa only [hf, add_halves] using hsum
  · obtain ⟨p, hp, hep⟩ := hne (m + 1) (by omega)
    obtain ⟨q, hq, hoq⟩ := hno m hmo
    refine ⟨q, p, ?_, ?_, ?_⟩
    · simpa only [hpar] using hq
    · convert hp using 1; omega
    · have hsum := boundary_error_add hep hoq
      have hf : (fun x => evenPart hK.2.2.2 f x + oddPart hK.2.2.2 f x) = f :=
        funext (evenPart_add_oddPart hK.2.2.2 f)
      simpa only [hf, add_halves, add_comm p q] using hsum

#print axioms neg_mem_frontier_of_symmetric
#print axioms evenPart_even
#print axioms oddPart_odd
#print axioms evenPart_add_oddPart
#print axioms boundary_error_add
#print axioms consecutive_degrees_of_even_and_odd

/-- The all-large-degrees assertion supplies an actual single sequence.
The choice of polynomial at degree 2n has accuracy indexed by the largest
admissible tolerance level at or below n. -/
theorem sequence_of_eventual_constant_approximation {d : ℕ} (K : Set (E d))
    (h : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∃ p : Polynomial d, p.IsHomogeneous (2 * n) ∧
        BoundaryErrorLT K p (fun _ => 1) ε) :
    ∃ p : ℕ → Polynomial d, (∀ n, (p n).IsHomogeneous (2 * n)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        BoundaryErrorLT K (p n) (fun _ => 1) ε := by
  classical
  let good : ℕ → ℕ → Prop := fun n m =>
    ∃ p : Polynomial d, p.IsHomogeneous (2 * n) ∧
      BoundaryErrorLT K p (fun _ => 1) (2 / ((m : ℝ) + 1))
  have hbase (n : ℕ) : good n 0 := by
    refine ⟨0, MvPolynomial.isHomogeneous_zero (Fin d) ℝ (2 * n), 1, ?_, ?_⟩
    · norm_num
    · intro x
      simp [evalPolynomial]
  let level : ℕ → ℕ := fun n => Nat.findGreatest (good n) n
  have hlevel (n : ℕ) : good n (level n) :=
    Nat.findGreatest_spec (Nat.zero_le n) (hbase n)
  choose p hp herr using hlevel
  refine ⟨p, hp, ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hsmall : 2 / ((M : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < (M : ℝ) + 1)).2
    have hmul := (div_lt_iff₀ hε).1 hM
    nlinarith
  obtain ⟨n₀, hn₀⟩ := h (2 / ((M : ℝ) + 1)) (by positivity)
  refine ⟨max n₀ M, ?_⟩
  intro n hn
  have hgood : good n M := hn₀ n (le_trans (le_max_left _ _) hn)
  have hMl : M ≤ level n :=
    Nat.le_findGreatest (le_trans (le_max_right _ _) hn) hgood
  have htol : 2 / ((level n : ℝ) + 1) ≤ 2 / ((M : ℝ) + 1) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (level n : ℝ) + 1)
      (by positivity : 0 < (M : ℝ) + 1)).2
    have hcast : (M : ℝ) ≤ (level n : ℝ) := by exact_mod_cast hMl
    linarith
  obtain ⟨b, hb, hpb⟩ := herr n
  exact ⟨b, (hb.trans_le htol).trans hsmall, hpb⟩

theorem constant_sequence_of_all_bodies_uniform
    (h : AllBodiesUniformStatement) : ConstantSequenceStatement := by
  intro d K hK
  apply sequence_of_eventual_constant_approximation K
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := h d ε hε
  exact ⟨n₀, fun n hn => hn₀ n hn K hK⟩

#print axioms sequence_of_eventual_constant_approximation
#print axioms constant_sequence_of_all_bodies_uniform

end Bandlimited
end
