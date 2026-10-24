module

public import Bandlimited.OneSidedDensity
public import Bandlimited.ConvexGaussianTheorem
public import Bandlimited.FiniteFamily

@[expose] public section
noncomputable section
namespace Bandlimited

/-- Full principal T11, using the proved fixed-bandwidth density theorem. -/
theorem convex_weighted_gaussian : ConvexWeightedGaussianStatement :=
  ConvexGaussian.convex_weighted_gaussian_of_one_sided_density one_sided_density

/-- Full principal T12 with the finite family chosen before the convex profile. -/
theorem finite_family : FiniteFamilyStatement :=
  finite_family_of_convex_weighted_gaussian convex_weighted_gaussian

#print axioms convex_weighted_gaussian
#print axioms finite_family
end Bandlimited
end
