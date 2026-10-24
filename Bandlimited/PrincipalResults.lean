module
public import Bandlimited.UniformGaussian
public import Bandlimited.SphericalTheorem
public import Bandlimited.KernelToBoundary
public import Bandlimited.BodyGauge
public import Bandlimited.UniformBodies
public import Bandlimited.PolynomialLifting
@[expose] public section
noncomputable section
namespace Bandlimited

 theorem bounded_norm_uniform : BoundedNormUniformStatement :=
   bounded_norm_uniform_of_kernels uniform_gaussian positive_spherical_quadrature

 theorem constant_sequence : ConstantSequenceStatement :=
   constant_sequence_of_bounded_norm_uniform bounded_norm_uniform

 theorem even_functions : EvenFunctionsStatement :=
   even_functions_of_constant_sequence constant_sequence

 theorem odd_functions : OddFunctionsStatement :=
   odd_functions_of_constant_sequence constant_sequence

 theorem consecutive_degrees : ConsecutiveDegreesStatement :=
   consecutive_degrees_of_constant_sequence constant_sequence

 theorem all_bodies_uniform : AllBodiesUniformStatement :=
   all_bodies_uniform_of_bounded_norm_uniform bounded_norm_uniform

 theorem principal_results : PrincipalResultsStatement :=
   ⟨constant_sequence, bounded_norm_uniform, consecutive_degrees, even_functions,
    odd_functions, all_bodies_uniform, uniform_gaussian, one_sided_density,
    tensor_density, fourier_cutoff, convex_weighted_gaussian, finite_family,
    positive_spherical_quadrature⟩

#print axioms constant_sequence
#print axioms bounded_norm_uniform
#print axioms consecutive_degrees
#print axioms even_functions
#print axioms odd_functions
#print axioms all_bodies_uniform
#print axioms uniform_gaussian
#print axioms one_sided_density
#print axioms tensor_density
#print axioms fourier_cutoff
#print axioms convex_weighted_gaussian
#print axioms finite_family
#print axioms positive_spherical_quadrature
#print axioms principal_results
end Bandlimited
end
