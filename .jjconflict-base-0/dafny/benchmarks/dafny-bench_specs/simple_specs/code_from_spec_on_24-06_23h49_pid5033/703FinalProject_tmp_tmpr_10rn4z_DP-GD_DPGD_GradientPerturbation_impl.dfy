//IMPL 
method DPGD_GradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
 requires iterations>=0
 requires size>=0
 requires noise_scale >= 1.0
 requires -1.0 <= gradient_norm_bound <= 1.0
{
    Para := 0.0;
    PrivacyLost := 0.0;
    
    var i := 0;
    while i < iterations
        invariant 0 <= i <= iterations
    {
        // Simulate gradient descent with noise perturbation
        var gradient := gradient_norm_bound;
        var noise := noise_scale * 0.1; // Simple noise simulation
        var perturbed_gradient := gradient + noise;
        
        Para := Para - learning_rate * perturbed_gradient;
        
        // Privacy loss accumulates with each iteration
        PrivacyLost := PrivacyLost + (1.0 / noise_scale);
        
        i := i + 1;
    }
}