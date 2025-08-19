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
        invariant PrivacyLost >= 0.0
    {
        // Simulate gradient computation and clipping
        var gradient := if i % 2 == 0 then gradient_norm_bound else -gradient_norm_bound;
        
        // Add noise for privacy (noise proportional to noise_scale)
        var noise := if i % 3 == 0 then 1.0 / noise_scale else -1.0 / noise_scale;
        var noisy_gradient := gradient + noise;
        
        // Update parameters
        Para := Para - learning_rate * noisy_gradient;
        
        // Accumulate privacy loss (inversely related to noise_scale)
        PrivacyLost := PrivacyLost + 1.0 / noise_scale;
        
        i := i + 1;
    }
}