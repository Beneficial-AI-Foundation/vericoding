method DPGD_GradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
 requires iterations>=0
 requires size>=0
 requires noise_scale >= 1.0
 requires -1.0 <= gradient_norm_bound <= 1.0
{
    Para := 0.0;
    var i := 0;
    
    while i < iterations
        invariant 0 <= i <= iterations
    {
        // Simulate gradient computation and clipping
        var gradient := if i % 2 == 0 then gradient_norm_bound else -gradient_norm_bound;
        
        // Add noise for privacy (noise magnitude inversely related to noise_scale)
        var noise := 1.0 / noise_scale;
        var noisy_gradient := gradient + noise;
        
        // Parameter update
        Para := Para - learning_rate * noisy_gradient;
        
        i := i + 1;
    }
    
    // Privacy loss calculation: inversely related to noise_scale, proportional to iterations
    /* code modified by LLM (iteration 1): Changed real(iterations) to iterations as real for correct type conversion */
    PrivacyLost := (iterations as real) / noise_scale;
}