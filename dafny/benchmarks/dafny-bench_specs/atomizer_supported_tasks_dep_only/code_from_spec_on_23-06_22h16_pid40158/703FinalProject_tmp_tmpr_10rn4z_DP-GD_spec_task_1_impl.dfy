//IMPL 
method DPGD_GradientPerturbation (size:int, learning_rate:real, noise_scale:real, gradient_norm_bound:real, iterations:int) returns (Para:real, PrivacyLost:real)
  requires iterations>=0
  requires size>=0
  requires noise_scale >= 1.0
  requires -1.0 <= gradient_norm_bound <= 1.0
{
    Para := 0.0;
    var i := 0;
    
    while i < iterations
    {
        var simulated_gradient := if i % 2 == 0 then 0.1 else -0.1;
        
        var clipped_gradient := if simulated_gradient > gradient_norm_bound then gradient_norm_bound
                               else if simulated_gradient < -gradient_norm_bound then -gradient_norm_bound
                               else simulated_gradient;
        
        var noise := 1.0 / noise_scale;
        var noisy_gradient := clipped_gradient + noise;
        
        Para := Para - learning_rate * noisy_gradient;
        i := i + 1;
    }
    
    PrivacyLost := if iterations > 0 then (iterations as real) / (noise_scale * noise_scale) else 0.0;
}