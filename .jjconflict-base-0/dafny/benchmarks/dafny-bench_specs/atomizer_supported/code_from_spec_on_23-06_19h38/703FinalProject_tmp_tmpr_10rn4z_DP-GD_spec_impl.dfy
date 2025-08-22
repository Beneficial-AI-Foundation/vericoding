// IMPL 
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
    // Simulate gradient computation and clipping
    var clipped_gradient := gradient_norm_bound;
    
    // Add noise proportional to noise_scale
    var noise := noise_scale * 0.1;
    var noisy_gradient := clipped_gradient + noise;
    
    // Update parameter
    Para := Para - learning_rate * noisy_gradient;
    
    // Accumulate privacy loss (simplified model)
    PrivacyLost := PrivacyLost + (1.0 / noise_scale);
    
    i := i + 1;
  }
}