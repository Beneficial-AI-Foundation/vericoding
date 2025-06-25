pub fn DPGD_GradientPerturbation(size: int, learning_rate: f64, noise_scale: f64, gradient_norm_bound: f64, iterations: int) -> (Para: f64, PrivacyLost: f64)
    requires(iterations >= 0)
    requires(size >= 0)
    requires(noise_scale >= 1.0)
    requires(-1.0 <= gradient_norm_bound <= 1.0)
{
}