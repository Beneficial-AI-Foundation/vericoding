pub fn ConeVolume(radius: f64, height: f64) -> (volume: f64)
    requires(radius > 0.0 && height > 0.0)
    ensures(|volume: f64| volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height)
{
}