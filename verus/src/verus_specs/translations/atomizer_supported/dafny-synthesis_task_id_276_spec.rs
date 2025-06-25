pub fn CylinderVolume(radius: f64, height: f64) -> (volume: f64)
    requires(radius > 0.0)
    requires(height > 0.0)
    ensures(|volume: f64| volume == 3.14159265359 * radius * radius * height)
{
}