pub fn SphereVolume(radius: f64) -> (volume: f64)
    requires(radius > 0.0)
    ensures(volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius)
{
}