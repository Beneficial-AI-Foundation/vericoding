pub fn CylinderVolume(radius: real, height: real) -> (volume: real)
    requires(radius > 0.0)
    requires(height > 0.0)
    ensures(|volume: real| volume == 3.14159265359 * radius * radius * height)
{
}