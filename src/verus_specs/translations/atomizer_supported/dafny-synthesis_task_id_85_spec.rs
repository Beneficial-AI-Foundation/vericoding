pub fn SphereSurfaceArea(radius: f64) -> (area: f64)
    requires(radius > 0.0)
    ensures(area == 4.0 * 3.14159265358979323846 * radius * radius)
{
}