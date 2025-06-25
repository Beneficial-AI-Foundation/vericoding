pub fn cylinder_surface_area(radius: f64, height: f64) -> (area: f64)
    requires(radius > 0.0 && height > 0.0)
    ensures(|area: f64| area == 2.0 * 3.14159265358979323846 * radius * (radius + height))
{
}