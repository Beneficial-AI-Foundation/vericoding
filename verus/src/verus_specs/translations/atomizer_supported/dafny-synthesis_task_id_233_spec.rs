pub fn CylinderLateralSurfaceArea(radius: f64, height: f64) -> (area: f64)
    requires(radius > 0.0 && height > 0.0)
    ensures(|area: f64| area == 2.0 * (radius * height) * 3.14)
{
}