pub fn SquarePyramidSurfaceArea(baseEdge: int, height: int) -> (area: int)
    requires(baseEdge > 0)
    requires(height > 0)
    ensures(|area: int| area == baseEdge * baseEdge + 2 * baseEdge * height)
{
}