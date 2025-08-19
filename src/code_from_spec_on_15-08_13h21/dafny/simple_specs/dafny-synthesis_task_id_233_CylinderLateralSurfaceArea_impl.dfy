//IMPL
method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * (radius * height) * 3.14
{
  /* code modified by LLM (iteration 1): removed invalid explanatory text that was causing compilation error */
  area := 2.0 * (radius * height) * 3.14;
}