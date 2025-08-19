//IMPL
method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
  requires radius > 0.0 && height > 0.0
  ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
{
  /* code modified by LLM (iteration 1): removed invalid text outside Dafny code block */
  area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}