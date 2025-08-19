//IMPL
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  requires radius > 0
  ensures area == radius * radius
{
  /* code modified by LLM (iteration 1): ensured proper assignment satisfies postcondition */
  area := radius * radius;
}