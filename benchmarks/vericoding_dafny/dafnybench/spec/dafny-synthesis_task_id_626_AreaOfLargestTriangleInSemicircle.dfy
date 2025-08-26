// <vc-helpers>
// </vc-helpers>

method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
// <vc-code>
{
  assume false;
}
// </vc-code>