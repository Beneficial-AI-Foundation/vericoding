// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  area := radius * radius;
}
// </vc-code>
