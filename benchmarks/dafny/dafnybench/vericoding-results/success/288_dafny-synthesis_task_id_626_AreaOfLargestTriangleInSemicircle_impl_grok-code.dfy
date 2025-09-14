

// <vc-helpers>
// No additional helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// <vc-code>
{
  area := radius * radius;
}
// </vc-code>

