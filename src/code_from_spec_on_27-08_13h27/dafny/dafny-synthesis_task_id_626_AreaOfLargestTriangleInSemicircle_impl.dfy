// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// </vc-spec>

// <vc-code>
method AreaOfLargestTriangleInSemicircleImpl(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
{
    area := radius * radius;
}
// </vc-code>
