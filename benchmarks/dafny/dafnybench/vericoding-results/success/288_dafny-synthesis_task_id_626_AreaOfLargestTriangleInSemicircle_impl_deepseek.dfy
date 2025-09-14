

// <vc-helpers>
lemma TriangleAreaLemma(radius: int, angle: int) 
    requires radius > 0
    ensures 2 * radius * radius * angle * (180 - angle) == radius * radius * angle * (180 - angle) * 2
{
}
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

