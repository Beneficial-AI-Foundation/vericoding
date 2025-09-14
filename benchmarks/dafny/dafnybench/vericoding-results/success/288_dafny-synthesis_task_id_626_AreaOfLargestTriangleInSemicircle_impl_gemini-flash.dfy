

// <vc-helpers>
lemma AreaOfLargestTriangleInSemicircleLemma(radius: int)
  requires radius > 0
  ensures radius * radius == (radius * radius) // Changed to make sense.
{
  assert radius * radius == radius * radius;
}
// </vc-helpers>

// <vc-spec>
method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
    requires radius > 0
    ensures area == radius * radius
// </vc-spec>
// <vc-code>
{
  // The largest triangle that can be inscribed in a semicircle has its base along the diameter
  // and its apex at any point on the arc.
  // When the apex is at a point on the arc such that the triangle is isosceles (the two
  //  sides from the apex to the diameter ends are equal), its height is maximized.
  // The base of such a triangle is the diameter of the semicircle, which is 2 * radius.
  // The height of such a triangle is the radius of the semicircle (when the apex is exactly
  //  above the center of the diameter).
  // The area of a triangle is (1/2) * base * height.
  // Area = (1/2) * (2 * radius) * radius = radius * radius.

  // We simply calculate radius * radius and assign it to area.
  // The postcondition ensures area == radius * radius.

  area := radius * radius;
  // AreaOfLargestTriangleInSemicircleLemma(radius); // The lemma is not needed and its postcondition was the one failing.
}
// </vc-code>

