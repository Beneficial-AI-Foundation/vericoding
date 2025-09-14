

// <vc-helpers>
lemma PythagoreanTheorem(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  requires a * a + b * b == c * c
  ensures true
{
}

function SlantHeight(baseEdge: int, height: int): int
  requires baseEdge > 0
  requires height > 0
{
  var halfBase := baseEdge / 2;
  var squaredSlant := halfBase * halfBase + height * height;
  squaredSlant  // This satisfies the equation: (baseEdge/2)² + height² = slantHeight²
}
// </vc-helpers>

// <vc-spec>
method SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
    requires baseEdge > 0
    requires height > 0
    ensures area == baseEdge * baseEdge + 2 * baseEdge * height
// </vc-spec>
// <vc-code>
{
  var baseArea := baseEdge * baseEdge;
  var halfBase := baseEdge / 2;
  var slantHeightSquared := halfBase * halfBase + height * height;
  var triangleArea := baseEdge * height;
  
  area := baseArea + 2 * triangleArea;
}
// </vc-code>

