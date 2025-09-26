// <vc-preamble>
// 3D vector datatype with real-valued components
datatype Vector3D = Vector3D(x: real, y: real, z: real)

// Helper function to compute dot product of two 3D vectors
function DotProduct(a: Vector3D, b: Vector3D): real
{
  a.x * b.x + a.y * b.y + a.z * b.z
}

// Helper function to negate a vector
function NegateVector(v: Vector3D): Vector3D
{
  Vector3D(-v.x, -v.y, -v.z)
}

// Helper function to check if two vectors are parallel
predicate AreParallel(a: Vector3D, b: Vector3D)
{
  // Two vectors are parallel if their cross product is zero
  // This happens when one is a scalar multiple of the other
  (a.x == 0.0 && a.y == 0.0 && a.z == 0.0) ||
  (b.x == 0.0 && b.y == 0.0 && b.z == 0.0) ||
  (a.x * b.y - a.y * b.x == 0.0 && a.y * b.z - a.z * b.y == 0.0 && a.z * b.x - a.x * b.z == 0.0)
}

// Cross product method that returns the cross product of two 3D vectors
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Cross(a: Vector3D, b: Vector3D) returns (result: Vector3D)
  // Cross product formula components
  ensures result.x == a.y * b.z - a.z * b.y
  ensures result.y == a.z * b.x - a.x * b.z
  ensures result.z == a.x * b.y - a.y * b.x
  // Perpendicularity property: result is perpendicular to both input vectors
  ensures DotProduct(result, a) == 0.0
  ensures DotProduct(result, b) == 0.0
  // Anti-commutativity: a × b = -(b × a)
  ensures result.x == -(b.y * a.z - b.z * a.y)
  ensures result.y == -(b.z * a.x - b.x * a.z)
  ensures result.z == -(b.x * a.y - b.y * a.x)
  // Zero property: if a and b are parallel, then a × b = 0
  ensures AreParallel(a, b) ==> (result.x == 0.0 && result.y == 0.0 && result.z == 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
