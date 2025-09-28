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
function CrossProductHelper(a: Vector3D, b: Vector3D): (real, real, real)
{
  (a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x)
}

lemma CrossPerpendicularLemma(a: Vector3D, b: Vector3D, result: Vector3D)
  requires result.x == a.y * b.z - a.z * b.y
  requires result.y == a.z * b.x - a.x * b.z
  requires result.z == a.x * b.y - a.y * b.x
  ensures DotProduct(result, a) == 0.0
  ensures DotProduct(result, b) == 0.0
{
  // Expand the dot products using the cross product components
  assert DotProduct(result, a) == result.x * a.x + result.y * a.y + result.z * a.z;
  assert DotProduct(result, b) == result.x * b.x + result.y * b.y + result.z * b.z;
  // These will simplify to 0 through algebraic identities
}

lemma CrossAntiCommutativeLemma(a: Vector3D, b: Vector3D, result: Vector3D)
  requires result.x == a.y * b.z - a.z * b.y
  requires result.y == a.z * b.x - a.x * b.z
  requires result.z == a.x * b.y - a.y * b.x
  ensures result.x == -(b.y * a.z - b.z * a.y)
  ensures result.y == -(b.z * a.x - b.x * a.z)
  ensures result.z == -(b.x * a.y - b.y * a.x)
{
  // Follows directly from the anti-commutative property of subtraction
  assert -(b.y * a.z - b.z * a.y) == -(b.y * a.z) + b.z * a.y == a.y * b.z - a.z * b.y;
  assert -(b.z * a.x - b.x * a.z) == -(b.z * a.x) + b.x * a.z == a.z * b.x - a.x * b.z;
  assert -(b.x * a.y - b.y * a.x) == -(b.x * a.y) + b.y * a.x == a.x * b.y - a.y * b.x;
}

/* helper modified by LLM (iteration 3): Added requires AreParallel precondition and proper proof */
lemma CrossZeroLemma(a: Vector3D, b: Vector3D, result: Vector3D)
  requires result.x == a.y * b.z - a.z * b.y
  requires result.y == a.z * b.x - a.x * b.z
  requires result.z == a.x * b.y - a.y * b.x
  requires AreParallel(a, b)
  ensures result.x == 0.0 && result.y == 0.0 && result.z == 0.0
{
  if a.x == 0.0 && a.y == 0.0 && a.z == 0.0 {
    // If a is zero vector, all cross product components are zero
    assert result.x == 0.0 * b.z - 0.0 * b.y == 0.0 - 0.0 == 0.0;
    assert result.y == 0.0 * b.x - 0.0 * b.z == 0.0 - 0.0 == 0.0;
    assert result.z == 0.0 * b.y - 0.0 * b.x == 0.0 - 0.0 == 0.0;
  } else if b.x == 0.0 && b.y == 0.0 && b.z == 0.0 {
    // If b is zero vector, all cross product components are zero
    assert result.x == a.y * 0.0 - a.z * 0.0 == 0.0 - 0.0 == 0.0;
    assert result.y == a.z * 0.0 - a.x * 0.0 == 0.0 - 0.0 == 0.0;
    assert result.z == a.x * 0.0 - a.y * 0.0 == 0.0 - 0.0 == 0.0;
  } else {
    // If both are non-zero but parallel, there exists some scalar k such that a = k * b
    // The cross product components must evaluate to zero
    assert a.x * b.y - a.y * b.x == 0.0;
    assert a.y * b.z - a.z * b.y == 0.0;
    assert a.z * b.x - a.x * b.z == 0.0;
  }
}
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
/* code modified by LLM (iteration 3): Only call CrossZeroLemma when vectors are parallel */
{
  var x := a.y * b.z - a.z * b.y;
  var y := a.z * b.x - a.x * b.z;
  var z := a.x * b.y - a.y * b.x;
  result := Vector3D(x, y, z);
  
  // Call lemmas to verify the postconditions
  CrossPerpendicularLemma(a, b, result);
  CrossAntiCommutativeLemma(a, b, result);
  
  // Only call CrossZeroLemma if vectors are parallel to avoid precondition violation
  if (AreParallel(a, b)) {
    CrossZeroLemma(a, b, result);
  }
}
// </vc-code>
