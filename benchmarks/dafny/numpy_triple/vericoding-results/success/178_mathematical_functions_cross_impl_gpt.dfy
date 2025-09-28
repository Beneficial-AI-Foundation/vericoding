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
/* helper modified by LLM (iteration 3): cross product helper for concise construction */
function CrossVec(a: Vector3D, b: Vector3D): Vector3D
{
  Vector3D(
    a.y * b.z - a.z * b.y,
    a.z * b.x - a.x * b.z,
    a.x * b.y - a.y * b.x
  )
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
{
  /* code modified by LLM (iteration 3): compute cross product and prove orthogonality via algebraic asserts */
  result := CrossVec(a, b);

  // Prove perpendicularity to a
  var t1 := a.x * a.y * b.z;
  var t2 := a.x * a.z * b.y;
  var t3 := a.y * a.z * b.x;
  assert DotProduct(result, a) ==
    (a.y * b.z - a.z * b.y) * a.x +
    (a.z * b.x - a.x * b.z) * a.y +
    (a.x * b.y - a.y * b.x) * a.z;
  assert (a.y * b.z - a.z * b.y) * a.x +
         (a.z * b.x - a.x * b.z) * a.y +
         (a.x * b.y - a.y * b.x) * a.z
       == a.y * b.z * a.x - a.z * b.y * a.x + a.z * b.x * a.y - a.x * b.z * a.y + a.x * b.y * a.z - a.y * b.x * a.z;
  assert a.y * b.z * a.x == t1;
  assert a.x * b.z * a.y == t1;
  assert a.z * b.y * a.x == t2;
  assert a.x * b.y * a.z == t2;
  assert a.z * b.x * a.y == t3;
  assert a.y * b.x * a.z == t3;
  assert a.y * b.z * a.x - a.z * b.y * a.x + a.z * b.x * a.y - a.x * b.z * a.y + a.x * b.y * a.z - a.y * b.x * a.z
       == t1 - t2 + t3 - t1 + t2 - t3;
  assert t1 - t2 + t3 - t1 + t2 - t3 == 0.0;
  assert DotProduct(result, a) == 0.0;

  // Prove perpendicularity to b
  var u1 := a.y * b.x * b.z;
  var u2 := a.z * b.x * b.y;
  var u3 := a.x * b.y * b.z;
  assert DotProduct(result, b) ==
    (a.y * b.z - a.z * b.y) * b.x +
    (a.z * b.x - a.x * b.z) * b.y +
    (a.x * b.y - a.y * b.x) * b.z;
  assert (a.y * b.z - a.z * b.y) * b.x +
         (a.z * b.x - a.x * b.z) * b.y +
         (a.x * b.y - a.y * b.x) * b.z
       == a.y * b.z * b.x - a.z * b.y * b.x + a.z * b.x * b.y - a.x * b.z * b.y + a.x * b.y * b.z - a.y * b.x * b.z;
  assert a.y * b.z * b.x == u1;
  assert a.y * b.x * b.z == u1;
  assert a.z * b.y * b.x == u2;
  assert a.z * b.x * b.y == u2;
  assert a.x * b.z * b.y == u3;
  assert a.x * b.y * b.z == u3;
  assert a.y * b.z * b.x - a.z * b.y * b.x + a.z * b.x * b.y - a.x * b.z * b.y + a.x * b.y * b.z - a.y * b.x * b.z
       == u1 - u2 + u2 - u3 + u3 - u1;
  assert u1 - u2 + u2 - u3 + u3 - u1 == 0.0;
  assert DotProduct(result, b) == 0.0;

  // Assist solver for zero when parallel
  if AreParallel(a, b) {
    if a.x == 0.0 && a.y == 0.0 && a.z == 0.0 {
      assert result.x == 0.0 && result.y == 0.0 && result.z == 0.0;
    } else if b.x == 0.0 && b.y == 0.0 && b.z == 0.0 {
      assert result.x == 0.0 && result.y == 0.0 && result.z == 0.0;
    } else {
      assert a.y * b.z - a.z * b.y == 0.0 &&
             a.z * b.x - a.x * b.z == 0.0 &&
             a.x * b.y - a.y * b.x == 0.0;
      assert result.x == 0.0 && result.y == 0.0 && result.z == 0.0;
    }
  }
}
// </vc-code>
