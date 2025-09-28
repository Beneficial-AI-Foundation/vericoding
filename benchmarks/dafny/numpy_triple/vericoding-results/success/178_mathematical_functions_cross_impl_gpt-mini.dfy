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
/* helper modified by LLM (iteration 2): CrossPerpendicular proof */
lemma CrossPerpendicular(a: Vector3D, b: Vector3D)
  ensures DotProduct(Vector3D(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x), a) == 0.0
  ensures DotProduct(Vector3D(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x), b) == 0.0
{
  var cx := a.y*b.z - a.z*b.y;
  var cy := a.z*b.x - a.x*b.z;
  var cz := a.x*b.y - a.y*b.x;
  var e1 := cx*a.x + cy*a.y + cz*a.z;
  assert e1 == (a.x*a.y*b.z - a.x*a.z*b.y) + (a.y*a.z*b.x - a.y*a.x*b.z) + (a.z*a.x*b.y - a.z*a.y*b.x);
  assert a.x*a.y*b.z - a.y*a.x*b.z == 0.0;
  assert -a.x*a.z*b.y + a.z*a.x*b.y == 0.0;
  assert a.y*a.z*b.x - a.z*a.y*b.x == 0.0;
  assert e1 == 0.0;
  assert DotProduct(Vector3D(cx,cy,cz), a) == 0.0;

  var e2 := cx*b.x + cy*b.y + cz*b.z;
  assert e2 == (a.y*b.z*b.x - a.z*b.y*b.x) + (a.z*b.x*b.y - a.x*b.z*b.y) + (a.x*b.y*b.z - a.y*b.x*b.z);
  assert a.y*b.z*b.x - a.y*b.x*b.z == 0.0;
  assert -a.z*b.y*b.x + a.z*b.x*b.y == 0.0;
  assert a.x*b.y*b.z - a.x*b.z*b.y == 0.0;
  assert e2 == 0.0;
  assert DotProduct(Vector3D(cx,cy,cz), b) == 0.0;
}

/* helper modified by LLM (iteration 2): CrossAntiCommutative proof */
lemma CrossAntiCommutative(a: Vector3D, b: Vector3D)
  ensures a.y*b.z - a.z*b.y == -(b.y*a.z - b.z*a.y)
  ensures a.z*b.x - a.x*b.z == -(b.z*a.x - b.x*a.z)
  ensures a.x*b.y - a.y*b.x == -(b.x*a.y - b.y*a.x)
{
  assert a.y*b.z - a.z*b.y == -(b.y*a.z) + (b.z*a.y);
  assert -(b.y*a.z) + (b.z*a.y) == -(b.y*a.z - b.z*a.y);
  assert a.z*b.x - a.x*b.z == -(b.z*a.x - b.x*a.z);
  assert a.x*b.y - a.y*b.x == -(b.x*a.y - b.y*a.x);
}

/* helper modified by LLM (iteration 2): CrossZeroIfParallel proof */
lemma CrossZeroIfParallel(a: Vector3D, b: Vector3D)
  requires AreParallel(a,b)
  ensures a.y*b.z - a.z*b.y == 0.0 && a.z*b.x - a.x*b.z == 0.0 && a.x*b.y - a.y*b.x == 0.0
{
  if a.x == 0.0 && a.y == 0.0 && a.z == 0.0 {
    assert a.y*b.z - a.z*b.y == 0.0;
    assert a.z*b.x - a.x*b.z == 0.0;
    assert a.x*b.y - a.y*b.x == 0.0;
  } else if b.x == 0.0 && b.y == 0.0 && b.z == 0.0 {
    assert a.y*b.z - a.z*b.y == 0.0;
    assert a.z*b.x - a.x*b.z == 0.0;
    assert a.x*b.y - a.y*b.x == 0.0;
  } else {
    // When neither vector is the zero vector, the third disjunct of AreParallel must hold by definition
    assert a.x*b.y - a.y*b.x == 0.0;
    assert a.y*b.z - a.z*b.y == 0.0;
    assert a.z*b.x - a.x*b.z == 0.0;
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
{
  /* code modified by LLM (iteration 2): compute cross product and apply helper lemmas */
  result := Vector3D(a.y * b.z - a.z * b.y,
                     a.z * b.x - a.x * b.z,
                     a.x * b.y - a.y * b.x);
  CrossPerpendicular(a, b);
  CrossAntiCommutative(a, b);
  if AreParallel(a, b) {
    CrossZeroIfParallel(a, b);
  }
}

// </vc-code>
