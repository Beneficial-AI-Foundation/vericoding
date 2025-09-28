// <vc-preamble>
// Type definition for 3D vectors
type Vector3D = seq<real>

// Predicate to ensure a sequence represents a valid 3D vector
predicate IsValidVector3D(v: Vector3D)
{
    |v| == 3
}

// Cross product method that computes the cross product of two 3D vectors
// </vc-preamble>

// <vc-helpers>

function crossX(a: Vector3D, b: Vector3D): real
  requires IsValidVector3D(a) && IsValidVector3D(b)
{
  a[1] * b[2] - a[2] * b[1]
}

function crossY(a: Vector3D, b: Vector3D): real
  requires IsValidVector3D(a) && IsValidVector3D(b)
{
  a[2] * b[0] - a[0] * b[2]
}

function crossZ(a: Vector3D, b: Vector3D): real
  requires IsValidVector3D(a) && IsValidVector3D(b)
{
  a[0] * b[1] - a[1] * b[0]
}

// </vc-helpers>

// <vc-spec>
method CrossProduct(x1: Vector3D, x2: Vector3D) returns (result: Vector3D)
    requires IsValidVector3D(x1)
    requires IsValidVector3D(x2)
    ensures IsValidVector3D(result)
    ensures result[0] == x1[1] * x2[2] - x1[2] * x2[1]
    ensures result[1] == x1[2] * x2[0] - x1[0] * x2[2]
    ensures result[2] == x1[0] * x2[1] - x1[1] * x2[0]
// </vc-spec>
// <vc-code>
{
  result := [crossX(x1, x2), crossY(x1, x2), crossZ(x1, x2)];
  assert |result| == 3;
  assert result[0] == x1[1] * x2[2] - x1[2] * x2[1];
  assert result[1] == x1[2] * x2[0] - x1[0] * x2[2];
  assert result[2] == x1[0] * x2[1] - x1[1] * x2[0];
}
// </vc-code>
