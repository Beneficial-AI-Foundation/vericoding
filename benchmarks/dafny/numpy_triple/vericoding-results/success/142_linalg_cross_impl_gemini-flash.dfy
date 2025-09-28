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
// No helpers needed for straight-forward cross product calculation
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
  /* code modified by LLM (iteration 3): Fix type errors for result initialization and assignments. */
  var temp_result: array<real> := new real[3];
  temp_result[0] := x1[1] * x2[2] - x1[2] * x2[1];
  temp_result[1] := x1[2] * x2[0] - x1[0] * x2[2];
  temp_result[2] := x1[0] * x2[1] - x1[1] * x2[0];
  result := temp_result[..];
}
// </vc-code>
