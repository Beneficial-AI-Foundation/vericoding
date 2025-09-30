

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DegreesToRadians(degrees: real) returns (radians: real)
    ensures radians == degrees * 3.14159265358979323846 / 180.0
// </vc-spec>
// <vc-code>
{
  radians := degrees * 3.14159265358979323846 / 180.0;
}
// </vc-code>

