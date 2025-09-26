// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SphereVolume(radius: real) returns (volume: real)
    requires radius > 0.0
    ensures volume == 4.0/3.0 * 3.1415926535 * radius * radius * radius
// </vc-spec>
// <vc-code>
{
    volume := 4.0/3.0 * 3.1415926535 * radius * radius * radius;
}
// </vc-code>
