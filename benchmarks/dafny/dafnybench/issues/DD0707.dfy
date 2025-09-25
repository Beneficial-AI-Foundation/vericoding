// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ConeVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0 && height > 0.0
    ensures volume == (1.0/3.0) * (3.14159265358979323846) * radius * radius * height
// </vc-spec>
// <vc-code>
{
    volume := (1.0/3.0) * (3.14159265358979323846) * radius * radius * height;
}
// </vc-code>
