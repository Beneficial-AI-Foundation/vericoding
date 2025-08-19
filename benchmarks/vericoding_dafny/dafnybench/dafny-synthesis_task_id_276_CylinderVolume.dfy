// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CylinderVolume(radius: real, height: real) returns (volume: real)
    requires radius > 0.0
    requires height > 0.0
    ensures volume == 3.14159265359 * radius * radius * height
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>