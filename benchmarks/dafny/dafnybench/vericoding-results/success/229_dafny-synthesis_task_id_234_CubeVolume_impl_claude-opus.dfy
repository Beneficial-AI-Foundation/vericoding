

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
  volume := size * size * size;
}
// </vc-code>

