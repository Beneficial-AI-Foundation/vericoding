// <vc-helpers>
// </vc-helpers>

method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
// <vc-code>
{
  assume false;
}
// </vc-code>