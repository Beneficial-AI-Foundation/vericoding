// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
