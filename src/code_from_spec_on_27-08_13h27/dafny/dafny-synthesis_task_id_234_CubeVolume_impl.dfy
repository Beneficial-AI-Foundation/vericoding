// <vc-helpers>
// No additional helpers or proofs needed for this simple calculation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CubeVolume(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// </vc-spec>

// <vc-code>
method CubeVolumeImpl(size: int) returns (volume: int)
    requires size > 0
    ensures volume == size * size * size
{
    volume := size * size * size;
}
// </vc-code>
