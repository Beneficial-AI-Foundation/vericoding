// <vc-helpers>
// No additional helpers or proofs needed for this verification
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputeTriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    volume := (base * height * length) / 2;
}
// </vc-code>
