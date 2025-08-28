// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CountArrays(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
// </vc-spec>
// </vc-spec>

// <vc-code>
method CountArraysImpl(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
{
    count := |arrays|;
}
// </vc-code>
