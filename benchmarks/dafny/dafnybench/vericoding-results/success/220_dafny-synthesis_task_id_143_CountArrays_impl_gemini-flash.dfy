

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountArrays(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
// </vc-spec>
// <vc-code>
{
  count := |arrays|;
}
// </vc-code>

