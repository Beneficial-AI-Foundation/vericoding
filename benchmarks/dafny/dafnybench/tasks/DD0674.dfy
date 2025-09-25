// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountArrays(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
