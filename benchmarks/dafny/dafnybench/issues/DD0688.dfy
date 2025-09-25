// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
// </vc-spec>
// <vc-code>
{
    result := [b, a];
}
// </vc-code>
