// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SplitAndAppend(list: array<int>, n: int) returns (new_list: seq<int>)
    requires list.Length > 0
    requires 0 < n < list.Length
    ensures new_list == list[n..list.Length] + list[0..n]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
