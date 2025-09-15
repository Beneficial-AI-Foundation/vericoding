// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReverseToK(list: array<int>, n: int) returns (reversed_list: seq<int>)
    requires
        list.Length > 0 &&
        0 < n < list.Length
    ensures
        reversed_list == list[0..n][..n] + list[n..list.Length]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
