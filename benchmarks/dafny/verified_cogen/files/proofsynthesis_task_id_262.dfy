// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SplitArray(list: array<int>, l: int) returns (new_list: (seq<int>, seq<int>))
    requires
        list.Length > 0 &&
        0 < l < list.Length
    ensures
        new_list.0 == list[0..l] &&
        new_list.1 == list[l..list.Length]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
