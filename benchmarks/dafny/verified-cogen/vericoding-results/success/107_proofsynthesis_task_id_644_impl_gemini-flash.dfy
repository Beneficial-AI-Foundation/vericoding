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
/* code modified by LLM (iteration 5): The previous attempt to build `reversed_list` element by element failed to satisfy the postcondition. This version directly constructs the `reversed_list` using sequence slicing and concatenation, which is simpler and more aligned with the `ensures` clause. */
{
    reversed_list := list[0..n][..n] + list[n..list.Length];
}
// </vc-code>
