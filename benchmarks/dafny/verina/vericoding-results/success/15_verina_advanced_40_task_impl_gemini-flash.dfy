// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause */
predicate IsMax(arr: array<int>, val: int)
    reads arr
{
    exists i :: 0 <= i < arr.Length && arr[i] == val
}
// </vc-helpers>

// <vc-spec>
method MaxOfList(lst: array<int>) returns (result: int)
    requires lst.Length > 0
    ensures exists i :: 0 <= i < lst.Length && lst[i] == result
    ensures forall i :: 0 <= i < lst.Length ==> lst[i] <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Initial implementation for finding max */
{
    result := lst[0];
    var i := 1;
    while i < lst.Length
        invariant 0 < i <= lst.Length
        invariant forall k :: 0 <= k < i ==> lst[k] <= result
        invariant exists k :: 0 <= k < i && lst[k] == result
        invariant lst[0] <= result
    {
        if lst[i] > result {
            result := lst[i];
        }
        i := i + 1;
    }
}
// </vc-code>
