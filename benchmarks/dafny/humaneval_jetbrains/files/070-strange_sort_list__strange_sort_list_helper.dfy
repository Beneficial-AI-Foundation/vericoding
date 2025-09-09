/*
function_signature: method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
Sort elements. Ensures: returns a sorted permutation of the input; returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)

    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
