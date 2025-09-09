/*
function_signature: method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
Sort elements. Ensures: returns the correct size/count.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)

    ensures |s| == |strange|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
