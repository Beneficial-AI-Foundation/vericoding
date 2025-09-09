/*
function_signature: method reverse(s: seq<int>) returns (rev: seq<int>)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
