// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed reverseHelper to properly reverse elements */
function reverseHelper(s: seq<int>, i: int): seq<int>
  requires 0 <= i <= |s|
  ensures |reverseHelper(s, i)| == i
  ensures forall k :: 0 <= k < i ==> reverseHelper(s, i)[k] == s[i - 1 - k]
{
  if i == 0 then []
  else [s[i-1]] + reverseHelper(s, i-1)
}
// </vc-helpers>

// <vc-spec>
method reverse(s: seq<int>) returns (rev: seq<int>)

  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Assign helper result to return variable */
{
  rev := reverseHelper(s, |s|);
}
// </vc-code>
