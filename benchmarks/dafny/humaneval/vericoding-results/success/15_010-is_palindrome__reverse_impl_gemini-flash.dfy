// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): append character to sequence */
{
  rev := "";
  var i := |str| - 1;
  while i >= 0
    invariant 0 <= i + 1 <= |str|
    invariant |rev| == |str| - (i + 1)
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k]
  {
    rev := rev + [str[i]];
    i := i - 1;
  }
}
// </vc-code>
