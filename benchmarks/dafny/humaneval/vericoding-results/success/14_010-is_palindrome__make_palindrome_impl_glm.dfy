// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)

    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implemented using a loop to build reversed string */
  var rev := "";
  var i := |s| - 1;
  while i >= 0
    invariant 0 <= i < |s| || i == -1
    invariant |rev| == |s| - 1 - i
    invariant forall j :: 0 <= j < |rev| ==> rev[j] == s[|s|-1-j]
  {
    rev := rev + s[i..i+1];
    i := i - 1;
  }
  result := s + rev;
}
// </vc-code>
