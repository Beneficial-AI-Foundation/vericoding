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
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implemented correct reverse using a sequence loop with invariant to satisfy postconditions */
  var result: seq<char> := [];
  for i := 0 to |str|
    invariant 0 <= i <= |str|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == str[i - 1 - k]
  {
    if i < |str| {
      result := [str[i]] + result;
    }
  }
  rev := result;
}
// </vc-code>
