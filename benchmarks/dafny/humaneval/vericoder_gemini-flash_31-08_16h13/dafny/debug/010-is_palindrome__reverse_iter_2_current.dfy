function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function is_palindrome_helper(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with_helper(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var rev_str := "";
  var i := |str| - 1;
  while i >= 0
    invariant -1 <= i < |str|
    invariant |rev_str| == |str| - (i + 1)
    invariant forall k :: 0 <= k < |rev_str| ==> rev_str[k] == str[|str| - 1 - k]
  {
    rev_str := rev_str + str[i..i+1];
    i := i - 1;
  }
  rev := rev_str;
}
// </vc-code>

