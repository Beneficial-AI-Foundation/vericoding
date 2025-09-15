// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed bounds checking in helper function */
function char_matches_mirror(s: string, i: int): bool
  requires 0 <= i < |s|
{
  s[i] == s[|s| - 1 - i]
}
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)

  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed loop invariant to properly establish palindrome property */
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant forall j :: 0 <= j < i ==> s[j] == s[|s| - 1 - j]
  {
    if s[i] != s[|s| - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
