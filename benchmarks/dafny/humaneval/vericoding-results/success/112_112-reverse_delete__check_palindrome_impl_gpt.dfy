// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)

  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
{
  result := is_palindrome_pred(s);
}
// </vc-code>
