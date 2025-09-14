// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>
lemma PalindromeHalf(s: string)
  requires forall k :: 0 <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k]
  ensures is_palindrome_pred(s)
{ }
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)

  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant result ==> (forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k])
  {
    if s[i] != s[|s| - 1 - i] {
      result := false;
      return;
    }
    i := i + 1;
  }

  if result {
    PalindromeHalf(s);
  }
}
// </vc-code>
