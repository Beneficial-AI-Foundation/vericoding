// <vc-preamble>
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)

  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var n := |s|;
  result := true;
  while i < n / 2 && result
    invariant 0 <= i <= n / 2
    invariant result <==> forall k :: 0 <= k < i ==> s[k] == s[n - 1 - k]
  {
    if s[i] != s[n - 1 - i] {
      result := false;
    }
    i := i + 1;
  }
}
// </vc-code>
