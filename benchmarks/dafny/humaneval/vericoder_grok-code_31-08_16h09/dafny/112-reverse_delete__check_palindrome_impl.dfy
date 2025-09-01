method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate is_palindrome_pred(s: string) {
  forall k :: 0 <= k < |s| / 2 ==> s[k] == s[|s| - 1 - k]
}
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
  {
    if s[i] != s[|s| - 1 - i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end