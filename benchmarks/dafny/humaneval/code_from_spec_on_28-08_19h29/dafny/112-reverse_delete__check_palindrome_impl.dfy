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
// Helper predicate to check if a string is a palindrome
function isPalindromePred(s: string): bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method check_palindrome(s: string) returns (result: bool)
Check condition. Ensures: the result is a palindrome.
*/
// </vc-description>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  ensures result == isPalindromePred(s)
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall k :: 0 <= k < i ==> s[k] == s[n - 1 - k]
  {
    if s[i] != s[n - 1 - i] {
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