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
// </vc-helpers>

// <vc-description>
/*
function_signature: method check_palindrome(s: string) returns (result: bool)
Check condition. Ensures: the result is a palindrome.
*/
// </vc-description>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  ensures result <==> is_palindrome_pred(s)
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    result := true;
  } else {
    result := true;
    var i := 0;
    while i < |s| / 2
      invariant 0 <= i <= |s| / 2
      invariant result <==> (forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k])
    {
      if s[i] != s[|s| - 1 - i] {
        result := false;
        break;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end