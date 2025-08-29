// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def is_palindrome(string: str) -> Bool
Checks if given string is a palindrome
*/
// </vc-description>

// <vc-spec>
method is_palindrome(s: string) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i])
// </vc-spec>
// <vc-code>
{
  if |s| <= 1 {
    result := true;
    return;
  }
  
  var left := 0;
  var right := |s| - 1;
  
  while left < right
    invariant 0 <= left <= right < |s|
    invariant forall i :: 0 <= i < left ==> s[i] == s[|s| - 1 - i]
    invariant forall i :: right < i < |s| ==> s[i] == s[|s| - 1 - i]
    decreases right - left
  {
    if s[left] != s[right] {
      result := false;
      return;
    }
    left := left + 1;
    right := right - 1;
  }
  
  result := true;
}
// </vc-code>
