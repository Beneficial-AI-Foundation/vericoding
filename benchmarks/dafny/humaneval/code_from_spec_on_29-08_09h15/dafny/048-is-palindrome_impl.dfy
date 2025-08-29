

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: def is_palindrome(string: str) -> Bool
Checks if given string is a palindrome
*/
// </vc-description>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
  if |text| <= 1 {
    result := true;
    return;
  }
  
  var i := 0;
  while i < |text| / 2
    invariant 0 <= i <= |text| / 2
    invariant forall j : int :: 0 <= j < i ==> text[j] == text[|text| - j - 1]
  {
    if text[i] != text[|text| - i - 1] {
      result := false;
      return;
    }
    i := i + 1;
  }
  
  result := true;
}
// </vc-code>

