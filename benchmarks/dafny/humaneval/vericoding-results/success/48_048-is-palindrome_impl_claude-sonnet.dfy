// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)

    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
// </vc-spec>
// <vc-code>
{
  if |text| == 0 {
    result := true;
    return;
  }
  
  var i := 0;
  result := true;
  
  while i < |text| / 2
    invariant 0 <= i <= |text| / 2
    invariant result == (forall j : int :: j >= 0 && j < i ==> text[j] == text[|text| - j - 1])
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
