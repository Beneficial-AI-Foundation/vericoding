

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  while i < |text| && result
    invariant 0 <= i <= |text| + 1
    invariant forall j :: 0 <= j < i && j < |text| / 2 ==> text[j] == text[|text| - 1 - j]
    invariant result ==> forall j :: 0 <= j < i && j < |text| / 2 ==> text[j] == text[|text| - 1 - j]
  {
    if i < |text| / 2 && text[i] != text[|text| - 1 - i] {
      result := false;
    }
    i := i + 1;
  }
}
// </vc-code>

