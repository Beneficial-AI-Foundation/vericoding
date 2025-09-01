

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := (forall i:int :: 0 <= i && i < |text| ==> text[i] == text[|text| - i - 1]);
}
// </vc-code>

