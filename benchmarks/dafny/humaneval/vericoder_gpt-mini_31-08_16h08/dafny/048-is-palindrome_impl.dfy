

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)
    // post-conditions-start
    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := forall i :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1];
}
// </vc-code>

