// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsPalindrome(text: string) { forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1] }
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)

    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
// </vc-spec>
// <vc-code>
{
  result := IsPalindrome(text);
}
// </vc-code>
