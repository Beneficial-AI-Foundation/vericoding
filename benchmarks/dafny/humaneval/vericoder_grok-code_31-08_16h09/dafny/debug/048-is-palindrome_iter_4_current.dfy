

// <vc-helpers>
lemma isPalindromeHalf(text: string)
  requires forall i : int :: 0 <= i < |text|/2 ==> text[i] == text[|text| - i - 1]
  ensures forall i : int :: 0 <= i < |text| ==> text[i] == text[|text| - i - 1]
{
  forall i : int | 0 <= i < |text| ensures text[i] == text[|text| - i - 1] {
    if i < |text|/2 {
      // from requires, text[i] == text[|text| - i - 1]
    } else {
      var j : int := |text| - i - 1;
      assert 0 <= j < |text|/2;
      assert text[j] == text[|text| - j - 1];  // from requires
      assert |text| - j - 1 == i;
    }
  }
}
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
    while i < |text| / 2 && result
        invariant 0 <= i <= |text| / 2
        invariant result ==> forall j :: 0 <= j < i ==> text[j] == text[|text| - 1 - j]
        decreases |text| - i
    {
        if text[i] != text[|text| - 1 - i] {
            result := false;
        }
        i := i + 1;
    }
    if result {
        isPalindromeHalf(text);
    }
}
// </vc-code>

