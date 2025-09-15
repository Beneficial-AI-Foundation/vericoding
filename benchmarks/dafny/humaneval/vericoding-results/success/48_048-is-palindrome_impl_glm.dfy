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
  /* code modified by LLM (iteration 2): fixed loop invariant and removed early break */
  var i := 0;
  result := true;
  while i < |text| / 2
      invariant 0 <= i <= |text| / 2
      invariant result == (forall j : int :: 0 <= j < i ==> text[j] == text[|text| - j - 1])
  {
      if text[i] != text[|text| - i - 1] {
          result := false;
      }
      i := i + 1;
  }
}
// </vc-code>
