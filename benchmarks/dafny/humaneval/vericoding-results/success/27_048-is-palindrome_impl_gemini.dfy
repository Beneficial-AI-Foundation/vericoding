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
  result := true;
  var i := 0;
  var n := |text|;
  while i < n / 2
    invariant 0 <= i <= (n + 1) / 2
    invariant forall k :: 0 <= k < i ==> text[k] == text[n - 1 - k]
  {
    if text[i] != text[n - 1 - i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
