// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed. */
// </vc-helpers>

// <vc-spec>
method is_palindrome(text : string) returns (result : bool)

    ensures result == (forall i : int :: i >= 0 && i < |text| ==> text[i] == text[|text| - i - 1])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed compilation error by changing '=' to ':=' in var declaration. */
  var halv := |text| / 2;
  var i := 0;
  while i < halv
    invariant 0 <= i <= halv
    invariant forall k :: 0 <= k < i ==> text[k] == text[|text|-1-k]
  {
    if text[i] != text[|text|-1-i] {
      return false;
    }
    i := i + 1;
  }
  assert (forall k :: 0 <= k < |text| ==> text[k] == text[|text|-k-1]);
  return true;
}
// </vc-code>
