// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): handled edge case for short arrays to fix loop invariant */
  result := true;
  if char_arr.Length >= 2 {
    var i := 1;
    while i < char_arr.Length
      invariant 1 <= i <= char_arr.Length
      invariant result == (forall k :: 1 <= k < i ==> char_arr[0] == char_arr[k])
    {
      if char_arr[i] != char_arr[0] {
        result := false;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
