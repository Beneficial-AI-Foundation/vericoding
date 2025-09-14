// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unnecessary helper from previous attempts. */
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation error by adding braces to the `if` statement within the loop. */
{
  if char_arr.Length == 0 {
    return true;
  }
  var first_char := char_arr[0];
  var i := 1;
  while i < char_arr.Length
    invariant 1 <= i <= char_arr.Length
    invariant forall k :: 1 <= k < i ==> char_arr[k] == first_char
  {
    if char_arr[i] != first_char {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
