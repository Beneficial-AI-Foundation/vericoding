// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array element access */
predicate AllSame(char_arr: array<char>) reads char_arr { forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i] }
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate and check all characters equal; maintain invariant linking result to prefix property */
  if char_arr.Length <= 1 {
    result := true;
    return;
  }
  var i := 1;
  result := true;
  while i < char_arr.Length
    invariant 1 <= i <= char_arr.Length
    invariant result == (forall j :: 1 <= j < i ==> char_arr[0] == char_arr[j])
    decreases char_arr.Length - i
  {
    if char_arr[i] != char_arr[0] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
