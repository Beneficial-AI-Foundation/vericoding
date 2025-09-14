// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added preconditions to avoid out-of-bounds and align with loop invariants */
predicate AllEqualToFirst(a: array<char>, i: int) reads a
  requires 0 < a.Length
  requires 1 <= i <= a.Length
{
  forall j :: 1 <= j < i ==> a[0] == a[j]
}
// </vc-helpers>

// <vc-spec>
method AllCharactersSame(char_arr: array<char>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < char_arr.Length ==> char_arr[0] == char_arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implemented safe loop with empty-array case and used helper predicate */
  if char_arr.Length == 0 {
    result := true;
  } else {
    var i := 1;
    var ok := true;
    while i < char_arr.Length
      invariant 0 < char_arr.Length
      invariant 1 <= i <= char_arr.Length
      invariant ok == AllEqualToFirst(char_arr, i)
      decreases char_arr.Length - i
    {
      ok := AllEqualToFirst(char_arr, i + 1);
      i := i + 1;
    }
    result := ok;
  }
}
// </vc-code>
