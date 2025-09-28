// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause for array access */
predicate IndexParity(arr: array<int>, i: int) reads arr { 0 <= i < arr.Length && (i % 2) == (arr[i] % 2) }
// </vc-helpers>

// <vc-spec>
method IsOddAtOddIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate array and check parity at each index */
  var ok := true;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant ok == (forall j :: 0 <= j < i ==> (j % 2) == (arr[j] % 2))
  {
    if arr[i] % 2 == i % 2 {
      // match, keep ok as true
    } else {
      ok := false;
    }
    i := i + 1;
  }
  result := ok;
}
// </vc-code>
