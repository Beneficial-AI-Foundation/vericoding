// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helpers not needed */
// </vc-helpers>

// <vc-spec>
method IsOddAtOddIndex(arr: array<int>) returns (result: bool)
    ensures result == forall i :: 0 <= i < arr.Length ==> ((i % 2) == (arr[i] % 2))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants to verify the forall postcondition */
{
  var i := 0;
  while i < arr.Length 
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> ((j % 2) == (arr[j] % 2))
  {
    if (i % 2) != (arr[i] % 2) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
