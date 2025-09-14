// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow accessing array elements */
predicate AllEqualFrom(arr: array<int>, start: int) reads arr
  requires 0 <= start <= arr.Length
{
  forall i :: start <= i < arr.Length ==> arr[start] == arr[i]
}
// </vc-helpers>

// <vc-spec>
method HasOnlyOneDistinctElement(arr: array<int>) returns (result: bool)
    ensures result == (forall i :: 1 <= i < arr.Length ==> arr[0] == arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate to detect mismatch */
  if arr.Length <= 1 {
    result := true;
    return;
  }
  var mismatch := -1;
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant (mismatch == -1) ==> (forall j :: 1 <= j < i ==> arr[0] == arr[j])
    invariant (mismatch != -1) ==> 0 <= mismatch < i && arr[mismatch] != arr[0]
    decreases arr.Length - i
  {
    if arr[i] != arr[0] {
      mismatch := i;
      i := arr.Length;
    } else {
      i := i + 1;
    }
  }
  result := (mismatch == -1);
}
// </vc-code>
