// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed unnecessary null check; predicate states all elements are less than number */
predicate AllLess(arr: array<int>, number: int)
  reads arr
{
  forall i :: 0 <= i < arr.Length ==> number > arr[i]
}
// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate through array and maintain invariant about processed elements */
  var ok := true;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant ok == (forall j :: 0 <= j < i ==> number > arr[j])
    decreases arr.Length - i
  {
    ok := ok && number > arr[i];
    i := i + 1;
  }
  result := ok;
}
// </vc-code>
