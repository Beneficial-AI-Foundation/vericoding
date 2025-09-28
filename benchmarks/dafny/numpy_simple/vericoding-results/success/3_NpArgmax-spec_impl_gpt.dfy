// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' to satisfy syntax */
function Max(a: int, b: int): int {
  if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method Argmax(arr: array<int>) returns (result: int)
    requires arr.Length > 0
    ensures 
        0 <= result < arr.Length &&
        (forall i :: 0 <= i < result ==> arr[result] > arr[i]) &&
        (forall i :: result < i < arr.Length ==> arr[result] >= arr[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented verified linear scan to compute argmax */
  var best := 0;
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant 0 <= best < i
    invariant forall j :: 0 <= j < i ==> arr[best] >= arr[j]
    invariant forall j :: 0 <= j < best ==> arr[best] > arr[j]
    decreases arr.Length - i
  {
    if arr[i] > arr[best] {
      best := i;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
