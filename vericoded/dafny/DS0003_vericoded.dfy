// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  result := 0;
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant 0 <= result < i
    invariant forall j :: 0 <= j < result ==> arr[result] > arr[j]
    invariant forall j :: result < j < i ==> arr[result] >= arr[j]
  {
    if arr[i] > arr[result] {
      result := i;
    }
    i := i + 1;
  }
}
// </vc-code>
