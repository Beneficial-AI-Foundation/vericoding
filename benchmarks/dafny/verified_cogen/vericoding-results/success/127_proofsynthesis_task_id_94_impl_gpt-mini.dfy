// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate ValidMatrix(arr: array<array<int>>) reads arr { arr.Length > 0 && forall i :: 0 <= i < arr.Length ==> arr[i].Length >= 2 }
// </vc-helpers>

// <vc-spec>
method MinSecondValueFirst(arr: array<array<int>>) returns (first_of_min_second: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> arr[i].Length >= 2
    ensures exists i :: (0 <= i < arr.Length && first_of_min_second == arr[i][0] && 
            (forall j :: 0 <= j < arr.Length ==> arr[i][1] <= arr[j][1]))
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var minIdx := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= minIdx < arr.Length
    invariant forall k :: 0 <= k < i ==> arr[minIdx][1] <= arr[k][1]
  {
    if arr[i][1] < arr[minIdx][1] {
      minIdx := i;
    }
    i := i + 1;
  }
  first_of_min_second := arr[minIdx][0];
}
// </vc-code>
