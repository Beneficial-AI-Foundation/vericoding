// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var min_index := 0;
  var i := 1;
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant 0 <= min_index < i
    invariant forall k :: 0 <= k < i ==> arr[min_index][1] <= arr[k][1]
  {
    if arr[i][1] < arr[min_index][1] {
      min_index := i;
    }
    i := i + 1;
  }
  first_of_min_second := arr[min_index][0];
}
// </vc-code>
