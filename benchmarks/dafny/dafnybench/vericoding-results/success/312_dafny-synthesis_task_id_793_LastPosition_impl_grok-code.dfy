

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := arr.Length;
  while i != j
    invariant 0 <= i <= j <= arr.Length
    invariant forall k :: 0 <= k < i ==> arr[k] <= elem
    invariant forall k :: j <= k < arr.Length ==> arr[k] > elem
  {
    var mid := (i + j) / 2;
    if arr[mid] <= elem {
      i := mid + 1;
    } else {
      j := mid;
    }
  }
  if i > 0 && arr[i - 1] == elem {
    pos := i - 1;
  } else {
    pos := -1;
  }
}
// </vc-code>

