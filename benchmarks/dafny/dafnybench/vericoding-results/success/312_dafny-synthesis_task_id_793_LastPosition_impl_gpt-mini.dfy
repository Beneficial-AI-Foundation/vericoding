

// <vc-helpers>

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
  pos := -1;
  var lo := 0;
  var hi := arr.Length - 1;
  while lo <= hi
    invariant 0 <= lo <= arr.Length
    invariant -1 <= hi < arr.Length
    invariant lo <= hi + 1
    invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
    invariant forall i :: pos < i < lo ==> arr[i] != elem
    invariant forall i :: hi < i < arr.Length ==> arr[i] > elem
    decreases hi - lo + 1
  {
    var mid := (lo + hi) / 2;
    if arr[mid] == elem {
      pos := mid;
      lo := mid + 1;
    } else if arr[mid] < elem {
      lo := mid + 1;
    } else {
      hi := mid - 1;
    }
  }
  return;
}
// </vc-code>

