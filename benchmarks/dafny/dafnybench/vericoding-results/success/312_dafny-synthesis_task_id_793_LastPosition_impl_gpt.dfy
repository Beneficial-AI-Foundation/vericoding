

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
  var i := arr.Length - 1;
  while 0 <= i
    invariant pos == -1
    invariant 0 <= i + 1 <= arr.Length
    decreases i + 1
  {
    if arr[i] == elem {
      pos := i;
      return;
    }
    i := i - 1;
  }
}
// </vc-code>

