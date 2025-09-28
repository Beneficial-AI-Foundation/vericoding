// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method IsSorted(arr: array<int>) returns (is_sorted: bool)

    requires
        arr.Length > 0

    ensures
        is_sorted == (forall i, j :: 0 <= i < j < arr.Length ==> (arr[i] <= arr[j]))
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  var ok := true;
  var badA := -1;
  var badB := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant ok ==> (forall a, b :: 0 <= a < b < n && a < i ==> arr[a] <= arr[b])
    invariant !ok ==> 0 <= badA < badB < n && arr[badA] > arr[badB]
  {
    var j := i + 1;
    while j < n && ok
      invariant i + 1 <= j <= n
      invariant ok ==> (forall a, b :: 0 <= a < b < n && (a < i || (a == i && b < j)) ==> arr[a] <= arr[b])
      invariant !ok ==> 0 <= badA < badB < n && arr[badA] > arr[badB]
    {
      if arr[i] > arr[j] {
        ok := false;
        badA := i;
        badB := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert ok ==> (forall a, b :: 0 <= a < b < n ==> arr[a] <= arr[b]);
  assert !ok ==> !(forall a, b :: 0 <= a < b < n ==> arr[a] <= arr[b]);
  is_sorted := ok;
}
// </vc-code>
