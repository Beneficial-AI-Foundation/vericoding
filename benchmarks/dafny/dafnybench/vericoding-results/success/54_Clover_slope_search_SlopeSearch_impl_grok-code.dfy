

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length1 - 1;
  while i < a.Length0 && j >= 0
    invariant -1 <= j && j < a.Length1
    invariant 0 <= i && i <= a.Length0
    invariant exists p, q :: i <= p < a.Length0 && 0 <= q <= j && a[p, q] == key
    decreases j, a.Length0 - 1 - i
  {
    if a[i,j] == key {
      return i, j;
    } else if a[i,j] > key {
      j := j - 1;
    } else {
      i := i + 1;
    }
  }
  assert false;  // Should not reach here due to existence precondition
}
// </vc-code>

