// <vc-helpers>
lemma SlopeSearchExists(a: array2<int>, key: int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures exists m,n :: 0<=m<a.Length0 && 0<=n<a.Length1 && a[m,n]==key
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
// </vc-spec>
// </vc-spec>

// <vc-code>
method SlopeSearchImpl(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
{
  m := 0;
  n := a.Length1 - 1;
  
  while m < a.Length0 && n >= 0
    invariant 0 <= m <= a.Length0
    invariant -1 <= n < a.Length1
    invariant exists i,j :: m <= i < a.Length0 && 0 <= j <= n && a[i,j]==key
    invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] < key
    invariant forall i,j :: 0 <= i < a.Length0 && n < j < a.Length1 ==> a[i,j] > key
    decreases a.Length0 - m + n + 1
  {
    if a[m,n] == key {
      return;
    } else if a[m,n] < key {
      m := m + 1;
    } else {
      n := n - 1;
    }
  }
  
  assert false;
}
// </vc-code>
