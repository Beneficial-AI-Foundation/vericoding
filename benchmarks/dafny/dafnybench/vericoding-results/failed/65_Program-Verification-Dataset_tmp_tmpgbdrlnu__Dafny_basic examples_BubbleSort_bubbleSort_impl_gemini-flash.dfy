predicate sorted(a:array<int>, from:int, to:int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null;
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

// <vc-helpers>
function AsMultiset<T>(s: seq<T>): multiset<T>
{
  multiset(s)
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n == 0 { return; }

  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < n - i ==> (forall l :: n - i <= l < n ==> a[k] <= a[l])
    invariant sorted(a, n - i, n)
    invariant AsMultiset(a[..]) == AsMultiset(old(a[..]))
  {
    for j := 0 to n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant forall k :: 0 <= k < j ==> a[k] <= a[k+1]
      invariant forall k :: 0 <= k <= j ==> (forall l :: n - i <= l < n ==> a[k] <= a[l])
      invariant sorted(a, n-i, n)
      invariant AsMultiset(a[..]) == AsMultiset(old(a[..]))
    {
      if a[j] > a[j+1]
      {
        a[j], a[j+1] := a[j+1], a[j];
      }
    }
  }
}
// </vc-code>

