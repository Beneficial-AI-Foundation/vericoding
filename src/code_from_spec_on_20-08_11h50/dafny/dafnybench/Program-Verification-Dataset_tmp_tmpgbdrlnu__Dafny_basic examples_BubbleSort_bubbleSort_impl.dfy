Let me analyze what the bubble sort algorithm does and fix the invariants accordingly.

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
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1;
    invariant sorted(a, n - i, n);
    invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v];
    invariant multiset(a[..]) == multiset(old(a[..]));
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i;
      invariant sorted(a, n - i, n);
      invariant forall u, v :: 0 <= u < n - i && n - i <= v < n ==> a[u] <= a[v];
      invariant multiset(a[..]) == multiset(old(a[..]));
      invariant forall k :: 0 <= k <= j ==> forall m :: j + 1 <= m < n - i ==> a[k] <= a[m];
    {
      if a[j] > a[j + 1] {
        var temp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := temp;
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>