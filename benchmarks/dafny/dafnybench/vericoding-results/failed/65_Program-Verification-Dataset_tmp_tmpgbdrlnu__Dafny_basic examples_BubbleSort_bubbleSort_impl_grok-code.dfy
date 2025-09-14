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
  while (i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant sorted(a, n - i, n)
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: n - i <= k < n ==> forall l :: 0 <= l < n - i ==> a[l] <= a[k]
  {
    var j := 0;
    while (j < n - i - 1)
      decreases n - i - 1 - j
      invariant 0 <= j <= n - i - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, n - i, n)
      invariant forall k :: n - i <= k < n ==> forall l :: 0 <= l < n - i ==> a[l] <= a[k]
    {
      if a[j] > a[j + 1]
      {
        var tmp := a[j];
        a[j] := a[j + 1];
        a[j + 1] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

