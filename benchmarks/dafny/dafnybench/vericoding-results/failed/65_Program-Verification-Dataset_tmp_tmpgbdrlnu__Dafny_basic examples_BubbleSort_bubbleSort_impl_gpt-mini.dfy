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
method swap(a: array<int>, i: int, j: int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length;
  modifies a;
  ensures multiset(a[..]) == old(multiset(a[..]));
{
  ghost var s := a[..];
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
  assert a[..] == s[i := s[j]][j := s[i]];
  assert multiset(a[..]) == multiset(s);
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
  ghost var orig := multiset(a[..]);

  var to := n;
  while to > 1
    invariant 1 <= to <= n;
    invariant sorted(a, to, n);
    invariant forall u, v :: 0 <= u < to <= v < n ==> a[u] <= a[v];
    decreases to
  {
    var i := 0;
    while i + 1 < to
      invariant 0 <= i < to;
      invariant sorted(a, to, n);
      invariant forall u, v :: 0 <= u < to <= v < n ==> a[u] <= a[v];
      decreases to - i
    {
      if a[i] > a[i+1] {
        swap(a, i, i+1);
      }
      i := i + 1;
    }
    to := to - 1;
  }

  // From invariants at loop exit (to == 1) derive sorted(a, 0, n)
  assert sorted(a, 1, n);
  assert forall v :: 1 <= v < n ==> a[0] <= a[v];
  assert forall u, v :: 0 <= u < v < n ==> a[u] <= a[v]
    by {
      fix u, v;
      if u == 0 {
        assert 0 <= u < v < n;
        assert 1 <= v < n by { assert u == 0 && u < v; }
        assert a[0] <= a[v];
      } else {
        assert 1 <= u < v < n;
        assert a[u] <= a[v];
      }
    }

  assert multiset(a[..]) == orig;
}
// </vc-code>

