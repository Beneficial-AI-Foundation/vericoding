

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (n:int)
  requires exists i::0<=i<a.Length && a[i]==e
  ensures 0<=n<a.Length && a[n]==e
  ensures forall k :: 0 <= k < n ==> a[k]!=e
// </vc-spec>
// <vc-code>
{
  var i := 0;
  ghost var w :| 0 <= w < a.Length && a[w] == e;
  while i < a.Length && a[i] != e
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
    invariant i <= w < a.Length
    invariant a[w] == e
    decreases a.Length - i
  {
    assert a[i] != e;
    assert i != w;
    assert i < w;
    i := i + 1;
  }
  n := i;
}
// </vc-code>

