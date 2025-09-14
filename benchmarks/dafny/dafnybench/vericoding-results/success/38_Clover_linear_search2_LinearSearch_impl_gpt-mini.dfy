

// <vc-helpers>
// (no helpers needed)
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
  while a[i] != e
    invariant 0 <= i < a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
    invariant exists k :: i <= k < a.Length && a[k] == e
    decreases a.Length - i
  {
    var j :| i <= j < a.Length && a[j] == e;
    assert a[j] == e;
    assert a[i] != e;
    assert j != i;
    i := i + 1;
    assert i <= j && j < a.Length && a[j] == e;
  }
  n := i;
}
// </vc-code>

