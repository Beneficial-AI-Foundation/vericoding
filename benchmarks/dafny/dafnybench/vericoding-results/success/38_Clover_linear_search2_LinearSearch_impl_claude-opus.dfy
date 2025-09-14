

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
  n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> a[k] != e
    invariant exists i :: n <= i < a.Length && a[i] == e
  {
    if a[n] == e {
      return n;
    }
    n := n + 1;
  }
}
// </vc-code>

