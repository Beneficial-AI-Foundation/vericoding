

// <vc-helpers>
lemma LinearSearchLemma(a: array<int>, e: int, n: int)
  requires exists i::0<=i<a.Length && a[i]==e
  requires 0 <= n < a.Length
  requires a[n] == e
  requires forall k :: 0 <= k < n ==> a[k] != e
  ensures 0<=n<a.Length && a[n]==e
  ensures forall k :: 0 <= k < n ==> a[k]!=e
{
}
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
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != e
  {
    if a[i] == e {
      n := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>

