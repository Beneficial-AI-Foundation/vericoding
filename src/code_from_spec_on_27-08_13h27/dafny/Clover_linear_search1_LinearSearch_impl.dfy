// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (n:int)
  ensures 0<=n<=a.Length
  ensures n==a.Length || a[n]==e
  ensures forall i::0<=i < n ==> e!=a[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method LinearSearchImpl(a: array<int>, e: int) returns (n: int)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == e
  ensures forall i :: 0 <= i < n ==> e != a[i]
{
  n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> e != a[i]
  {
    if a[n] == e {
      return;
    }
    n := n + 1;
  }
}
// </vc-code>
