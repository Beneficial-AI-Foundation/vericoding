// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method QuicksortPartition(X: array<int>, n: int, p: int) returns (a: int, b: int)
modifies X;
  requires X.Length>=1 && n == X.Length;
  ensures b>=n;
  ensures forall x:: 0<=x<a<n ==> X[x] <= p;
  ensures forall x:: a==n || (0<=a<=x<n ==> X[x] > p);
  ensures multiset(X[..])==multiset(old(X[..]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Resubmitting correct implementation as previous errors were compilation warnings in non-editable code. */
  a := 0;
  b := 0;
  while (b < n)
    invariant 0 <= a <= b <= n
    invariant multiset(X[..]) == multiset(old(X[..]))
    invariant forall i :: 0 <= i < a ==> X[i] <= p
    invariant forall i :: a <= i < b ==> X[i] > p
    decreases n - b
  {
    if (X[b] <= p)
    {
      X[a], X[b] := X[b], X[a];
      a := a + 1;
    }
    b := b + 1;
  }
}
// </vc-code>
