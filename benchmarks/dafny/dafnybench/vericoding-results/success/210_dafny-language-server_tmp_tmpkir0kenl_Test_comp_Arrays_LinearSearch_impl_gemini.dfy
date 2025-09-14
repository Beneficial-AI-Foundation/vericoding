// <vc-preamble>
method PrintArray<A>(a: array?<A>)
{
  assume{:axiom} false;
}

type lowercase = ch | 'a' <= ch <= 'z' witness 'd'

method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
    requires rows >= 0 && cols >= 0
{
  assume{:axiom} false;
}

method PrintMatrix<A>(m: array2<A>)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
// </vc-spec>
// <vc-code>
{
  n := 0;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> a[k] != key
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}
// </vc-code>
