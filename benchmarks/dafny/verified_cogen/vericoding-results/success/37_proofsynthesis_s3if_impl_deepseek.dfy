// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma TripleLemma(n: int)
  requires n >= 0
  ensures 3 * n == n + n + n { }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 3 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var total := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total == 3 * i
  {
    total := total + 3;
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
