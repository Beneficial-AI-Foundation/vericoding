// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires b.Length == N
    requires sum.Length == 1
    requires N < 1000
    ensures forall k :: 0 <= k < N ==> a[k] == 2 * N + 1
    modifies a, b, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == 2 * N + 1
  {
    a[i] := 2 * N + 1;
    i := i + 1;
  }
}
// </vc-code>
