// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumOfTwos(k: nat): int { 2 * k }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 2 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == 2
    invariant s == SumOfTwos(i)
    modifies a
    decreases N - i
  {
    a[i] := 2;
    s := s + a[i];
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
