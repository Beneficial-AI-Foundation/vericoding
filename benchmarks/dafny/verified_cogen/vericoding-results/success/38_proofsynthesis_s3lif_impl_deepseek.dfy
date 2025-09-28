// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FourTimes(n: int): int { 4 * n }
lemma FourTimesLemma(n: int) 
  requires n > 0
  ensures FourTimes(n) == 4 * n 
{ }

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var total := 0;
  while i < N
    invariant i <= N
    invariant total == 4 * i
    decreases N - i
  {
    total := total + 4;
    i := i + 1;
  }
  assert total == 4 * N;
  sum[0] := total;
}
// </vc-code>
