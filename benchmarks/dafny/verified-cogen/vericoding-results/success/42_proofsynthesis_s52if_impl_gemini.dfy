// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SixTimes(n: int): int
  requires n >= 0
{
  if n == 0 then 0 else 6 + SixTimes(n - 1)
}

lemma LemmaSixTimes(n: int)
  requires n >= 0
  ensures SixTimes(n) == 6 * n
{
  if n > 0 {
    LemmaSixTimes(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 6 * N
// </vc-spec>
// <vc-code>
{
    var s: int := 0;
    var i: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant s == 6 * i
    {
        s := s + 6;
        i := i + 1;
    }
    sum[0] := s;
}
// </vc-code>
