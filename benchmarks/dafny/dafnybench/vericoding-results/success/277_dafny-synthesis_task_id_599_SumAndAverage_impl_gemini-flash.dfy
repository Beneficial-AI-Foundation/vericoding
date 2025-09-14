

// <vc-helpers>
function SumUpTo(n: int): int
  requires n >= 0
  ensures SumUpTo(n) == n * (n + 1) / 2
{
  if n == 0 then 0 else n + SumUpTo(n - 1)
}
// </vc-helpers>

// <vc-spec>
method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
// </vc-spec>
// <vc-code>
{
  var s: int := 0;
  var i: int := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant s == SumUpTo(i - 1)
  {
    s := s + i;
    i := i + 1;
  }
  sum := s;
  average := sum as real / n as real;
}
// </vc-code>

