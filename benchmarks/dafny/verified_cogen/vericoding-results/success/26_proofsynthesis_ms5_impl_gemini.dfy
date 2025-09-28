// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ComputeSum(n: int): int
  requires n >= 0
{
  if n == 0 then 0 else 4 + ComputeSum(n-1)
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    modifies sum
    ensures
        sum[0] <= 4 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var total := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total == 4*i
  {
    total := total + 4;
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
